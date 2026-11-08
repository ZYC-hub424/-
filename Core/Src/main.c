/* USER CODE BEGIN Header */
/**
  ******************************************************************************
  * @file           : main.c
  * @brief          : Main program body
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; Copyright (c) 2026 STMicroelectronics.
  * All rights reserved.</center></h2>
  *
  * This software component is licensed by ST under BSD 3-Clause license,
  * the "License"; You may not use this file except in compliance with the
  * License. You may obtain a copy of the License at:
  *                        opensource.org/licenses/BSD-3-Clause
  *
  ******************************************************************************
  */
/* USER CODE END Header */
/* Includes ------------------------------------------------------------------*/
#include "main.h"
#include "adc.h"
#include "dma.h"
#include "tim.h"
#include "usart.h"
#include "gpio.h"

/* Private includes ----------------------------------------------------------*/
/* USER CODE BEGIN Includes */
#include <stdio.h>
#include <string.h>

/* USER CODE END Includes */

/* Private typedef -----------------------------------------------------------*/
/* USER CODE BEGIN PTD */

/* USER CODE END PTD */

/* Private define ------------------------------------------------------------*/
/* USER CODE BEGIN PD */
//每帧参数
#define APP_NPTS 100u //每帧每通道的采样点数
#define APP_FRAME_LEN 456u //上行帧总字节数
#define APP_DIV_NUM 3u //档位数量：10ms/5ms/1ms每格
#define APP_FRAME_PERIOD 20u //两帧最小间隔（ms）

//调试用USART1，发送用(&huart6)/USART6
#define APP_UART            (&huart6)
#define APP_UART_INST       USART6

//帧字节偏移
#define F_HEAD0 0u //AA
#define F_HEAD1 1u //55
#define F_SEQ 2u //帧序号0~255
#define F_FLAGS 3u //通道使能位图 bit0~bit4
#define F_DIV 4u //档位号0~2
#define F_TRIGSRC 5u //触发源（基础部分没有触发）
#define F_TRIGPOS 6u //触发点（无触发为0xFF）
#define F_NPTS 7u //点数，恒100
#define F_CH1 8u //CH1[100] 200字节
#define F_CH2 208u //CH2[100] 200字节
#define F_DIG 408u //DIG[3][13] 39字节
#define F_DT 447u //采样间隔us，uint16奇数偏移
#define F_ACK 449u //最近执行的下行命令码
#define F_TAIL 450u //5A
#define F_EXT 451u //扩展5字节：FREQ1(2) FREQ2(2) WAVE_EN(1)，之前自发自收加的，现在没用了

//下行命令码
#define CMD_SET_DIV 0x01u //档位设置
#define CMD_SET_CH_EN 0x02u //通道使能设置
#define CMD_SET_WAVE_HZ 0x04u //矩形波频率设置
#define CMD_SET_WAVE_EN 0x05u //矩形波使能，0无/1有
#define CMD_GET_STATUS 0x06u //空

//数字通道
#define DIG1_PORT GPIOI
#define DIG1_PIN GPIO_PIN_3 //PI3
#define DIG2_PORT GPIOG
#define DIG2_PIN GPIO_PIN_6 //PG6
#define DIG3_PORT GPIOG
#define DIG3_PIN GPIO_PIN_7 //PG7

//矩形波发生器输出
#define WAVE_BASE_HZ 1000000u //PSC分频之后的频率
#define WAVE_HZ_MIN 100u //100hz
#define WAVE_HZ_MAX 10000u //10khz
/* USER CODE END PD */

/* Private macro -------------------------------------------------------------*/
/* USER CODE BEGIN PM */

/* USER CODE END PM */

/* Private variables ---------------------------------------------------------*/

/* USER CODE BEGIN PV */
//运行状态
static uint8_t g_div=0u;//显示档位
static uint16_t g_dt_us=200u;//采样间隔（us）
static uint8_t g_ch_en=0x1Fu;//通道使能
static uint8_t g_seq=0u;//帧序号
static uint8_t g_ack=0u;//执行成功的命令
static uint8_t g_trig_src=0u;//触发源，基础部分为0
//数字通道采集缓冲
//TIM2中断写入，切换半区时清零新半区
static uint8_t g_dig[2][3u*13u];//两半交替写，每半3通道×13字节=39字节，13x8=104刚好能装100个点
static volatile uint8_t g_dig_w=0u;//正在写的半区，0对应采样点0~99，1对应100~199
static uint8_t g_dig_idx=0u;//采样点号
//PWM
static uint16_t g_wave_hz=1000u;//初始1000hz
//ADC缓冲
static uint16_t g_adc_buf[4u*APP_NPTS];
//双缓冲
static uint16_t g_snap[2][2u*APP_NPTS];
static uint8_t g_snap_dig[2][3u*13u];
static volatile uint8_t g_snap_w =0u; //最近写完的下标
static volatile uint32_t g_snap_seq =0u; //写入完成数量
static volatile uint8_t g_drop= 0u; //切档位后待丢弃份数
//串口收发
static uint8_t g_rx[16]; //循环DMA接收缓冲
static volatile uint8_t g_tx_busy =0u; //DMA发送空闲标志
static uint32_t g_tx_last =0u; //上次发包的时间
static uint8_t g_rx_win[8]; //命令8字节滑动窗口
static uint16_t g_rx_pos =0u; //已填满到的下标
//发送帧缓冲
static uint8_t g_frame[APP_FRAME_LEN] __attribute__((aligned(4)));//按四字节对齐
//ADC溢出次数
static volatile uint32_t g_ovr_cnt =0u;
/* USER CODE END PV */

/* Private function prototypes -----------------------------------------------*/
void SystemClock_Config(void);
/* USER CODE BEGIN PFP */
//函数声明
static void app_apply_div(uint8_t div);
static void app_wave_hz(uint16_t hz);
static uint8_t app_dig_level(void);
static void app_dig_push(uint8_t lv);
static void app_snap_write(const uint16_t *src,const uint8_t *dig);
static int app_snap_read(uint16_t *dst,uint8_t *dst_dig);
static void app_frame_build(const uint16_t *src,const uint8_t *dig);
static void app_rx_poll(void);
static void app_cmd_exec(uint8_t cmd,uint8_t a0,uint8_t a1);
static void app_init(void);
static void app_task(void);
/* USER CODE END PFP */

/* Private user code ---------------------------------------------------------*/
/* USER CODE BEGIN 0 */
//三个显示档位
static const uint16_t k_dt_us[APP_DIV_NUM] ={200u,100u,20u}; //采样点间隔，10，5，1ms
static const uint16_t k_t2_arr[APP_DIV_NUM] ={5399u,2699u,539u}; //ARR=DT*27-1，PSC=3
/* USER CODE END 0 */

/**
  * @brief  The application entry point.
  * @retval int
  */
int main(void)
{
  /* USER CODE BEGIN 1 */

  /* USER CODE END 1 */

  /* MCU Configuration--------------------------------------------------------*/

  /* Reset of all peripherals, Initializes the Flash interface and the Systick. */
  HAL_Init();

  /* USER CODE BEGIN Init */

  /* USER CODE END Init */

  /* Configure the system clock */
  SystemClock_Config();

  /* USER CODE BEGIN SysInit */

  /* USER CODE END SysInit */

  /* Initialize all configured peripherals */
  MX_GPIO_Init();
  MX_DMA_Init();
  MX_USART6_UART_Init();
  MX_ADC3_Init();
  MX_USART1_UART_Init();
  MX_TIM2_Init();
  MX_TIM3_Init();
  /* USER CODE BEGIN 2 */
  app_init();
  /* USER CODE END 2 */

  /* Infinite loop */
  /* USER CODE BEGIN WHILE */
  while (1)
  {
	  app_task();
    /* USER CODE END WHILE */

    /* USER CODE BEGIN 3 */
  }
  /* USER CODE END 3 */
}

/**
  * @brief System Clock Configuration
  * @retval None
  */
void SystemClock_Config(void)
{
  RCC_OscInitTypeDef RCC_OscInitStruct = {0};
  RCC_ClkInitTypeDef RCC_ClkInitStruct = {0};
  RCC_PeriphCLKInitTypeDef PeriphClkInitStruct = {0};

  /** Configure the main internal regulator output voltage
  */
  __HAL_RCC_PWR_CLK_ENABLE();
  __HAL_PWR_VOLTAGESCALING_CONFIG(PWR_REGULATOR_VOLTAGE_SCALE1);
  /** Initializes the RCC Oscillators according to the specified parameters
  * in the RCC_OscInitTypeDef structure.
  */
  RCC_OscInitStruct.OscillatorType = RCC_OSCILLATORTYPE_HSE;
  RCC_OscInitStruct.HSEState = RCC_HSE_ON;
  RCC_OscInitStruct.PLL.PLLState = RCC_PLL_ON;
  RCC_OscInitStruct.PLL.PLLSource = RCC_PLLSOURCE_HSE;
  RCC_OscInitStruct.PLL.PLLM = 25;
  RCC_OscInitStruct.PLL.PLLN = 432;
  RCC_OscInitStruct.PLL.PLLP = RCC_PLLP_DIV2;
  RCC_OscInitStruct.PLL.PLLQ = 2;
  if (HAL_RCC_OscConfig(&RCC_OscInitStruct) != HAL_OK)
  {
    Error_Handler();
  }
  /** Activate the Over-Drive mode
  */
  if (HAL_PWREx_EnableOverDrive() != HAL_OK)
  {
    Error_Handler();
  }
  /** Initializes the CPU, AHB and APB buses clocks
  */
  RCC_ClkInitStruct.ClockType = RCC_CLOCKTYPE_HCLK|RCC_CLOCKTYPE_SYSCLK
                              |RCC_CLOCKTYPE_PCLK1|RCC_CLOCKTYPE_PCLK2;
  RCC_ClkInitStruct.SYSCLKSource = RCC_SYSCLKSOURCE_PLLCLK;
  RCC_ClkInitStruct.AHBCLKDivider = RCC_SYSCLK_DIV1;
  RCC_ClkInitStruct.APB1CLKDivider = RCC_HCLK_DIV4;
  RCC_ClkInitStruct.APB2CLKDivider = RCC_HCLK_DIV2;

  if (HAL_RCC_ClockConfig(&RCC_ClkInitStruct, FLASH_LATENCY_7) != HAL_OK)
  {
    Error_Handler();
  }
  PeriphClkInitStruct.PeriphClockSelection = RCC_PERIPHCLK_USART1|RCC_PERIPHCLK_USART6;
  PeriphClkInitStruct.Usart1ClockSelection = RCC_USART1CLKSOURCE_PCLK2;
  PeriphClkInitStruct.Usart6ClockSelection = RCC_USART6CLKSOURCE_PCLK2;
  if (HAL_RCCEx_PeriphCLKConfig(&PeriphClkInitStruct) != HAL_OK)
  {
    Error_Handler();
  }
}

/* USER CODE BEGIN 4 */
//读取数字通道引脚状态
static uint8_t app_dig_level(void)
{
	uint8_t lv=0u;
	if((DIG1_PORT->IDR & DIG1_PIN)!=0u)
		lv|=0x01u;//0000 0001
	if((DIG2_PORT->IDR & DIG2_PIN)!=0u)
		lv|=0x02u;//0000 0010
	if((DIG3_PORT->IDR & DIG3_PIN)!=0u)
		lv|=0x04u;//0000 0100
	return lv;
}

//设置矩形波发生器频率
static void app_wave_hz(uint16_t hz)
{
	uint32_t arr,crr;
	if(hz<WAVE_HZ_MIN)
		hz=WAVE_HZ_MIN;
	if(hz>WAVE_HZ_MAX)
		hz=WAVE_HZ_MAX;
	arr=WAVE_BASE_HZ/(uint32_t)hz;
	if(arr==0u)
		arr=1u;
	arr-=1u;
	crr=(arr+1u)/2u;//占空比50%
	g_wave_hz=hz;
	__HAL_TIM_SET_AUTORELOAD(&htim3,arr);
	__HAL_TIM_SET_COMPARE(&htim3,TIM_CHANNEL_1,crr);
	htim3.Instance->EGR=TIM_EGR_UG;//更改事件产生寄存器，立即修改ARR和CRR
}

//切换档位
static void app_apply_div(uint8_t div)
{
	if(div>=APP_DIV_NUM)
		div=0u;
	g_div=div;
	g_dt_us=k_dt_us[div];
	__HAL_TIM_SET_AUTORELOAD(&htim2,k_t2_arr[div]);
	__HAL_TIM_SET_COUNTER(&htim2,0u);
	htim2.Instance->EGR=TIM_EGR_UG;//重启TIM2
	g_drop=2u;//丢弃之前采的完整的，现在没采完的
}

//双缓冲读取
static void app_snap_write(const uint16_t *src,const uint8_t *dig)
{
	uint8_t w=(uint8_t)(g_snap_w^1u); //缓冲复制另外一份
	memcpy(g_snap[w],src,2u*APP_NPTS*sizeof(uint16_t));
	memcpy(g_snap_dig[w],dig,3u*13u);
	g_snap_w=w;
	g_snap_seq++; //写入数量加一
}

static int app_snap_read(uint16_t *dst, uint8_t *dst_dig)
{
	uint32_t s1,s2;
	uint8_t idx;
	idx=g_snap_w;
	s1=g_snap_seq;
	if(s1==0u)
		return 0;//第一帧处理
	memcpy(dst,g_snap[idx],2u*APP_NPTS*sizeof(uint16_t));
	memcpy(dst_dig,g_snap_dig[idx],3u*13u);
	s2=g_snap_seq;
	return (s1==s2)?1:0;//防止中断打断
}

//数字通道电平写入位图
static void app_dig_push(uint8_t lv)
{
	uint8_t *d=g_dig[g_dig_w];
	uint8_t bi=(uint8_t)(g_dig_idx>>3);//求字节偏移
	uint8_t mk=(uint8_t)(1u<<(g_dig_idx&7u));//求字节内位偏移并生成掩码
	if((lv & 0x01u)!=0u)
		d[bi]|=mk;
	if((lv & 0x02u)!=0u)
		d[13u+bi]|=mk;
	if((lv & 0x04u)!=0u)
		d[26u+bi]|=mk;
	g_dig_idx++;
	if(g_dig_idx>=APP_NPTS)
	{
		g_dig_idx=0u;
		g_dig_w^=1u;//换半区
		memset(g_dig[g_dig_w],0,39u);//清空下一个要写入的半区
	}
}

//组帧
static void app_frame_build(const uint16_t *src,const uint8_t *dig)
{
	uint16_t *p1=(uint16_t *)&g_frame[F_CH1];
	uint16_t *p2=(uint16_t *)&g_frame[F_CH2];
	uint32_t i;
	uint8_t div=g_div;
	uint16_t dt_us=g_dt_us;
	uint8_t ch_en=g_ch_en;
	uint8_t trig=g_trig_src;
	uint8_t ack=g_ack;
	uint8_t seq=g_seq;
	uint16_t wave=g_wave_hz;
	//解交织
	for(i=0u;i<APP_NPTS;i++)
	{
		p1[i]=src[2u*i];//电位器
		p2[i]=src[2u*i+1u];//麦克风
	}
	//数字位图
	memcpy(&g_frame[F_DIG],dig,39u);
	//帧头
  g_frame[F_HEAD0]=0xAAu;
  g_frame[F_HEAD1]=0x55u;
  g_frame[F_NPTS]=(uint8_t)APP_NPTS;
	g_frame[F_SEQ]=seq;
	g_frame[F_FLAGS]=(uint8_t)(ch_en & 0x1Fu);//没有触发
	g_frame[F_DIV]=div;
	g_frame[F_ACK]=ack;
	g_frame[F_TRIGSRC]=trig;
	g_frame[F_TRIGPOS]=0xFFu;//0xFF表示无触发
	//时间基准
	g_frame[F_DT]=(uint8_t)(dt_us & 0xFFu);
	g_frame[F_DT+1u]=(uint8_t)(dt_us>>8);//高字节在后
	//帧尾
	g_frame[F_TAIL]=0x5Au;
	//帧尾扩展部分
	g_frame[F_EXT]=(uint8_t)(wave & 0xFFu);
	g_frame[F_EXT+1u]=(uint8_t)(wave>>8);//矩形波发生器的频率
	g_frame[F_EXT+2u]=0u;
	g_frame[F_EXT+3u]=0u;
	g_frame[F_EXT+4u]=1u;//数字通道采集的外部信号
	//帧序号加一
	g_seq=(uint8_t)(seq+1u);//（uint8_t）截断可以实现自动重排
}

//接受命令，滑动窗口搜索帧头帧尾
static void app_rx_poll(void)
{
    uint16_t ndtr=(uint16_t)__HAL_DMA_GET_COUNTER(APP_UART->hdmarx);
    uint16_t head=(uint16_t)((16u-ndtr)&15u);//循环下标，（16-NDTR）&15，NDTR记录的是缓冲区剩余量
    while(g_rx_pos!=head)
    {
    	uint8_t b=g_rx[g_rx_pos];
        g_rx_pos=(uint16_t)((g_rx_pos+1u)&15u);//下标右移一位
        //窗口左移一字节，新字节放末尾
        uint8_t i;
        for(i=1u;i<8u;i++)
        {
            g_rx_win[i-1u]=g_rx_win[i];
        }
        g_rx_win[7]=b;
        //找到帧头和帧尾就执行命令
        if ((g_rx_win[0]==0xAAu)&&(g_rx_win[1]==0x55u)&&(g_rx_win[7]==0x5Au))
            app_cmd_exec(g_rx_win[2], g_rx_win[3], g_rx_win[4]);
    }
}

//执行命令，3号命令是设置触发，未使用
static void app_cmd_exec(uint8_t cmd,uint8_t a0,uint8_t a1)
{
    uint16_t hz;
    switch (cmd)
    {
    case CMD_SET_DIV://切档位
        if(a0<APP_DIV_NUM)
        {
            app_apply_div(a0);
            g_ack=CMD_SET_DIV;
        }
        break;
    case CMD_SET_CH_EN://通道使能
        g_ch_en=(uint8_t)(a0 & 0x1Fu);
        g_ack=CMD_SET_CH_EN;
        break;
    case CMD_SET_WAVE_HZ://设置矩形波输出频率
        hz=(uint16_t)((uint16_t)a0 | ((uint16_t)a1 << 8));
        app_wave_hz(hz);
        g_ack=CMD_SET_WAVE_HZ;
        break;
    case CMD_SET_WAVE_EN://矩形波输出使能
        if(a0!=0u)
        	HAL_TIM_PWM_Start(&htim3,TIM_CHANNEL_1);
        else
        	HAL_TIM_PWM_Stop(&htim3,TIM_CHANNEL_1);
        g_ack=CMD_SET_WAVE_EN;
        break;
    case CMD_GET_STATUS://回执
        g_ack=CMD_GET_STATUS;
        break;
    default:
        break;
    }
}

//初始化
static void app_init(void)
{
    //帧静态段
    memset(g_frame,0,sizeof(g_frame));
    //档位
    app_apply_div(0u);
    //矩形波发生器
    app_wave_hz(g_wave_hz);
    HAL_TIM_PWM_Start(&htim3, TIM_CHANNEL_1);
    //清空数字通道位图缓冲
    memset(g_dig,0,sizeof(g_dig));
    //启动命令接收
    HAL_UART_Receive_DMA(APP_UART,g_rx,(uint16_t)sizeof(g_rx));
    //启动ADC+DMA
    HAL_ADC_Start_DMA(&hadc3,(uint32_t *)g_adc_buf,4u*APP_NPTS);
    //改软件触发
    ADC3->CR2 &= ~ADC_CR2_EXTEN;
    //启动TIM2更新中断，由中断发起SWSTART
    HAL_TIM_Base_Start_IT(&htim2);
}

//主循环任务
static void app_task(void)
{
    static uint16_t buf[2u*APP_NPTS];
    static uint8_t digbuf[3u*13u];
    //命令解析
    app_rx_poll();
    //上一帧DMA还没发完
    if(g_tx_busy!=0u)
    	return;
    //距上一帧不足20ms，返回，串口速率限制
    if((HAL_GetTick()-g_tx_last)<APP_FRAME_PERIOD)
    	return;
    //读缓存的时候被中断打断了
    if(app_snap_read(buf, digbuf)==0)
    	return;
    //组帧并启动DMA发送
    app_frame_build(buf, digbuf);

    if (HAL_UART_Transmit_DMA(APP_UART,g_frame,APP_FRAME_LEN)==HAL_OK)//串口发送成功
    {
        g_tx_busy=1u;
        g_tx_last=HAL_GetTick();
    }
}

//TIM2中断触发位图写入和ADC采样
void HAL_TIM_PeriodElapsedCallback(TIM_HandleTypeDef *htim)
{
    if (htim->Instance==TIM2)
    {
    	app_dig_push(app_dig_level());
    	ADC3->CR2|=ADC_CR2_SWSTART;//为了控制采样率和通道确定采用中断里面触发ADC
    }
    else
    	return;
}

//ADC半满、全满、错误回调函数
void HAL_ADC_ConvHalfCpltCallback(ADC_HandleTypeDef* hadc)//半满
{
	if(hadc->Instance!=ADC3)
		return;
	if(g_drop!=0u)
	{
		g_drop--;
		return;
	}
	app_snap_write(&g_adc_buf[0],g_dig[g_dig_w^1u]);
}

void HAL_ADC_ConvCpltCallback(ADC_HandleTypeDef* hadc)//全满
{
	if(hadc->Instance!=ADC3)
		return;
	if(g_drop!=0u)
	{
		g_drop--;
		return;
	}
	app_snap_write(&g_adc_buf[2u*APP_NPTS],g_dig[g_dig_w^1u]);
}

void HAL_ADC_ErrorCallback(ADC_HandleTypeDef *hadc)//溢出
{
	if(hadc->Instance!=ADC3)
		return;
	__HAL_ADC_CLEAR_FLAG(hadc,ADC_FLAG_OVR);
	g_ovr_cnt++;
}

//串口发送完成、出错
void HAL_UART_TxCpltCallback(UART_HandleTypeDef *huart)//发送完成
{
    if(huart->Instance!=APP_UART_INST)
    	return;
    g_tx_busy=0u;//发送空闲
}

void HAL_UART_ErrorCallback(UART_HandleTypeDef *huart)//出错
{
    if(huart->Instance!=APP_UART_INST)
    	return;
    if(huart->RxState==HAL_UART_STATE_READY)//HAL_UART_Receive_DMA()在串口处于占用时调用会返回HAL_BUSY，不会重新接收
        HAL_UART_Receive_DMA(APP_UART,g_rx,(uint16_t)sizeof(g_rx));
}

/* USER CODE END 4 */

/**
  * @brief  This function is executed in case of error occurrence.
  * @retval None
  */
void Error_Handler(void)
{
  /* USER CODE BEGIN Error_Handler_Debug */
  /* User can add his own implementation to report the HAL error return state */
  __disable_irq();
  while (1)
  {
  }
  /* USER CODE END Error_Handler_Debug */
}

#ifdef  USE_FULL_ASSERT
/**
  * @brief  Reports the name of the source file and the source line number
  *         where the assert_param error has occurred.
  * @param  file: pointer to the source file name
  * @param  line: assert_param error line source number
  * @retval None
  */
void assert_failed(uint8_t *file, uint32_t line)
{
  /* USER CODE BEGIN 6 */
  /* User can add his own implementation to report the file name and line number,
     ex: printf("Wrong parameters value: file %s on line %d\r\n", file, line) */
  /* USER CODE END 6 */
}
#endif /* USE_FULL_ASSERT */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
