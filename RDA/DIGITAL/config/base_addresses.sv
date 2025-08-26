localparam shortint unsigned BASE_ADDR_INFO = 16'h0000;
localparam shortint unsigned SIZE_INFO = 16'h0020;
localparam shortint unsigned BASE_ADDR_SUPPLY = 16'h0000;
localparam shortint unsigned SIZE_SUPPLY = 16'h0040;
localparam shortint unsigned BASE_ADDR_TIMEBASE = 16'h0000;
localparam shortint unsigned SIZE_TIMEBASE = 16'h0050;
localparam shortint unsigned BASE_ADDR_INTERRUPT = 16'h0000;
localparam shortint unsigned SIZE_INTERRUPT = 16'h0060;
localparam shortint unsigned BASE_ADDR_BUFFER_IRQS = 16'h0000;
localparam shortint unsigned SIZE_BUFFER_IRQS = 16'h0070;
localparam shortint unsigned BASE_ADDR_SPI = 16'h0000;
localparam shortint unsigned SIZE_SPI = 16'h0090;
localparam shortint unsigned BASE_ADDR_DSI_COMMON = 16'h0000;
localparam shortint unsigned SIZE_DSI_COMMON = 16'h00a0;
localparam shortint unsigned BASE_ADDR_RAM = 16'h0400;
localparam shortint unsigned SIZE_RAM = 16'h0c00;
localparam shortint unsigned BASE_ADDR_OTP_CTRL = 16'h0000;
localparam shortint unsigned SIZE_OTP_CTRL = 16'h0074;
//DSI_Trimming_0 ist ein ARRAY! --> BASE_ADDR_DSI_TRIMMING : 16'h0010
//DSI_Trimming_1 ist ein ARRAY! --> BASE_ADDR_DSI_TRIMMING : 16'h0012
localparam shortint unsigned BASE_ADDR_GPIO = 16'h0000;
localparam shortint unsigned SIZE_GPIO = 16'h0010;
//DSI_0 ist ein ARRAY! --> BASE_ADDR_DSI : 16'h00a0
//DSI_1 ist ein ARRAY! --> BASE_ADDR_DSI : 16'h00c0
localparam shortint unsigned BASE_ADDR_SPI_CMD_STAT = 16'h0100;
localparam shortint unsigned SIZE_SPI_CMD_STAT = 16'h0010;
//DSI_CMD_STAT_0 ist ein ARRAY! --> BASE_ADDR_DSI_CMD_STAT : 16'h0110
//DSI_CMD_STAT_1 ist ein ARRAY! --> BASE_ADDR_DSI_CMD_STAT : 16'h0120
//DSI_CRM_STAT_0 ist ein ARRAY! --> BASE_ADDR_DSI_CRM_STAT : 16'h0130
//DSI_CRM_STAT_1 ist ein ARRAY! --> BASE_ADDR_DSI_CRM_STAT : 16'h0140
//DSI_PDCM_STAT_0 ist ein ARRAY! --> BASE_ADDR_DSI_PDCM_STAT : 16'h0150
//DSI_PDCM_STAT_1 ist ein ARRAY! --> BASE_ADDR_DSI_PDCM_STAT : 16'h0160
localparam shortint unsigned BASE_ADDR_SPI_CMD_BUF = 16'h0400;
localparam shortint unsigned SIZE_SPI_CMD_BUF = 16'h0100;
//DSI_CMD_BUF_0 ist ein ARRAY! --> BASE_ADDR_DSI_CMD_BUF : 16'h0500
//DSI_CMD_BUF_1 ist ein ARRAY! --> BASE_ADDR_DSI_CMD_BUF : 16'h0580
//DSI_CRM_BUF_0 ist ein ARRAY! --> BASE_ADDR_DSI_CRM_BUF : 16'h0600
//DSI_CRM_BUF_1 ist ein ARRAY! --> BASE_ADDR_DSI_CRM_BUF : 16'h0680
//DSI_TDMA_0 ist ein ARRAY! --> BASE_ADDR_DSI_TDMA : 16'h0700
//DSI_TDMA_1 ist ein ARRAY! --> BASE_ADDR_DSI_TDMA : 16'h0730
//DSI_PDCM_BUF_0 ist ein ARRAY! --> BASE_ADDR_DSI_PDCM_BUF : 16'h0800
//DSI_PDCM_BUF_1 ist ein ARRAY! --> BASE_ADDR_DSI_PDCM_BUF : 16'h0c00
localparam shortint unsigned BASE_ADDR_DSI_TRIMMING [0:1]= {16'h0010,16'h0012};
localparam shortint unsigned BASE_ADDR_DSI [0:1]= {16'h00a0,16'h00c0};
localparam shortint unsigned BASE_ADDR_DSI_CMD_STAT [0:1]= {16'h0110,16'h0120};
localparam shortint unsigned BASE_ADDR_DSI_CRM_STAT [0:1]= {16'h0130,16'h0140};
localparam shortint unsigned BASE_ADDR_DSI_PDCM_STAT [0:1]= {16'h0150,16'h0160};
localparam shortint unsigned BASE_ADDR_DSI_CMD_BUF [0:1]= {16'h0500,16'h0580};
localparam shortint unsigned BASE_ADDR_DSI_CRM_BUF [0:1]= {16'h0600,16'h0680};
localparam shortint unsigned BASE_ADDR_DSI_TDMA [0:1]= {16'h0700,16'h0730};
localparam shortint unsigned BASE_ADDR_DSI_PDCM_BUF [0:1]= {16'h0800,16'h0c00};
localparam shortint unsigned SIZE_DSI_TRIMMING = 16'h0002;
localparam shortint unsigned SIZE_DSI = 16'h0020;
localparam shortint unsigned SIZE_DSI_CMD_STAT = 16'h0010;
localparam shortint unsigned SIZE_DSI_CRM_STAT = 16'h0010;
localparam shortint unsigned SIZE_DSI_PDCM_STAT = 16'h0010;
localparam shortint unsigned SIZE_DSI_CMD_BUF = 16'h0080;
localparam shortint unsigned SIZE_DSI_CRM_BUF = 16'h0080;
localparam shortint unsigned SIZE_DSI_TDMA = 16'h0030;
localparam shortint unsigned SIZE_DSI_PDCM_BUF = 16'h0400;
