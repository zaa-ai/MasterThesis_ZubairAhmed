localparam shortint unsigned BASE_ADDR_TEST_TOP = 16'h0000;
localparam shortint unsigned SIZE_TEST_TOP = 16'h00ff;
localparam shortint unsigned BASE_ADDR_TEST_SUP = 16'h0010;
localparam shortint unsigned SIZE_TEST_SUP = 16'h0010;
localparam shortint unsigned BASE_ADDR_TEST_OSC = 16'h0020;
localparam shortint unsigned SIZE_TEST_OSC = 16'h0010;
//TEST_DSI_0 ist ein ARRAY! --> BASE_ADDR_TEST_DSI : 16'h0030
//TEST_DSI_1 ist ein ARRAY! --> BASE_ADDR_TEST_DSI : 16'h0040
localparam shortint unsigned BASE_ADDR_TEST_SCAN = 16'h00b0;
localparam shortint unsigned SIZE_TEST_SCAN = 16'h0010;
localparam shortint unsigned BASE_ADDR_TEST_SRAM = 16'h00c0;
localparam shortint unsigned SIZE_TEST_SRAM = 16'h0010;
localparam shortint unsigned BASE_ADDR_TEST_OTP_CONFIG = 16'h0000;
localparam shortint unsigned SIZE_TEST_OTP_CONFIG = 16'h00b0;
localparam shortint unsigned BASE_ADDR_TEST_OTP = 16'h0000;
localparam shortint unsigned SIZE_TEST_OTP = 16'h00b0;
localparam shortint unsigned BASE_ADDR_TEST_ELIP = 16'h0000;
localparam shortint unsigned SIZE_TEST_ELIP = 16'h00d0;
//TEST_WS_0 ist ein ARRAY! --> BASE_ADDR_TEST_WS : 16'h0050
//TEST_WS_1 ist ein ARRAY! --> BASE_ADDR_TEST_WS : 16'h0060
localparam shortint unsigned BASE_ADDR_TEST_DSI [0:1]= {16'h0030,16'h0040};
localparam shortint unsigned BASE_ADDR_TEST_WS [0:1]= {16'h0050,16'h0060};
localparam shortint unsigned SIZE_TEST_DSI = 16'h0010;
localparam shortint unsigned SIZE_TEST_WS = 16'h0010;
