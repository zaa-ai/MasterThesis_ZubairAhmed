`define dr_length 28
`define ir_length 8

typedef struct packed {
	logic [`ir_length-1:0] ir;
	logic [`dr_length-1:0] dr;
} t_irdr;
/*
•   JTAG einschalten
    o   TMODE = High
    o   IR_TMR_DIG_OUT_GPIO.ENINTB (0xcb) = 1 -> Bit 28
    o   IR_TMR_DIG_OUT_GPIO.SELINTB = 2 -> enable TDO

•   Analog TX schalten
    o   IR_TMR_DIG_IN (0xce) = 0b1xxx1xxx (xxx: TX2, TX1)
        0   CSB
        1   SCK
        2   MOSI
        3   MISO
        4   RFC
        5   DCR2B
        6   DCR1B
        7   INTB
        TX2 EN, RFC, TX1 EN, DCR1B -> 'h9A
•   Analog RX schalten: Je nach Pin, noch nicht festgelegt
    o   IR_TMR_DIG_OUT_SPI (0xca)
    o   IR_TMR_DIG_OUT_GPIO (0xcb)
        3   DSI3 receiver   rxd1[0] Receiver lower threshold for Channel 1 -> CSB
        4   DSI3 receiver   rxd1[1] Receiver lower threshold for Channel 2 -> SCK
        5   DSI3 receiver   rxd2[0] Receiver higher threshold for Channel 1 -> MOSI
        6   DSI3 receiver   rxd2[1] Receiver higher threshold for Channel 2 -> MISO
 */

/* TMR_DIG_IN */

`define TMR_DIG_IN 8'h0
`define IR_TMR_DIG_IN 8'hce
`define EXTENDED_TMR_DIG_IN 28'b0
`define LSB_VALUE_EXTENDED_TMR_DIG_IN 20

`define BIT_EN_TX2  7
`define LSB_PIN_TX2 4
`define BIT_EN_TX1 3
`define LSB_PIN_TX1 0

`define VALUE_PIN_TMR_DIG_IN_CSB    3'h0
`define VALUE_PIN_TMR_DIG_IN_SCK    3'h1
`define VALUE_PIN_TMR_DIG_IN_MOSI   3'h2
`define VALUE_PIN_TMR_DIG_IN_MISO   3'h3
`define VALUE_PIN_TMR_DIG_IN_RFC    3'h4
`define VALUE_PIN_TMR_DIG_IN_DCR2B  3'h5
`define VALUE_PIN_TMR_DIG_IN_DCR1B  3'h6
`define VALUE_PIN_TMR_DIG_IN_INTB   3'h7

`define VALUE_TMR_DIG_IN (`TMR_DIG_IN | 1'b1 << `BIT_EN_TX2  | \
`VALUE_PIN_TMR_DIG_IN_DCR1B << `LSB_PIN_TX2 | \
1'b1 << `BIT_EN_TX1  | \
`VALUE_PIN_TMR_DIG_IN_RFC << `LSB_PIN_TX1 )

/*DR data should be left aligned*/
`define VALUE_EXTENDED_TMR_DIG_IN (`EXTENDED_TMR_DIG_IN | `VALUE_TMR_DIG_IN << `LSB_VALUE_EXTENDED_TMR_DIG_IN)

/* TMR_DIG_OUT_SPI */

`define  TMR_DIG_OUT_SPI    28'h0
`define  IR_TMR_DIG_OUT_SPI  8'hca

`define  Receiver_lower_threshold_for_Channel_1   6'h03
`define  Receiver_lower_threshold_for_Channel_2   6'h04
`define  Receiver_higher_threshold_for_Channel_1  6'h05
`define  Receiver_higher_threshold_for_Channel_2  6'h06

`define  BIT_TMR_DIG_OUT_SPI_ENMOSI 27
`define  LSB_TMR_DIG_OUT_SPI_MOSI   21
`define  BIT_TMR_DIG_OUT_SPI_ENMISO 20
`define  LSB_TMR_DIG_OUT_SPI_MISO   14
`define  BIT_TMR_DIG_OUT_SPI_ENSCK  13
`define  LSB_TMR_DIG_OUT_SPI_SCK     7
`define  BIT_TMR_DIG_OUT_SPI_ENCSB   6
`define  LSB_TMR_DIG_OUT_SPI_CSB     0

`define VALUE_TMR_DIG_OUT_SPI  (`TMR_DIG_OUT_SPI | \
1'b1                        			 <<  `BIT_TMR_DIG_OUT_SPI_ENMOSI | \
`Receiver_lower_threshold_for_Channel_1  << `LSB_TMR_DIG_OUT_SPI_MOSI | \
1'b1                        			 <<  `BIT_TMR_DIG_OUT_SPI_ENMISO | \
`Receiver_higher_threshold_for_Channel_1 << `LSB_TMR_DIG_OUT_SPI_MISO | \
1'b1                        			 <<  `BIT_TMR_DIG_OUT_SPI_ENSCK | \
`Receiver_lower_threshold_for_Channel_2  << `LSB_TMR_DIG_OUT_SPI_SCK | \
1'b1                     				 <<  `BIT_TMR_DIG_OUT_SPI_ENCSB | \
`Receiver_higher_threshold_for_Channel_2 << `LSB_TMR_DIG_OUT_SPI_CSB)

localparam t_irdr [1:0] mem  = {{`IR_TMR_DIG_IN,`VALUE_EXTENDED_TMR_DIG_IN},{`IR_TMR_DIG_OUT_SPI,`VALUE_TMR_DIG_OUT_SPI}};
