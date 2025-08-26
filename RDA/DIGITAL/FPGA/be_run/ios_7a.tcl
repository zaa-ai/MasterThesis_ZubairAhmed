#
# Board: Xilinx Artix-7 FPGA-Modul (TE0725)
# Vendor: Trenz Electronic
# www: http://shop.trenz-electronic.de/de/TE0725-02-100-2C-Xilinx-Artix-7-FPGA-Modul-XC7A100T-2CSG324C-mit-2-x-50-Pin
#
# JTAG Adapter: XMOD FTDI JTAG Adapter (TE0790-02 )
# Vendor: Trenz Electronic
# www: http://shop.trenz-electronic.de/de/TE0790-02-XMOD-FTDI-JTAG-Adapter
#
# FPGA--Modul Pinout:
#
# J1-01  GND                            J2-01  GND
# J1-02  GND                            J2-02  GND
# J1-03  B35_L23_N   -> K1          J2-03  B34_L24_N   -> T8
# J1-04  B35_L23_P   -> K2          J2-04  B34_L24_P   -> R8
# J1-05  3.3V                       J2-05  3.3V
# J1-06  VCCIO35                    J2-06  VCCIO34
# J1-07  B35_L15_N   -> G2          J2-07  B34_L21_N   -> V9
# J1-08  B35_L15_P   -> H2          J2-08  B34_L21_P   -> U9
# J1-09  B35_L13_N   -> F3          J2-09  B34_L18_N   -> N6
# J1-10  B35_L13_P   -> F4          J2-10  B34_L18_P   -> M6
# J1-11  B35_L12_N   -> D3          J2-11  B34_L22_N   -> U6
# J1-12  B35_L12_P   -> E3          J2-12  B34_L22_P   -> U7
# J1-13  B35_L22_P   -> J3          J2-13  B34_L20_N   -> V6
# J1-14  B35_L22_N   -> J2          J2-14  B34_L20_P   -> V7
# J1-15  B35_L17_N   -> G1          J2-15  B34_L23_N   -> T6
# J1-16  B35_L17_P   -> H1          J2-16  B34_L23_P   -> R7
# J1-17  B35_L18_N   -> E1          J2-17  B34_L10_N   -> V4
# J1-18  B35_L18_P   -> F1          J2-18  B34_L10_P   -> V5
# J1-19  B35_L14_N   -> D2          J2-19  B34_L19_P   -> R6
# J1-20  B35_L14_P   -> E2          J2-20  B34_L19_N   -> R5
# J1-21  B35_L16_P   -> C2          J2-21  B34_L8_P    -> U4
# J1-22  B35_L16_N   -> C1          J2-22  B34_L8_N    -> U3
# J1-23  B35_L9_N    -> A1          J2-23  B34_L9_N    -> V2
# J1-24  B35_L9_P    -> B1          J2-24  B34_L9_P    -> U2
# J1-25  B35_L10_P   -> B3          J2-25  B34_L7_N    -> V1
# J1-26  B35_L10_N   -> B2          J2-26  B34_L7_P    -> U1
# J1-27  B35_L8_N    -> A3          J2-27  B34_L13_P   -> N5
# J1-28  B35_L8_P    -> A4          J2-28  B34_L13_N   -> P5
# J1-29  B35_L11_N   -> D4          J2-29  B34_L12_P   -> T5
# J1-30  B35_L11_P   -> D5          J2-30  B34_L12_N   -> T4
# J1-31  B35_L3_N    -> A5          J2-31  B34_L11_N   -> T3
# J1-32  B35_L3_P    -> A6          J2-32  B34_L11_P   -> R3
# J1-33  B35_L2_N    -> B6          J2-33  B34_L14_P   -> P4
# J1-34  B35_L2_P    -> B7          J2-34  B34_L14_N   -> P3
# J1-35  B35_L7_N    -> B4          J2-35  B34_L16_N   -> N4
# J1-36  B35_L7_P    -> C4          J2-36  B34_L16_P   -> M4
# J1-37  B35_L1_N    -> C5          J2-37  B34_L17_N   -> T1
# J1-38  B35_L1_P    -> C6          J2-38  B34_L17_P   -> R1
# J1-39  B35_L5_N    -> E5          J2-39  B34_L15_N   -> R2
# J1-40  B35_L5_P    -> E6          J2-40  B34_L15_P   -> P2
# J1-41  B35_L6_N    -> D7          J2-41  B34_L3_N    -> N1
# J1-42  B35_L6_P    -> E7          J2-42  B34_L3_P    -> N2
# J1-43  B35_L19_P   -> G6          J2-43  B34_L1_N    -> M1
# J1-44  B35_L19_N   -> F6          J2-44  B34_L1_P    -> L1
# J1-45  VCCIO35                    J2-45  VCCIO34
# J1-46  3.3V                       J2-46  3.3V
# J1-47  B35_L4_N    -> C7          J2-47  B34_L4_P    -> M3
# J1-48  B35_L4_P    -> D8          J2-48  B34_L4_N    -> M2
# J1-49  GND                        J2-49  GND
# J1-50  GND                        J2-50  GND

# CLK_SYS -> P17
# SYSLED -> M16
# UART_TXD -> L18
# UART_RXD -> M18
# XMOD_E -> M17
# UART_TXD       U1
# UART_RXD       P5

array set PORT_DEFINES {
    SYS_LED[0]        			  A8
    SYS_LED[1]        			  L15
    SYS_LED[2]        			  R17
    CLK_100           			  P17
    BUTTON[0]                             K13
    BUTTON[1]                             J13
    BUTTON[2]                             K15
    BUTTON[3]                             J15
    DBG_0                                  M3
    DBG_10                                 L3
    DBG_11                                 K3
    DBG_12                                 P5
    DBG_13                                 N5
    DBG_14                                 V4
    DBG_15                                 V5
    DBG_1                                  M2
    DBG_2                                  N2
    DBG_3                                  N1
    DBG_4                                  P4
    DBG_5                                  P3
    DBG_6                                  L1
    DBG_7                                  M1
    DBG_8                                  U2
    DBG_9                                  V2
    DSI_SUPPLY_OFF_1_TO_6_FPGA            E15
    DSI_SUPPLY_OFF_7_TO_12_FPGA           E16
    DUT_RESET                             L18
    LED[0]                                C11
    LED[1]                                C10
    LED[2]                                A10
    LED[3]                                 A9
    LED[4]                                 C9
    LED[5]                                 B9
    LED[6]                                 L6
    LED[7]                                 L5
    MAZ_JTAG_DBGRQ_GPIO02                 H15
    MAZ_JTAG_NTRST                        E18
    MAZ_JTAG_RTCK_GPIO01                  G18
    MAZ_JTAG_STRST                        J14
    MAZ_JTAG_TCK                          J17
    MAZ_JTAG_TDI_TDA                      D18
    MAZ_JTAG_TDO                          F18
    MAZ_JTAG_TMS                          J18
    NODE1_CLKREF                          N16
    NODE1_CSB                             M16
    NODE1_DBG[0]                          V11
    NODE1_DBG[1]                          V10
    NODE1_DBG[2]                          U12
    NODE1_DBG[3]                          V12
    NODE1_DBG[4]                          N14
    NODE1_DCR1B                            K2
    NODE1_DCR2B                            J2
    NODE1_DSI_OFF                         N15
    NODE1_INTB                             K1
    NODE1_MISO                             E5
    NODE1_MOSI                             E6
    NODE1_RESB                             F4
    NODE1_RFC                              J3
    NODE1_SCK                             M17
    NODE1_TESTMODE                         F3
    NODE2_CLKREF                           D4
    NODE2_CSB                              E3
    NODE2_DBG[0]                          P14
    NODE2_DBG[1]                           C5
    NODE2_DBG[2]                           C6
    NODE2_DBG[3]                           L4
    NODE2_DBG[4]                           K5
    NODE2_DCR1B                            F1
    NODE2_DCR2B                            C1
    NODE2_DSI_OFF                          D5
    NODE2_INTB                             E1
    NODE2_MISO                             G1
    NODE2_MOSI                             H1
    NODE2_RESB                             B1
    NODE2_RFC                              C2
    NODE2_SCK                              D3
    NODE2_TESTMODE                         A1
    NODE3_CLKREF                           B3
    NODE3_CSB                              A3
    NODE3_DBG[0]                           N6
    NODE3_DBG[1]                           M6
    NODE3_DBG[2]                           T8
    NODE3_DBG[3]                           R8
    NODE3_DBG[4]                          D13
    NODE3_DCR1B                            B6
    NODE3_DCR2B                            J5
    NODE3_DSI_OFF                          B2
    NODE3_INTB                             B7
    NODE3_MISO                             A6
    NODE3_MOSI                             A5
    NODE3_RESB                             D8
    NODE3_RFC                              F5
    NODE3_SCK                              A4
    NODE3_TESTMODE                         C7
    NODE4_CLKREF                           C4
    NODE4_CSB                              D7
    NODE4_DBG[0]                          A16
    NODE4_DBG[1]                          A15
    NODE4_DBG[2]                          G16
    NODE4_DBG[3]                          H16
    NODE4_DBG[4]                          F16
    NODE4_DCR1B                            G2
    NODE4_DCR2B                            G3
    NODE4_DSI_OFF                          B4
    NODE4_INTB                             H2
    NODE4_MISO                             G6
    NODE4_MOSI                             F6
    NODE4_RESB                             D2
    NODE4_RFC                              G4
    NODE4_SCK                              E7
    NODE4_TESTMODE                         E2
    NODE5_CLKREF                           J4
    NODE5_CSB                              H5
    NODE5_DBG[0]                          F15
    NODE5_DBG[1]                          A14
    NODE5_DBG[2]                          A13
    NODE5_DBG[3]                          C15
    NODE5_DBG[4]                          D15
    NODE5_DCR1B                           U11
    NODE5_DCR2B                           R15
    NODE5_DSI_OFF                          H4
    NODE5_INTB                            T11
    NODE5_MISO                            T10
    NODE5_MOSI                             T9
    NODE5_RESB                            T15
    NODE5_RFC                             P15
    NODE5_SCK                              H6
    NODE5_TESTMODE                        T14
    NODE6_CLKREF                          G17
    NODE6_CSB                             E17
    NODE6_DBG[0]                          A11
    NODE6_DBG[1]                          B11
    NODE6_DBG[2]                          R10
    NODE6_DBG[3]                          R13
    NODE6_DBG[4]                          R12
    NODE6_DCR1B                           D14
    NODE6_DCR2B                           N17
    NODE6_DSI_OFF                         H17
    NODE6_INTB                            C14
    NODE6_MISO                            C16
    NODE6_MOSI                            C17
    NODE6_RESB                            B13
    NODE6_RFC                             B14
    NODE6_SCK                             D17
    NODE6_TESTMODE                        C12
    NODE_SUPPLY_OFF_FPGA                  R16
    PICO[0]                                T1
    PICO[10]                               U6
    PICO[11]                               U7
    PICO[12]                               T3
    PICO[13]                               V6
    PICO[14]                               R2
    PICO[15]                               R3
    PICO[1]                                U1
    PICO[2]                                T4
    PICO[3]                                T5
    PICO[4]                                U4
    PICO[5]                                R1
    PICO[6]                                V1
    PICO[7]                                U3
    PICO[8]                                V7
    PICO[9]                                P2
    SW[1]                                  U9
    SW[2]                                  V9
    SW[3]                                  T6
    SW[4]                                  R7
    TP10                                  B12
    TP8                                   M13
    TP9                                   M18
    UMB_MISO                               R5
    UMB_MOSI                               M4
    UMB_SCK                                N4
    UMB_SCSN                               R6
    USB2SPI_GPIO[0]                       B18
    USB2SPI_GPIO[1]                       A18
    USB2SPI_GPIO[2]                       B17
    USB2SPI_GPIO[3]                       B16
    USB2SPI_MISO                          F14
    USB2SPI_MOSI                          F13
    USB2SPI_RESET                         G14
    USB2SPI_SCK                           H14
    USB2SPI_SS0O                          D12
}

foreach names [array names PORT_DEFINES] {
    if {[string length $names] > 0 && [string length $PORT_DEFINES($names)] > 0} {
	puts "$names is $PORT_DEFINES($names)"
	set_property PACKAGE_PIN $PORT_DEFINES($names) [get_ports $names]
	set_property IOSTANDARD LVCMOS33 [get_ports $names]
    }
}

#set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets dbg_clk_c]

set_property PULLDOWN true [get_ports USB2SPI_GPIO[0]]

# externes Reset auf RESB... MBIS DBG_5 / UMB DBG_7
set_property PULLUP true [get_ports DBG_5]
set_property PULLUP true [get_ports DBG_7]
# externes Reset parallel zum Pushbutton DUT_RESET
set_property PULLUP true [get_ports DBG_15]

#set_property PULLUP true [get_ports LIN_RXD2]
#set_property PULLUP true [get_ports LIN_RXD3]
#set_property PULLUP true [get_ports LIN_RXD4]
#
#set_property PULLUP true [get_ports NRESET]
#set_property PULLUP true [get_ports DBG_SWDATA]
#set_property PULLUP true [get_ports DBG_SWCLK]
#set_property PULLUP true [get_ports DBG_RESET]
#
#set_property DRIVE 16  [get_ports [list ADA_CONV]]
#set_property SLEW FAST [get_ports [list ADA_CONV]]

#
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 66 [current_design]
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR YES [current_design]
set_property BITSTREAM.CONFIG.M1PIN PULLNONE [current_design]
set_property BITSTREAM.CONFIG.M2PIN PULLNONE [current_design]
set_property BITSTREAM.CONFIG.M0PIN PULLNONE [current_design]
#
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
set_property CONFIG_MODE SPIx4 [current_design]

#
set_property BITSTREAM.CONFIG.USR_ACCESS TIMESTAMP [current_design]

