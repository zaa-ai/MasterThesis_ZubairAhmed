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

array set PORT_DEFINES {
  CLK_100        F22
  LED0           K26
  ADC_SDO        K25
  ADC_SCK        M26
  ADC_CONV       N26
  DAC_SCK        L25
  DAC_CS         M25
  DAC_SDI        P26
  DAC_CLR        R26
  DRV_TDO        N24
  DRV_TDI        P24
  DRV_TCK        T25
  DRV_TMS        T24
  DRV_TMEN       N22
  AMP_DCLK       N21
  AMP_DIN        N23
  AMP_RTC        P23
  AMP_RTC_ON     R16
  NRESET         R17
  GPIO[0]        P21
  GPIO[1]        R21
  GPIO[2]        T17
  GPIO[3]        U17
  DBG_TST        P16
  DBG_SWCLK      N17
  DBG_SWDIO      L24
  DBG_SWO        M24
  DGB_RESET      M20
  DSI_CO         N19
  DSI_CS1        M22
  DSI_CS2        M21
  DSI_BUS        P18
  ST1[0]         R18
  ST1[1]         M19
  ST1[2]         N18
  ST1[3]         R23
  ST1[4]         R22
  ST1[5]         R20
  ST1[6]         T20
  ST1[7]         U19
  ST2[0]         U20
  ST2[1]         P19
  ST2[2]         P20
  ST2[3]         T19
  SCI_TXD        T18
  SCI_RXD        T22
  SCI_RTS        T23
  SCI_CTS        P25
  TMEN           R25
}

foreach names [array names PORT_DEFINES] {
  if {[string length $names] > 0 && [string length $PORT_DEFINES($names)] > 0} {
    puts "$names is $PORT_DEFINES($names)"
    set_property PACKAGE_PIN $PORT_DEFINES($names) [get_ports $names]
    set_property IOSTANDARD LVCMOS33 [get_ports $names]
  }
}

set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets swclk_c]

set_property PULLUP true [get_ports NRESET]
set_property PULLUP true [get_ports DBG_SWDIO]

set_property PULLDOWN true [get_ports SCI_RXD]

set_property PULLUP   true [get_ports ST1[0]]
set_property PULLUP   true [get_ports ST1[1]]
set_property PULLDOWN true [get_ports ST1[6]]
set_property PULLDOWN true [get_ports ST1[7]]
set_property PULLDOWN true [get_ports ST2[0]]
set_property PULLDOWN true [get_ports ST2[1]]
set_property PULLDOWN true [get_ports ST2[2]]
set_property PULLDOWN true [get_ports ST2[3]]

#
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

