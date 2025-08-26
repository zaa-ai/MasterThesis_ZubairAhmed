#
# Board: Xilinx Kintex-7 FPGA-Modul (TE0741)
# Vendor: Trenz Electronic
#
# JTAG Adapter: XMOD FTDI JTAG Adapter (TE0790-02 )
# Vendor: Trenz Electronic
#


array set PORT_DEFINES {
  CLK_100_P      F22
  CLK_100_N      E23
  EN_CLK         C26
  LED0           D26
  LED1           E26
  LED2           G21
  LED3           U21
  ADC_SDO        K26
  ADC_SCK        K25
  ADC_CONV       M26
  DAC_SCK        N26
  DAC_CS         L25
  DAC_SDI        M25
  DAC_CLR        P26
  DRV_DAMP_EN    R26
  DRV_P1         N24
  DRV_P2         P24
  DRV_PLOAD      T25
  DRV_PDRV       T24
  DRV_PSTOP      N22
  DRV_PSW1       N21
  DRV_PSW2       N23
  DRV_PSW3       P23
  DRV_PSW5       R16      
  AMP_DCLK       R17
  AMP_DIN        P21
  AMP_RTC        R21
  AMP_RTC_ON     P16
  NRESET         N17
  GPIO[0]        L24
  GPIO[1]        M24
  GPIO[2]        P18
  GPIO[3]        R18
  HVGPIO_EN      M19
  DBG_TST        V23
  DBG_SWCLK      V24
  DBG_SWDIO      W26
  DBG_SWO        W25
  DGB_RESET      W24
  LIN_RXD1       W23
  LIN_TXD1       AB26
  LIN_RXD2       AC26
  LIN_TXD2       AD25
  LIN_RXD3       AE25
  LIN_TXD3       AD26
  LIN_RXD4       AE26
  LIN_TXD4       AD24
  LIN_EN         AD23
  LIN_SW         W20
  ST1[0]         Y21
  ST1[1]         W21
  ST1[2]         V21
  ST1[3]         U26
  ST1[4]         V26
  ST1[5]         Y23
  ST1[6]         AA24
  ST1[7]         AC23
  ST2[0]         AC24
  ST2[1]         Y22
  ST2[2]         AA22
  ST2[3]         Y26
  UART_RTS       Y25
  UART_CTS       AA25
  TMEN           AB25
}

foreach names [array names PORT_DEFINES] {
  if {[string length $names] > 0 && [string length $PORT_DEFINES($names)] > 0} {
    puts "$names is $PORT_DEFINES($names)"
    set_property PACKAGE_PIN $PORT_DEFINES($names) [get_ports $names]
    set_property IOSTANDARD LVCMOS33 [get_ports $names]
  }
}

reset_property IOSTANDARD [get_ports CLK_100_P]
reset_property IOSTANDARD [get_ports CLK_100_N]
set_property IOSTANDARD LVDS_25 [get_ports CLK_100_N]
set_property IOSTANDARD LVDS_25 [get_ports CLK_100_P]

set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets swclk_c]

set_property PULLUP true [get_ports LIN_RXD1]
set_property PULLUP true [get_ports LIN_RXD2]
set_property PULLUP true [get_ports LIN_RXD3]
set_property PULLUP true [get_ports LIN_RXD4]

set_property PULLUP true [get_ports NRESET]
set_property PULLUP true [get_ports DBG_SWDIO]

#set_property PULLDOWN true [get_ports UART_RXD]

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

