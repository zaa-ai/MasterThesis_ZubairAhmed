/****************************************************************************
 * macro_defines_inc.sv
 ****************************************************************************/

/**
 * File : macro_defines_inc.sv
 * 
 * Description: Contents some useful project dependend macro definitions
 */


`define connect_52142_node(INDEX) \
opad opad_TESTMODE_NODE``INDEX``_inst (.PAD(NODE``INDEX``_TESTMODE), .I(jtag_master_trstn)); \
opad opad_TCK_NODE``INDEX``_inst      (.PAD(NODE``INDEX``_DCR2B   ), .I(jtag_master_tck  )); \
opad opad_TMS_NODE``INDEX``_inst      (.PAD(NODE``INDEX``_RFC     ), .I(dsi_tx_muxed[(``INDEX`` - 1) * 2])); \
opad opad_TDI_NODE``INDEX``_inst      (.PAD(NODE``INDEX``_DCR1B   ), .I(dsi_tx_muxed[(``INDEX`` * 2) - 1])); \
ipad ipad_RX2_L_TH_NODE``INDEX``_inst  (.PAD(NODE``INDEX``_MISO    ), .C(I_DSI_RXD1[ (``INDEX`` - 1) * 2]  )); \
ipad ipad_RX1_L_TH_NODE``INDEX``_inst  (.PAD(NODE``INDEX``_MOSI    ), .C(I_DSI_RXD2[ (``INDEX`` - 1) * 2]  )); \
ipad ipad_RX1_H_TH_NODE``INDEX``_inst  (.PAD(NODE``INDEX``_SCK     ), .C(I_DSI_RXD1[ (``INDEX`` * 2) - 1]  )); \
ipad ipad_RX2_H_TH_NODE``INDEX``_inst  (.PAD(NODE``INDEX``_CSB     ), .C(I_DSI_RXD2[ (``INDEX`` * 2) - 1]  )); \
opad opad_NODE``INDEX``_DSI_OFF_inst  (.PAD(NODE``INDEX``_DSI_OFF ), .I(1'b0)); 

