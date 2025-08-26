/*------------------------------------------------------------------------------
 * File          : packet_stat_multiplexer.sv
 * Project       : p52144
 * Author        : jvoi
 * Creation date : Mar 23, 2023
 * Description   :
 *------------------------------------------------------------------------------*/

module packet_stat_multiplexer import dsi3_pkg::*;  #() (
		input	channel_mode_t		i_mode,
		DSI3_channel_registers_PACKET_STAT_if.slave		to_register,
		DSI3_channel_registers_PACKET_STAT_if.master	from_crm,
		DSI3_channel_registers_PACKET_STAT_if.master	from_pdcm
	);
	
	`define to_register_if(_to_if_,_field_) to_register.``_field_``_in = _to_if_``.``_field_``_in ; \
			to_register.``_field_``_set = _to_if_``.``_field_``_set ;
	
	`define from_register_if(_to_if_,_field_) _to_if_``.``_field_ = to_register.``_field_;
    
    `define to_register(_to_if_) `to_register_if(_to_if_, CLK_ERR) \
        `to_register_if(_to_if_, CRC_ERR) \
        `to_register_if(_to_if_, SCE) \
        `to_register_if(_to_if_, SYMBOL_COUNT) \
        `to_register_if(_to_if_, SYMBOL_ERROR) \
        `to_register_if(_to_if_, TE) \
        `to_register_if(_to_if_, VDSI_ERR)
    
    `define from_register(_to_if_) `from_register_if(_to_if_, CLK_ERR) \
        `from_register_if(_to_if_, CRC_ERR) \
        `from_register_if(_to_if_, SCE) \
        `from_register_if(_to_if_, SYMBOL_COUNT) \
        `from_register_if(_to_if_, SYMBOL_ERROR) \
        `from_register_if(_to_if_, TE) \
        `from_register_if(_to_if_, VDSI_ERR) \
        _to_if_.value = to_register.value;
    
	
	always_comb begin
		case(i_mode)
			default: begin
                `to_register(from_crm)
			end
			MODE_PDCM: begin
                `to_register(from_pdcm)
			end
		endcase
	end
	
	always_comb begin
        `from_register(from_crm)
	end
	always_comb begin
        `from_register(from_pdcm)
	end
	
endmodule