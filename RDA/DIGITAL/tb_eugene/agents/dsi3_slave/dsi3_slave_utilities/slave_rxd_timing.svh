/**
 * Class: slave_rxd_timing
 * 
 * Contains the timing information for the DSI3 receiver hardware
 */
class slave_rxd_timing;
	
	int		info_corner;
	int		info_temp__j__;
	real	info_i__quite_rec__;
	real	info_dtr__ib__;
	real	info_i__offset_rec__;
	real	info_i__max_slave__;
	real	info_c__dsi_bus__;
	real	info_r__dsi_bus__;
	
	time t_rxd1[2:0][2:0];
	time t_rxd2[2:0][2:0];
	
	virtual function string to_string();
		return $sformatf("Corner=%1d, Temp=%3d°C, Iq=%2.1fmA, Trim_Ib=%1d, I_Offset_Rec=%2.1fmA, I_max_slave=%2.1fmA, Cbus=%2.1fnF, Rbus=%2.1f",
				info_corner, info_temp__j__, info_i__quite_rec__*1000.0, info_dtr__ib__, info_i__offset_rec__*1000.0, info_i__max_slave__*1000.0, info_c__dsi_bus__*1000000000.0, info_r__dsi_bus__);
	endfunction
	
	virtual function string get_table_string();
		return $sformatf(" %4d  | %3d   | %4.1fmA |    %2d   |   %4.1fmA | %4.1fmA | %2.1fnF | %2.1f",
				info_corner, info_temp__j__, info_i__quite_rec__*1000.0, int'(info_dtr__ib__), info_i__offset_rec__*1000.0, info_i__max_slave__*1000.0, info_c__dsi_bus__*1000000000.0, info_r__dsi_bus__);		
	endfunction
		
	virtual function string get_table_header();
		return $sformatf("Corner | Temp  |   Iq   | Trim_Ib | I_OffRec |  I_max |  Cbus  |  Rbus  ");
	endfunction

endclass

class default_slave_rxd_timing extends slave_rxd_timing;
	
	function new();
		for (int i=0; i<3; i++) begin
			for (int j=0; j<3; j++) begin
				t_rxd1[i][j] = 0ns;
				t_rxd2[i][j] = 0ns;
			end
		end		
		
		t_rxd1[0][1] = 0.5us;
		t_rxd1[1][0] = 0.5us;
		t_rxd1[0][2] = 0.33us;
		t_rxd1[2][0] = 0.66us;
		
		t_rxd2[0][2] = 0.66us;
		t_rxd2[1][2] = 0.5us;
		t_rxd2[2][0] = 0.33us;
		t_rxd2[2][1] = 0.5us;
			
	endfunction
	
endclass

class no_slave_timing extends slave_rxd_timing;
	
	function new();
		for (int i=0; i<3; i++) begin
			for (int j=0; j<3; j++) begin
				t_rxd1[i][j] = 0ns;
				t_rxd2[i][j] = 0ns;
			end
		end		
		
		t_rxd1[0][1] = 1ns;
		t_rxd1[1][0] = 1ns;
		t_rxd1[0][2] = 1ns;
		t_rxd1[2][0] = 2ns;
			
		t_rxd2[0][2] = 2ns;
		t_rxd2[1][2] = 1ns;
		t_rxd2[2][0] = 1ns;
		t_rxd2[2][1] = 1ns;
			
	endfunction
	
endclass
