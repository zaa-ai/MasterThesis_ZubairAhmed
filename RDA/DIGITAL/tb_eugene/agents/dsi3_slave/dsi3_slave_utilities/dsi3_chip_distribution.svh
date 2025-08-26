/**
 * Class: dsi3_chip_distribution
 * 
 * class for collection distribution data for chips in a slave transmission
 */
class dsi3_chip_distribution;

	int		chip_distribution[3];
	
	function new(logic[3:0] data[$]);
		add_data(data);
	endfunction
	
	virtual function string get_string();
		string temp = "";
		foreach (chip_distribution[i]) begin
			temp = {temp, $sformatf("%1d=%1d   ", i, chip_distribution[i])};
		end
		
		return temp;
	endfunction
	
	virtual function void add_data(logic[3:0] data[$]);
		dsi3_pkg::dsi3_symbol symbol;
		foreach (data[k]) begin
			if (data[k] !== 4'hx) begin
				symbol = dsi3_pkg::dsi3_symbol_lut[data[k]];
				for (int j=2; j>=0; j--) begin
					chip_distribution[symbol[j]]++;
				end
			end
		end
	endfunction
	
	virtual function void clear();
		foreach(chip_distribution[j]) begin
			chip_distribution[j] = 0;
		end
	endfunction

endclass


