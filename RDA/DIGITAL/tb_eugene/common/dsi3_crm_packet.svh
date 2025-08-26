/**
 * Class: dsi3_crm_packet
 * 
 * CRM message packet
 */
class dsi3_crm_packet extends dsi3_packet;
	
	`uvm_object_utils(dsi3_crm_packet)
	
	constraint co_data	{ data.size() == 8;}
	
	/************************ Methods declarations ************************/
	function new(string name ="dsi3_crm_packet");
		super.new(name);
	endfunction : new
	
	function void post_randomize();
		update_crc();
	endfunction : post_randomize
	
	static function dsi3_crm_packet create_packet(logic[3:0] data_queue[$]);
		dsi3_crm_packet packet = new();
		packet.data = data_queue;
		packet.check_crc();
		return packet;
	endfunction
	
	/************************ User defined methods declarations ************************/
	
	virtual function bit check_crc();
		logic[15:0] temp_crc;
		crc_correct = 1'b0;
		if(data.size() > 7) begin
			temp_crc = crc_calculation_pkg::dsi3_calculate_correct_crc(data, dsi3_pkg::SID_0Bit);
			crc_correct = (temp_crc === 16'd0) ? 1'b1 : 1'b0;
		end
		return crc_correct;
	endfunction 
	
	virtual function void update_crc();
		if (data.size > 7) begin
			logic[3:0] temp_data[$];
			logic[15:0] calculated_crc;
			for (int i=0; i<6; i++) begin
				temp_data.push_back(data[i]);
			end
			temp_data.push_back(4'd0);
			temp_data.push_back(4'd0);
			
			calculated_crc = crc_calculation_pkg::dsi3_calculate_crc(crc_correct, temp_data, dsi3_pkg::SID_0Bit);
			data[6] = calculated_crc[7:4];
			data[7] = calculated_crc[3:0];
		end
	endfunction 
	
	virtual function void set_data(logic[15:0] queue[$]);
		if (queue.size() != 2)
			`uvm_error(this.get_type_name(), $sformatf("Queue size is not correct for a CRM packet = %1d. exp. 2", queue.size()))
		else begin
			super.set_data(queue);
		end
	endfunction : set_data
	
	static function dsi3_crm_packet get_from_queue(logic[15:0] queue[$], int symbol_count=-1);
		dsi3_crm_packet new_packet = new();
		common_pkg::convert_queue #(16, 4)::convert(queue, new_packet.data);
		if (symbol_count >= 0) begin
			if (symbol_count <= new_packet.data.size()) begin
				new_packet.data = new_packet.data[0:symbol_count-1];
			end
			else begin
				`uvm_error("dsi3_crm_packet", $sformatf("Symbol count (=%1d) is greater than queue size (=%1d)", symbol_count, new_packet.data.size()))
			end
		end
		return new_packet;
	endfunction	
	
endclass : dsi3_crm_packet
