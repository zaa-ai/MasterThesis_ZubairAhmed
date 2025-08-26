/**
 * Class: check_transmit
 * 
 * Class for checking DSI3 master transmissions
 */
class check_transmit extends uvm_scoreboard;
	`uvm_component_utils(check_transmit)
	
	uvm_analysis_imp_dsi3_master	#(dsi3_master_tr,		check_transmit)  dsi3_master_export;
	uvm_analysis_imp_frame_writer	#(spi_command_frame_seq,check_transmit)  frame_export;
	
	//TODO: check period
	//TODO: check WAIT
	
	int error_count;
	dsi3_master_tr	transmissions[$];
	dsi3_slave_agent	slave_agent;
	
	protected dsi3_master_configuration_tr	configuration;
	
	function new (string name = "check_transmit", uvm_component parent=null);
		super.new(name, parent);
		frame_export = new("frame_export", this);
		dsi3_master_export = new("dsi3_master_export", this);
	endfunction
	
	function void write_frame_writer(spi_command_frame_seq t);
		// input..
		int command_index;
		for (command_index = 0; command_index < t.commands.size(); command_index++) begin
			spi_seq command = t.commands[command_index];
			case (command.get_type_name())
				spi_crm_seq::type_name: begin
					spi_crm_seq crm_seq;
					dsi3_master_tr new_tr = new();
					new_tr.msg_type = CRM;
					new_tr.bit_time = configuration.bit_time;
					if (spi_seq_factory #(spi_crm_seq)::cast(command, crm_seq)) begin
						dsi3_crm_packet packet = crm_seq.crm_packet;
						`uvm_info(this.get_type_name(), $sformatf("%s", crm_seq.convert2string()), UVM_DEBUG)
						if (configuration.crc_en == 1'b1) begin
							packet.crc_correct = 1'b1;
							packet.update_crc();
						end
						void'(convert_queue #(4, 1)::convert(packet.data, new_tr.data));
					end
					transmissions.push_back(new_tr);
				end
				
				spi_pdcm_seq::type_name: begin
					spi_pdcm_seq pdcm_seq;
					if(spi_seq_factory #(spi_pdcm_seq)::cast(command, pdcm_seq)) begin
						dsi3_master_tr new_tr = new();
						`uvm_info(this.get_type_name(), $sformatf("%s", pdcm_seq.convert2string()), UVM_DEBUG)
						new_tr.msg_type = PDCM;
						new_tr.bit_time = configuration.bit_time;
						new_tr.data.push_back(1'b0);
						repeat(pdcm_seq.pulse_count) begin
							transmissions.push_back(new_tr);
						end
					end
				end
				
				spi_discovery_mode_seq::type_name: begin
					spi_discovery_mode_seq	dm_seq;
					if(spi_seq_factory #(spi_discovery_mode_seq)::cast(command, dm_seq)) begin
						int dm_pulse_counter = 0;
						dsi3_master_tr new_tr = new();
						`uvm_info(this.get_type_name(), $sformatf("%s", dm_seq.convert2string()), UVM_DEBUG)
						new_tr.msg_type = DM;
						new_tr.bit_time = configuration.bit_time;
						transmissions.push_back(new_tr);
						for (int slave = 0; slave < slave_agent.m_config.dm_scheme.packets.size(); slave++) begin
							if (dm_pulse_counter < 15) begin
								if (slave_agent.m_config.dm_scheme.packets[slave].is_enabled()) begin
									dm_pulse_counter++;
									//new_tr.data.push_back(1'b0);
									transmissions.push_back(new_tr);
								end
							end
						end
					end
				end
				
				spi_dsi_wait_seq::type_name: begin
					`uvm_error(this.get_type_name(), "this is a WAIT sequence")
				end
				spi_sync_dsi_channels_seq::type_name: begin
					`uvm_error(this.get_type_name(), "this is a SYNC sequence")
				end
				spi_clear_dsi_data_buffers_seq::type_name: begin
					`uvm_error(this.get_type_name(), "this is a CLEAR DATA BUFFERS sequence")
				end
				spi_upload_tdma_packet_seq::type_name, spi_validate_tdma_scheme_seq::type_name: begin
					//TODO: check for necessary checks
                end
                spi_measure_quiescent_current_seq::type_name: begin
					//TODO: check for necessary checks
                end
				default: begin
					`uvm_error(this.get_type_name(), $sformatf("this is an unsupported sequence name! %s", command.get_type_name()))
				end
			endcase
		end
	endfunction
	
	function void write_dsi3_master(dsi3_master_tr t);
		`uvm_info(this.get_type_name(), $sformatf("DSI3 MASTER:%s", t.convert2string()), UVM_DEBUG)
		if (transmissions.size()>0) begin
			dsi3_master_tr frame_tr = transmissions.pop_front();
			default_comparer#(.number_of_messages(10)) comparer = new();
			`uvm_info(this.get_type_name(), $sformatf("from frame :%s", frame_tr.convert2string()), UVM_DEBUG)
			void'(t.compare(frame_tr, comparer));
		end
		else begin
			`uvm_error(this.get_type_name(), $sformatf("No transmission expected"))
		end
		// check
	endfunction
	
	function void set_configuration(dsi3_master_configuration_tr	t);
		this.configuration = t;
	endfunction
	
	protected function void check_data();
		if (transmissions.size() > 0) begin
			`uvm_error(this.get_type_name(), $sformatf("not all tranmissions transmitted via DSI. %1d remaining", transmissions.size()))
			foreach (transmissions[i]) begin
				`uvm_info(this.get_type_name(), $sformatf("%s",transmissions[i].convert2string()), UVM_INFO)
			end
			error_count++;
		end
	endfunction
	
	function void initialize();
		transmissions.delete();
		error_count = 0;
	endfunction
	
	function int get_error_count();
		check_data();
		return error_count;
	endfunction
	
	
endclass


