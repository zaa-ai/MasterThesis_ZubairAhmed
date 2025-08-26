import pattern_pkg::*;

class dsi_voltage extends value_storage#(virtual dsi3_slave_if);
	
	function new(time period, virtual dsi3_slave_if _vif, string name);
		super.new(period, _vif, '{name}, 1);
		powered_up = 0;
		x_before_edge = 2.0us;
		x_after_edge = 5.0us;
		x_powerup = 1.11ms;
		_is_output = 1'b1;
	endfunction
	
	virtual function void sample();
		if (enable_sampling) this.value.push_back(vif.cable.Voltage);
		else this.value.push_back(1'bx);
	endfunction
	
endclass

class dsi_current extends value_storage#(virtual dsi3_slave_if);
	
	function new(time period, virtual dsi3_slave_if _vif, string name);
		super.new(period, _vif, '{{name," 1"}, {name," 2"}}, 2);
		powered_up = 1'b1; 
		_is_output = 1'b0;
	endfunction
	
	virtual function void sample();
		case(vif.cable.Current)
			0: this.value.push_back(2'b11);
			1: this.value.push_back(2'b10);
			2: this.value.push_back(2'b00);
			default : $error("wrong current level: got %1d", vif.cable.Current);
		endcase
	endfunction
	
endclass

class spi_pins extends value_storage#(virtual spi_if);
	
	function new(time period, virtual spi_if _vif);
		super.new(period, _vif, '{"SDO","SDI","SCK","CSN"}, 4);
		powered_up = 1'b1;
		_is_output = {{28{1'b1}}, 3'b0, 1'b1};
		enable_sampling = 1'b0;
	endfunction
	
	virtual function void sample();
		logic[3:0]	new_value;
		logic	sdo_value = 1'bx;
        logic   previous_csn_value = value[$-1][3];
		if ((enable_sampling) && (vif.CSN == 1'b0) && (previous_csn_value == 1'b0) && (vif.SCK == 1'b0))
			sdo_value = vif.SDO;
		new_value = {vif.CSN, vif.SCK, vif.SDI, sdo_value};
		this.value.push_back(new_value);
	endfunction
	
endclass

class digital_pin extends value_storage#(virtual digital_signal_if);
	function new(time period, virtual digital_signal_if _vif, string name[$], int size=1);
		super.new(period, _vif, name, 1);
		_is_output = 1'b0;
	endfunction
	
	virtual function void sample();
		this.value.push_back(vif.D);
	endfunction
endclass

class digital_input_pin extends digital_pin;
	function new(time period, virtual digital_signal_if _vif, string name);
		super.new(period, _vif, '{name}, 1);
		powered_up = 1;
		_is_output = 1'b0;
	endfunction
endclass

class intb_pin extends digital_pin;
	function new(time period, virtual digital_signal_if _vif, string name);
		super.new(period, _vif, '{name}, 1);
		powered_up = 1'b1;
		x_before_edge = 30us;
		x_after_edge = 60us;
		_is_output = 1'b1;
	endfunction
endclass

class dab_pin extends digital_pin;
	function new(time period, virtual digital_signal_if _vif, string name);
		super.new(period, _vif, '{name}, 1);
		powered_up = 1'b1;
		x_before_edge = 20us;
		x_after_edge = 20us;
		_is_output = 1'b1;
	endfunction
endclass

class bfwb_pin extends digital_pin;
	function new(time period, virtual digital_signal_if _vif, string name);
		super.new(period, _vif, '{name}, 1);
		powered_up = 1'b1;
		x_before_edge = 2us;
		x_after_edge = 30us;
		_is_output = 1'b1;
	endfunction
endclass

class clock_pin extends value_storage#(virtual osc_if);
	function new(time period, virtual osc_if _vif, string name, int size=1);
		super.new(period, _vif, '{name}, 1);
        powered_up = 1'b1;
		_is_output = 1'b0;
	endfunction
	
	virtual function void sample();
		this.value.push_back(vif.CLK);
	endfunction
endclass

class pdcm_packets extends uvm_report_object;
    
    dsi3_pdcm_packet packets[][2:0];
    
    function new(int number_of_frames);
        packets = new[number_of_frames];
        for (int frame_index=0; frame_index<number_of_frames; frame_index++) begin
            packets[frame_index][0] = create_pdcm_packet(dsi3_pkg::SID_0Bit     , 12);
            packets[frame_index][1] = create_pdcm_packet(dsi3_pkg::SID_16Bit_CRC, 13);
            packets[frame_index][2] = create_pdcm_packet(dsi3_pkg::SID_8Bit     , 15);
        end
    endfunction
    
    virtual function dsi3_pdcm_packet create_pdcm_packet(dsi3_pkg::sid_length_e source_id_symbols, int symbols);
        dsi3_pdcm_packet pdcm_packet;
        pdcm_packet = dsi3_pdcm_packet::new("PDCM_PACKET");
        if (!pdcm_packet.randomize() with {source_id_symbols==source_id_symbols; data.size() == symbols;}) `uvm_error(this.get_type_name(), "Randomization of CRM packet failed")
        return pdcm_packet;
    endfunction
    
    virtual function dsi3_pdcm_packet get_packet(int frame, int packet);
        return packets[frame][packet];
    endfunction
    
endclass

class applicative_pattern_seq extends base_dsi_master_seq;
	
	protected string pattern_name = "applicative_pattern";
	protected time	period = 100ns;
	
	pattern		_pattern;
	
	spi_pins	spi_signals;
	dsi_voltage	dsi_voltages[$];
	
	int	interrupt_addresses[$];
    
    int NUMBER_OF_PDCM_FRAMES = 2;
	
	`uvm_object_utils(applicative_pattern_seq)

	function new(string name = "");
		super.new("applicative_pattern");
	endfunction
	
	function void create_interrupt_addresses();
		interrupt_addresses.delete();
		foreach (regmodel.DSI[channel]) begin
			interrupt_addresses.push_back(regmodel.DSI[channel].DSI3_channel_registers.DSI_IRQ_STAT.get_address());
		end
		interrupt_addresses.push_back(regmodel.SPI.SPI_registers.SPI_IRQ_STAT.get_address());
		interrupt_addresses.push_back(regmodel.Supply.supply_registers.SUP_IRQ_STAT.get_address());
		interrupt_addresses.push_back(regmodel.Buffer_IRQs.buffer_interrupt_registers.BUF_IRQ_STAT.get_address());
		interrupt_addresses.push_back(regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_MASK.get_address());
		interrupt_addresses.push_back(regmodel.Interrupt.Interrupt_Registers.ECC_CORR_IRQ_STAT.get_address());
		interrupt_addresses.push_back(regmodel.Interrupt.Interrupt_Registers.IRQ_STAT.get_address());
	endfunction
	
	virtual task run_tests();
		power_up(0us);
		make_pattern();
		#100us;
	endtask
	
	virtual task make_pattern();
		initialize();
		do_pattern();
		`uvm_info(this.get_type_name(), "writing pattern file", UVM_NONE);
		write_pattern();
		#1ms;
	endtask
	
	virtual function void write_pattern();
		pat_pattern_writer#(.PIN_DESCRIPTION("Main.pin"), .TIMING("Main.tim")) writer;
		writer = new(.use_repeats(1'b0), .serial_domains(1'b1));
		writer.set_timeplate("default");
		writer.write_pattern(pattern_name, _pattern);
	endfunction
	
	virtual function void initialize();
		spi_config			spi_cfg = m_spi_agent.m_config;
		jtag_master_config	jtag_cfg = m_jtag_master_agent.m_config;
		
		no_slave_timing_container timings = new();
		
		spi_cfg.cycle_time = 2*period;
		spi_cfg.sck_init_value = 1'b0;
		spi_cfg.csn_to_sck = 3*period;
		spi_cfg.sck_to_csn = 3*period;
		spi_cfg.vif.SCK = 0;
		jtag_cfg.cycle_time = 3*period;
		
		for(int channel=0; channel<project_pkg::DSI_CHANNELS; channel++) begin
			dsi3_slave_agent agent;
			agent = get_slave_agent(channel);
			agent.set_rxd_timing(timings);
		end
		
		create_interrupt_addresses();
		
		_pattern = new();
		_pattern.add_domain(create_domain_MDM500(period));
		_pattern.add_domain(create_domain_MMXHE(period));
		
	endfunction
	
	virtual function pattern_domain create_domain_MDM500(int period);
		pattern_domain domain;
		domain = new(period, "MdmDpins", "MDM500");
		begin : add_digital_signals
			digital_pin	signal;
			signal = bfwb_pin::new(period, bfwb, "BFWB");
			domain.add_signal(signal);
			signal = dab_pin::new(period, dab, "DAB");
			domain.add_signal(signal);
			signal = digital_input_pin::new(period, syncb, "SYNCB");
			domain.add_signal(signal);
			signal = intb_pin::new(period, intb, "INTB");
			domain.add_signal(signal);
			signal = digital_input_pin::new(period, resb, "RESB");
			domain.add_signal(signal);
		end
		return domain;
	endfunction
	
	virtual function pattern_domain create_domain_MMXHE(int period);
		spi_config			spi_cfg = m_spi_agent.m_config;
		pattern_domain domain;
		domain = new(period, "MmxheDpins", "MMXHE");
		begin : add_spi_signals
			spi_signals = new(period, spi_cfg.vif);
			spi_signals.vif = spi_cfg.vif;
			domain.add_signal(spi_signals);
		end
		begin : add_dsi_voltages
			dsi_voltage	voltage;
			dsi3_master_config master_config;
			for (int channel = 0; channel < project_pkg::DSI_CHANNELS; channel++) begin
				master_config = get_master_agent(channel).m_config;
				voltage = new(period, master_config.vif, $sformatf("DSI%1d", channel));
				voltage.vif = master_config.vif;
				dsi_voltages[channel] = voltage;
				domain.add_signal(voltage);
			end
		end
		begin : add_clkref
			clock_pin	clk_signal;
			clk_signal = clock_pin::new(period, m_osc_agent.m_config.vif, "CLKREF");
			domain.add_signal(clk_signal);
		end
		begin : add_dsi_currents
			dsi_current	current;
			dsi3_master_config master_config;
			for (int channel = 0; channel < 2; channel++) begin
				master_config = get_master_agent(channel).m_config;
				current = new(period, master_config.vif, $sformatf("DSI_RX%1d_%1d", channel, channel+2));
				current.vif = master_config.vif;
				domain.add_signal(current);
			end
		end
		
		return domain;
	endfunction
	
    pdcm_packets        packets;
    
	virtual task do_pattern();
        tdma_scheme_pdcm    scheme_pdcm;
        
        packets = new(.number_of_frames(NUMBER_OF_PDCM_FRAMES+1));
        
		foreach (dsi_voltages[i])	dsi_voltages[i].set_sampling(1'b0);
		spi_signals.set_sampling(1'b0);
		set_clock_ref(.enable(0));
		_pattern.start_sampling();
		#12ns;
		`uvm_info(this.get_type_name, "Starting pattern", UVM_NONE)
		
        check_resb_debouncer();
        
		#400us;
		comment_pattern("enable CLKREF input");
		set_clock_ref(.enable(1));
		#400us;

		fork
			#1300us;
			begin
				make_buffer_full_and_set_BFBW_pin();
				configure_channels(dsi3_pkg::BITTIME_16US);
			end
		join
		
		spi_signals.set_sampling(1'b1);
		read_interrupts();
		reset_interrupts();
		
		// Jira P52143-483: SPI communication with CSB=1
        spi_communication_with_csb_high();
		
		foreach (dsi_voltages[i])	dsi_voltages[i].set_sampling(1'b1);
		#20us;
		
		set_TDMA_schemes();
		send_crm_command();
        send_crm_answer();
		
        upload_tdma_scheme(packets, scheme_pdcm);
        
		send_pdcm_command();
		
        send_pdcm_answer(packets, scheme_pdcm);
        
		read_data();
		
		read_interrupts();
        
        invalidate_TDMA();
		#1us;
		_pattern.stop_sampling();
		
		`uvm_info(this.get_type_name, "Ending pattern", UVM_NONE);
		
    endtask
    
    virtual task check_resb_debouncer();
        uvm_reg register_under_test = regmodel.Interrupt.Interrupt_Registers.ECC_IRQ_MASK;
        shortint register_reset_value = shortint'(register_under_test.get_reset());
        shortint register_change_value = 16'd0;
        get_checker_config().enable_hardware_error_check = 1'b0;
        #1us;
        comment_pattern("reset SPI");
        `spi_frame_begin
            `spi_frame_create(spi_reset_seq,)
        `spi_frame_end
        
        comment_pattern("check RESB debouncer");
        comment_pattern($sformatf("write %s register", register_under_test.get_name()));
        register_under_test.write(status, register_change_value);
        comment_pattern($sformatf("read %s register again", register_under_test.get_name()));
        read_register_without_sampling_of_status_and_CRC(register_under_test, register_change_value);
        comment_pattern("apply short pulse at RESB");
        set_resb(1'b0);
        #500ns;
        set_resb(1'b1);
        #5us;
        comment_pattern($sformatf("read %s after short RESB pulse", register_under_test.get_name()));
        read_register_without_sampling_of_status_and_CRC(register_under_test, register_change_value);
        comment_pattern("set RESB => 0");
        set_resb(1'b0);
        #10us;
        comment_pattern("set RESB => 1");
        set_resb(1'b1);
        #10us;
        comment_pattern($sformatf("read %s after RESB pulse", register_under_test.get_name()));
        read_register_without_sampling_of_status_and_CRC(register_under_test, register_reset_value);
        get_checker_config().enable_hardware_error_check = 1'b1;
    endtask
    
    virtual task read_register_without_sampling_of_status_and_CRC(uvm_reg register_to_be_read, shortint compare_value);
        uvm_reg_data_t read_value;
        fork 
            register_to_be_read.read(status, read_value);
            begin
                repeat (17) 
                    @(negedge spi.SCK) #1ns;
                spi_signals.set_sampling(1'b1);
            end
            begin
                repeat (49) 
                    @(negedge spi.SCK) #1ns;
                spi_signals.set_sampling(1'b0);
            end
        join
        spi_signals.set_sampling(1'b0);
        if (read_value[15:0] != compare_value) begin
            `uvm_error(this.get_type_name(), $sformatf("Content of register %s is not expected. Expected 0x%4h but got 0x%4h", register_to_be_read.get_name(), compare_value, read_value[15:0]))
        end
    endtask
    
    virtual task comment_start_of_master_command(int channel);
        @(negedge m_dsi3_master_agent[channel].m_config.vif.cable.Voltage);
        comment_pattern($sformatf("DSI channel %1d command (start of transmission)", channel));
    endtask
    
    virtual task comment_start_of_slave_response(int channel, int packet);
        comment_pattern($sformatf("DSI channel %1d response (start of transmission of packet %1d)", channel, packet));
    endtask
	
	virtual function void comment_pattern(string _comment);
		_pattern.set_comment(_comment);
		`uvm_info(this.get_type_name(), _comment, UVM_NONE)
	endfunction
	
	virtual function void set_TDMA_schemes();
		dsi3_crm_packet packet = new();
        tdma_scheme_pdcm scheme = new();
		if(!packet.randomize()) `uvm_error(this.get_name(), "randomization error")
        
        if(!scheme.randomize() with {packets.size() == 16; symbol_count_max <=16; chiptime == 3; bit_time == dsi3_pkg::BITTIME_8US;}) `uvm_error(get_type_name(), "failed to randomize TDMA scheme")
        
        // disable all packets in this scheme
        foreach(scheme.packets[i]) begin
            scheme.packets[i].enable = 1'b0;
        end
        
		for (int channel=0; channel<project_pkg::DSI_CHANNELS; channel++) begin
			set_tdma_scheme_crm(channel, tdma_scheme_crm::no_answer());
            set_tdma_scheme_pdcm(channel, scheme);
		end
	endfunction
	
	virtual task configure_channels(dsi3_pkg::dsi3_bit_time_e bit_time);
        uvm_reg_data_t read_value;
        int crm_duration = int'(320*dsi3_pkg::get_bit_time_factor(dsi3_pkg::BITTIME_16US) + 24*1.05*dsi3_pkg::CHIPTIME_3US + 30);
		comment_pattern($sformatf("set bit time to %s", bit_time.name()));
		regmodel.DSI_common.common_DSI3_block_registers.DSI_CFG.BITTIME.write(status, 1);
		comment_pattern($sformatf("set CRM_TIME to %s", crm_duration+70));
        regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME.TIME.write(status, crm_duration+70);
		comment_pattern($sformatf("read CRM_TIME"));
        regmodel.DSI_common.common_DSI3_block_registers.CRM_TIME.TIME.read(status, read_value);
	endtask
	
	virtual task send_crm_command();
		comment_pattern("start CRM via SPI");
		`spi_frame_begin
            `spi_frame_create(spi_measure_quiescent_current_seq, channel_bits == 2'b11;)
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b10; wait_time == 15'd50;)
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b01; wait_time == 15'd25;)
			`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b0; channel_bits == 2'b11;)
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b00; wait_time == 15'h7fff;) // -> leads to SCE flag
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b10; wait_time == 15'd00;)
			`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b01; wait_time == 15'd900;)
			`spi_frame_create(spi_crm_seq, channel_bits == 2'b11; broad_cast == 1'b0;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
        #0.5us;
        regmodel.SPI.SPI_registers.SPI_IRQ_STAT.CMD_IGN.write(status, 1);
        #0.5us;
	endtask
	
    virtual task send_slave_crm_response(dsi3_packet crm_packet, int channel);
        start_response(610us, crm_packet, 0, '{channel});
    endtask
    
    virtual task send_crm_answer();
        dsi3_packet crm_packet, crm_packet2;
        crm_packet = create_crm_packet();
        crm_packet2 = create_crm_packet();
        
        fork
            begin
                comment_start_of_master_command(0);
                start_response(610us, crm_packet, 0, '{0, 1});
            end
            begin
                comment_start_of_master_command(1);
                start_response(610us, crm_packet2, 0, '{0, 1});
            end
        join
        
        #150us;
    endtask
    
    virtual task upload_tdma_scheme(pdcm_packets packets, output tdma_scheme_pdcm scheme);
        upload_tdma_scheme_seq upload_seq;
        // 3 Packets
        // (one to early, one too late, one correct)
        // one with CRC error one without
        // different sizes e.g. 8, 13, 17
        scheme = new("applicative_TDMA_scheme");
        scheme.pdcm_period = 600;
        scheme.chiptime = 3;
        scheme.add_packet(tdma_scheme_packet_pdcm::new_packet( 70, 100, packets.get_packet(0, 0).data.size(), packets.get_packet(0, 0).source_id_symbols));
        scheme.add_packet(tdma_scheme_packet_pdcm::new_packet(195, 235, packets.get_packet(0, 1).data.size(), packets.get_packet(0, 0).source_id_symbols));
        scheme.add_packet(tdma_scheme_packet_pdcm::new_packet(390, 410, packets.get_packet(0, 2).data.size(), packets.get_packet(0, 0).source_id_symbols));
        
        `uvm_create(upload_seq)
        if(!upload_seq.randomize() with {channels == 2'b11;}) `uvm_error(get_type_name(), "failed to randomize");
        upload_seq.scheme = scheme;
        
        log_sim_description($sformatf("uploading TDMA scheme with %0d packets at channels %2b", scheme.get_packet_count(), upload_seq.channels), LOG_LEVEL_OTHERS);
        comment_pattern($sformatf("upload TDMA scheme"));
        `uvm_send(upload_seq)
        #1us;
        comment_pattern("set shift value to 40");
        regmodel.DSI_common.common_DSI3_block_registers.DSI_TX_SHIFT.SHIFT.write(status, 100);
        #1us;
    endtask
    
	virtual task send_pdcm_command();
		comment_pattern("start PDCM via SPI");
		`spi_frame_begin
    		`spi_frame_create(spi_sync_dsi_channels_seq, external_sync == 1'b1; channel_bits == 2'b11;)
    		`spi_frame_create(spi_dsi_wait_seq, channel_bits == 2'b10; wait_time == 15'd200;)
    		`spi_frame_create(spi_pdcm_seq, channel_bits == 2'b11; pulse_count == 8'd2;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
    endtask
    
    virtual task send_pdcm_answer(pdcm_packets packets, tdma_scheme_pdcm scheme);
        fork
            begin
                #200us;
                comment_pattern("set SYNCB pin");
                set_syncb(1'b1);
                #10us;
                set_syncb(1'b0);
            end
            repeat (2) comment_start_of_master_command(0);
            repeat (2) comment_start_of_master_command(1);
            
            send_pdcm_answer_on_channel(packets, scheme);
        join
    endtask
    
    virtual task send_pdcm_answer_on_channel(pdcm_packets packets, tdma_scheme_pdcm scheme);
        int channels[$][];
        channels.push_back('{0});
        channels.push_back('{0,1});
        channels.push_back('{0,1});
        for (int frame_index = 0; frame_index < NUMBER_OF_PDCM_FRAMES+1; frame_index++) begin
            @(negedge m_dsi3_master_agent[0].m_config.vif.cable.Voltage or negedge m_dsi3_master_agent[1].m_config.vif.cable.Voltage);
            fork
                start_response(scheme.packets[0].get_earliest_start_time() - 8us, packets.get_packet(frame_index, 0), 0, channels[frame_index]);
                start_response(scheme.packets[1].get_latest_start_time()   + 10us, packets.get_packet(frame_index, 1), 1, channels[frame_index]);
                start_response(scheme.packets[2].get_earliest_start_time() + 10us, packets.get_packet(frame_index, 2), 2, channels[frame_index]);
            join_none
            #(scheme.pdcm_period*1us - 20us);
        end
        #50us;
    endtask
    
    virtual task start_response(time wait_time, dsi3_packet packet, int packet_index, int channels[]);
        #(wait_time);
        comment_start_of_slave_response(0, packet_index);
        send_packet(packet, channels);
    endtask
	
	virtual task read_data();
		comment_pattern("read CRM response of DSI0 via SPI");
        `spi_frame_begin
            `spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b01;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #1us;
        
		comment_pattern("read CRM response of DSI1 via SPI");
        `spi_frame_begin
            `spi_frame_create(spi_read_crm_data_packets_seq, channel_bits == 2'b10;)
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #1us;
		
		comment_pattern("read PDCM responses of DSI0 via SPI");
        `spi_frame_begin
            `spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01; )
            `spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b01; )
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #1us;
        
		comment_pattern("read PDCM responses of DSI1 via SPI");
        `spi_frame_begin
            `spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b10; )
            `spi_frame_create(spi_read_pdcm_frame_seq, channel_bits == 2'b10; )
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
        `spi_frame_end
        #1us;
	endtask
	
	virtual task read_ram();
		spi_read_master_register_seq reg_seq;
		`uvm_create_on(reg_seq, m_spi_agent.m_sequencer)
		void'(reg_seq.randomize() with {address == 12'(project_pkg::BASE_ADDR_RAM);});
		reg_seq.burst_addresses.delete();
		for (int i=int'(project_pkg::BASE_ADDR_RAM); i<int'(project_pkg::BASE_ADDR_RAM+project_pkg::SIZE_RAM); i++)
			reg_seq.burst_addresses.push_back(i);
		`uvm_send(reg_seq)
	endtask
	
	virtual task make_buffer_full_and_set_BFBW_pin();
        m_spi_agent.m_config.csb_handler = per_frame_csb_hander::create(); //for debugging
        comment_pattern("make SPI buffer full and thus set BFWB pin");
        `spi_frame_begin
            for (int i=0; i < int'(project_pkg::SIZE_SPI_CMD_BUF)-10; i++) begin
                `spi_frame_create(spi_pdcm_seq,)
            end
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b0;)
        `spi_frame_end
        m_spi_agent.m_config.csb_handler = per_word_csb_hander::create();
	endtask
		
	virtual task set_tre(input bit enable, input bit disable_miso_sampling = 1'b0);
		comment_pattern($sformatf("set TRE for DSI channels to %1d", enable));
		if (disable_miso_sampling)
				spi_signals.set_sampling(1'b0);
		regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.TRE.write(status, (enable)?'1:'0);
		#10us;
	endtask
	
	virtual task read_interrupts();
		spi_read_master_register_seq read_seq;
		
		comment_pattern("read interrupt registers");
		`spi_frame_begin
			`spi_frame_send(read_seq, address == 0; burst_addresses.size() == local::interrupt_addresses.size(); foreach(interrupt_addresses[i]) burst_addresses[i] ==  local::interrupt_addresses[i][11:0];)
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#3us;
	endtask
	
	virtual task reset_interrupts();
		comment_pattern("Clear interrupts");
		`spi_frame_begin
			for(int address=0; address < interrupt_addresses.size(); address++) begin
				logic[11:0] interrupt_address;
				interrupt_address = interrupt_addresses[address][11:0];
				`spi_frame_create(spi_write_master_register_seq, {address == local::interrupt_address;data == 16'hffff;})
			end
			`spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;)
		`spi_frame_end
		#3us;
	endtask
	
	virtual task spi_communication_with_csb_high();
		uvm_reg_addr_t address = regmodel.DSI_common.common_DSI3_block_registers.DSI_ENABLE.get_address();
		comment_pattern("Do SPI communication with CSB high");
        m_spi_agent.m_config.csb_handler = always_high_csb_hander::create(); 
		`spi_frame_begin
			`spi_frame_create(spi_write_master_register_seq, {address==local::address[11:0]; data=='0;})
		`spi_frame_end
        m_spi_agent.m_config.csb_handler = per_frame_csb_hander::create();
	endtask
	
	virtual task send_packet(dsi3_packet packet, int channels[]);
		dsi3_slave_agent agent;
		foreach(channels[i]) begin
			dsi3_slave_seq	seq = new("slave_response");
			dsi3_slave_tr	m_slave_tr;
			m_slave_tr = dsi3_slave_tr::type_id::create("dsi3_slave_tr");
			
			// create slave transaction with correct msg_type; tolerance & chiptime from tdma scheme
			if (!m_slave_tr.randomize with {
					msg_type == dsi3_pkg::CRM;
					tolerance_int == 1000;
					data.size() == 8;
					chiptime == 3;
					chips_per_symbol == 3;
					symbol_coding_error_injection == NEVER_ERROR;
					chip_length_error_injection == NEVER_ERROR;
				}) begin
				`uvm_error(this.get_type_name(), "randomization error for slave transaction")
			end
			
			// set data of transaction from the packet
			seq.packet = packet;
			seq.req = m_slave_tr;
			agent = get_slave_agent(channels[i]);
			fork
				automatic dsi3_slave_agent current_agent = agent;
				automatic dsi3_slave_seq current_seq = seq;
				current_seq.start(current_agent.m_sequencer);
			join_none
		end
	endtask
	
	virtual function dsi3_crm_packet create_crm_packet();
        dsi3_crm_packet crm_packet;
        crm_packet = new("CRM_PACKET");
        if (!crm_packet.randomize()) `uvm_error(this.get_type_name(), "Randomization of CRM packet failed")
        return crm_packet;
    endfunction
    
	task invalidate_TDMA();
        comment_pattern("invalidate TDMA scheme");
        `spi_frame_begin                
            `spi_frame_create(spi_validate_tdma_scheme_seq, channel_bits == 2'b11; packet_count == 4'd0; pdcm_period == 16'(100);) 
            `spi_frame_create(spi_tx_crc_request_seq, mosi_crc_correct == 1'b1;) 
        `spi_frame_end
    endtask
	
endclass
