
task run_phase(uvm_phase phase);
	// initialize SPI interface
	spi_init();
	forever
	begin
		seq_item_port.get_next_item(req);
		do_drive();
		seq_item_port.item_done(rsp);
	end
endtask : run_phase

task do_drive ();
	case (req.tr_type)
		spi_pkg::SPI_START:	spi_start_req();	// initialize SPI transfer
		spi_pkg::SPI_DATA:	spi_send_req();		// send SPI data
		spi_pkg::SPI_END:	spi_end_req();	// finish SPI
	endcase
endtask : do_drive

task spi_send_req();
	logic[15:0] temp = 16'hxxxx;
	req.data_out = 16'hxxxx; 
		
	for (int bit_index = 15; bit_index >= 16 - req.bit_count; bit_index--) begin
		spi_clock(req.data_in[bit_index], temp[bit_index]); 
	end
	req.data_out = temp;
	#(m_config.inter_word_gap);
endtask : spi_send_req

task spi_init();
	vif.SDI = 1'b0;
	vif.SCK = m_config.sck_init_value;
	vif.CSN = ~m_config.csn_polarity;
	#10ns;
endtask : spi_init

task spi_start_req();
	/* e.g. (CPHA=1), CPOL=0
	 *      _____
	 * CSN       \______
	 * SCK  XXXXX_______          
	 */
	vif.SCK = m_config.sck_polarity;
	#30ns;
	vif.CSN = m_config.csn_polarity;
	#(m_config.csn_to_sck);
endtask : spi_start_req

task spi_end_req();
	/* e.g. (CPHA=1), CPOL=0
	 *             _____
	 * CSN  ______/
	 * SCK  _______XXXXX          
	 */
	#(m_config.sck_to_csn);
	vif.CSN = ~m_config.csn_polarity;
	#30ns;
	vif.SCK = m_config.sck_init_value; //x stört in der gate simulation!
endtask : spi_end_req

task spi_clock(logic sdi, output logic sdo);
	if (m_config.sck_phase==0) begin  // phase = 0 // apply SDI first and sample with first SCK -> shift with next SCK
		vif.SDI = sdi;
		#(m_config.cycle_time/2);
		vif.SCK = ~m_config.sck_polarity;
		sdo = vif.SDO;
		#(m_config.cycle_time/2);
		vif.SCK = m_config.sck_polarity;
	end
	else begin  // phase = 1 // shift first and sample then
		vif.SCK = ~m_config.sck_polarity;
		vif.SDI = sdi;
		#(m_config.cycle_time/2);
		vif.SCK = m_config.sck_polarity;
		sdo = vif.SDO;
		#(m_config.cycle_time/2);
	end
endtask : spi_clock
