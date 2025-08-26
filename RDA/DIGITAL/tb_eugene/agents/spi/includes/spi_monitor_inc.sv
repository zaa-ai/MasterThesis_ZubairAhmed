logic[15:0] temp_in;
logic[15:0] temp_out;
int i;
bit word_complete;
int word_index;

task do_mon();
	
	forever begin 
		// initialze
		i = 15;
		temp_in  = 16'hxxxx;
		temp_out = 16'hxxxx;
		word_complete = 1'b0;
		
		// wait for CSN active		
		if (m_config.csn_polarity) begin
			@(posedge vif.CSN);
		end else begin
			@(negedge vif.CSN);
		end
		
		word_index = -1;
		void'(begin_tr(m_trans, "spi-start"));
		m_trans.set_name("mon-start");
		m_trans.data_in  = 16'hxxxx; // empty
		m_trans.data_out = 16'hxxxx; // empty
		m_trans.tr_type = spi_pkg::SPI_START;
		m_trans.bit_count = 0;
		m_trans.word_index = word_index;
		end_tr(m_trans, $time() + m_config.csn_to_sck);
		analysis_port.write(m_trans);
		
		
		// sample data at SCK
		while (vif.CSN == m_config.csn_polarity) begin
			if (m_config.sck_polarity==m_config.sck_phase) begin
				if (m_config.csn_polarity) begin
					@(posedge vif.SCK or negedge vif.CSN);
				end else begin
					@(posedge vif.SCK or posedge vif.CSN);
				end
			end	else begin
				if (m_config.csn_polarity) begin
					@(negedge vif.SCK or negedge vif.CSN);
				end else begin
					@(negedge vif.SCK or posedge vif.CSN);
				end
			end
			
			if (vif.CSN == m_config.csn_polarity) begin
				temp_in[i] = vif.SDI;
				temp_out[i]= vif.SDO;
				
				if(i==15) begin
					void'(begin_tr(m_trans, "spi-data"));
					word_index++;
					m_trans.set_name("mon-data");
					m_trans.tr_type = spi_pkg::SPI_DATA;
					m_trans.word_index = word_index;
				end
				
				if (i==0) begin
					m_trans.data_in = temp_in;
					m_trans.data_out = temp_out;
					m_trans.bit_count = 16;
					end_tr(m_trans);
					analysis_port.write(m_trans);
					word_complete = 1'b1;
					i=15;
				end
				else begin
					i--;
				end
			end
		end
		
		if(word_complete == 1'b0) begin
			m_trans.data_in = temp_in;
			m_trans.data_out = temp_out;
			m_trans.bit_count = 16 - (i+1);
			end_tr(m_trans);
			analysis_port.write(m_trans);
		end
		
		void'(begin_tr(m_trans, "spi-end"));
		m_trans.set_name("mon-end");
		m_trans.tr_type = spi_pkg::SPI_END;
		m_trans.data_in  = 16'hxxxx; // empty
		m_trans.data_out = 16'hxxxx; // empty
		m_trans.bit_count = 0;
		m_trans.word_index = -1;
		end_tr(m_trans, $time() + m_config.sck_to_csn);
		analysis_port.write(m_trans);
	end
endtask


