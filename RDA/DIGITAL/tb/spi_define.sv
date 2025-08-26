spi_int_if 		spi_vif(); 
l16				data_out[$]; 

task spi_write(input l16 data[$], output l16 data_out[$]); 
	data_out.delete();
	spi_enable(); 
	foreach (data[i])
		spi_write_data(data[i], data_out[i]); 
	#(spi_clock_period_half);
	spi_disable(); 
endtask  
task spi_write_data(l16 data, output l16 data_out); 
	for(int i=15;  i>=0;  i--) begin
		spi_clock(data[i], data_out[i]); 	
	end 
endtask 
task spi_clock(logic data, output logic data_out); 
	spi_vif.sck = 1'b1;
	#5ns;
	spi_vif.sdi = data; 
	#(spi_clock_period_half-5ns);
	spi_vif.sck = 1'b0;
	#(spi_clock_period_half-5ns); 
	data_out = spi_vif.sdo;
	#5ns;
endtask 
task spi_idle(); 
	spi_disable();
	spi_vif.sck = 1'b0; 
endtask 

task spi_enable();
	spi_vif.csb = 1'b0;
	spi_vif.csb_resn = 1'b1;
	#20ns;
endtask

task spi_disable();
	spi_vif.csb = 1'b1;
	spi_vif.csb_resn = 1'b0;	
endtask