class otp_random_trimming_seq extends base_otp_seq;

	`uvm_object_utils(otp_random_trimming_seq)
	
	function new(string name = "");
		super.new("otp_random_trimming");
	endfunction : new
	
	virtual task run_tests();
		trimming trimmings[$];
		log_sim_description("read random trimming values from OTP", LOG_LEVEL_SEQUENCE);
		
		for (int k=0; k < 30; k++) begin
			string file_name = $sformatf("otp_random_%0d.dat", k);
			init_trimmings(trimmings);
			write_trimmings(trimmings, file_name);
			
			reset(file_name);
			
			foreach(trimmings[i]) begin
				trimmings[i].check_register_value();				
				trimmings[i].check_port_value();
			end
		end
	endtask
endclass