class otp_vcc_uv_during_read_seq extends base_otp_seq;

	`uvm_object_utils(otp_vcc_uv_during_read_seq)
	
	function new(string name = "");
		super.new("otp_vcc_uv_during_read");
	endfunction 
	
	virtual task run_tests();
		string file_name = "otp_vcc_uv.dat";
		trimming trimmings[$];
		log_sim_description("VCC under voltage during OTP read", LOG_LEVEL_SEQUENCE);
		get_checker_config().enable_hardware_error_check = 1'b0;
		
		repeat(1024) begin
			trimmings.push_back(create_trimming(regmodel.Info.IC_revision_and_ID_registers.CHIP_ID_LOW,	""));
		end
		
		write_trimmings(trimmings, file_name);
		
		fork
			begin
				reset(file_name, .rfc_timeout(10ms));
			end
			begin
				#500us;
				repeat(20) begin
					int delay = $urandom_range(200, 50);
					int duration = $urandom_range(100, 1);

					#(delay * 1us);
					set_vcc_uv(1'b1);
					#(duration * 1us);
					set_vcc_uv(1'b0);
				end
			end
		join
		
		#500us;
		// last access to CHIP_ID_LOW should win
		trimmings[$].check_register_value();				
	endtask
endclass