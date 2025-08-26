/**
 * Real signal sequence that drives a PWM signal using a real signal driver.
 */
class real_signal_pwm_sequence extends real_signal_default_seq;

	`uvm_object_utils(real_signal_pwm_sequence)
	
	rand longint period;
	rand longint start_duty_cycle;
	rand longint target_duty_cycle;
	rand int unsigned count;
	rand int unsigned repeat_count;
		
	rand longint value_off = 0;
	rand longint value_on = 1;
	rand longint edge_duration = 0;
	rand int unsigned duty_scale_value;
	
	function new(string name="");
		super.new("real_signal_pwm_sequence");
	endfunction : new
  
	/************************ User defined methods declarations ************************/
	
	virtual task body();
		longint on, off;
		real scaled_start_duty_cycle, scaled_target_duty_cycle;
		real duty_cycle, duty_cycle_step;
		real_signal_tr transaction;
	
		scaled_start_duty_cycle = start_duty_cycle * 1.0;
		scaled_start_duty_cycle = scaled_start_duty_cycle / duty_scale_value;
		
		scaled_target_duty_cycle = target_duty_cycle * 1.0;
		scaled_target_duty_cycle = scaled_target_duty_cycle / duty_scale_value;
		
		duty_cycle = scaled_start_duty_cycle;
		duty_cycle_step = (scaled_target_duty_cycle - scaled_start_duty_cycle) / count;
		
		repeat(count) begin
			on = period * duty_cycle;
			off = period * (1.0 - duty_cycle);
			repeat(repeat_count) begin
				// on			
				`uvm_do_with(transaction, { value == value_on; duration == on; edge_duration == local::edge_duration;});
				// off
				`uvm_do_with(transaction, { value == value_off; duration == off; edge_duration == local::edge_duration;});
			end	
			duty_cycle += duty_cycle_step;	
		end
	endtask : body
	
endclass 