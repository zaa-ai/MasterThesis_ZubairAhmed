/**
 * Class: default_comparer
 * 
 * default comparer for all comparisons used
 */
class default_comparer#(number_of_messages=3, uvm_severity severity = UVM_ERROR) extends uvm_comparer;

	function new();
		super.new();
		show_max = number_of_messages;
		sev = severity;
	endfunction

endclass


