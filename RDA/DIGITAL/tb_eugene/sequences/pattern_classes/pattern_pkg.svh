package pattern_pkg;
	
	typedef logic logic_bitstream_t[$];
	typedef	string string_stream[$];
	
	`include "value_storage_interface.svh"
	`include "value_storage.svh"
	`include "signal_writer.svh"
	`include "pattern_domain.svh"
	`include "pattern.svh"
	`include "pattern_domain_iterator.svh"
	`include "pattern_writer.svh"
	`include "pat_signal_writer.svh"
	`include "pattern_domain_writer.svh"
	`include "pat_domain_writer.svh"
	`include "pat_parallel_domain_writer.svh"
	`include "pat_serial_domain_writer.svh"
	`include "pat_pattern_writer.svh"
//	`include "wgl_pattern_writer.svh"
	
endpackage : pattern_pkg