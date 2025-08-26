`ifndef RAL_JTAG_TEST_REGISTERS
package test_regmodel_pkg;

`include "uvm_macros.svh"

`define RAL_JTAG_TEST_REGISTERS

import uvm_pkg::*;

class ral_reg_TEST_TOP_TMR_ANA extends uvm_reg;
	rand uvm_reg_field ENABLE_ATB;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ENABLE_ATB: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_TOP_TMR_ANA");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ENABLE_ATB = uvm_reg_field::type_id::create("ENABLE_ATB",,get_full_name());
      this.ENABLE_ATB.configure(this, 1, 0, "RW", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_TOP_TMR_ANA)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_TOP_TMR_ANA


class ral_reg_TEST_TOP_TMR_DIG extends uvm_reg;
	rand uvm_reg_field USE_JTAG;
	rand uvm_reg_field SEL_SYNC;
	rand uvm_reg_field IGNORE_OSC_READY;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   USE_JTAG: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SEL_SYNC: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   IGNORE_OSC_READY: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_TOP_TMR_DIG");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.USE_JTAG = uvm_reg_field::type_id::create("USE_JTAG",,get_full_name());
      this.USE_JTAG.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.SEL_SYNC = uvm_reg_field::type_id::create("SEL_SYNC",,get_full_name());
      this.SEL_SYNC.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
      this.IGNORE_OSC_READY = uvm_reg_field::type_id::create("IGNORE_OSC_READY",,get_full_name());
      this.IGNORE_OSC_READY.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_TOP_TMR_DIG)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_TOP_TMR_DIG


class ral_reg_TEST_TOP_TMR_IN extends uvm_reg;
	rand uvm_reg_field tmr_in_0;
	rand uvm_reg_field tmr_in_1;
	rand uvm_reg_field tmr_in_2;
	rand uvm_reg_field tmr_in_3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   tmr_in_0: coverpoint {m_data[3:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {5'b???00};
	      wildcard bins bit_0_wr_as_1 = {5'b???10};
	      wildcard bins bit_0_rd_as_0 = {5'b???01};
	      wildcard bins bit_0_rd_as_1 = {5'b???11};
	      wildcard bins bit_1_wr_as_0 = {5'b??0?0};
	      wildcard bins bit_1_wr_as_1 = {5'b??1?0};
	      wildcard bins bit_1_rd_as_0 = {5'b??0?1};
	      wildcard bins bit_1_rd_as_1 = {5'b??1?1};
	      wildcard bins bit_2_wr_as_0 = {5'b?0??0};
	      wildcard bins bit_2_wr_as_1 = {5'b?1??0};
	      wildcard bins bit_2_rd_as_0 = {5'b?0??1};
	      wildcard bins bit_2_rd_as_1 = {5'b?1??1};
	      wildcard bins bit_3_wr_as_0 = {5'b0???0};
	      wildcard bins bit_3_wr_as_1 = {5'b1???0};
	      wildcard bins bit_3_rd_as_0 = {5'b0???1};
	      wildcard bins bit_3_rd_as_1 = {5'b1???1};
	      option.weight = 16;
	   }
	   tmr_in_1: coverpoint {m_data[7:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {5'b???00};
	      wildcard bins bit_0_wr_as_1 = {5'b???10};
	      wildcard bins bit_0_rd_as_0 = {5'b???01};
	      wildcard bins bit_0_rd_as_1 = {5'b???11};
	      wildcard bins bit_1_wr_as_0 = {5'b??0?0};
	      wildcard bins bit_1_wr_as_1 = {5'b??1?0};
	      wildcard bins bit_1_rd_as_0 = {5'b??0?1};
	      wildcard bins bit_1_rd_as_1 = {5'b??1?1};
	      wildcard bins bit_2_wr_as_0 = {5'b?0??0};
	      wildcard bins bit_2_wr_as_1 = {5'b?1??0};
	      wildcard bins bit_2_rd_as_0 = {5'b?0??1};
	      wildcard bins bit_2_rd_as_1 = {5'b?1??1};
	      wildcard bins bit_3_wr_as_0 = {5'b0???0};
	      wildcard bins bit_3_wr_as_1 = {5'b1???0};
	      wildcard bins bit_3_rd_as_0 = {5'b0???1};
	      wildcard bins bit_3_rd_as_1 = {5'b1???1};
	      option.weight = 16;
	   }
	   tmr_in_2: coverpoint {m_data[11:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {5'b???00};
	      wildcard bins bit_0_wr_as_1 = {5'b???10};
	      wildcard bins bit_0_rd_as_0 = {5'b???01};
	      wildcard bins bit_0_rd_as_1 = {5'b???11};
	      wildcard bins bit_1_wr_as_0 = {5'b??0?0};
	      wildcard bins bit_1_wr_as_1 = {5'b??1?0};
	      wildcard bins bit_1_rd_as_0 = {5'b??0?1};
	      wildcard bins bit_1_rd_as_1 = {5'b??1?1};
	      wildcard bins bit_2_wr_as_0 = {5'b?0??0};
	      wildcard bins bit_2_wr_as_1 = {5'b?1??0};
	      wildcard bins bit_2_rd_as_0 = {5'b?0??1};
	      wildcard bins bit_2_rd_as_1 = {5'b?1??1};
	      wildcard bins bit_3_wr_as_0 = {5'b0???0};
	      wildcard bins bit_3_wr_as_1 = {5'b1???0};
	      wildcard bins bit_3_rd_as_0 = {5'b0???1};
	      wildcard bins bit_3_rd_as_1 = {5'b1???1};
	      option.weight = 16;
	   }
	   tmr_in_3: coverpoint {m_data[15:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {5'b???00};
	      wildcard bins bit_0_wr_as_1 = {5'b???10};
	      wildcard bins bit_0_rd_as_0 = {5'b???01};
	      wildcard bins bit_0_rd_as_1 = {5'b???11};
	      wildcard bins bit_1_wr_as_0 = {5'b??0?0};
	      wildcard bins bit_1_wr_as_1 = {5'b??1?0};
	      wildcard bins bit_1_rd_as_0 = {5'b??0?1};
	      wildcard bins bit_1_rd_as_1 = {5'b??1?1};
	      wildcard bins bit_2_wr_as_0 = {5'b?0??0};
	      wildcard bins bit_2_wr_as_1 = {5'b?1??0};
	      wildcard bins bit_2_rd_as_0 = {5'b?0??1};
	      wildcard bins bit_2_rd_as_1 = {5'b?1??1};
	      wildcard bins bit_3_wr_as_0 = {5'b0???0};
	      wildcard bins bit_3_wr_as_1 = {5'b1???0};
	      wildcard bins bit_3_rd_as_0 = {5'b0???1};
	      wildcard bins bit_3_rd_as_1 = {5'b1???1};
	      option.weight = 16;
	   }
	endgroup
	function new(string name = "TEST_TOP_TMR_IN");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.tmr_in_0 = uvm_reg_field::type_id::create("tmr_in_0",,get_full_name());
      this.tmr_in_0.configure(this, 4, 0, "RW", 0, 0, 1, 0, 0);
      this.tmr_in_1 = uvm_reg_field::type_id::create("tmr_in_1",,get_full_name());
      this.tmr_in_1.configure(this, 4, 4, "RW", 0, 0, 1, 0, 0);
      this.tmr_in_2 = uvm_reg_field::type_id::create("tmr_in_2",,get_full_name());
      this.tmr_in_2.configure(this, 4, 8, "RW", 0, 0, 1, 0, 0);
      this.tmr_in_3 = uvm_reg_field::type_id::create("tmr_in_3",,get_full_name());
      this.tmr_in_3.configure(this, 4, 12, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_TOP_TMR_IN)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_TOP_TMR_IN


class ral_reg_TEST_TOP_TMR_OUT_CSB_SCK extends uvm_reg;
	rand uvm_reg_field SEL_SCK;
	rand uvm_reg_field EN_SCK;
	rand uvm_reg_field SEL_CSB;
	rand uvm_reg_field EN_CSB;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   SEL_SCK: coverpoint {m_data[5:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   EN_SCK: coverpoint {m_data[7:7], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SEL_CSB: coverpoint {m_data[13:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   EN_CSB: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_TOP_TMR_OUT_CSB_SCK");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.SEL_SCK = uvm_reg_field::type_id::create("SEL_SCK",,get_full_name());
      this.SEL_SCK.configure(this, 6, 0, "RW", 0, 0, 1, 0, 0);
      this.EN_SCK = uvm_reg_field::type_id::create("EN_SCK",,get_full_name());
      this.EN_SCK.configure(this, 1, 7, "RW", 0, 0, 1, 0, 0);
      this.SEL_CSB = uvm_reg_field::type_id::create("SEL_CSB",,get_full_name());
      this.SEL_CSB.configure(this, 6, 8, "RW", 0, 0, 1, 0, 0);
      this.EN_CSB = uvm_reg_field::type_id::create("EN_CSB",,get_full_name());
      this.EN_CSB.configure(this, 1, 15, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_TOP_TMR_OUT_CSB_SCK)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_TOP_TMR_OUT_CSB_SCK


class ral_reg_TEST_TOP_TMR_OUT_MOSI_MISO extends uvm_reg;
	rand uvm_reg_field SEL_MISO;
	rand uvm_reg_field EN_MISO;
	rand uvm_reg_field SEL_MOSI;
	rand uvm_reg_field EN_MOSI;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   SEL_MISO: coverpoint {m_data[5:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   EN_MISO: coverpoint {m_data[7:7], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SEL_MOSI: coverpoint {m_data[13:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   EN_MOSI: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_TOP_TMR_OUT_MOSI_MISO");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.SEL_MISO = uvm_reg_field::type_id::create("SEL_MISO",,get_full_name());
      this.SEL_MISO.configure(this, 6, 0, "RW", 0, 0, 1, 0, 0);
      this.EN_MISO = uvm_reg_field::type_id::create("EN_MISO",,get_full_name());
      this.EN_MISO.configure(this, 1, 7, "RW", 0, 0, 1, 0, 0);
      this.SEL_MOSI = uvm_reg_field::type_id::create("SEL_MOSI",,get_full_name());
      this.SEL_MOSI.configure(this, 6, 8, "RW", 0, 0, 1, 0, 0);
      this.EN_MOSI = uvm_reg_field::type_id::create("EN_MOSI",,get_full_name());
      this.EN_MOSI.configure(this, 1, 15, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_TOP_TMR_OUT_MOSI_MISO)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_TOP_TMR_OUT_MOSI_MISO


class ral_reg_TEST_TOP_TMR_OUT_BFWB_SYNCB extends uvm_reg;
	rand uvm_reg_field SEL_SYNCB;
	rand uvm_reg_field EN_SYNCB;
	rand uvm_reg_field SEL_BFWB;
	rand uvm_reg_field EN_BFWB;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   SEL_SYNCB: coverpoint {m_data[5:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   EN_SYNCB: coverpoint {m_data[7:7], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SEL_BFWB: coverpoint {m_data[13:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   EN_BFWB: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_TOP_TMR_OUT_BFWB_SYNCB");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.SEL_SYNCB = uvm_reg_field::type_id::create("SEL_SYNCB",,get_full_name());
      this.SEL_SYNCB.configure(this, 6, 0, "RW", 0, 0, 1, 0, 0);
      this.EN_SYNCB = uvm_reg_field::type_id::create("EN_SYNCB",,get_full_name());
      this.EN_SYNCB.configure(this, 1, 7, "RW", 0, 0, 1, 0, 0);
      this.SEL_BFWB = uvm_reg_field::type_id::create("SEL_BFWB",,get_full_name());
      this.SEL_BFWB.configure(this, 6, 8, "RW", 0, 0, 1, 0, 0);
      this.EN_BFWB = uvm_reg_field::type_id::create("EN_BFWB",,get_full_name());
      this.EN_BFWB.configure(this, 1, 15, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_TOP_TMR_OUT_BFWB_SYNCB)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_TOP_TMR_OUT_BFWB_SYNCB


class ral_reg_TEST_TOP_TMR_OUT_DAB_INTB extends uvm_reg;
	rand uvm_reg_field SEL_INTB;
	rand uvm_reg_field EN_INTB;
	rand uvm_reg_field SEL_DAB;
	rand uvm_reg_field EN_DAB;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   SEL_INTB: coverpoint {m_data[5:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   EN_INTB: coverpoint {m_data[7:7], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SEL_DAB: coverpoint {m_data[13:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   EN_DAB: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_TOP_TMR_OUT_DAB_INTB");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.SEL_INTB = uvm_reg_field::type_id::create("SEL_INTB",,get_full_name());
      this.SEL_INTB.configure(this, 6, 0, "RW", 0, 0, 1, 0, 0);
      this.EN_INTB = uvm_reg_field::type_id::create("EN_INTB",,get_full_name());
      this.EN_INTB.configure(this, 1, 7, "RW", 0, 0, 1, 0, 0);
      this.SEL_DAB = uvm_reg_field::type_id::create("SEL_DAB",,get_full_name());
      this.SEL_DAB.configure(this, 6, 8, "RW", 0, 0, 1, 0, 0);
      this.EN_DAB = uvm_reg_field::type_id::create("EN_DAB",,get_full_name());
      this.EN_DAB.configure(this, 1, 15, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_TOP_TMR_OUT_DAB_INTB)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_TOP_TMR_OUT_DAB_INTB


class ral_reg_TEST_TOP_TMR_OUT_RFC extends uvm_reg;
	rand uvm_reg_field SEL_RFC;
	rand uvm_reg_field EN_RFC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   SEL_RFC: coverpoint {m_data[5:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   EN_RFC: coverpoint {m_data[7:7], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_TOP_TMR_OUT_RFC");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.SEL_RFC = uvm_reg_field::type_id::create("SEL_RFC",,get_full_name());
      this.SEL_RFC.configure(this, 6, 0, "RW", 0, 0, 1, 0, 0);
      this.EN_RFC = uvm_reg_field::type_id::create("EN_RFC",,get_full_name());
      this.EN_RFC.configure(this, 1, 7, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_TOP_TMR_OUT_RFC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_TOP_TMR_OUT_RFC


class ral_regfile_TEST_TOP extends uvm_reg_file;

	rand ral_reg_TEST_TOP_TMR_ANA TMR_ANA;
	rand ral_reg_TEST_TOP_TMR_DIG TMR_DIG;
	rand ral_reg_TEST_TOP_TMR_IN TMR_IN;
	rand ral_reg_TEST_TOP_TMR_OUT_CSB_SCK TMR_OUT_CSB_SCK;
	rand ral_reg_TEST_TOP_TMR_OUT_MOSI_MISO TMR_OUT_MOSI_MISO;
	rand ral_reg_TEST_TOP_TMR_OUT_BFWB_SYNCB TMR_OUT_BFWB_SYNCB;
	rand ral_reg_TEST_TOP_TMR_OUT_DAB_INTB TMR_OUT_DAB_INTB;
	rand ral_reg_TEST_TOP_TMR_OUT_RFC TMR_OUT_RFC;


	function new(string name = "TEST_TOP");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.TMR_ANA = ral_reg_TEST_TOP_TMR_ANA::type_id::create("TMR_ANA",,get_full_name());
		if(this.TMR_ANA.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_ANA.cg_bits.option.name = {get_name(), ".TMR_ANA_bits"};
		this.TMR_ANA.configure(get_block(), this, "");
		this.TMR_ANA.build();
		this.TMR_ANA.add_hdl_path('{
            '{"i_TEST_TOP.i_TEST_TOP_TMR_ANA.ENABLE_ATB", 0, 1}
		});

		this.TMR_DIG = ral_reg_TEST_TOP_TMR_DIG::type_id::create("TMR_DIG",,get_full_name());
		if(this.TMR_DIG.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_DIG.cg_bits.option.name = {get_name(), ".TMR_DIG_bits"};
		this.TMR_DIG.configure(get_block(), this, "");
		this.TMR_DIG.build();
		this.TMR_DIG.add_hdl_path('{
            '{"i_TEST_TOP.i_TEST_TOP_TMR_DIG.USE_JTAG", 0, 1},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_DIG.SEL_SYNC", 1, 1},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_DIG.IGNORE_OSC_READY", 2, 1}
		});

		this.TMR_IN = ral_reg_TEST_TOP_TMR_IN::type_id::create("TMR_IN",,get_full_name());
		if(this.TMR_IN.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_IN.cg_bits.option.name = {get_name(), ".TMR_IN_bits"};
		this.TMR_IN.configure(get_block(), this, "");
		this.TMR_IN.build();
		this.TMR_IN.add_hdl_path('{
            '{"i_TEST_TOP.i_TEST_TOP_TMR_IN.tmr_in_0", 0, 4},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_IN.tmr_in_1", 4, 4},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_IN.tmr_in_2", 8, 4},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_IN.tmr_in_3", 12, 4}
		});

		this.TMR_OUT_CSB_SCK = ral_reg_TEST_TOP_TMR_OUT_CSB_SCK::type_id::create("TMR_OUT_CSB_SCK",,get_full_name());
		if(this.TMR_OUT_CSB_SCK.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_OUT_CSB_SCK.cg_bits.option.name = {get_name(), ".TMR_OUT_CSB_SCK_bits"};
		this.TMR_OUT_CSB_SCK.configure(get_block(), this, "");
		this.TMR_OUT_CSB_SCK.build();
		this.TMR_OUT_CSB_SCK.add_hdl_path('{
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_CSB_SCK.SEL_SCK", 0, 6},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_CSB_SCK.EN_SCK", 7, 1},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_CSB_SCK.SEL_CSB", 8, 6},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_CSB_SCK.EN_CSB", 15, 1}
		});

		this.TMR_OUT_MOSI_MISO = ral_reg_TEST_TOP_TMR_OUT_MOSI_MISO::type_id::create("TMR_OUT_MOSI_MISO",,get_full_name());
		if(this.TMR_OUT_MOSI_MISO.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_OUT_MOSI_MISO.cg_bits.option.name = {get_name(), ".TMR_OUT_MOSI_MISO_bits"};
		this.TMR_OUT_MOSI_MISO.configure(get_block(), this, "");
		this.TMR_OUT_MOSI_MISO.build();
		this.TMR_OUT_MOSI_MISO.add_hdl_path('{
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_MOSI_MISO.SEL_MISO", 0, 6},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_MOSI_MISO.EN_MISO", 7, 1},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_MOSI_MISO.SEL_MOSI", 8, 6},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_MOSI_MISO.EN_MOSI", 15, 1}
		});

		this.TMR_OUT_BFWB_SYNCB = ral_reg_TEST_TOP_TMR_OUT_BFWB_SYNCB::type_id::create("TMR_OUT_BFWB_SYNCB",,get_full_name());
		if(this.TMR_OUT_BFWB_SYNCB.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_OUT_BFWB_SYNCB.cg_bits.option.name = {get_name(), ".TMR_OUT_BFWB_SYNCB_bits"};
		this.TMR_OUT_BFWB_SYNCB.configure(get_block(), this, "");
		this.TMR_OUT_BFWB_SYNCB.build();
		this.TMR_OUT_BFWB_SYNCB.add_hdl_path('{
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_BFWB_SYNCB.SEL_SYNCB", 0, 6},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_BFWB_SYNCB.EN_SYNCB", 7, 1},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_BFWB_SYNCB.SEL_BFWB", 8, 6},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_BFWB_SYNCB.EN_BFWB", 15, 1}
		});

		this.TMR_OUT_DAB_INTB = ral_reg_TEST_TOP_TMR_OUT_DAB_INTB::type_id::create("TMR_OUT_DAB_INTB",,get_full_name());
		if(this.TMR_OUT_DAB_INTB.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_OUT_DAB_INTB.cg_bits.option.name = {get_name(), ".TMR_OUT_DAB_INTB_bits"};
		this.TMR_OUT_DAB_INTB.configure(get_block(), this, "");
		this.TMR_OUT_DAB_INTB.build();
		this.TMR_OUT_DAB_INTB.add_hdl_path('{
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_DAB_INTB.SEL_INTB", 0, 6},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_DAB_INTB.EN_INTB", 7, 1},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_DAB_INTB.SEL_DAB", 8, 6},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_DAB_INTB.EN_DAB", 15, 1}
		});

		this.TMR_OUT_RFC = ral_reg_TEST_TOP_TMR_OUT_RFC::type_id::create("TMR_OUT_RFC",,get_full_name());
		if(this.TMR_OUT_RFC.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_OUT_RFC.cg_bits.option.name = {get_name(), ".TMR_OUT_RFC_bits"};
		this.TMR_OUT_RFC.configure(get_block(), this, "");
		this.TMR_OUT_RFC.build();
		this.TMR_OUT_RFC.add_hdl_path('{
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_RFC.SEL_RFC", 0, 6},
            '{"i_TEST_TOP.i_TEST_TOP_TMR_OUT_RFC.EN_RFC", 7, 1}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(TMR_ANA, offset+`UVM_REG_ADDR_WIDTH'h1);
	  mp.add_reg(TMR_DIG, offset+`UVM_REG_ADDR_WIDTH'h2);
	  mp.add_reg(TMR_IN, offset+`UVM_REG_ADDR_WIDTH'h5);
	  mp.add_reg(TMR_OUT_CSB_SCK, offset+`UVM_REG_ADDR_WIDTH'h6);
	  mp.add_reg(TMR_OUT_MOSI_MISO, offset+`UVM_REG_ADDR_WIDTH'h7);
	  mp.add_reg(TMR_OUT_BFWB_SYNCB, offset+`UVM_REG_ADDR_WIDTH'h8);
	  mp.add_reg(TMR_OUT_DAB_INTB, offset+`UVM_REG_ADDR_WIDTH'h9);
	  mp.add_reg(TMR_OUT_RFC, offset+`UVM_REG_ADDR_WIDTH'hA);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  TMR_ANA.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h1);
	  TMR_DIG.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h2);
	  TMR_IN.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h5);
	  TMR_OUT_CSB_SCK.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h6);
	  TMR_OUT_MOSI_MISO.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h7);
	  TMR_OUT_BFWB_SYNCB.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h8);
	  TMR_OUT_DAB_INTB.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h9);
	  TMR_OUT_RFC.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hA);

	endfunction

	`uvm_object_utils(ral_regfile_TEST_TOP)
endclass : ral_regfile_TEST_TOP




class ral_reg_JTAG_standard_registers_JTAG_ID extends uvm_reg;
	uvm_reg_field MANUFACTURER;
	uvm_reg_field PROJECT;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MANUFACTURER: coverpoint {m_data[11:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {12'b??????????00};
	      wildcard bins bit_0_wr_as_1 = {12'b??????????10};
	      wildcard bins bit_0_rd_as_0 = {12'b??????????01};
	      wildcard bins bit_0_rd_as_1 = {12'b??????????11};
	      wildcard bins bit_1_wr_as_0 = {12'b?????????0?0};
	      wildcard bins bit_1_wr_as_1 = {12'b?????????1?0};
	      wildcard bins bit_1_rd_as_0 = {12'b?????????0?1};
	      wildcard bins bit_1_rd_as_1 = {12'b?????????1?1};
	      wildcard bins bit_2_wr_as_0 = {12'b????????0??0};
	      wildcard bins bit_2_wr_as_1 = {12'b????????1??0};
	      wildcard bins bit_2_rd_as_0 = {12'b????????0??1};
	      wildcard bins bit_2_rd_as_1 = {12'b????????1??1};
	      wildcard bins bit_3_wr_as_0 = {12'b???????0???0};
	      wildcard bins bit_3_wr_as_1 = {12'b???????1???0};
	      wildcard bins bit_3_rd_as_0 = {12'b???????0???1};
	      wildcard bins bit_3_rd_as_1 = {12'b???????1???1};
	      wildcard bins bit_4_wr_as_0 = {12'b??????0????0};
	      wildcard bins bit_4_wr_as_1 = {12'b??????1????0};
	      wildcard bins bit_4_rd_as_0 = {12'b??????0????1};
	      wildcard bins bit_4_rd_as_1 = {12'b??????1????1};
	      wildcard bins bit_5_wr_as_0 = {12'b?????0?????0};
	      wildcard bins bit_5_wr_as_1 = {12'b?????1?????0};
	      wildcard bins bit_5_rd_as_0 = {12'b?????0?????1};
	      wildcard bins bit_5_rd_as_1 = {12'b?????1?????1};
	      wildcard bins bit_6_wr_as_0 = {12'b????0??????0};
	      wildcard bins bit_6_wr_as_1 = {12'b????1??????0};
	      wildcard bins bit_6_rd_as_0 = {12'b????0??????1};
	      wildcard bins bit_6_rd_as_1 = {12'b????1??????1};
	      wildcard bins bit_7_wr_as_0 = {12'b???0???????0};
	      wildcard bins bit_7_wr_as_1 = {12'b???1???????0};
	      wildcard bins bit_7_rd_as_0 = {12'b???0???????1};
	      wildcard bins bit_7_rd_as_1 = {12'b???1???????1};
	      wildcard bins bit_8_wr_as_0 = {12'b??0????????0};
	      wildcard bins bit_8_wr_as_1 = {12'b??1????????0};
	      wildcard bins bit_8_rd_as_0 = {12'b??0????????1};
	      wildcard bins bit_8_rd_as_1 = {12'b??1????????1};
	      wildcard bins bit_9_wr_as_0 = {12'b?0?????????0};
	      wildcard bins bit_9_wr_as_1 = {12'b?1?????????0};
	      wildcard bins bit_9_rd_as_0 = {12'b?0?????????1};
	      wildcard bins bit_9_rd_as_1 = {12'b?1?????????1};
	      wildcard bins bit_10_wr_as_0 = {12'b0??????????0};
	      wildcard bins bit_10_wr_as_1 = {12'b1??????????0};
	      wildcard bins bit_10_rd_as_0 = {12'b0??????????1};
	      wildcard bins bit_10_rd_as_1 = {12'b1??????????1};
	      option.weight = 44;
	   }
	   PROJECT: coverpoint {m_data[27:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd_as_0 = {17'b???????????????01};
	      wildcard bins bit_0_rd_as_1 = {17'b???????????????11};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {17'b??????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {17'b??????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {17'b?????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {17'b?????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {17'b????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {17'b????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd_as_0 = {17'b???????????0????1};
	      wildcard bins bit_4_rd_as_1 = {17'b???????????1????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {17'b??????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {17'b??????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {17'b?????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {17'b?????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {17'b????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {17'b????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd_as_0 = {17'b???????0????????1};
	      wildcard bins bit_8_rd_as_1 = {17'b???????1????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {17'b??????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {17'b??????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {17'b?????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {17'b?????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {17'b????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {17'b????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd_as_0 = {17'b???0????????????1};
	      wildcard bins bit_12_rd_as_1 = {17'b???1????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {17'b??0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {17'b??1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {17'b?0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {17'b?1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {17'b0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {17'b1???????????????1};
	      option.weight = 64;
	   }
	endgroup
	function new(string name = "JTAG_standard_registers_JTAG_ID");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MANUFACTURER = uvm_reg_field::type_id::create("MANUFACTURER",,get_full_name());
      this.MANUFACTURER.configure(this, 11, 1, "RO", 0, 69, 1, 0, 0);
      this.PROJECT = uvm_reg_field::type_id::create("PROJECT",,get_full_name());
      this.PROJECT.configure(this, 16, 12, "RO", 0, 52144, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_JTAG_standard_registers_JTAG_ID)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_JTAG_standard_registers_JTAG_ID


class ral_reg_JTAG_standard_registers_JTAG_BYPASS extends uvm_reg;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	endgroup
	function new(string name = "JTAG_standard_registers_JTAG_BYPASS");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
   endfunction: build

	`uvm_object_utils(ral_reg_JTAG_standard_registers_JTAG_BYPASS)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_JTAG_standard_registers_JTAG_BYPASS


class ral_regfile_JTAG_standard_registers extends uvm_reg_file;

	rand ral_reg_JTAG_standard_registers_JTAG_ID JTAG_ID;
	rand ral_reg_JTAG_standard_registers_JTAG_BYPASS JTAG_BYPASS;


	function new(string name = "JTAG_standard_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.JTAG_ID = ral_reg_JTAG_standard_registers_JTAG_ID::type_id::create("JTAG_ID",,get_full_name());
		if(this.JTAG_ID.has_coverage(UVM_CVR_REG_BITS))
			this.JTAG_ID.cg_bits.option.name = {get_name(), ".JTAG_ID_bits"};
		this.JTAG_ID.configure(get_block(), this, "");
		this.JTAG_ID.build();
		this.JTAG_ID.add_hdl_path('{
            '{"i_JTAG_standard_registers.i_JTAG_standard_registers_JTAG_ID.MANUFACTURER", 1, 11},
            '{"i_JTAG_standard_registers.i_JTAG_standard_registers_JTAG_ID.PROJECT", 12, 16}
		});

		this.JTAG_BYPASS = ral_reg_JTAG_standard_registers_JTAG_BYPASS::type_id::create("JTAG_BYPASS",,get_full_name());
		if(this.JTAG_BYPASS.has_coverage(UVM_CVR_REG_BITS))
			this.JTAG_BYPASS.cg_bits.option.name = {get_name(), ".JTAG_BYPASS_bits"};
		this.JTAG_BYPASS.configure(get_block(), this, "");
		this.JTAG_BYPASS.build();
		this.JTAG_BYPASS.add_hdl_path('{

		   '{"i_JTAG_standard_registers.i_JTAG_standard_registers_JTAG_BYPASS", -1, -1}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(JTAG_ID, offset+`UVM_REG_ADDR_WIDTH'hFB);
	  mp.add_reg(JTAG_BYPASS, offset+`UVM_REG_ADDR_WIDTH'hFF);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  JTAG_ID.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hFB);
	  JTAG_BYPASS.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hFF);

	endfunction

	`uvm_object_utils(ral_regfile_JTAG_standard_registers)
endclass : ral_regfile_JTAG_standard_registers




class ral_block_test_top extends uvm_reg_block;
	rand ral_regfile_TEST_TOP TEST_TOP;
	rand ral_regfile_JTAG_standard_registers JTAG_standard_registers;

	function new(string name = "test_top");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.TEST_TOP = ral_regfile_TEST_TOP::type_id::create("TEST_TOP",,get_full_name());
      this.TEST_TOP.configure(this, null, "");
      this.TEST_TOP.build();
      this.TEST_TOP.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
      this.JTAG_standard_registers = ral_regfile_JTAG_standard_registers::type_id::create("JTAG_standard_registers",,get_full_name());
      this.JTAG_standard_registers.configure(this, null, "");
      this.JTAG_standard_registers.build();
      this.JTAG_standard_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_test_top)

endclass : ral_block_test_top


class ral_reg_TEST_SUPPLY_TMR_ANA_SUPPLY extends uvm_reg;
	rand uvm_reg_field IBP10U_2_ATB;
	rand uvm_reg_field IC5U_2_ATB;
	rand uvm_reg_field VDDD_2_ATB;
	rand uvm_reg_field VBG_2_ATB;
	rand uvm_reg_field VRR_2_ATB;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   IBP10U_2_ATB: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   IC5U_2_ATB: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VDDD_2_ATB: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VBG_2_ATB: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VRR_2_ATB: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_SUPPLY_TMR_ANA_SUPPLY");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.IBP10U_2_ATB = uvm_reg_field::type_id::create("IBP10U_2_ATB",,get_full_name());
      this.IBP10U_2_ATB.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.IC5U_2_ATB = uvm_reg_field::type_id::create("IC5U_2_ATB",,get_full_name());
      this.IC5U_2_ATB.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
      this.VDDD_2_ATB = uvm_reg_field::type_id::create("VDDD_2_ATB",,get_full_name());
      this.VDDD_2_ATB.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
      this.VBG_2_ATB = uvm_reg_field::type_id::create("VBG_2_ATB",,get_full_name());
      this.VBG_2_ATB.configure(this, 1, 3, "RW", 0, 0, 1, 0, 0);
      this.VRR_2_ATB = uvm_reg_field::type_id::create("VRR_2_ATB",,get_full_name());
      this.VRR_2_ATB.configure(this, 1, 4, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_SUPPLY_TMR_ANA_SUPPLY)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_SUPPLY_TMR_ANA_SUPPLY


class ral_reg_TEST_SUPPLY_TMR_ANA_TEMP_SENSOR extends uvm_reg;
	rand uvm_reg_field TS_2_ATB;
	rand uvm_reg_field DISCONNECT_TS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TS_2_ATB: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   DISCONNECT_TS: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_SUPPLY_TMR_ANA_TEMP_SENSOR");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TS_2_ATB = uvm_reg_field::type_id::create("TS_2_ATB",,get_full_name());
      this.TS_2_ATB.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.DISCONNECT_TS = uvm_reg_field::type_id::create("DISCONNECT_TS",,get_full_name());
      this.DISCONNECT_TS.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_SUPPLY_TMR_ANA_TEMP_SENSOR)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_SUPPLY_TMR_ANA_TEMP_SENSOR


class ral_reg_TEST_SUPPLY_TMR_ANA_OTP extends uvm_reg;
	rand uvm_reg_field OTP_VBG;
	rand uvm_reg_field OTP_VREF;
	rand uvm_reg_field OTP_VRR;
	rand uvm_reg_field OTP_VPP;
	rand uvm_reg_field OTP_VPP_LOAD;
	rand uvm_reg_field OTP_VRR_LOAD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OTP_VBG: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTP_VREF: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTP_VRR: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTP_VPP: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTP_VPP_LOAD: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTP_VRR_LOAD: coverpoint {m_data[5:5], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_SUPPLY_TMR_ANA_OTP");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OTP_VBG = uvm_reg_field::type_id::create("OTP_VBG",,get_full_name());
      this.OTP_VBG.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.OTP_VREF = uvm_reg_field::type_id::create("OTP_VREF",,get_full_name());
      this.OTP_VREF.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
      this.OTP_VRR = uvm_reg_field::type_id::create("OTP_VRR",,get_full_name());
      this.OTP_VRR.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
      this.OTP_VPP = uvm_reg_field::type_id::create("OTP_VPP",,get_full_name());
      this.OTP_VPP.configure(this, 1, 3, "RW", 0, 0, 1, 0, 0);
      this.OTP_VPP_LOAD = uvm_reg_field::type_id::create("OTP_VPP_LOAD",,get_full_name());
      this.OTP_VPP_LOAD.configure(this, 1, 4, "RW", 0, 0, 1, 0, 0);
      this.OTP_VRR_LOAD = uvm_reg_field::type_id::create("OTP_VRR_LOAD",,get_full_name());
      this.OTP_VRR_LOAD.configure(this, 1, 5, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_SUPPLY_TMR_ANA_OTP)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_SUPPLY_TMR_ANA_OTP


class ral_reg_TEST_SUPPLY_TMR_DIG_SUPPLY extends uvm_reg;
	rand uvm_reg_field PREVENT_OVERTEMPERATURE_SWITCH_OFF;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PREVENT_OVERTEMPERATURE_SWITCH_OFF: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_SUPPLY_TMR_DIG_SUPPLY");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PREVENT_OVERTEMPERATURE_SWITCH_OFF = uvm_reg_field::type_id::create("PREVENT_OVERTEMPERATURE_SWITCH_OFF",,get_full_name());
      this.PREVENT_OVERTEMPERATURE_SWITCH_OFF.configure(this, 1, 0, "RW", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_SUPPLY_TMR_DIG_SUPPLY)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_SUPPLY_TMR_DIG_SUPPLY


class ral_regfile_TEST_SUPPLY extends uvm_reg_file;

	rand ral_reg_TEST_SUPPLY_TMR_ANA_SUPPLY TMR_ANA_SUPPLY;
	rand ral_reg_TEST_SUPPLY_TMR_ANA_TEMP_SENSOR TMR_ANA_TEMP_SENSOR;
	rand ral_reg_TEST_SUPPLY_TMR_ANA_OTP TMR_ANA_OTP;
	rand ral_reg_TEST_SUPPLY_TMR_DIG_SUPPLY TMR_DIG_SUPPLY;


	function new(string name = "TEST_SUPPLY");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.TMR_ANA_SUPPLY = ral_reg_TEST_SUPPLY_TMR_ANA_SUPPLY::type_id::create("TMR_ANA_SUPPLY",,get_full_name());
		if(this.TMR_ANA_SUPPLY.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_ANA_SUPPLY.cg_bits.option.name = {get_name(), ".TMR_ANA_SUPPLY_bits"};
		this.TMR_ANA_SUPPLY.configure(get_block(), this, "");
		this.TMR_ANA_SUPPLY.build();
		this.TMR_ANA_SUPPLY.add_hdl_path('{
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_SUPPLY.IBP10U_2_ATB", 0, 1},
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_SUPPLY.IC5U_2_ATB", 1, 1},
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_SUPPLY.VDDD_2_ATB", 2, 1},
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_SUPPLY.VBG_2_ATB", 3, 1},
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_SUPPLY.VRR_2_ATB", 4, 1}
		});

		this.TMR_ANA_TEMP_SENSOR = ral_reg_TEST_SUPPLY_TMR_ANA_TEMP_SENSOR::type_id::create("TMR_ANA_TEMP_SENSOR",,get_full_name());
		if(this.TMR_ANA_TEMP_SENSOR.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_ANA_TEMP_SENSOR.cg_bits.option.name = {get_name(), ".TMR_ANA_TEMP_SENSOR_bits"};
		this.TMR_ANA_TEMP_SENSOR.configure(get_block(), this, "");
		this.TMR_ANA_TEMP_SENSOR.build();
		this.TMR_ANA_TEMP_SENSOR.add_hdl_path('{
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_TEMP_SENSOR.TS_2_ATB", 0, 1},
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_TEMP_SENSOR.DISCONNECT_TS", 1, 1}
		});

		this.TMR_ANA_OTP = ral_reg_TEST_SUPPLY_TMR_ANA_OTP::type_id::create("TMR_ANA_OTP",,get_full_name());
		if(this.TMR_ANA_OTP.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_ANA_OTP.cg_bits.option.name = {get_name(), ".TMR_ANA_OTP_bits"};
		this.TMR_ANA_OTP.configure(get_block(), this, "");
		this.TMR_ANA_OTP.build();
		this.TMR_ANA_OTP.add_hdl_path('{
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_OTP.OTP_VBG", 0, 1},
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_OTP.OTP_VREF", 1, 1},
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_OTP.OTP_VRR", 2, 1},
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_OTP.OTP_VPP", 3, 1},
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_OTP.OTP_VPP_LOAD", 4, 1},
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_ANA_OTP.OTP_VRR_LOAD", 5, 1}
		});

		this.TMR_DIG_SUPPLY = ral_reg_TEST_SUPPLY_TMR_DIG_SUPPLY::type_id::create("TMR_DIG_SUPPLY",,get_full_name());
		if(this.TMR_DIG_SUPPLY.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_DIG_SUPPLY.cg_bits.option.name = {get_name(), ".TMR_DIG_SUPPLY_bits"};
		this.TMR_DIG_SUPPLY.configure(get_block(), this, "");
		this.TMR_DIG_SUPPLY.build();
		this.TMR_DIG_SUPPLY.add_hdl_path('{
            '{"i_TEST_SUPPLY.i_TEST_SUPPLY_TMR_DIG_SUPPLY.PREVENT_OVERTEMPERATURE_SWITCH_OFF", 0, 1}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(TMR_ANA_SUPPLY, offset+`UVM_REG_ADDR_WIDTH'h0);
	  mp.add_reg(TMR_ANA_TEMP_SENSOR, offset+`UVM_REG_ADDR_WIDTH'h4);
	  mp.add_reg(TMR_ANA_OTP, offset+`UVM_REG_ADDR_WIDTH'h5);
	  mp.add_reg(TMR_DIG_SUPPLY, offset+`UVM_REG_ADDR_WIDTH'h1);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  TMR_ANA_SUPPLY.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h0);
	  TMR_ANA_TEMP_SENSOR.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h4);
	  TMR_ANA_OTP.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h5);
	  TMR_DIG_SUPPLY.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h1);

	endfunction

	`uvm_object_utils(ral_regfile_TEST_SUPPLY)
endclass : ral_regfile_TEST_SUPPLY




class ral_block_test_supply extends uvm_reg_block;
	rand ral_regfile_TEST_SUPPLY TEST_SUPPLY;

	function new(string name = "test_supply");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.TEST_SUPPLY = ral_regfile_TEST_SUPPLY::type_id::create("TEST_SUPPLY",,get_full_name());
      this.TEST_SUPPLY.configure(this, null, "");
      this.TEST_SUPPLY.build();
      this.TEST_SUPPLY.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_test_supply)

endclass : ral_block_test_supply


class ral_reg_TEST_OSC_TMR_ANA_TB_PLL extends uvm_reg;
	rand uvm_reg_field PLL_IC5U;
	rand uvm_reg_field PLL_DOWN;
	rand uvm_reg_field PLL_UP;
	rand uvm_reg_field PLL_HiZ;
	rand uvm_reg_field PLL_PD_N;
	rand uvm_reg_field PLL_VCTRL;
	rand uvm_reg_field PLL_VTUNE;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PLL_IC5U: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PLL_DOWN: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PLL_UP: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PLL_HiZ: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PLL_PD_N: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PLL_VCTRL: coverpoint {m_data[5:5], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PLL_VTUNE: coverpoint {m_data[6:6], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_OSC_TMR_ANA_TB_PLL");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PLL_IC5U = uvm_reg_field::type_id::create("PLL_IC5U",,get_full_name());
      this.PLL_IC5U.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.PLL_DOWN = uvm_reg_field::type_id::create("PLL_DOWN",,get_full_name());
      this.PLL_DOWN.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
      this.PLL_UP = uvm_reg_field::type_id::create("PLL_UP",,get_full_name());
      this.PLL_UP.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
      this.PLL_HiZ = uvm_reg_field::type_id::create("PLL_HiZ",,get_full_name());
      this.PLL_HiZ.configure(this, 1, 3, "RW", 0, 0, 1, 0, 0);
      this.PLL_PD_N = uvm_reg_field::type_id::create("PLL_PD_N",,get_full_name());
      this.PLL_PD_N.configure(this, 1, 4, "RW", 0, 0, 1, 0, 0);
      this.PLL_VCTRL = uvm_reg_field::type_id::create("PLL_VCTRL",,get_full_name());
      this.PLL_VCTRL.configure(this, 1, 5, "RW", 0, 0, 1, 0, 0);
      this.PLL_VTUNE = uvm_reg_field::type_id::create("PLL_VTUNE",,get_full_name());
      this.PLL_VTUNE.configure(this, 1, 6, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_OSC_TMR_ANA_TB_PLL)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_OSC_TMR_ANA_TB_PLL


class ral_reg_TEST_OSC_TMR_ANA_TB_OSC extends uvm_reg;
	rand uvm_reg_field OSC_SFMIN;
	rand uvm_reg_field OSC_SFMAX;
	rand uvm_reg_field OSC_PREAMP;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OSC_SFMIN: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OSC_SFMAX: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OSC_PREAMP: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_OSC_TMR_ANA_TB_OSC");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OSC_SFMIN = uvm_reg_field::type_id::create("OSC_SFMIN",,get_full_name());
      this.OSC_SFMIN.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.OSC_SFMAX = uvm_reg_field::type_id::create("OSC_SFMAX",,get_full_name());
      this.OSC_SFMAX.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
      this.OSC_PREAMP = uvm_reg_field::type_id::create("OSC_PREAMP",,get_full_name());
      this.OSC_PREAMP.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_OSC_TMR_ANA_TB_OSC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_OSC_TMR_ANA_TB_OSC


class ral_reg_TEST_OSC_TMR_DIG_TB extends uvm_reg;
	rand uvm_reg_field CLKSW_TST_EN;
	rand uvm_reg_field CLKSW_TST_SEL;
	rand uvm_reg_field CLK_AUTO_TRIM_EN;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CLKSW_TST_EN: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CLKSW_TST_SEL: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CLK_AUTO_TRIM_EN: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_OSC_TMR_DIG_TB");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CLKSW_TST_EN = uvm_reg_field::type_id::create("CLKSW_TST_EN",,get_full_name());
      this.CLKSW_TST_EN.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.CLKSW_TST_SEL = uvm_reg_field::type_id::create("CLKSW_TST_SEL",,get_full_name());
      this.CLKSW_TST_SEL.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
      this.CLK_AUTO_TRIM_EN = uvm_reg_field::type_id::create("CLK_AUTO_TRIM_EN",,get_full_name());
      this.CLK_AUTO_TRIM_EN.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_OSC_TMR_DIG_TB)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_OSC_TMR_DIG_TB


class ral_reg_TEST_OSC_TMR_VAL_TB extends uvm_reg;
	rand uvm_reg_field PLL_ON;
	rand uvm_reg_field PLL_HOLD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PLL_ON: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PLL_HOLD: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_OSC_TMR_VAL_TB");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PLL_ON = uvm_reg_field::type_id::create("PLL_ON",,get_full_name());
      this.PLL_ON.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.PLL_HOLD = uvm_reg_field::type_id::create("PLL_HOLD",,get_full_name());
      this.PLL_HOLD.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_OSC_TMR_VAL_TB)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_OSC_TMR_VAL_TB


class ral_reg_TEST_OSC_TMR_SEL_TB extends uvm_reg;
	rand uvm_reg_field PLL_ON;
	rand uvm_reg_field PLL_HOLD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PLL_ON: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PLL_HOLD: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_OSC_TMR_SEL_TB");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PLL_ON = uvm_reg_field::type_id::create("PLL_ON",,get_full_name());
      this.PLL_ON.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.PLL_HOLD = uvm_reg_field::type_id::create("PLL_HOLD",,get_full_name());
      this.PLL_HOLD.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_OSC_TMR_SEL_TB)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_OSC_TMR_SEL_TB


class ral_regfile_TEST_OSC extends uvm_reg_file;

	rand ral_reg_TEST_OSC_TMR_ANA_TB_PLL TMR_ANA_TB_PLL;
	rand ral_reg_TEST_OSC_TMR_ANA_TB_OSC TMR_ANA_TB_OSC;
	rand ral_reg_TEST_OSC_TMR_DIG_TB TMR_DIG_TB;
	rand ral_reg_TEST_OSC_TMR_VAL_TB TMR_VAL_TB;
	rand ral_reg_TEST_OSC_TMR_SEL_TB TMR_SEL_TB;


	function new(string name = "TEST_OSC");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.TMR_ANA_TB_PLL = ral_reg_TEST_OSC_TMR_ANA_TB_PLL::type_id::create("TMR_ANA_TB_PLL",,get_full_name());
		if(this.TMR_ANA_TB_PLL.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_ANA_TB_PLL.cg_bits.option.name = {get_name(), ".TMR_ANA_TB_PLL_bits"};
		this.TMR_ANA_TB_PLL.configure(get_block(), this, "");
		this.TMR_ANA_TB_PLL.build();
		this.TMR_ANA_TB_PLL.add_hdl_path('{
            '{"i_TEST_OSC.i_TEST_OSC_TMR_ANA_TB_PLL.PLL_IC5U", 0, 1},
            '{"i_TEST_OSC.i_TEST_OSC_TMR_ANA_TB_PLL.PLL_DOWN", 1, 1},
            '{"i_TEST_OSC.i_TEST_OSC_TMR_ANA_TB_PLL.PLL_UP", 2, 1},
            '{"i_TEST_OSC.i_TEST_OSC_TMR_ANA_TB_PLL.PLL_HiZ", 3, 1},
            '{"i_TEST_OSC.i_TEST_OSC_TMR_ANA_TB_PLL.PLL_PD_N", 4, 1},
            '{"i_TEST_OSC.i_TEST_OSC_TMR_ANA_TB_PLL.PLL_VCTRL", 5, 1},
            '{"i_TEST_OSC.i_TEST_OSC_TMR_ANA_TB_PLL.PLL_VTUNE", 6, 1}
		});

		this.TMR_ANA_TB_OSC = ral_reg_TEST_OSC_TMR_ANA_TB_OSC::type_id::create("TMR_ANA_TB_OSC",,get_full_name());
		if(this.TMR_ANA_TB_OSC.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_ANA_TB_OSC.cg_bits.option.name = {get_name(), ".TMR_ANA_TB_OSC_bits"};
		this.TMR_ANA_TB_OSC.configure(get_block(), this, "");
		this.TMR_ANA_TB_OSC.build();
		this.TMR_ANA_TB_OSC.add_hdl_path('{
            '{"i_TEST_OSC.i_TEST_OSC_TMR_ANA_TB_OSC.OSC_SFMIN", 0, 1},
            '{"i_TEST_OSC.i_TEST_OSC_TMR_ANA_TB_OSC.OSC_SFMAX", 1, 1},
            '{"i_TEST_OSC.i_TEST_OSC_TMR_ANA_TB_OSC.OSC_PREAMP", 2, 1}
		});

		this.TMR_DIG_TB = ral_reg_TEST_OSC_TMR_DIG_TB::type_id::create("TMR_DIG_TB",,get_full_name());
		if(this.TMR_DIG_TB.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_DIG_TB.cg_bits.option.name = {get_name(), ".TMR_DIG_TB_bits"};
		this.TMR_DIG_TB.configure(get_block(), this, "");
		this.TMR_DIG_TB.build();
		this.TMR_DIG_TB.add_hdl_path('{
            '{"i_TEST_OSC.i_TEST_OSC_TMR_DIG_TB.CLKSW_TST_EN", 0, 1},
            '{"i_TEST_OSC.i_TEST_OSC_TMR_DIG_TB.CLKSW_TST_SEL", 1, 1},
            '{"i_TEST_OSC.i_TEST_OSC_TMR_DIG_TB.CLK_AUTO_TRIM_EN", 2, 1}
		});

		this.TMR_VAL_TB = ral_reg_TEST_OSC_TMR_VAL_TB::type_id::create("TMR_VAL_TB",,get_full_name());
		if(this.TMR_VAL_TB.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_VAL_TB.cg_bits.option.name = {get_name(), ".TMR_VAL_TB_bits"};
		this.TMR_VAL_TB.configure(get_block(), this, "");
		this.TMR_VAL_TB.build();
		this.TMR_VAL_TB.add_hdl_path('{
            '{"i_TEST_OSC.i_TEST_OSC_TMR_VAL_TB.PLL_ON", 0, 1},
            '{"i_TEST_OSC.i_TEST_OSC_TMR_VAL_TB.PLL_HOLD", 1, 1}
		});

		this.TMR_SEL_TB = ral_reg_TEST_OSC_TMR_SEL_TB::type_id::create("TMR_SEL_TB",,get_full_name());
		if(this.TMR_SEL_TB.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_SEL_TB.cg_bits.option.name = {get_name(), ".TMR_SEL_TB_bits"};
		this.TMR_SEL_TB.configure(get_block(), this, "");
		this.TMR_SEL_TB.build();
		this.TMR_SEL_TB.add_hdl_path('{
            '{"i_TEST_OSC.i_TEST_OSC_TMR_SEL_TB.PLL_ON", 0, 1},
            '{"i_TEST_OSC.i_TEST_OSC_TMR_SEL_TB.PLL_HOLD", 1, 1}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(TMR_ANA_TB_PLL, offset+`UVM_REG_ADDR_WIDTH'h0);
	  mp.add_reg(TMR_ANA_TB_OSC, offset+`UVM_REG_ADDR_WIDTH'h1);
	  mp.add_reg(TMR_DIG_TB, offset+`UVM_REG_ADDR_WIDTH'h2);
	  mp.add_reg(TMR_VAL_TB, offset+`UVM_REG_ADDR_WIDTH'h3);
	  mp.add_reg(TMR_SEL_TB, offset+`UVM_REG_ADDR_WIDTH'h4);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  TMR_ANA_TB_PLL.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h0);
	  TMR_ANA_TB_OSC.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h1);
	  TMR_DIG_TB.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h2);
	  TMR_VAL_TB.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h3);
	  TMR_SEL_TB.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h4);

	endfunction

	`uvm_object_utils(ral_regfile_TEST_OSC)
endclass : ral_regfile_TEST_OSC




class ral_block_test_osc extends uvm_reg_block;
	rand ral_regfile_TEST_OSC TEST_OSC;

	function new(string name = "test_osc");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.TEST_OSC = ral_regfile_TEST_OSC::type_id::create("TEST_OSC",,get_full_name());
      this.TEST_OSC.configure(this, null, "");
      this.TEST_OSC.build();
      this.TEST_OSC.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_test_osc)

endclass : ral_block_test_osc


class ral_reg_TEST_DSI_TMR_ANA_DSI3_TX extends uvm_reg;
	rand uvm_reg_field VNC2_CH1_2;
	rand uvm_reg_field VNC0_CH1_2;
	rand uvm_reg_field VNG0_CH1_2;
	rand uvm_reg_field INN_CH1_2;
	rand uvm_reg_field INP_CH1_2;
	rand uvm_reg_field VBN5V_DIV_CH1_2;
	rand uvm_reg_field IDAC_TX_CH1_2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   VNC2_CH1_2: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VNC0_CH1_2: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VNG0_CH1_2: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   INN_CH1_2: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   INP_CH1_2: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VBN5V_DIV_CH1_2: coverpoint {m_data[5:5], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   IDAC_TX_CH1_2: coverpoint {m_data[6:6], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_DSI_TMR_ANA_DSI3_TX");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.VNC2_CH1_2 = uvm_reg_field::type_id::create("VNC2_CH1_2",,get_full_name());
      this.VNC2_CH1_2.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.VNC0_CH1_2 = uvm_reg_field::type_id::create("VNC0_CH1_2",,get_full_name());
      this.VNC0_CH1_2.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
      this.VNG0_CH1_2 = uvm_reg_field::type_id::create("VNG0_CH1_2",,get_full_name());
      this.VNG0_CH1_2.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
      this.INN_CH1_2 = uvm_reg_field::type_id::create("INN_CH1_2",,get_full_name());
      this.INN_CH1_2.configure(this, 1, 3, "RW", 0, 0, 1, 0, 0);
      this.INP_CH1_2 = uvm_reg_field::type_id::create("INP_CH1_2",,get_full_name());
      this.INP_CH1_2.configure(this, 1, 4, "RW", 0, 0, 1, 0, 0);
      this.VBN5V_DIV_CH1_2 = uvm_reg_field::type_id::create("VBN5V_DIV_CH1_2",,get_full_name());
      this.VBN5V_DIV_CH1_2.configure(this, 1, 5, "RW", 0, 0, 1, 0, 0);
      this.IDAC_TX_CH1_2 = uvm_reg_field::type_id::create("IDAC_TX_CH1_2",,get_full_name());
      this.IDAC_TX_CH1_2.configure(this, 1, 6, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_DSI_TMR_ANA_DSI3_TX)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_DSI_TMR_ANA_DSI3_TX


class ral_reg_TEST_DSI_TMR_ANA_DSI3_RX extends uvm_reg;
	rand uvm_reg_field I_Q_2_ATB;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   I_Q_2_ATB: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_DSI_TMR_ANA_DSI3_RX");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.I_Q_2_ATB = uvm_reg_field::type_id::create("I_Q_2_ATB",,get_full_name());
      this.I_Q_2_ATB.configure(this, 1, 0, "RW", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_DSI_TMR_ANA_DSI3_RX)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_DSI_TMR_ANA_DSI3_RX


class ral_reg_TEST_DSI_TMR_DIG_DSI3 extends uvm_reg;
	rand uvm_reg_field PREVENT_DEACTIVATION;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PREVENT_DEACTIVATION: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_DSI_TMR_DIG_DSI3");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PREVENT_DEACTIVATION = uvm_reg_field::type_id::create("PREVENT_DEACTIVATION",,get_full_name());
      this.PREVENT_DEACTIVATION.configure(this, 1, 0, "RW", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_DSI_TMR_DIG_DSI3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_DSI_TMR_DIG_DSI3


class ral_reg_TEST_DSI_TMR_SEL_DSI3 extends uvm_reg;
	rand uvm_reg_field TX;
	rand uvm_reg_field RX_TXN;
	rand uvm_reg_field TX_ON;
	rand uvm_reg_field HVCASC_ON;
	rand uvm_reg_field RX_ON;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TX: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RX_TXN: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   TX_ON: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   HVCASC_ON: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RX_ON: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_DSI_TMR_SEL_DSI3");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TX = uvm_reg_field::type_id::create("TX",,get_full_name());
      this.TX.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.RX_TXN = uvm_reg_field::type_id::create("RX_TXN",,get_full_name());
      this.RX_TXN.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
      this.TX_ON = uvm_reg_field::type_id::create("TX_ON",,get_full_name());
      this.TX_ON.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
      this.HVCASC_ON = uvm_reg_field::type_id::create("HVCASC_ON",,get_full_name());
      this.HVCASC_ON.configure(this, 1, 3, "RW", 0, 0, 1, 0, 0);
      this.RX_ON = uvm_reg_field::type_id::create("RX_ON",,get_full_name());
      this.RX_ON.configure(this, 1, 4, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_DSI_TMR_SEL_DSI3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_DSI_TMR_SEL_DSI3


class ral_reg_TEST_DSI_TMR_VAL_DSI3 extends uvm_reg;
	rand uvm_reg_field TX;
	rand uvm_reg_field RX_TXN;
	rand uvm_reg_field TX_ON;
	rand uvm_reg_field HVCASC_ON;
	rand uvm_reg_field RX_ON;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TX: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RX_TXN: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   TX_ON: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   HVCASC_ON: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RX_ON: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_DSI_TMR_VAL_DSI3");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TX = uvm_reg_field::type_id::create("TX",,get_full_name());
      this.TX.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.RX_TXN = uvm_reg_field::type_id::create("RX_TXN",,get_full_name());
      this.RX_TXN.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
      this.TX_ON = uvm_reg_field::type_id::create("TX_ON",,get_full_name());
      this.TX_ON.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
      this.HVCASC_ON = uvm_reg_field::type_id::create("HVCASC_ON",,get_full_name());
      this.HVCASC_ON.configure(this, 1, 3, "RW", 0, 0, 1, 0, 0);
      this.RX_ON = uvm_reg_field::type_id::create("RX_ON",,get_full_name());
      this.RX_ON.configure(this, 1, 4, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_DSI_TMR_VAL_DSI3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_DSI_TMR_VAL_DSI3


class ral_reg_TEST_DSI_TMR_IN_DSI3 extends uvm_reg;
	rand uvm_reg_field tmr_in_tx;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   tmr_in_tx: coverpoint {m_data[2:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {4'b??00};
	      wildcard bins bit_0_wr_as_1 = {4'b??10};
	      wildcard bins bit_0_rd_as_0 = {4'b??01};
	      wildcard bins bit_0_rd_as_1 = {4'b??11};
	      wildcard bins bit_1_wr_as_0 = {4'b?0?0};
	      wildcard bins bit_1_wr_as_1 = {4'b?1?0};
	      wildcard bins bit_1_rd_as_0 = {4'b?0?1};
	      wildcard bins bit_1_rd_as_1 = {4'b?1?1};
	      wildcard bins bit_2_wr_as_0 = {4'b0??0};
	      wildcard bins bit_2_wr_as_1 = {4'b1??0};
	      wildcard bins bit_2_rd_as_0 = {4'b0??1};
	      wildcard bins bit_2_rd_as_1 = {4'b1??1};
	      option.weight = 12;
	   }
	endgroup
	function new(string name = "TEST_DSI_TMR_IN_DSI3");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.tmr_in_tx = uvm_reg_field::type_id::create("tmr_in_tx",,get_full_name());
      this.tmr_in_tx.configure(this, 3, 0, "RW", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_DSI_TMR_IN_DSI3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_DSI_TMR_IN_DSI3


class ral_regfile_TEST_DSI extends uvm_reg_file;

	rand ral_reg_TEST_DSI_TMR_ANA_DSI3_TX TMR_ANA_DSI3_TX;
	rand ral_reg_TEST_DSI_TMR_ANA_DSI3_RX TMR_ANA_DSI3_RX;
	rand ral_reg_TEST_DSI_TMR_DIG_DSI3 TMR_DIG_DSI3;
	rand ral_reg_TEST_DSI_TMR_SEL_DSI3 TMR_SEL_DSI3;
	rand ral_reg_TEST_DSI_TMR_VAL_DSI3 TMR_VAL_DSI3;
	rand ral_reg_TEST_DSI_TMR_IN_DSI3 TMR_IN_DSI3;


	function new(string name = "TEST_DSI");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.TMR_ANA_DSI3_TX = ral_reg_TEST_DSI_TMR_ANA_DSI3_TX::type_id::create("TMR_ANA_DSI3_TX",,get_full_name());
		if(this.TMR_ANA_DSI3_TX.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_ANA_DSI3_TX.cg_bits.option.name = {get_name(), ".TMR_ANA_DSI3_TX_bits"};
		this.TMR_ANA_DSI3_TX.configure(get_block(), this, "");
		this.TMR_ANA_DSI3_TX.build();
		this.TMR_ANA_DSI3_TX.add_hdl_path('{
            '{"i_TEST_DSI.i_TEST_DSI_TMR_ANA_DSI3_TX.VNC2_CH1_2", 0, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_ANA_DSI3_TX.VNC0_CH1_2", 1, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_ANA_DSI3_TX.VNG0_CH1_2", 2, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_ANA_DSI3_TX.INN_CH1_2", 3, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_ANA_DSI3_TX.INP_CH1_2", 4, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_ANA_DSI3_TX.VBN5V_DIV_CH1_2", 5, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_ANA_DSI3_TX.IDAC_TX_CH1_2", 6, 1}
		});

		this.TMR_ANA_DSI3_RX = ral_reg_TEST_DSI_TMR_ANA_DSI3_RX::type_id::create("TMR_ANA_DSI3_RX",,get_full_name());
		if(this.TMR_ANA_DSI3_RX.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_ANA_DSI3_RX.cg_bits.option.name = {get_name(), ".TMR_ANA_DSI3_RX_bits"};
		this.TMR_ANA_DSI3_RX.configure(get_block(), this, "");
		this.TMR_ANA_DSI3_RX.build();
		this.TMR_ANA_DSI3_RX.add_hdl_path('{
            '{"i_TEST_DSI.i_TEST_DSI_TMR_ANA_DSI3_RX.I_Q_2_ATB", 0, 1}
		});

		this.TMR_DIG_DSI3 = ral_reg_TEST_DSI_TMR_DIG_DSI3::type_id::create("TMR_DIG_DSI3",,get_full_name());
		if(this.TMR_DIG_DSI3.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_DIG_DSI3.cg_bits.option.name = {get_name(), ".TMR_DIG_DSI3_bits"};
		this.TMR_DIG_DSI3.configure(get_block(), this, "");
		this.TMR_DIG_DSI3.build();
		this.TMR_DIG_DSI3.add_hdl_path('{
            '{"i_TEST_DSI.i_TEST_DSI_TMR_DIG_DSI3.PREVENT_DEACTIVATION", 0, 1}
		});

		this.TMR_SEL_DSI3 = ral_reg_TEST_DSI_TMR_SEL_DSI3::type_id::create("TMR_SEL_DSI3",,get_full_name());
		if(this.TMR_SEL_DSI3.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_SEL_DSI3.cg_bits.option.name = {get_name(), ".TMR_SEL_DSI3_bits"};
		this.TMR_SEL_DSI3.configure(get_block(), this, "");
		this.TMR_SEL_DSI3.build();
		this.TMR_SEL_DSI3.add_hdl_path('{
            '{"i_TEST_DSI.i_TEST_DSI_TMR_SEL_DSI3.TX", 0, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_SEL_DSI3.RX_TXN", 1, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_SEL_DSI3.TX_ON", 2, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_SEL_DSI3.HVCASC_ON", 3, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_SEL_DSI3.RX_ON", 4, 1}
		});

		this.TMR_VAL_DSI3 = ral_reg_TEST_DSI_TMR_VAL_DSI3::type_id::create("TMR_VAL_DSI3",,get_full_name());
		if(this.TMR_VAL_DSI3.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_VAL_DSI3.cg_bits.option.name = {get_name(), ".TMR_VAL_DSI3_bits"};
		this.TMR_VAL_DSI3.configure(get_block(), this, "");
		this.TMR_VAL_DSI3.build();
		this.TMR_VAL_DSI3.add_hdl_path('{
            '{"i_TEST_DSI.i_TEST_DSI_TMR_VAL_DSI3.TX", 0, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_VAL_DSI3.RX_TXN", 1, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_VAL_DSI3.TX_ON", 2, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_VAL_DSI3.HVCASC_ON", 3, 1},
            '{"i_TEST_DSI.i_TEST_DSI_TMR_VAL_DSI3.RX_ON", 4, 1}
		});

		this.TMR_IN_DSI3 = ral_reg_TEST_DSI_TMR_IN_DSI3::type_id::create("TMR_IN_DSI3",,get_full_name());
		if(this.TMR_IN_DSI3.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_IN_DSI3.cg_bits.option.name = {get_name(), ".TMR_IN_DSI3_bits"};
		this.TMR_IN_DSI3.configure(get_block(), this, "");
		this.TMR_IN_DSI3.build();
		this.TMR_IN_DSI3.add_hdl_path('{
            '{"i_TEST_DSI.i_TEST_DSI_TMR_IN_DSI3.tmr_in_tx", 0, 3}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(TMR_ANA_DSI3_TX, offset+`UVM_REG_ADDR_WIDTH'h0);
	  mp.add_reg(TMR_ANA_DSI3_RX, offset+`UVM_REG_ADDR_WIDTH'h1);
	  mp.add_reg(TMR_DIG_DSI3, offset+`UVM_REG_ADDR_WIDTH'h2);
	  mp.add_reg(TMR_SEL_DSI3, offset+`UVM_REG_ADDR_WIDTH'h3);
	  mp.add_reg(TMR_VAL_DSI3, offset+`UVM_REG_ADDR_WIDTH'h4);
	  mp.add_reg(TMR_IN_DSI3, offset+`UVM_REG_ADDR_WIDTH'h5);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  TMR_ANA_DSI3_TX.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h0);
	  TMR_ANA_DSI3_RX.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h1);
	  TMR_DIG_DSI3.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h2);
	  TMR_SEL_DSI3.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h3);
	  TMR_VAL_DSI3.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h4);
	  TMR_IN_DSI3.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h5);

	endfunction

	`uvm_object_utils(ral_regfile_TEST_DSI)
endclass : ral_regfile_TEST_DSI




class ral_block_test_dsi extends uvm_reg_block;
	rand ral_regfile_TEST_DSI TEST_DSI;

	function new(string name = "test_dsi");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.TEST_DSI = ral_regfile_TEST_DSI::type_id::create("TEST_DSI",,get_full_name());
      this.TEST_DSI.configure(this, null, "");
      this.TEST_DSI.build();
      this.TEST_DSI.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_test_dsi)

endclass : ral_block_test_dsi


class ral_reg_scan_registers_SCAN extends uvm_reg;
	rand uvm_reg_field SCAN;
	rand uvm_reg_field VDD_RDIV_DIS;
	rand uvm_reg_field COMPRESSION;
	rand uvm_reg_field VDD_ILOAD_DIS;
	rand uvm_reg_field VDD_DIS;
	rand uvm_reg_field DISABLE_OSC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   SCAN: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VDD_RDIV_DIS: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   COMPRESSION: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VDD_ILOAD_DIS: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VDD_DIS: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   DISABLE_OSC: coverpoint {m_data[5:5], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "scan_registers_SCAN");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.SCAN = uvm_reg_field::type_id::create("SCAN",,get_full_name());
      this.SCAN.configure(this, 1, 0, "W1S", 0, 0, 1, 0, 0);
      this.VDD_RDIV_DIS = uvm_reg_field::type_id::create("VDD_RDIV_DIS",,get_full_name());
      this.VDD_RDIV_DIS.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
      this.COMPRESSION = uvm_reg_field::type_id::create("COMPRESSION",,get_full_name());
      this.COMPRESSION.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
      this.VDD_ILOAD_DIS = uvm_reg_field::type_id::create("VDD_ILOAD_DIS",,get_full_name());
      this.VDD_ILOAD_DIS.configure(this, 1, 3, "RW", 0, 0, 1, 0, 0);
      this.VDD_DIS = uvm_reg_field::type_id::create("VDD_DIS",,get_full_name());
      this.VDD_DIS.configure(this, 1, 4, "RW", 0, 0, 1, 0, 0);
      this.DISABLE_OSC = uvm_reg_field::type_id::create("DISABLE_OSC",,get_full_name());
      this.DISABLE_OSC.configure(this, 1, 5, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_scan_registers_SCAN)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_scan_registers_SCAN


class ral_regfile_scan_registers extends uvm_reg_file;

	rand ral_reg_scan_registers_SCAN SCAN;


	function new(string name = "scan_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.SCAN = ral_reg_scan_registers_SCAN::type_id::create("SCAN",,get_full_name());
		if(this.SCAN.has_coverage(UVM_CVR_REG_BITS))
			this.SCAN.cg_bits.option.name = {get_name(), ".SCAN_bits"};
		this.SCAN.configure(get_block(), this, "");
		this.SCAN.build();
		this.SCAN.add_hdl_path('{
            '{"i_scan_registers.i_scan_registers_SCAN.SCAN", 0, 1},
            '{"i_scan_registers.i_scan_registers_SCAN.VDD_RDIV_DIS", 1, 1},
            '{"i_scan_registers.i_scan_registers_SCAN.COMPRESSION", 2, 1},
            '{"i_scan_registers.i_scan_registers_SCAN.VDD_ILOAD_DIS", 3, 1},
            '{"i_scan_registers.i_scan_registers_SCAN.VDD_DIS", 4, 1},
            '{"i_scan_registers.i_scan_registers_SCAN.DISABLE_OSC", 5, 1}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(SCAN, offset+`UVM_REG_ADDR_WIDTH'h0);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  SCAN.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h0);

	endfunction

	`uvm_object_utils(ral_regfile_scan_registers)
endclass : ral_regfile_scan_registers




class ral_block_SCAN_TEST extends uvm_reg_block;
	rand ral_regfile_scan_registers scan_registers;

	function new(string name = "SCAN_TEST");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.scan_registers = ral_regfile_scan_registers::type_id::create("scan_registers",,get_full_name());
      this.scan_registers.configure(this, null, "");
      this.scan_registers.build();
      this.scan_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_SCAN_TEST)

endclass : ral_block_SCAN_TEST


class ral_reg_SRAM_BIST_registers_SRAM_BIST_CTRL extends uvm_reg;
	rand uvm_reg_field EN;
	rand uvm_reg_field BITWISE;
	rand uvm_reg_field FOUR_6N;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   EN: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   BITWISE: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   FOUR_6N: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "SRAM_BIST_registers_SRAM_BIST_CTRL");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.EN = uvm_reg_field::type_id::create("EN",,get_full_name());
      this.EN.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.BITWISE = uvm_reg_field::type_id::create("BITWISE",,get_full_name());
      this.BITWISE.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
      this.FOUR_6N = uvm_reg_field::type_id::create("FOUR_6N",,get_full_name());
      this.FOUR_6N.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_SRAM_BIST_registers_SRAM_BIST_CTRL)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_SRAM_BIST_registers_SRAM_BIST_CTRL


class ral_reg_SRAM_BIST_registers_SRAM_BIST_STAT extends uvm_reg;
	uvm_reg_field STATUS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   STATUS: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd_as_0 = {3'b?01};
	      wildcard bins bit_0_rd_as_1 = {3'b?11};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd_as_0 = {3'b0?1};
	      wildcard bins bit_1_rd_as_1 = {3'b1?1};
	      option.weight = 8;
	   }
	endgroup
	function new(string name = "SRAM_BIST_registers_SRAM_BIST_STAT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.STATUS = uvm_reg_field::type_id::create("STATUS",,get_full_name());
      this.STATUS.configure(this, 2, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_SRAM_BIST_registers_SRAM_BIST_STAT)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_SRAM_BIST_registers_SRAM_BIST_STAT


class ral_reg_SRAM_BIST_registers_SRAM_ECC_CONTROL extends uvm_reg;
	rand uvm_reg_field SRAM_ECC_VAL;
	rand uvm_reg_field SRAM_ECC_SEL;
	rand uvm_reg_field SRAM_ECC_SWAP;
	rand uvm_reg_field ELIP_ECC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   SRAM_ECC_VAL: coverpoint {m_data[6:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {8'b??????00};
	      wildcard bins bit_0_wr_as_1 = {8'b??????10};
	      wildcard bins bit_0_rd_as_0 = {8'b??????01};
	      wildcard bins bit_0_rd_as_1 = {8'b??????11};
	      wildcard bins bit_1_wr_as_0 = {8'b?????0?0};
	      wildcard bins bit_1_wr_as_1 = {8'b?????1?0};
	      wildcard bins bit_1_rd_as_0 = {8'b?????0?1};
	      wildcard bins bit_1_rd_as_1 = {8'b?????1?1};
	      wildcard bins bit_2_wr_as_0 = {8'b????0??0};
	      wildcard bins bit_2_wr_as_1 = {8'b????1??0};
	      wildcard bins bit_2_rd_as_0 = {8'b????0??1};
	      wildcard bins bit_2_rd_as_1 = {8'b????1??1};
	      wildcard bins bit_3_wr_as_0 = {8'b???0???0};
	      wildcard bins bit_3_wr_as_1 = {8'b???1???0};
	      wildcard bins bit_3_rd_as_0 = {8'b???0???1};
	      wildcard bins bit_3_rd_as_1 = {8'b???1???1};
	      wildcard bins bit_4_wr_as_0 = {8'b??0????0};
	      wildcard bins bit_4_wr_as_1 = {8'b??1????0};
	      wildcard bins bit_4_rd_as_0 = {8'b??0????1};
	      wildcard bins bit_4_rd_as_1 = {8'b??1????1};
	      wildcard bins bit_5_wr_as_0 = {8'b?0?????0};
	      wildcard bins bit_5_wr_as_1 = {8'b?1?????0};
	      wildcard bins bit_5_rd_as_0 = {8'b?0?????1};
	      wildcard bins bit_5_rd_as_1 = {8'b?1?????1};
	      wildcard bins bit_6_wr_as_0 = {8'b0??????0};
	      wildcard bins bit_6_wr_as_1 = {8'b1??????0};
	      wildcard bins bit_6_rd_as_0 = {8'b0??????1};
	      wildcard bins bit_6_rd_as_1 = {8'b1??????1};
	      option.weight = 28;
	   }
	   SRAM_ECC_SEL: coverpoint {m_data[7:7], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SRAM_ECC_SWAP: coverpoint {m_data[8:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ELIP_ECC: coverpoint {m_data[14:9], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	endgroup
	function new(string name = "SRAM_BIST_registers_SRAM_ECC_CONTROL");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.SRAM_ECC_VAL = uvm_reg_field::type_id::create("SRAM_ECC_VAL",,get_full_name());
      this.SRAM_ECC_VAL.configure(this, 7, 0, "RW", 0, 0, 1, 0, 0);
      this.SRAM_ECC_SEL = uvm_reg_field::type_id::create("SRAM_ECC_SEL",,get_full_name());
      this.SRAM_ECC_SEL.configure(this, 1, 7, "RW", 0, 0, 1, 0, 0);
      this.SRAM_ECC_SWAP = uvm_reg_field::type_id::create("SRAM_ECC_SWAP",,get_full_name());
      this.SRAM_ECC_SWAP.configure(this, 1, 8, "RW", 0, 0, 1, 0, 0);
      this.ELIP_ECC = uvm_reg_field::type_id::create("ELIP_ECC",,get_full_name());
      this.ELIP_ECC.configure(this, 6, 9, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_SRAM_BIST_registers_SRAM_ECC_CONTROL)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_SRAM_BIST_registers_SRAM_ECC_CONTROL


class ral_regfile_SRAM_BIST_registers extends uvm_reg_file;

	rand ral_reg_SRAM_BIST_registers_SRAM_BIST_CTRL SRAM_BIST_CTRL;
	rand ral_reg_SRAM_BIST_registers_SRAM_BIST_STAT SRAM_BIST_STAT;
	rand ral_reg_SRAM_BIST_registers_SRAM_ECC_CONTROL SRAM_ECC_CONTROL;


	function new(string name = "SRAM_BIST_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.SRAM_BIST_CTRL = ral_reg_SRAM_BIST_registers_SRAM_BIST_CTRL::type_id::create("SRAM_BIST_CTRL",,get_full_name());
		if(this.SRAM_BIST_CTRL.has_coverage(UVM_CVR_REG_BITS))
			this.SRAM_BIST_CTRL.cg_bits.option.name = {get_name(), ".SRAM_BIST_CTRL_bits"};
		this.SRAM_BIST_CTRL.configure(get_block(), this, "");
		this.SRAM_BIST_CTRL.build();
		this.SRAM_BIST_CTRL.add_hdl_path('{
            '{"i_SRAM_BIST_registers.i_SRAM_BIST_registers_SRAM_BIST_CTRL.EN", 0, 1},
            '{"i_SRAM_BIST_registers.i_SRAM_BIST_registers_SRAM_BIST_CTRL.BITWISE", 1, 1},
            '{"i_SRAM_BIST_registers.i_SRAM_BIST_registers_SRAM_BIST_CTRL.FOUR_6N", 2, 1}
		});

		this.SRAM_BIST_STAT = ral_reg_SRAM_BIST_registers_SRAM_BIST_STAT::type_id::create("SRAM_BIST_STAT",,get_full_name());
		if(this.SRAM_BIST_STAT.has_coverage(UVM_CVR_REG_BITS))
			this.SRAM_BIST_STAT.cg_bits.option.name = {get_name(), ".SRAM_BIST_STAT_bits"};
		this.SRAM_BIST_STAT.configure(get_block(), this, "");
		this.SRAM_BIST_STAT.build();
		this.SRAM_BIST_STAT.add_hdl_path('{
            '{"i_SRAM_BIST_registers.i_SRAM_BIST_registers_SRAM_BIST_STAT.STATUS", 0, 2}
		});

		this.SRAM_ECC_CONTROL = ral_reg_SRAM_BIST_registers_SRAM_ECC_CONTROL::type_id::create("SRAM_ECC_CONTROL",,get_full_name());
		if(this.SRAM_ECC_CONTROL.has_coverage(UVM_CVR_REG_BITS))
			this.SRAM_ECC_CONTROL.cg_bits.option.name = {get_name(), ".SRAM_ECC_CONTROL_bits"};
		this.SRAM_ECC_CONTROL.configure(get_block(), this, "");
		this.SRAM_ECC_CONTROL.build();
		this.SRAM_ECC_CONTROL.add_hdl_path('{
            '{"i_SRAM_BIST_registers.i_SRAM_BIST_registers_SRAM_ECC_CONTROL.SRAM_ECC_VAL", 0, 7},
            '{"i_SRAM_BIST_registers.i_SRAM_BIST_registers_SRAM_ECC_CONTROL.SRAM_ECC_SEL", 7, 1},
            '{"i_SRAM_BIST_registers.i_SRAM_BIST_registers_SRAM_ECC_CONTROL.SRAM_ECC_SWAP", 8, 1},
            '{"i_SRAM_BIST_registers.i_SRAM_BIST_registers_SRAM_ECC_CONTROL.ELIP_ECC", 9, 6}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(SRAM_BIST_CTRL, offset+`UVM_REG_ADDR_WIDTH'h8);
	  mp.add_reg(SRAM_BIST_STAT, offset+`UVM_REG_ADDR_WIDTH'h9);
	  mp.add_reg(SRAM_ECC_CONTROL, offset+`UVM_REG_ADDR_WIDTH'h7);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  SRAM_BIST_CTRL.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h8);
	  SRAM_BIST_STAT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h9);
	  SRAM_ECC_CONTROL.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h7);

	endfunction

	`uvm_object_utils(ral_regfile_SRAM_BIST_registers)
endclass : ral_regfile_SRAM_BIST_registers




class ral_block_SRAM_BIST extends uvm_reg_block;
	rand ral_regfile_SRAM_BIST_registers SRAM_BIST_registers;

	function new(string name = "SRAM_BIST");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.SRAM_BIST_registers = ral_regfile_SRAM_BIST_registers::type_id::create("SRAM_BIST_registers",,get_full_name());
      this.SRAM_BIST_registers.configure(this, null, "");
      this.SRAM_BIST_registers.build();
      this.SRAM_BIST_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_SRAM_BIST)

endclass : ral_block_SRAM_BIST


class ral_reg_OTP_test_registers_OTP_WRITE_PULSE_WIDTH extends uvm_reg;
	rand uvm_reg_field PULSE_WIDTH;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PULSE_WIDTH: coverpoint {m_data[11:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	endgroup
	function new(string name = "OTP_test_registers_OTP_WRITE_PULSE_WIDTH");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PULSE_WIDTH = uvm_reg_field::type_id::create("PULSE_WIDTH",,get_full_name());
      this.PULSE_WIDTH.configure(this, 12, 0, "RW", 0, 1800, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_OTP_test_registers_OTP_WRITE_PULSE_WIDTH)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_OTP_test_registers_OTP_WRITE_PULSE_WIDTH


class ral_regfile_OTP_test_registers extends uvm_reg_file;

	rand ral_reg_OTP_test_registers_OTP_WRITE_PULSE_WIDTH OTP_WRITE_PULSE_WIDTH;


	function new(string name = "OTP_test_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.OTP_WRITE_PULSE_WIDTH = ral_reg_OTP_test_registers_OTP_WRITE_PULSE_WIDTH::type_id::create("OTP_WRITE_PULSE_WIDTH",,get_full_name());
		if(this.OTP_WRITE_PULSE_WIDTH.has_coverage(UVM_CVR_REG_BITS))
			this.OTP_WRITE_PULSE_WIDTH.cg_bits.option.name = {get_name(), ".OTP_WRITE_PULSE_WIDTH_bits"};
		this.OTP_WRITE_PULSE_WIDTH.configure(get_block(), this, "");
		this.OTP_WRITE_PULSE_WIDTH.build();
		this.OTP_WRITE_PULSE_WIDTH.add_hdl_path('{
            '{"i_OTP_test_registers.i_OTP_test_registers_OTP_WRITE_PULSE_WIDTH.PULSE_WIDTH", 0, 12}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(OTP_WRITE_PULSE_WIDTH, offset+`UVM_REG_ADDR_WIDTH'hAF);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  OTP_WRITE_PULSE_WIDTH.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hAF);

	endfunction

	`uvm_object_utils(ral_regfile_OTP_test_registers)
endclass : ral_regfile_OTP_test_registers




class ral_block_otp_test extends uvm_reg_block;
	rand ral_regfile_OTP_test_registers OTP_test_registers;

	function new(string name = "otp_test");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.OTP_test_registers = ral_regfile_OTP_test_registers::type_id::create("OTP_test_registers",,get_full_name());
      this.OTP_test_registers.configure(this, null, "");
      this.OTP_test_registers.build();
      this.OTP_test_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_otp_test)

endclass : ral_block_otp_test


class ral_reg_Test_Registers_OTP_CONTROL extends uvm_reg;
	rand uvm_reg_field EN_AUTO;
	rand uvm_reg_field VRREN;
	rand uvm_reg_field VPPEN;
	rand uvm_reg_field EN;
	rand uvm_reg_field SEL;
	rand uvm_reg_field CTRL_CLK;
	rand uvm_reg_field CTRL_WE;
	rand uvm_reg_field OTP_MON;
	rand uvm_reg_field AUTOINC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   EN_AUTO: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VRREN: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VPPEN: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   EN: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SEL: coverpoint {m_data[6:6], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CTRL_CLK: coverpoint {m_data[8:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CTRL_WE: coverpoint {m_data[9:9], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTP_MON: coverpoint {m_data[11:10], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd_as_0 = {3'b?01};
	      wildcard bins bit_0_rd_as_1 = {3'b?11};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd_as_0 = {3'b0?1};
	      wildcard bins bit_1_rd_as_1 = {3'b1?1};
	      option.weight = 8;
	   }
	   AUTOINC: coverpoint {m_data[12:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "Test_Registers_OTP_CONTROL");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.EN_AUTO = uvm_reg_field::type_id::create("EN_AUTO",,get_full_name());
      this.EN_AUTO.configure(this, 1, 0, "RW", 0, 1, 1, 0, 0);
      this.VRREN = uvm_reg_field::type_id::create("VRREN",,get_full_name());
      this.VRREN.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
      this.VPPEN = uvm_reg_field::type_id::create("VPPEN",,get_full_name());
      this.VPPEN.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
      this.EN = uvm_reg_field::type_id::create("EN",,get_full_name());
      this.EN.configure(this, 1, 4, "RW", 0, 0, 1, 0, 0);
      this.SEL = uvm_reg_field::type_id::create("SEL",,get_full_name());
      this.SEL.configure(this, 1, 6, "RW", 0, 0, 1, 0, 0);
      this.CTRL_CLK = uvm_reg_field::type_id::create("CTRL_CLK",,get_full_name());
      this.CTRL_CLK.configure(this, 1, 8, "RW", 0, 0, 1, 0, 0);
      this.CTRL_WE = uvm_reg_field::type_id::create("CTRL_WE",,get_full_name());
      this.CTRL_WE.configure(this, 1, 9, "RW", 0, 0, 1, 0, 0);
      this.OTP_MON = uvm_reg_field::type_id::create("OTP_MON",,get_full_name());
      this.OTP_MON.configure(this, 2, 10, "RW", 0, 0, 1, 0, 0);
      this.AUTOINC = uvm_reg_field::type_id::create("AUTOINC",,get_full_name());
      this.AUTOINC.configure(this, 1, 12, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_Test_Registers_OTP_CONTROL)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_Test_Registers_OTP_CONTROL


class ral_reg_Test_Registers_OTP_CONFIG extends uvm_reg;
	rand uvm_reg_field OTP_MPP;
	rand uvm_reg_field OTP_MRR;
	rand uvm_reg_field OTP_MR;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OTP_MPP: coverpoint {m_data[7:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd_as_0 = {9'b???????01};
	      wildcard bins bit_0_rd_as_1 = {9'b???????11};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd_as_0 = {9'b??????0?1};
	      wildcard bins bit_1_rd_as_1 = {9'b??????1?1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd_as_0 = {9'b?????0??1};
	      wildcard bins bit_2_rd_as_1 = {9'b?????1??1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd_as_0 = {9'b????0???1};
	      wildcard bins bit_3_rd_as_1 = {9'b????1???1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd_as_0 = {9'b???0????1};
	      wildcard bins bit_4_rd_as_1 = {9'b???1????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd_as_0 = {9'b??0?????1};
	      wildcard bins bit_5_rd_as_1 = {9'b??1?????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd_as_0 = {9'b?0??????1};
	      wildcard bins bit_6_rd_as_1 = {9'b?1??????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd_as_0 = {9'b0???????1};
	      wildcard bins bit_7_rd_as_1 = {9'b1???????1};
	      option.weight = 32;
	   }
	   OTP_MRR: coverpoint {m_data[23:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd_as_0 = {17'b???????????????01};
	      wildcard bins bit_0_rd_as_1 = {17'b???????????????11};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {17'b??????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {17'b??????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {17'b?????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {17'b?????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {17'b????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {17'b????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd_as_0 = {17'b???????????0????1};
	      wildcard bins bit_4_rd_as_1 = {17'b???????????1????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {17'b??????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {17'b??????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {17'b?????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {17'b?????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {17'b????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {17'b????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd_as_0 = {17'b???????0????????1};
	      wildcard bins bit_8_rd_as_1 = {17'b???????1????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {17'b??????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {17'b??????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {17'b?????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {17'b?????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {17'b????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {17'b????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd_as_0 = {17'b???0????????????1};
	      wildcard bins bit_12_rd_as_1 = {17'b???1????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {17'b??0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {17'b??1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {17'b?0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {17'b?1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {17'b0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {17'b1???????????????1};
	      option.weight = 64;
	   }
	   OTP_MR: coverpoint {m_data[31:24], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd_as_0 = {9'b???????01};
	      wildcard bins bit_0_rd_as_1 = {9'b???????11};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd_as_0 = {9'b??????0?1};
	      wildcard bins bit_1_rd_as_1 = {9'b??????1?1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd_as_0 = {9'b?????0??1};
	      wildcard bins bit_2_rd_as_1 = {9'b?????1??1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd_as_0 = {9'b????0???1};
	      wildcard bins bit_3_rd_as_1 = {9'b????1???1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd_as_0 = {9'b???0????1};
	      wildcard bins bit_4_rd_as_1 = {9'b???1????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd_as_0 = {9'b??0?????1};
	      wildcard bins bit_5_rd_as_1 = {9'b??1?????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd_as_0 = {9'b?0??????1};
	      wildcard bins bit_6_rd_as_1 = {9'b?1??????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd_as_0 = {9'b0???????1};
	      wildcard bins bit_7_rd_as_1 = {9'b1???????1};
	      option.weight = 32;
	   }
	endgroup
	function new(string name = "Test_Registers_OTP_CONFIG");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OTP_MPP = uvm_reg_field::type_id::create("OTP_MPP",,get_full_name());
      this.OTP_MPP.configure(this, 8, 0, "RW", 0, 0, 1, 0, 1);
      this.OTP_MRR = uvm_reg_field::type_id::create("OTP_MRR",,get_full_name());
      this.OTP_MRR.configure(this, 16, 8, "RW", 0, 0, 1, 0, 1);
      this.OTP_MR = uvm_reg_field::type_id::create("OTP_MR",,get_full_name());
      this.OTP_MR.configure(this, 8, 24, "RW", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_Test_Registers_OTP_CONFIG)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_Test_Registers_OTP_CONFIG


class ral_reg_Test_Registers_OTP_WRITE extends uvm_reg;
	rand uvm_reg_field data;
	rand uvm_reg_field address;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   data: coverpoint {m_data[19:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	   address: coverpoint {m_data[31:20], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	endgroup
	function new(string name = "Test_Registers_OTP_WRITE");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.data = uvm_reg_field::type_id::create("data",,get_full_name());
      this.data.configure(this, 12, 8, "RW", 0, 0, 1, 0, 0);
      this.address = uvm_reg_field::type_id::create("address",,get_full_name());
      this.address.configure(this, 12, 20, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_Test_Registers_OTP_WRITE)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_Test_Registers_OTP_WRITE


class ral_reg_Test_Registers_OTP_READ extends uvm_reg;
	uvm_reg_field data;
	rand uvm_reg_field address;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   data: coverpoint {m_data[11:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	   address: coverpoint {m_data[31:20], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	endgroup
	function new(string name = "Test_Registers_OTP_READ");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.data = uvm_reg_field::type_id::create("data",,get_full_name());
      this.data.configure(this, 12, 0, "RO", 0, 0, 1, 0, 1);
      this.address = uvm_reg_field::type_id::create("address",,get_full_name());
      this.address.configure(this, 12, 20, "RW", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_Test_Registers_OTP_READ)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_Test_Registers_OTP_READ


class ral_reg_Test_Registers_OTP_BIST_CONTROL extends uvm_reg;
	rand uvm_reg_field OTP_PGM;
	rand uvm_reg_field OTP_READ;
	rand uvm_reg_field SOAK;
	rand uvm_reg_field EN_SOAK;
	rand uvm_reg_field STRESS;
	rand uvm_reg_field SEL_TRP;
	rand uvm_reg_field SEL_RD;
	rand uvm_reg_field SEL_MPP;
	rand uvm_reg_field SEL_MRR;
	rand uvm_reg_field SEL_MR;
	rand uvm_reg_field MAX_SOAK;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OTP_PGM: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTP_READ: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SOAK: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   EN_SOAK: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   STRESS: coverpoint {m_data[5:5], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SEL_TRP: coverpoint {m_data[6:6], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SEL_RD: coverpoint {m_data[7:7], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SEL_MPP: coverpoint {m_data[8:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SEL_MRR: coverpoint {m_data[9:9], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SEL_MR: coverpoint {m_data[10:10], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   MAX_SOAK: coverpoint {m_data[14:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {4'b??00};
	      wildcard bins bit_0_wr_as_1 = {4'b??10};
	      wildcard bins bit_0_rd_as_0 = {4'b??01};
	      wildcard bins bit_0_rd_as_1 = {4'b??11};
	      wildcard bins bit_1_wr_as_0 = {4'b?0?0};
	      wildcard bins bit_1_wr_as_1 = {4'b?1?0};
	      wildcard bins bit_1_rd_as_0 = {4'b?0?1};
	      wildcard bins bit_1_rd_as_1 = {4'b?1?1};
	      wildcard bins bit_2_wr_as_0 = {4'b0??0};
	      wildcard bins bit_2_wr_as_1 = {4'b1??0};
	      wildcard bins bit_2_rd_as_0 = {4'b0??1};
	      wildcard bins bit_2_rd_as_1 = {4'b1??1};
	      option.weight = 12;
	   }
	endgroup
	function new(string name = "Test_Registers_OTP_BIST_CONTROL");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OTP_PGM = uvm_reg_field::type_id::create("OTP_PGM",,get_full_name());
      this.OTP_PGM.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.OTP_READ = uvm_reg_field::type_id::create("OTP_READ",,get_full_name());
      this.OTP_READ.configure(this, 1, 1, "RW", 0, 1, 1, 0, 0);
      this.SOAK = uvm_reg_field::type_id::create("SOAK",,get_full_name());
      this.SOAK.configure(this, 1, 2, "RW", 0, 0, 1, 0, 0);
      this.EN_SOAK = uvm_reg_field::type_id::create("EN_SOAK",,get_full_name());
      this.EN_SOAK.configure(this, 1, 4, "RW", 0, 0, 1, 0, 0);
      this.STRESS = uvm_reg_field::type_id::create("STRESS",,get_full_name());
      this.STRESS.configure(this, 1, 5, "RW", 0, 0, 1, 0, 0);
      this.SEL_TRP = uvm_reg_field::type_id::create("SEL_TRP",,get_full_name());
      this.SEL_TRP.configure(this, 1, 6, "RW", 0, 0, 1, 0, 0);
      this.SEL_RD = uvm_reg_field::type_id::create("SEL_RD",,get_full_name());
      this.SEL_RD.configure(this, 1, 7, "RW", 0, 0, 1, 0, 0);
      this.SEL_MPP = uvm_reg_field::type_id::create("SEL_MPP",,get_full_name());
      this.SEL_MPP.configure(this, 1, 8, "RW", 0, 0, 1, 0, 0);
      this.SEL_MRR = uvm_reg_field::type_id::create("SEL_MRR",,get_full_name());
      this.SEL_MRR.configure(this, 1, 9, "RW", 0, 0, 1, 0, 0);
      this.SEL_MR = uvm_reg_field::type_id::create("SEL_MR",,get_full_name());
      this.SEL_MR.configure(this, 1, 10, "RW", 0, 0, 1, 0, 0);
      this.MAX_SOAK = uvm_reg_field::type_id::create("MAX_SOAK",,get_full_name());
      this.MAX_SOAK.configure(this, 3, 12, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_Test_Registers_OTP_BIST_CONTROL)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_Test_Registers_OTP_BIST_CONTROL


class ral_reg_Test_Registers_OTP_READ_CONFIG extends uvm_reg;
	rand uvm_reg_field TRP;
	rand uvm_reg_field RD_MODE;
	uvm_reg_field ECCERR_L;
	uvm_reg_field ECCERR_H;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TRP: coverpoint {m_data[6:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {8'b??????00};
	      wildcard bins bit_0_wr_as_1 = {8'b??????10};
	      wildcard bins bit_0_rd_as_0 = {8'b??????01};
	      wildcard bins bit_0_rd_as_1 = {8'b??????11};
	      wildcard bins bit_1_wr_as_0 = {8'b?????0?0};
	      wildcard bins bit_1_wr_as_1 = {8'b?????1?0};
	      wildcard bins bit_1_rd_as_0 = {8'b?????0?1};
	      wildcard bins bit_1_rd_as_1 = {8'b?????1?1};
	      wildcard bins bit_2_wr_as_0 = {8'b????0??0};
	      wildcard bins bit_2_wr_as_1 = {8'b????1??0};
	      wildcard bins bit_2_rd_as_0 = {8'b????0??1};
	      wildcard bins bit_2_rd_as_1 = {8'b????1??1};
	      wildcard bins bit_3_wr_as_0 = {8'b???0???0};
	      wildcard bins bit_3_wr_as_1 = {8'b???1???0};
	      wildcard bins bit_3_rd_as_0 = {8'b???0???1};
	      wildcard bins bit_3_rd_as_1 = {8'b???1???1};
	      wildcard bins bit_4_wr_as_0 = {8'b??0????0};
	      wildcard bins bit_4_wr_as_1 = {8'b??1????0};
	      wildcard bins bit_4_rd_as_0 = {8'b??0????1};
	      wildcard bins bit_4_rd_as_1 = {8'b??1????1};
	      wildcard bins bit_5_wr_as_0 = {8'b?0?????0};
	      wildcard bins bit_5_wr_as_1 = {8'b?1?????0};
	      wildcard bins bit_5_rd_as_0 = {8'b?0?????1};
	      wildcard bins bit_5_rd_as_1 = {8'b?1?????1};
	      wildcard bins bit_6_wr_as_0 = {8'b0??????0};
	      wildcard bins bit_6_wr_as_1 = {8'b1??????0};
	      wildcard bins bit_6_rd_as_0 = {8'b0??????1};
	      wildcard bins bit_6_rd_as_1 = {8'b1??????1};
	      option.weight = 28;
	   }
	   RD_MODE: coverpoint {m_data[9:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd_as_0 = {3'b?01};
	      wildcard bins bit_0_rd_as_1 = {3'b?11};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd_as_0 = {3'b0?1};
	      wildcard bins bit_1_rd_as_1 = {3'b1?1};
	      option.weight = 8;
	   }
	   ECCERR_L: coverpoint {m_data[13:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd_as_0 = {3'b?01};
	      wildcard bins bit_0_rd_as_1 = {3'b?11};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd_as_0 = {3'b0?1};
	      wildcard bins bit_1_rd_as_1 = {3'b1?1};
	      option.weight = 8;
	   }
	   ECCERR_H: coverpoint {m_data[15:14], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd_as_0 = {3'b?01};
	      wildcard bins bit_0_rd_as_1 = {3'b?11};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd_as_0 = {3'b0?1};
	      wildcard bins bit_1_rd_as_1 = {3'b1?1};
	      option.weight = 8;
	   }
	endgroup
	function new(string name = "Test_Registers_OTP_READ_CONFIG");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TRP = uvm_reg_field::type_id::create("TRP",,get_full_name());
      this.TRP.configure(this, 7, 0, "RW", 0, 0, 1, 0, 1);
      this.RD_MODE = uvm_reg_field::type_id::create("RD_MODE",,get_full_name());
      this.RD_MODE.configure(this, 2, 8, "RW", 0, 0, 1, 0, 0);
      this.ECCERR_L = uvm_reg_field::type_id::create("ECCERR_L",,get_full_name());
      this.ECCERR_L.configure(this, 2, 12, "RO", 0, 0, 1, 0, 0);
      this.ECCERR_H = uvm_reg_field::type_id::create("ECCERR_H",,get_full_name());
      this.ECCERR_H.configure(this, 2, 14, "RO", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_Test_Registers_OTP_READ_CONFIG)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_Test_Registers_OTP_READ_CONFIG


class ral_reg_Test_Registers_OTP_BIST_STATUS extends uvm_reg;
	uvm_reg_field PROG_BIT;
	uvm_reg_field DONE;
	uvm_reg_field SOAK_PULSE;
	uvm_reg_field BUSY;
	uvm_reg_field FAIL0;
	uvm_reg_field FAIL1;
	uvm_reg_field SOAK;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PROG_BIT: coverpoint {m_data[5:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   DONE: coverpoint {m_data[7:7], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SOAK_PULSE: coverpoint {m_data[11:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {5'b???00};
	      wildcard bins bit_0_wr_as_1 = {5'b???10};
	      wildcard bins bit_0_rd_as_0 = {5'b???01};
	      wildcard bins bit_0_rd_as_1 = {5'b???11};
	      wildcard bins bit_1_wr_as_0 = {5'b??0?0};
	      wildcard bins bit_1_wr_as_1 = {5'b??1?0};
	      wildcard bins bit_1_rd_as_0 = {5'b??0?1};
	      wildcard bins bit_1_rd_as_1 = {5'b??1?1};
	      wildcard bins bit_2_wr_as_0 = {5'b?0??0};
	      wildcard bins bit_2_wr_as_1 = {5'b?1??0};
	      wildcard bins bit_2_rd_as_0 = {5'b?0??1};
	      wildcard bins bit_2_rd_as_1 = {5'b?1??1};
	      wildcard bins bit_3_wr_as_0 = {5'b0???0};
	      wildcard bins bit_3_wr_as_1 = {5'b1???0};
	      wildcard bins bit_3_rd_as_0 = {5'b0???1};
	      wildcard bins bit_3_rd_as_1 = {5'b1???1};
	      option.weight = 16;
	   }
	   BUSY: coverpoint {m_data[12:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   FAIL0: coverpoint {m_data[13:13], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   FAIL1: coverpoint {m_data[14:14], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SOAK: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "Test_Registers_OTP_BIST_STATUS");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PROG_BIT = uvm_reg_field::type_id::create("PROG_BIT",,get_full_name());
      this.PROG_BIT.configure(this, 6, 0, "RO", 0, 0, 1, 0, 0);
      this.DONE = uvm_reg_field::type_id::create("DONE",,get_full_name());
      this.DONE.configure(this, 1, 7, "RO", 0, 0, 1, 0, 0);
      this.SOAK_PULSE = uvm_reg_field::type_id::create("SOAK_PULSE",,get_full_name());
      this.SOAK_PULSE.configure(this, 4, 8, "RO", 0, 0, 1, 0, 0);
      this.BUSY = uvm_reg_field::type_id::create("BUSY",,get_full_name());
      this.BUSY.configure(this, 1, 12, "RO", 0, 0, 1, 0, 0);
      this.FAIL0 = uvm_reg_field::type_id::create("FAIL0",,get_full_name());
      this.FAIL0.configure(this, 1, 13, "RO", 0, 0, 1, 0, 0);
      this.FAIL1 = uvm_reg_field::type_id::create("FAIL1",,get_full_name());
      this.FAIL1.configure(this, 1, 14, "RO", 0, 0, 1, 0, 0);
      this.SOAK = uvm_reg_field::type_id::create("SOAK",,get_full_name());
      this.SOAK.configure(this, 1, 15, "RO", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_Test_Registers_OTP_BIST_STATUS)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_Test_Registers_OTP_BIST_STATUS


class ral_regfile_Test_Registers extends uvm_reg_file;

	rand ral_reg_Test_Registers_OTP_CONTROL OTP_CONTROL;
	rand ral_reg_Test_Registers_OTP_CONFIG OTP_CONFIG;
	rand ral_reg_Test_Registers_OTP_WRITE OTP_WRITE;
	rand ral_reg_Test_Registers_OTP_READ OTP_READ;
	rand ral_reg_Test_Registers_OTP_BIST_CONTROL OTP_BIST_CONTROL;
	rand ral_reg_Test_Registers_OTP_READ_CONFIG OTP_READ_CONFIG;
	rand ral_reg_Test_Registers_OTP_BIST_STATUS OTP_BIST_STATUS;


	function new(string name = "Test_Registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.OTP_CONTROL = ral_reg_Test_Registers_OTP_CONTROL::type_id::create("OTP_CONTROL",,get_full_name());
		if(this.OTP_CONTROL.has_coverage(UVM_CVR_REG_BITS))
			this.OTP_CONTROL.cg_bits.option.name = {get_name(), ".OTP_CONTROL_bits"};
		this.OTP_CONTROL.configure(get_block(), this, "");
		this.OTP_CONTROL.build();
		this.OTP_CONTROL.add_hdl_path('{
            '{"i_Test_Registers.i_Test_Registers_OTP_CONTROL.EN_AUTO", 0, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_CONTROL.VRREN", 1, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_CONTROL.VPPEN", 2, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_CONTROL.EN", 4, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_CONTROL.SEL", 6, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_CONTROL.CTRL_CLK", 8, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_CONTROL.CTRL_WE", 9, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_CONTROL.OTP_MON", 10, 2},
            '{"i_Test_Registers.i_Test_Registers_OTP_CONTROL.AUTOINC", 12, 1}
		});

		this.OTP_CONFIG = ral_reg_Test_Registers_OTP_CONFIG::type_id::create("OTP_CONFIG",,get_full_name());
		if(this.OTP_CONFIG.has_coverage(UVM_CVR_REG_BITS))
			this.OTP_CONFIG.cg_bits.option.name = {get_name(), ".OTP_CONFIG_bits"};
		this.OTP_CONFIG.configure(get_block(), this, "");
		this.OTP_CONFIG.build();
		this.OTP_CONFIG.add_hdl_path('{
            '{"i_Test_Registers.i_Test_Registers_OTP_CONFIG.OTP_MPP", 0, 8},
            '{"i_Test_Registers.i_Test_Registers_OTP_CONFIG.OTP_MRR", 8, 16},
            '{"i_Test_Registers.i_Test_Registers_OTP_CONFIG.OTP_MR", 24, 8}
		});

		this.OTP_WRITE = ral_reg_Test_Registers_OTP_WRITE::type_id::create("OTP_WRITE",,get_full_name());
		if(this.OTP_WRITE.has_coverage(UVM_CVR_REG_BITS))
			this.OTP_WRITE.cg_bits.option.name = {get_name(), ".OTP_WRITE_bits"};
		this.OTP_WRITE.configure(get_block(), this, "");
		this.OTP_WRITE.build();
		this.OTP_WRITE.add_hdl_path('{
            '{"i_Test_Registers.i_Test_Registers_OTP_WRITE.data", 8, 12},
            '{"i_Test_Registers.i_Test_Registers_OTP_WRITE.address", 20, 12}
		});

		this.OTP_READ = ral_reg_Test_Registers_OTP_READ::type_id::create("OTP_READ",,get_full_name());
		if(this.OTP_READ.has_coverage(UVM_CVR_REG_BITS))
			this.OTP_READ.cg_bits.option.name = {get_name(), ".OTP_READ_bits"};
		this.OTP_READ.configure(get_block(), this, "");
		this.OTP_READ.build();
		this.OTP_READ.add_hdl_path('{
            '{"i_Test_Registers.i_Test_Registers_OTP_READ.data", 0, 12},
            '{"i_Test_Registers.i_Test_Registers_OTP_READ.address", 20, 12}
		});

		this.OTP_BIST_CONTROL = ral_reg_Test_Registers_OTP_BIST_CONTROL::type_id::create("OTP_BIST_CONTROL",,get_full_name());
		if(this.OTP_BIST_CONTROL.has_coverage(UVM_CVR_REG_BITS))
			this.OTP_BIST_CONTROL.cg_bits.option.name = {get_name(), ".OTP_BIST_CONTROL_bits"};
		this.OTP_BIST_CONTROL.configure(get_block(), this, "");
		this.OTP_BIST_CONTROL.build();
		this.OTP_BIST_CONTROL.add_hdl_path('{
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_CONTROL.OTP_PGM", 0, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_CONTROL.OTP_READ", 1, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_CONTROL.SOAK", 2, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_CONTROL.EN_SOAK", 4, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_CONTROL.STRESS", 5, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_CONTROL.SEL_TRP", 6, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_CONTROL.SEL_RD", 7, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_CONTROL.SEL_MPP", 8, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_CONTROL.SEL_MRR", 9, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_CONTROL.SEL_MR", 10, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_CONTROL.MAX_SOAK", 12, 3}
		});

		this.OTP_READ_CONFIG = ral_reg_Test_Registers_OTP_READ_CONFIG::type_id::create("OTP_READ_CONFIG",,get_full_name());
		if(this.OTP_READ_CONFIG.has_coverage(UVM_CVR_REG_BITS))
			this.OTP_READ_CONFIG.cg_bits.option.name = {get_name(), ".OTP_READ_CONFIG_bits"};
		this.OTP_READ_CONFIG.configure(get_block(), this, "");
		this.OTP_READ_CONFIG.build();
		this.OTP_READ_CONFIG.add_hdl_path('{
            '{"i_Test_Registers.i_Test_Registers_OTP_READ_CONFIG.TRP", 0, 7},
            '{"i_Test_Registers.i_Test_Registers_OTP_READ_CONFIG.RD_MODE", 8, 2},
            '{"i_Test_Registers.i_Test_Registers_OTP_READ_CONFIG.ECCERR_L", 12, 2},
            '{"i_Test_Registers.i_Test_Registers_OTP_READ_CONFIG.ECCERR_H", 14, 2}
		});

		this.OTP_BIST_STATUS = ral_reg_Test_Registers_OTP_BIST_STATUS::type_id::create("OTP_BIST_STATUS",,get_full_name());
		if(this.OTP_BIST_STATUS.has_coverage(UVM_CVR_REG_BITS))
			this.OTP_BIST_STATUS.cg_bits.option.name = {get_name(), ".OTP_BIST_STATUS_bits"};
		this.OTP_BIST_STATUS.configure(get_block(), this, "");
		this.OTP_BIST_STATUS.build();
		this.OTP_BIST_STATUS.add_hdl_path('{
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_STATUS.PROG_BIT", 0, 6},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_STATUS.DONE", 7, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_STATUS.SOAK_PULSE", 8, 4},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_STATUS.BUSY", 12, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_STATUS.FAIL0", 13, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_STATUS.FAIL1", 14, 1},
            '{"i_Test_Registers.i_Test_Registers_OTP_BIST_STATUS.SOAK", 15, 1}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(OTP_CONTROL, offset+`UVM_REG_ADDR_WIDTH'hA0);
	  mp.add_reg(OTP_CONFIG, offset+`UVM_REG_ADDR_WIDTH'hA1);
	  mp.add_reg(OTP_WRITE, offset+`UVM_REG_ADDR_WIDTH'hA2);
	  mp.add_reg(OTP_READ, offset+`UVM_REG_ADDR_WIDTH'hA4);
	  mp.add_reg(OTP_BIST_CONTROL, offset+`UVM_REG_ADDR_WIDTH'hA6);
	  mp.add_reg(OTP_READ_CONFIG, offset+`UVM_REG_ADDR_WIDTH'hA7);
	  mp.add_reg(OTP_BIST_STATUS, offset+`UVM_REG_ADDR_WIDTH'hA8);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  OTP_CONTROL.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hA0);
	  OTP_CONFIG.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hA1);
	  OTP_WRITE.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hA2);
	  OTP_READ.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hA4);
	  OTP_BIST_CONTROL.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hA6);
	  OTP_READ_CONFIG.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hA7);
	  OTP_BIST_STATUS.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hA8);

	endfunction

	`uvm_object_utils(ral_regfile_Test_Registers)
endclass : ral_regfile_Test_Registers




class ral_block_mem extends uvm_reg_block;
	rand ral_regfile_Test_Registers Test_Registers;

	function new(string name = "mem");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.Test_Registers = ral_regfile_Test_Registers::type_id::create("Test_Registers",,get_full_name());
      this.Test_Registers.configure(this, null, "");
      this.Test_Registers.build();
      this.Test_Registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_mem)

endclass : ral_block_mem


class ral_reg_ELIP_test_register_IR_ELIP_RDF extends uvm_reg;
	uvm_reg_field DATA;
	rand uvm_reg_field ADDR;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DATA: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd_as_0 = {17'b???????????????01};
	      wildcard bins bit_0_rd_as_1 = {17'b???????????????11};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {17'b??????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {17'b??????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {17'b?????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {17'b?????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {17'b????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {17'b????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd_as_0 = {17'b???????????0????1};
	      wildcard bins bit_4_rd_as_1 = {17'b???????????1????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {17'b??????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {17'b??????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {17'b?????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {17'b?????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {17'b????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {17'b????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd_as_0 = {17'b???????0????????1};
	      wildcard bins bit_8_rd_as_1 = {17'b???????1????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {17'b??????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {17'b??????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {17'b?????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {17'b?????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {17'b????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {17'b????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd_as_0 = {17'b???0????????????1};
	      wildcard bins bit_12_rd_as_1 = {17'b???1????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {17'b??0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {17'b??1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {17'b?0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {17'b?1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {17'b0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {17'b1???????????????1};
	      option.weight = 64;
	   }
	   ADDR: coverpoint {m_data[31:16], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      option.weight = 32;
	   }
	endgroup
	function new(string name = "ELIP_test_register_IR_ELIP_RDF");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DATA = uvm_reg_field::type_id::create("DATA",,get_full_name());
      this.DATA.configure(this, 16, 0, "RO", 0, 0, 1, 0, 1);
      this.ADDR = uvm_reg_field::type_id::create("ADDR",,get_full_name());
      this.ADDR.configure(this, 16, 16, "WO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_ELIP_test_register_IR_ELIP_RDF)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_ELIP_test_register_IR_ELIP_RDF


class ral_reg_ELIP_test_register_IR_ELIP_RD extends uvm_reg;
	uvm_reg_field DATA;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DATA: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd_as_0 = {17'b???????????????01};
	      wildcard bins bit_0_rd_as_1 = {17'b???????????????11};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {17'b??????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {17'b??????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {17'b?????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {17'b?????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {17'b????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {17'b????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd_as_0 = {17'b???????????0????1};
	      wildcard bins bit_4_rd_as_1 = {17'b???????????1????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {17'b??????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {17'b??????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {17'b?????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {17'b?????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {17'b????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {17'b????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd_as_0 = {17'b???????0????????1};
	      wildcard bins bit_8_rd_as_1 = {17'b???????1????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {17'b??????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {17'b??????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {17'b?????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {17'b?????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {17'b????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {17'b????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd_as_0 = {17'b???0????????????1};
	      wildcard bins bit_12_rd_as_1 = {17'b???1????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {17'b??0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {17'b??1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {17'b?0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {17'b?1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {17'b0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {17'b1???????????????1};
	      option.weight = 64;
	   }
	endgroup
	function new(string name = "ELIP_test_register_IR_ELIP_RD");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DATA = uvm_reg_field::type_id::create("DATA",,get_full_name());
      this.DATA.configure(this, 16, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_ELIP_test_register_IR_ELIP_RD)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_ELIP_test_register_IR_ELIP_RD


class ral_reg_ELIP_test_register_IR_ELIP_RDI extends uvm_reg;
	uvm_reg_field DATA;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DATA: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd_as_0 = {17'b???????????????01};
	      wildcard bins bit_0_rd_as_1 = {17'b???????????????11};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {17'b??????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {17'b??????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {17'b?????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {17'b?????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {17'b????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {17'b????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd_as_0 = {17'b???????????0????1};
	      wildcard bins bit_4_rd_as_1 = {17'b???????????1????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {17'b??????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {17'b??????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {17'b?????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {17'b?????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {17'b????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {17'b????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd_as_0 = {17'b???????0????????1};
	      wildcard bins bit_8_rd_as_1 = {17'b???????1????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {17'b??????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {17'b??????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {17'b?????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {17'b?????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {17'b????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {17'b????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd_as_0 = {17'b???0????????????1};
	      wildcard bins bit_12_rd_as_1 = {17'b???1????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {17'b??0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {17'b??1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {17'b?0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {17'b?1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {17'b0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {17'b1???????????????1};
	      option.weight = 64;
	   }
	endgroup
	function new(string name = "ELIP_test_register_IR_ELIP_RDI");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DATA = uvm_reg_field::type_id::create("DATA",,get_full_name());
      this.DATA.configure(this, 16, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_ELIP_test_register_IR_ELIP_RDI)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_ELIP_test_register_IR_ELIP_RDI


class ral_reg_ELIP_test_register_IR_ELIP_WRF extends uvm_reg;
	rand uvm_reg_field DATA;
	rand uvm_reg_field ADDR;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DATA: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      option.weight = 32;
	   }
	   ADDR: coverpoint {m_data[31:16], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      option.weight = 32;
	   }
	endgroup
	function new(string name = "ELIP_test_register_IR_ELIP_WRF");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DATA = uvm_reg_field::type_id::create("DATA",,get_full_name());
      this.DATA.configure(this, 16, 0, "WO", 0, 0, 1, 0, 1);
      this.ADDR = uvm_reg_field::type_id::create("ADDR",,get_full_name());
      this.ADDR.configure(this, 16, 16, "WO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_ELIP_test_register_IR_ELIP_WRF)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_ELIP_test_register_IR_ELIP_WRF


class ral_reg_ELIP_test_register_IR_ELIP_WR extends uvm_reg;
	uvm_reg_field DATA;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DATA: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd_as_0 = {17'b???????????????01};
	      wildcard bins bit_0_rd_as_1 = {17'b???????????????11};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {17'b??????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {17'b??????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {17'b?????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {17'b?????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {17'b????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {17'b????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd_as_0 = {17'b???????????0????1};
	      wildcard bins bit_4_rd_as_1 = {17'b???????????1????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {17'b??????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {17'b??????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {17'b?????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {17'b?????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {17'b????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {17'b????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd_as_0 = {17'b???????0????????1};
	      wildcard bins bit_8_rd_as_1 = {17'b???????1????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {17'b??????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {17'b??????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {17'b?????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {17'b?????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {17'b????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {17'b????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd_as_0 = {17'b???0????????????1};
	      wildcard bins bit_12_rd_as_1 = {17'b???1????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {17'b??0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {17'b??1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {17'b?0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {17'b?1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {17'b0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {17'b1???????????????1};
	      option.weight = 64;
	   }
	endgroup
	function new(string name = "ELIP_test_register_IR_ELIP_WR");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DATA = uvm_reg_field::type_id::create("DATA",,get_full_name());
      this.DATA.configure(this, 16, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_ELIP_test_register_IR_ELIP_WR)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_ELIP_test_register_IR_ELIP_WR


class ral_reg_ELIP_test_register_IR_ELIP_WRI extends uvm_reg;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	endgroup
	function new(string name = "ELIP_test_register_IR_ELIP_WRI");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
   endfunction: build

	`uvm_object_utils(ral_reg_ELIP_test_register_IR_ELIP_WRI)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_ELIP_test_register_IR_ELIP_WRI


class ral_regfile_ELIP_test_register extends uvm_reg_file;

	rand ral_reg_ELIP_test_register_IR_ELIP_RDF IR_ELIP_RDF;
	rand ral_reg_ELIP_test_register_IR_ELIP_RD IR_ELIP_RD;
	rand ral_reg_ELIP_test_register_IR_ELIP_RDI IR_ELIP_RDI;
	rand ral_reg_ELIP_test_register_IR_ELIP_WRF IR_ELIP_WRF;
	rand ral_reg_ELIP_test_register_IR_ELIP_WR IR_ELIP_WR;
	rand ral_reg_ELIP_test_register_IR_ELIP_WRI IR_ELIP_WRI;


	function new(string name = "ELIP_test_register");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.IR_ELIP_RDF = ral_reg_ELIP_test_register_IR_ELIP_RDF::type_id::create("IR_ELIP_RDF",,get_full_name());
		if(this.IR_ELIP_RDF.has_coverage(UVM_CVR_REG_BITS))
			this.IR_ELIP_RDF.cg_bits.option.name = {get_name(), ".IR_ELIP_RDF_bits"};
		this.IR_ELIP_RDF.configure(get_block(), this, "");
		this.IR_ELIP_RDF.build();
		this.IR_ELIP_RDF.add_hdl_path('{
            '{"i_ELIP_test_register.i_ELIP_test_register_IR_ELIP_RDF.DATA", 0, 16},
            '{"i_ELIP_test_register.i_ELIP_test_register_IR_ELIP_RDF.ADDR", 16, 16}
		});

		this.IR_ELIP_RD = ral_reg_ELIP_test_register_IR_ELIP_RD::type_id::create("IR_ELIP_RD",,get_full_name());
		if(this.IR_ELIP_RD.has_coverage(UVM_CVR_REG_BITS))
			this.IR_ELIP_RD.cg_bits.option.name = {get_name(), ".IR_ELIP_RD_bits"};
		this.IR_ELIP_RD.configure(get_block(), this, "");
		this.IR_ELIP_RD.build();
		this.IR_ELIP_RD.add_hdl_path('{
            '{"i_ELIP_test_register.i_ELIP_test_register_IR_ELIP_RD.DATA", 0, 16}
		});

		this.IR_ELIP_RDI = ral_reg_ELIP_test_register_IR_ELIP_RDI::type_id::create("IR_ELIP_RDI",,get_full_name());
		if(this.IR_ELIP_RDI.has_coverage(UVM_CVR_REG_BITS))
			this.IR_ELIP_RDI.cg_bits.option.name = {get_name(), ".IR_ELIP_RDI_bits"};
		this.IR_ELIP_RDI.configure(get_block(), this, "");
		this.IR_ELIP_RDI.build();
		this.IR_ELIP_RDI.add_hdl_path('{
            '{"i_ELIP_test_register.i_ELIP_test_register_IR_ELIP_RDI.DATA", 0, 16}
		});

		this.IR_ELIP_WRF = ral_reg_ELIP_test_register_IR_ELIP_WRF::type_id::create("IR_ELIP_WRF",,get_full_name());
		if(this.IR_ELIP_WRF.has_coverage(UVM_CVR_REG_BITS))
			this.IR_ELIP_WRF.cg_bits.option.name = {get_name(), ".IR_ELIP_WRF_bits"};
		this.IR_ELIP_WRF.configure(get_block(), this, "");
		this.IR_ELIP_WRF.build();
		this.IR_ELIP_WRF.add_hdl_path('{
            '{"i_ELIP_test_register.i_ELIP_test_register_IR_ELIP_WRF.DATA", 0, 16},
            '{"i_ELIP_test_register.i_ELIP_test_register_IR_ELIP_WRF.ADDR", 16, 16}
		});

		this.IR_ELIP_WR = ral_reg_ELIP_test_register_IR_ELIP_WR::type_id::create("IR_ELIP_WR",,get_full_name());
		if(this.IR_ELIP_WR.has_coverage(UVM_CVR_REG_BITS))
			this.IR_ELIP_WR.cg_bits.option.name = {get_name(), ".IR_ELIP_WR_bits"};
		this.IR_ELIP_WR.configure(get_block(), this, "");
		this.IR_ELIP_WR.build();
		this.IR_ELIP_WR.add_hdl_path('{
            '{"i_ELIP_test_register.i_ELIP_test_register_IR_ELIP_WR.DATA", 0, 16}
		});

		this.IR_ELIP_WRI = ral_reg_ELIP_test_register_IR_ELIP_WRI::type_id::create("IR_ELIP_WRI",,get_full_name());
		if(this.IR_ELIP_WRI.has_coverage(UVM_CVR_REG_BITS))
			this.IR_ELIP_WRI.cg_bits.option.name = {get_name(), ".IR_ELIP_WRI_bits"};
		this.IR_ELIP_WRI.configure(get_block(), this, "");
		this.IR_ELIP_WRI.build();
		this.IR_ELIP_WRI.add_hdl_path('{

		   '{"i_ELIP_test_register.i_ELIP_test_register_IR_ELIP_WRI", -1, -1}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(IR_ELIP_RDF, offset+`UVM_REG_ADDR_WIDTH'hC0);
	  mp.add_reg(IR_ELIP_RD, offset+`UVM_REG_ADDR_WIDTH'hC1);
	  mp.add_reg(IR_ELIP_RDI, offset+`UVM_REG_ADDR_WIDTH'hC2);
	  mp.add_reg(IR_ELIP_WRF, offset+`UVM_REG_ADDR_WIDTH'hC3);
	  mp.add_reg(IR_ELIP_WR, offset+`UVM_REG_ADDR_WIDTH'hC4);
	  mp.add_reg(IR_ELIP_WRI, offset+`UVM_REG_ADDR_WIDTH'hC5);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  IR_ELIP_RDF.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hC0);
	  IR_ELIP_RD.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hC1);
	  IR_ELIP_RDI.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hC2);
	  IR_ELIP_WRF.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hC3);
	  IR_ELIP_WR.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hC4);
	  IR_ELIP_WRI.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hC5);

	endfunction

	`uvm_object_utils(ral_regfile_ELIP_test_register)
endclass : ral_regfile_ELIP_test_register




class ral_block_jtag_elip extends uvm_reg_block;
	rand ral_regfile_ELIP_test_register ELIP_test_register;

	function new(string name = "jtag_elip");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.ELIP_test_register = ral_regfile_ELIP_test_register::type_id::create("ELIP_test_register",,get_full_name());
      this.ELIP_test_register.configure(this, null, "");
      this.ELIP_test_register.build();
      this.ELIP_test_register.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_jtag_elip)

endclass : ral_block_jtag_elip


class ral_reg_TEST_WS_TMR_SEL_WS extends uvm_reg;
	rand uvm_reg_field DAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DAC: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "TEST_WS_TMR_SEL_WS");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DAC = uvm_reg_field::type_id::create("DAC",,get_full_name());
      this.DAC.configure(this, 1, 0, "RW", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_WS_TMR_SEL_WS)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_WS_TMR_SEL_WS


class ral_reg_TEST_WS_TMR_VAL_WS extends uvm_reg;
	rand uvm_reg_field DAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DAC: coverpoint {m_data[4:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	endgroup
	function new(string name = "TEST_WS_TMR_VAL_WS");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DAC = uvm_reg_field::type_id::create("DAC",,get_full_name());
      this.DAC.configure(this, 5, 0, "RW", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_TEST_WS_TMR_VAL_WS)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_TEST_WS_TMR_VAL_WS


class ral_regfile_TEST_WS extends uvm_reg_file;

	rand ral_reg_TEST_WS_TMR_SEL_WS TMR_SEL_WS;
	rand ral_reg_TEST_WS_TMR_VAL_WS TMR_VAL_WS;


	function new(string name = "TEST_WS");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.TMR_SEL_WS = ral_reg_TEST_WS_TMR_SEL_WS::type_id::create("TMR_SEL_WS",,get_full_name());
		if(this.TMR_SEL_WS.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_SEL_WS.cg_bits.option.name = {get_name(), ".TMR_SEL_WS_bits"};
		this.TMR_SEL_WS.configure(get_block(), this, "");
		this.TMR_SEL_WS.build();
		this.TMR_SEL_WS.add_hdl_path('{
            '{"i_TEST_WS.i_TEST_WS_TMR_SEL_WS.DAC", 0, 1}
		});

		this.TMR_VAL_WS = ral_reg_TEST_WS_TMR_VAL_WS::type_id::create("TMR_VAL_WS",,get_full_name());
		if(this.TMR_VAL_WS.has_coverage(UVM_CVR_REG_BITS))
			this.TMR_VAL_WS.cg_bits.option.name = {get_name(), ".TMR_VAL_WS_bits"};
		this.TMR_VAL_WS.configure(get_block(), this, "");
		this.TMR_VAL_WS.build();
		this.TMR_VAL_WS.add_hdl_path('{
            '{"i_TEST_WS.i_TEST_WS_TMR_VAL_WS.DAC", 0, 5}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(TMR_SEL_WS, offset+`UVM_REG_ADDR_WIDTH'h0);
	  mp.add_reg(TMR_VAL_WS, offset+`UVM_REG_ADDR_WIDTH'h1);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  TMR_SEL_WS.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h0);
	  TMR_VAL_WS.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h1);

	endfunction

	`uvm_object_utils(ral_regfile_TEST_WS)
endclass : ral_regfile_TEST_WS




class ral_block_test_ws extends uvm_reg_block;
	rand ral_regfile_TEST_WS TEST_WS;

	function new(string name = "test_ws");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.TEST_WS = ral_regfile_TEST_WS::type_id::create("TEST_WS",,get_full_name());
      this.TEST_WS.configure(this, null, "");
      this.TEST_WS.build();
      this.TEST_WS.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_test_ws)

endclass : ral_block_test_ws


class ral_sys_jtag_test_registers extends uvm_reg_block;

   rand ral_block_test_top TEST_TOP;
   rand ral_block_test_supply TEST_SUP;
   rand ral_block_test_osc TEST_OSC;
   rand ral_block_test_dsi TEST_DSI[2];
   rand ral_block_SCAN_TEST TEST_SCAN;
   rand ral_block_SRAM_BIST TEST_SRAM;
   rand ral_block_otp_test TEST_OTP_CONFIG;
   rand ral_block_mem TEST_OTP;
   rand ral_block_jtag_elip TEST_ELIP;
   rand ral_block_test_ws TEST_WS_0;
   rand ral_block_test_ws TEST_WS_1;

	function new(string name = "jtag_test_registers");
		super.new(name);
	endfunction: new

	function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.TEST_TOP = ral_block_test_top::type_id::create("TEST_TOP",,get_full_name());
      this.TEST_TOP.configure(this, "i_test.i_test_top");
      this.TEST_TOP.build();
      this.default_map.add_submap(this.TEST_TOP.default_map, `UVM_REG_ADDR_WIDTH'h0);
      this.TEST_SUP = ral_block_test_supply::type_id::create("TEST_SUP",,get_full_name());
      this.TEST_SUP.configure(this, "i_main_control.i_test_supply");
      this.TEST_SUP.build();
      this.default_map.add_submap(this.TEST_SUP.default_map, `UVM_REG_ADDR_WIDTH'h10);
      this.TEST_OSC = ral_block_test_osc::type_id::create("TEST_OSC",,get_full_name());
      this.TEST_OSC.configure(this, "i_timebase.i_test_osc");
      this.TEST_OSC.build();
      this.default_map.add_submap(this.TEST_OSC.default_map, `UVM_REG_ADDR_WIDTH'h20);
      foreach (this.TEST_DSI[i]) begin
         int J = i;
         this.TEST_DSI[J] = ral_block_test_dsi::type_id::create($psprintf("TEST_DSI[%0d]", J),,get_full_name());
         this.TEST_DSI[J].configure(this, $psprintf("i_dsi3.generate_dsi3_blocks[%0d].i_dsi3_block.i_test_dsi", J));
         this.TEST_DSI[J].build();
         this.default_map.add_submap(this.TEST_DSI[J].default_map, `UVM_REG_ADDR_WIDTH'h30+J*`UVM_REG_ADDR_WIDTH'h10);
      end
      this.TEST_SCAN = ral_block_SCAN_TEST::type_id::create("TEST_SCAN",,get_full_name());
      this.TEST_SCAN.configure(this, "i_test.i_test_control");
      this.TEST_SCAN.build();
      this.default_map.add_submap(this.TEST_SCAN.default_map, `UVM_REG_ADDR_WIDTH'hB0);
      this.TEST_SRAM = ral_block_SRAM_BIST::type_id::create("TEST_SRAM",,get_full_name());
      this.TEST_SRAM.configure(this, "i_data_storage.i_ram_wrapper_ecc_with_bist");
      this.TEST_SRAM.build();
      this.default_map.add_submap(this.TEST_SRAM.default_map, `UVM_REG_ADDR_WIDTH'hC0);
      this.TEST_OTP_CONFIG = ral_block_otp_test::type_id::create("TEST_OTP_CONFIG",,get_full_name());
      this.TEST_OTP_CONFIG.configure(this, "i_test.i_test_control");
      this.TEST_OTP_CONFIG.build();
      this.default_map.add_submap(this.TEST_OTP_CONFIG.default_map, `UVM_REG_ADDR_WIDTH'h0);
      this.TEST_OTP = ral_block_mem::type_id::create("TEST_OTP",,get_full_name());
      this.TEST_OTP.configure(this, "");
      this.TEST_OTP.build();
      this.default_map.add_submap(this.TEST_OTP.default_map, `UVM_REG_ADDR_WIDTH'h0);
      this.TEST_ELIP = ral_block_jtag_elip::type_id::create("TEST_ELIP",,get_full_name());
      this.TEST_ELIP.configure(this, "i_test.i_test_control.i_jtag_elip");
      this.TEST_ELIP.build();
      this.default_map.add_submap(this.TEST_ELIP.default_map, `UVM_REG_ADDR_WIDTH'h0);
      this.TEST_WS_0 = ral_block_test_ws::type_id::create("TEST_WS_0",,get_full_name());
      this.TEST_WS_0.configure(this, "i_dsi3.i_wave_shaping.generate_wave_shape[%i].i_test_ws");
      this.TEST_WS_0.build();
      this.default_map.add_submap(this.TEST_WS_0.default_map, `UVM_REG_ADDR_WIDTH'h50);
      this.TEST_WS_1 = ral_block_test_ws::type_id::create("TEST_WS_1",,get_full_name());
      this.TEST_WS_1.configure(this, "i_dsi3.i_wave_shaping.generate_wave_shape[%i].i_test_ws");
      this.TEST_WS_1.build();
      this.default_map.add_submap(this.TEST_WS_1.default_map, `UVM_REG_ADDR_WIDTH'h60);
	  uvm_config_db #(uvm_reg_block)::set(null,"","RegisterModel_Debug",this);
	endfunction : build

	`uvm_object_utils(ral_sys_jtag_test_registers)
endclass : ral_sys_jtag_test_registers



`endif

endpackage
