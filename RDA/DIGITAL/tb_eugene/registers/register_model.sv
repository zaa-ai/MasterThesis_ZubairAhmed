`ifndef RAL_DEVICE_REGISTERS
package regmodel_pkg;

`include "uvm_macros.svh"

`define RAL_DEVICE_REGISTERS

import uvm_pkg::*;

class ral_reg_IC_revision_and_ID_registers_IC_REVISION extends uvm_reg;
	uvm_reg_field REVISION;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   REVISION: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "IC_revision_and_ID_registers_IC_REVISION");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.REVISION = uvm_reg_field::type_id::create("REVISION",,get_full_name());
      this.REVISION.configure(this, 16, 0, "RO", 0, 1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_IC_revision_and_ID_registers_IC_REVISION)

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
endclass : ral_reg_IC_revision_and_ID_registers_IC_REVISION


class ral_reg_IC_revision_and_ID_registers_CHIP_ID_LOW extends uvm_reg;
	uvm_reg_field CHIP_ID_LOW;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CHIP_ID_LOW: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "IC_revision_and_ID_registers_CHIP_ID_LOW");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CHIP_ID_LOW = uvm_reg_field::type_id::create("CHIP_ID_LOW",,get_full_name());
      this.CHIP_ID_LOW.configure(this, 16, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_IC_revision_and_ID_registers_CHIP_ID_LOW)

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
endclass : ral_reg_IC_revision_and_ID_registers_CHIP_ID_LOW


class ral_reg_IC_revision_and_ID_registers_CHIP_ID_HIGH extends uvm_reg;
	uvm_reg_field CHIP_ID_HIGH;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CHIP_ID_HIGH: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "IC_revision_and_ID_registers_CHIP_ID_HIGH");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CHIP_ID_HIGH = uvm_reg_field::type_id::create("CHIP_ID_HIGH",,get_full_name());
      this.CHIP_ID_HIGH.configure(this, 16, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_IC_revision_and_ID_registers_CHIP_ID_HIGH)

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
endclass : ral_reg_IC_revision_and_ID_registers_CHIP_ID_HIGH


class ral_regfile_IC_revision_and_ID_registers extends uvm_reg_file;

	rand ral_reg_IC_revision_and_ID_registers_IC_REVISION IC_REVISION;
	rand ral_reg_IC_revision_and_ID_registers_CHIP_ID_LOW CHIP_ID_LOW;
	rand ral_reg_IC_revision_and_ID_registers_CHIP_ID_HIGH CHIP_ID_HIGH;


	function new(string name = "IC_revision_and_ID_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.IC_REVISION = ral_reg_IC_revision_and_ID_registers_IC_REVISION::type_id::create("IC_REVISION",,get_full_name());
		if(this.IC_REVISION.has_coverage(UVM_CVR_REG_BITS))
			this.IC_REVISION.cg_bits.option.name = {get_name(), ".IC_REVISION_bits"};
		this.IC_REVISION.configure(get_block(), this, "");
		this.IC_REVISION.build();
		this.IC_REVISION.add_hdl_path('{
            '{"i_IC_revision_and_ID_registers.i_IC_revision_and_ID_registers_IC_REVISION.REVISION", 0, 16}
		});

		this.CHIP_ID_LOW = ral_reg_IC_revision_and_ID_registers_CHIP_ID_LOW::type_id::create("CHIP_ID_LOW",,get_full_name());
		if(this.CHIP_ID_LOW.has_coverage(UVM_CVR_REG_BITS))
			this.CHIP_ID_LOW.cg_bits.option.name = {get_name(), ".CHIP_ID_LOW_bits"};
		this.CHIP_ID_LOW.configure(get_block(), this, "");
		this.CHIP_ID_LOW.build();
		this.CHIP_ID_LOW.add_hdl_path('{
            '{"i_IC_revision_and_ID_registers.i_IC_revision_and_ID_registers_CHIP_ID_LOW.CHIP_ID_LOW", 0, 16}
		});

		this.CHIP_ID_HIGH = ral_reg_IC_revision_and_ID_registers_CHIP_ID_HIGH::type_id::create("CHIP_ID_HIGH",,get_full_name());
		if(this.CHIP_ID_HIGH.has_coverage(UVM_CVR_REG_BITS))
			this.CHIP_ID_HIGH.cg_bits.option.name = {get_name(), ".CHIP_ID_HIGH_bits"};
		this.CHIP_ID_HIGH.configure(get_block(), this, "");
		this.CHIP_ID_HIGH.build();
		this.CHIP_ID_HIGH.add_hdl_path('{
            '{"i_IC_revision_and_ID_registers.i_IC_revision_and_ID_registers_CHIP_ID_HIGH.CHIP_ID_HIGH", 0, 16}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(IC_REVISION, offset+`UVM_REG_ADDR_WIDTH'h1F);
	  uvm_resource_db#(bit)::set({"REG::", IC_REVISION.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(bit)::set({"REG::", IC_REVISION.get_full_name()}, "NO_REG_HW_RESET_TEST", 1, this);
	  mp.add_reg(CHIP_ID_LOW, offset+`UVM_REG_ADDR_WIDTH'h1);
	  mp.add_reg(CHIP_ID_HIGH, offset+`UVM_REG_ADDR_WIDTH'h2);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  IC_REVISION.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h1F);
	  CHIP_ID_LOW.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h1);
	  CHIP_ID_HIGH.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h2);

	endfunction

	`uvm_object_utils(ral_regfile_IC_revision_and_ID_registers)
endclass : ral_regfile_IC_revision_and_ID_registers




class ral_block_info extends uvm_reg_block;
	rand ral_regfile_IC_revision_and_ID_registers IC_revision_and_ID_registers;

	function new(string name = "info");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 2, UVM_LITTLE_ENDIAN, 0);
      this.IC_revision_and_ID_registers = ral_regfile_IC_revision_and_ID_registers::type_id::create("IC_revision_and_ID_registers",,get_full_name());
      this.IC_revision_and_ID_registers.configure(this, null, "");
      this.IC_revision_and_ID_registers.build();
      this.IC_revision_and_ID_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_info)

endclass : ral_block_info


class ral_reg_supply_registers_TRIM_IREF extends uvm_reg;
	uvm_reg_field IREF;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   IREF: coverpoint {m_data[3:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "supply_registers_TRIM_IREF");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.IREF = uvm_reg_field::type_id::create("IREF",,get_full_name());
      this.IREF.configure(this, 4, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_supply_registers_TRIM_IREF)

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
endclass : ral_reg_supply_registers_TRIM_IREF


class ral_reg_supply_registers_TRIM_OT extends uvm_reg;
	uvm_reg_field TRIM_OT;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TRIM_OT: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "supply_registers_TRIM_OT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TRIM_OT = uvm_reg_field::type_id::create("TRIM_OT",,get_full_name());
      this.TRIM_OT.configure(this, 2, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_supply_registers_TRIM_OT)

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
endclass : ral_reg_supply_registers_TRIM_OT


class ral_reg_supply_registers_SUP_HW_CTRL extends uvm_reg;
	rand uvm_reg_field IGNORE_UV;
	rand uvm_reg_field IGNORE_HWF;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   IGNORE_UV: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   IGNORE_HWF: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "supply_registers_SUP_HW_CTRL");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.IGNORE_UV = uvm_reg_field::type_id::create("IGNORE_UV",,get_full_name());
      this.IGNORE_UV.configure(this, 1, 0, "RW", 0, 0, 1, 0, 0);
      this.IGNORE_HWF = uvm_reg_field::type_id::create("IGNORE_HWF",,get_full_name());
      this.IGNORE_HWF.configure(this, 1, 1, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_supply_registers_SUP_HW_CTRL)

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
endclass : ral_reg_supply_registers_SUP_HW_CTRL


class ral_reg_supply_registers_SUP_IRQ_STAT extends uvm_reg;
	rand uvm_reg_field REF_FAIL;
	rand uvm_reg_field VCCUV;
	rand uvm_reg_field LDOUV;
	rand uvm_reg_field OTE;
	rand uvm_reg_field OTW;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   REF_FAIL: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VCCUV: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   LDOUV: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTE: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTW: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "supply_registers_SUP_IRQ_STAT");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.REF_FAIL = uvm_reg_field::type_id::create("REF_FAIL",,get_full_name());
      this.REF_FAIL.configure(this, 1, 0, "W1C", 0, 0, 1, 0, 0);
      this.VCCUV = uvm_reg_field::type_id::create("VCCUV",,get_full_name());
      this.VCCUV.configure(this, 1, 1, "W1C", 0, 0, 1, 0, 0);
      this.LDOUV = uvm_reg_field::type_id::create("LDOUV",,get_full_name());
      this.LDOUV.configure(this, 1, 2, "W1C", 0, 0, 1, 0, 0);
      this.OTE = uvm_reg_field::type_id::create("OTE",,get_full_name());
      this.OTE.configure(this, 1, 3, "W1C", 0, 0, 1, 0, 0);
      this.OTW = uvm_reg_field::type_id::create("OTW",,get_full_name());
      this.OTW.configure(this, 1, 4, "W1C", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_supply_registers_SUP_IRQ_STAT)

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
endclass : ral_reg_supply_registers_SUP_IRQ_STAT


class ral_reg_supply_registers_SUP_IRQ_MASK extends uvm_reg;
	rand uvm_reg_field REF_FAIL;
	rand uvm_reg_field VCCUV;
	rand uvm_reg_field LDOUV;
	rand uvm_reg_field OTE;
	rand uvm_reg_field OTW;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   REF_FAIL: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VCCUV: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   LDOUV: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTE: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTW: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "supply_registers_SUP_IRQ_MASK");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.REF_FAIL = uvm_reg_field::type_id::create("REF_FAIL",,get_full_name());
      this.REF_FAIL.configure(this, 1, 0, "RW", 0, 1, 1, 0, 0);
      this.VCCUV = uvm_reg_field::type_id::create("VCCUV",,get_full_name());
      this.VCCUV.configure(this, 1, 1, "RW", 0, 1, 1, 0, 0);
      this.LDOUV = uvm_reg_field::type_id::create("LDOUV",,get_full_name());
      this.LDOUV.configure(this, 1, 2, "RW", 0, 1, 1, 0, 0);
      this.OTE = uvm_reg_field::type_id::create("OTE",,get_full_name());
      this.OTE.configure(this, 1, 3, "RW", 0, 1, 1, 0, 0);
      this.OTW = uvm_reg_field::type_id::create("OTW",,get_full_name());
      this.OTW.configure(this, 1, 4, "RW", 0, 1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_supply_registers_SUP_IRQ_MASK)

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
endclass : ral_reg_supply_registers_SUP_IRQ_MASK


class ral_reg_supply_registers_SUP_STAT extends uvm_reg;
	uvm_reg_field REF_FAIL;
	uvm_reg_field VCCUV;
	uvm_reg_field LDOUV;
	uvm_reg_field OTE;
	uvm_reg_field OTW;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   REF_FAIL: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VCCUV: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   LDOUV: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTE: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   OTW: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "supply_registers_SUP_STAT");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.REF_FAIL = uvm_reg_field::type_id::create("REF_FAIL",,get_full_name());
      this.REF_FAIL.configure(this, 1, 0, "RO", 0, 0, 1, 0, 0);
      this.VCCUV = uvm_reg_field::type_id::create("VCCUV",,get_full_name());
      this.VCCUV.configure(this, 1, 1, "RO", 0, 0, 1, 0, 0);
      this.LDOUV = uvm_reg_field::type_id::create("LDOUV",,get_full_name());
      this.LDOUV.configure(this, 1, 2, "RO", 0, 0, 1, 0, 0);
      this.OTE = uvm_reg_field::type_id::create("OTE",,get_full_name());
      this.OTE.configure(this, 1, 3, "RO", 0, 0, 1, 0, 0);
      this.OTW = uvm_reg_field::type_id::create("OTW",,get_full_name());
      this.OTW.configure(this, 1, 4, "RO", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_supply_registers_SUP_STAT)

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
endclass : ral_reg_supply_registers_SUP_STAT


class ral_reg_supply_registers_SUP_CTRL extends uvm_reg;
	rand uvm_reg_field EN_LDO;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   EN_LDO: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "supply_registers_SUP_CTRL");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.EN_LDO = uvm_reg_field::type_id::create("EN_LDO",,get_full_name());
      this.EN_LDO.configure(this, 1, 0, "RW", 0, 1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_supply_registers_SUP_CTRL)

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
endclass : ral_reg_supply_registers_SUP_CTRL


class ral_reg_supply_registers_IO_CTRL extends uvm_reg;
	rand uvm_reg_field HICUR;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HICUR: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "supply_registers_IO_CTRL");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HICUR = uvm_reg_field::type_id::create("HICUR",,get_full_name());
      this.HICUR.configure(this, 1, 0, "RW", 0, 1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_supply_registers_IO_CTRL)

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
endclass : ral_reg_supply_registers_IO_CTRL


class ral_regfile_supply_registers extends uvm_reg_file;

	rand ral_reg_supply_registers_TRIM_IREF TRIM_IREF;
	rand ral_reg_supply_registers_TRIM_OT TRIM_OT;
	rand ral_reg_supply_registers_SUP_HW_CTRL SUP_HW_CTRL;
	rand ral_reg_supply_registers_SUP_IRQ_STAT SUP_IRQ_STAT;
	rand ral_reg_supply_registers_SUP_IRQ_MASK SUP_IRQ_MASK;
	rand ral_reg_supply_registers_SUP_STAT SUP_STAT;
	rand ral_reg_supply_registers_SUP_CTRL SUP_CTRL;
	rand ral_reg_supply_registers_IO_CTRL IO_CTRL;


	function new(string name = "supply_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.TRIM_IREF = ral_reg_supply_registers_TRIM_IREF::type_id::create("TRIM_IREF",,get_full_name());
		if(this.TRIM_IREF.has_coverage(UVM_CVR_REG_BITS))
			this.TRIM_IREF.cg_bits.option.name = {get_name(), ".TRIM_IREF_bits"};
		this.TRIM_IREF.configure(get_block(), this, "");
		this.TRIM_IREF.build();
		this.TRIM_IREF.add_hdl_path('{
            '{"i_supply_registers.i_supply_registers_TRIM_IREF.IREF", 0, 4}
		});

		this.TRIM_OT = ral_reg_supply_registers_TRIM_OT::type_id::create("TRIM_OT",,get_full_name());
		if(this.TRIM_OT.has_coverage(UVM_CVR_REG_BITS))
			this.TRIM_OT.cg_bits.option.name = {get_name(), ".TRIM_OT_bits"};
		this.TRIM_OT.configure(get_block(), this, "");
		this.TRIM_OT.build();
		this.TRIM_OT.add_hdl_path('{
            '{"i_supply_registers.i_supply_registers_TRIM_OT.TRIM_OT", 0, 2}
		});

		this.SUP_HW_CTRL = ral_reg_supply_registers_SUP_HW_CTRL::type_id::create("SUP_HW_CTRL",,get_full_name());
		if(this.SUP_HW_CTRL.has_coverage(UVM_CVR_REG_BITS))
			this.SUP_HW_CTRL.cg_bits.option.name = {get_name(), ".SUP_HW_CTRL_bits"};
		this.SUP_HW_CTRL.configure(get_block(), this, "");
		this.SUP_HW_CTRL.build();
		this.SUP_HW_CTRL.add_hdl_path('{
            '{"i_supply_registers.i_supply_registers_SUP_HW_CTRL.IGNORE_UV", 0, 1},
            '{"i_supply_registers.i_supply_registers_SUP_HW_CTRL.IGNORE_HWF", 1, 1}
		});

		this.SUP_IRQ_STAT = ral_reg_supply_registers_SUP_IRQ_STAT::type_id::create("SUP_IRQ_STAT",,get_full_name());
		if(this.SUP_IRQ_STAT.has_coverage(UVM_CVR_REG_BITS))
			this.SUP_IRQ_STAT.cg_bits.option.name = {get_name(), ".SUP_IRQ_STAT_bits"};
		this.SUP_IRQ_STAT.configure(get_block(), this, "");
		this.SUP_IRQ_STAT.build();
		this.SUP_IRQ_STAT.add_hdl_path('{
            '{"i_supply_registers.i_supply_registers_SUP_IRQ_STAT.REF_FAIL", 0, 1},
            '{"i_supply_registers.i_supply_registers_SUP_IRQ_STAT.VCCUV", 1, 1},
            '{"i_supply_registers.i_supply_registers_SUP_IRQ_STAT.LDOUV", 2, 1},
            '{"i_supply_registers.i_supply_registers_SUP_IRQ_STAT.OTE", 3, 1},
            '{"i_supply_registers.i_supply_registers_SUP_IRQ_STAT.OTW", 4, 1}
		});

		this.SUP_IRQ_MASK = ral_reg_supply_registers_SUP_IRQ_MASK::type_id::create("SUP_IRQ_MASK",,get_full_name());
		if(this.SUP_IRQ_MASK.has_coverage(UVM_CVR_REG_BITS))
			this.SUP_IRQ_MASK.cg_bits.option.name = {get_name(), ".SUP_IRQ_MASK_bits"};
		this.SUP_IRQ_MASK.configure(get_block(), this, "");
		this.SUP_IRQ_MASK.build();
		this.SUP_IRQ_MASK.add_hdl_path('{
            '{"i_supply_registers.i_supply_registers_SUP_IRQ_MASK.REF_FAIL", 0, 1},
            '{"i_supply_registers.i_supply_registers_SUP_IRQ_MASK.VCCUV", 1, 1},
            '{"i_supply_registers.i_supply_registers_SUP_IRQ_MASK.LDOUV", 2, 1},
            '{"i_supply_registers.i_supply_registers_SUP_IRQ_MASK.OTE", 3, 1},
            '{"i_supply_registers.i_supply_registers_SUP_IRQ_MASK.OTW", 4, 1}
		});

		this.SUP_STAT = ral_reg_supply_registers_SUP_STAT::type_id::create("SUP_STAT",,get_full_name());
		if(this.SUP_STAT.has_coverage(UVM_CVR_REG_BITS))
			this.SUP_STAT.cg_bits.option.name = {get_name(), ".SUP_STAT_bits"};
		this.SUP_STAT.configure(get_block(), this, "");
		this.SUP_STAT.build();
		this.SUP_STAT.add_hdl_path('{
            '{"i_supply_registers.i_supply_registers_SUP_STAT.REF_FAIL", 0, 1},
            '{"i_supply_registers.i_supply_registers_SUP_STAT.VCCUV", 1, 1},
            '{"i_supply_registers.i_supply_registers_SUP_STAT.LDOUV", 2, 1},
            '{"i_supply_registers.i_supply_registers_SUP_STAT.OTE", 3, 1},
            '{"i_supply_registers.i_supply_registers_SUP_STAT.OTW", 4, 1}
		});

		this.SUP_CTRL = ral_reg_supply_registers_SUP_CTRL::type_id::create("SUP_CTRL",,get_full_name());
		if(this.SUP_CTRL.has_coverage(UVM_CVR_REG_BITS))
			this.SUP_CTRL.cg_bits.option.name = {get_name(), ".SUP_CTRL_bits"};
		this.SUP_CTRL.configure(get_block(), this, "");
		this.SUP_CTRL.build();
		this.SUP_CTRL.add_hdl_path('{
            '{"i_supply_registers.i_supply_registers_SUP_CTRL.EN_LDO", 0, 1}
		});

		this.IO_CTRL = ral_reg_supply_registers_IO_CTRL::type_id::create("IO_CTRL",,get_full_name());
		if(this.IO_CTRL.has_coverage(UVM_CVR_REG_BITS))
			this.IO_CTRL.cg_bits.option.name = {get_name(), ".IO_CTRL_bits"};
		this.IO_CTRL.configure(get_block(), this, "");
		this.IO_CTRL.build();
		this.IO_CTRL.add_hdl_path('{
            '{"i_supply_registers.i_supply_registers_IO_CTRL.HICUR", 0, 1}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(TRIM_IREF, offset+`UVM_REG_ADDR_WIDTH'h3);
	  mp.add_reg(TRIM_OT, offset+`UVM_REG_ADDR_WIDTH'h4);
	  mp.add_reg(SUP_HW_CTRL, offset+`UVM_REG_ADDR_WIDTH'h3C);
	  mp.add_reg(SUP_IRQ_STAT, offset+`UVM_REG_ADDR_WIDTH'h3A);
	  mp.add_reg(SUP_IRQ_MASK, offset+`UVM_REG_ADDR_WIDTH'h3B);
	  mp.add_reg(SUP_STAT, offset+`UVM_REG_ADDR_WIDTH'h3D);
	  mp.add_reg(SUP_CTRL, offset+`UVM_REG_ADDR_WIDTH'h3E);
	  mp.add_reg(IO_CTRL, offset+`UVM_REG_ADDR_WIDTH'h3F);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  TRIM_IREF.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h3);
	  TRIM_OT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h4);
	  SUP_HW_CTRL.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h3C);
	  SUP_IRQ_STAT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h3A);
	  SUP_IRQ_MASK.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h3B);
	  SUP_STAT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h3D);
	  SUP_CTRL.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h3E);
	  IO_CTRL.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h3F);

	endfunction

	`uvm_object_utils(ral_regfile_supply_registers)
endclass : ral_regfile_supply_registers




class ral_block_supply extends uvm_reg_block;
	rand ral_regfile_supply_registers supply_registers;

	function new(string name = "supply");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 2, UVM_LITTLE_ENDIAN, 0);
      this.supply_registers = ral_regfile_supply_registers::type_id::create("supply_registers",,get_full_name());
      this.supply_registers.configure(this, null, "");
      this.supply_registers.build();
      this.supply_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_supply)

endclass : ral_block_supply


class ral_reg_time_base_registers_CLKREF_CONF extends uvm_reg;
	rand uvm_reg_field CLKREF_FREQ;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CLKREF_FREQ: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "time_base_registers_CLKREF_CONF");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CLKREF_FREQ = uvm_reg_field::type_id::create("CLKREF_FREQ",,get_full_name());
      this.CLKREF_FREQ.configure(this, 2, 0, "RW", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_time_base_registers_CLKREF_CONF)

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
endclass : ral_reg_time_base_registers_CLKREF_CONF


class ral_reg_time_base_registers_TB_CNT extends uvm_reg;
	uvm_reg_field CNT;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CNT: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "time_base_registers_TB_CNT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CNT = uvm_reg_field::type_id::create("CNT",,get_full_name());
      this.CNT.configure(this, 16, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_time_base_registers_TB_CNT)

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
endclass : ral_reg_time_base_registers_TB_CNT


class ral_reg_time_base_registers_TRIM_OSC extends uvm_reg;
	uvm_reg_field TRIM_OSC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TRIM_OSC: coverpoint {m_data[6:0], m_is_read} iff(m_be != 0) {
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
	endgroup
	function new(string name = "time_base_registers_TRIM_OSC");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TRIM_OSC = uvm_reg_field::type_id::create("TRIM_OSC",,get_full_name());
      this.TRIM_OSC.configure(this, 7, 0, "RO", 0, 32, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_time_base_registers_TRIM_OSC)

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
endclass : ral_reg_time_base_registers_TRIM_OSC


class ral_reg_time_base_registers_TRIM_OSC_TCF extends uvm_reg;
	uvm_reg_field TCF;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TCF: coverpoint {m_data[2:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "time_base_registers_TRIM_OSC_TCF");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TCF = uvm_reg_field::type_id::create("TCF",,get_full_name());
      this.TCF.configure(this, 3, 0, "RO", 0, 3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_time_base_registers_TRIM_OSC_TCF)

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
endclass : ral_reg_time_base_registers_TRIM_OSC_TCF


class ral_regfile_time_base_registers extends uvm_reg_file;

	rand ral_reg_time_base_registers_CLKREF_CONF CLKREF_CONF;
	rand ral_reg_time_base_registers_TB_CNT TB_CNT;
	rand ral_reg_time_base_registers_TRIM_OSC TRIM_OSC;
	rand ral_reg_time_base_registers_TRIM_OSC_TCF TRIM_OSC_TCF;


	function new(string name = "time_base_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.CLKREF_CONF = ral_reg_time_base_registers_CLKREF_CONF::type_id::create("CLKREF_CONF",,get_full_name());
		if(this.CLKREF_CONF.has_coverage(UVM_CVR_REG_BITS))
			this.CLKREF_CONF.cg_bits.option.name = {get_name(), ".CLKREF_CONF_bits"};
		this.CLKREF_CONF.configure(get_block(), this, "");
		this.CLKREF_CONF.build();
		this.CLKREF_CONF.add_hdl_path('{
            '{"i_time_base_registers.i_time_base_registers_CLKREF_CONF.CLKREF_FREQ", 0, 2}
		});

		this.TB_CNT = ral_reg_time_base_registers_TB_CNT::type_id::create("TB_CNT",,get_full_name());
		if(this.TB_CNT.has_coverage(UVM_CVR_REG_BITS))
			this.TB_CNT.cg_bits.option.name = {get_name(), ".TB_CNT_bits"};
		this.TB_CNT.configure(get_block(), this, "");
		this.TB_CNT.build();
		this.TB_CNT.add_hdl_path('{
            '{"i_time_base_registers.i_time_base_registers_TB_CNT.CNT", 0, 16}
		});

		this.TRIM_OSC = ral_reg_time_base_registers_TRIM_OSC::type_id::create("TRIM_OSC",,get_full_name());
		if(this.TRIM_OSC.has_coverage(UVM_CVR_REG_BITS))
			this.TRIM_OSC.cg_bits.option.name = {get_name(), ".TRIM_OSC_bits"};
		this.TRIM_OSC.configure(get_block(), this, "");
		this.TRIM_OSC.build();
		this.TRIM_OSC.add_hdl_path('{
            '{"i_time_base_registers.i_time_base_registers_TRIM_OSC.TRIM_OSC", 0, 7}
		});

		this.TRIM_OSC_TCF = ral_reg_time_base_registers_TRIM_OSC_TCF::type_id::create("TRIM_OSC_TCF",,get_full_name());
		if(this.TRIM_OSC_TCF.has_coverage(UVM_CVR_REG_BITS))
			this.TRIM_OSC_TCF.cg_bits.option.name = {get_name(), ".TRIM_OSC_TCF_bits"};
		this.TRIM_OSC_TCF.configure(get_block(), this, "");
		this.TRIM_OSC_TCF.build();
		this.TRIM_OSC_TCF.add_hdl_path('{
            '{"i_time_base_registers.i_time_base_registers_TRIM_OSC_TCF.TCF", 0, 3}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(CLKREF_CONF, offset+`UVM_REG_ADDR_WIDTH'h40);
	  mp.add_reg(TB_CNT, offset+`UVM_REG_ADDR_WIDTH'h41);
	  uvm_resource_db#(bit)::set({"REG::", TB_CNT.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(bit)::set({"REG::", TB_CNT.get_full_name()}, "NO_REG_HW_RESET_TEST", 1, this);
	  mp.add_reg(TRIM_OSC, offset+`UVM_REG_ADDR_WIDTH'h6);
	  mp.add_reg(TRIM_OSC_TCF, offset+`UVM_REG_ADDR_WIDTH'h7);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  CLKREF_CONF.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h40);
	  TB_CNT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h41);
	  TRIM_OSC.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h6);
	  TRIM_OSC_TCF.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h7);

	endfunction

	`uvm_object_utils(ral_regfile_time_base_registers)
endclass : ral_regfile_time_base_registers




class ral_block_timebase extends uvm_reg_block;
	rand ral_regfile_time_base_registers time_base_registers;

	function new(string name = "timebase");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 2, UVM_LITTLE_ENDIAN, 0);
      this.time_base_registers = ral_regfile_time_base_registers::type_id::create("time_base_registers",,get_full_name());
      this.time_base_registers.configure(this, null, "");
      this.time_base_registers.build();
      this.time_base_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_timebase)

endclass : ral_block_timebase


class ral_reg_Interrupt_Registers_IRQ_STAT extends uvm_reg;
	rand uvm_reg_field OTPFAIL;
	rand uvm_reg_field CLKREF;
	rand uvm_reg_field RESET;
	uvm_reg_field SPI;
	uvm_reg_field BUF;
	uvm_reg_field DSI;
	uvm_reg_field SUPPLY;
	uvm_reg_field ECC_FAIL;
	uvm_reg_field RESERVED;
	rand uvm_reg_field HW_FAIL;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OTPFAIL: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CLKREF: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RESET: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SPI: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   BUF: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   DSI: coverpoint {m_data[6:5], m_is_read} iff(m_be != 0) {
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
	   SUPPLY: coverpoint {m_data[9:9], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ECC_FAIL: coverpoint {m_data[10:10], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RESERVED: coverpoint {m_data[11:11], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   HW_FAIL: coverpoint {m_data[12:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "Interrupt_Registers_IRQ_STAT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OTPFAIL = uvm_reg_field::type_id::create("OTPFAIL",,get_full_name());
      this.OTPFAIL.configure(this, 1, 0, "W1C", 0, 0, 1, 0, 0);
      this.CLKREF = uvm_reg_field::type_id::create("CLKREF",,get_full_name());
      this.CLKREF.configure(this, 1, 1, "W1C", 0, 0, 1, 0, 0);
      this.RESET = uvm_reg_field::type_id::create("RESET",,get_full_name());
      this.RESET.configure(this, 1, 2, "W1C", 0, 1, 1, 0, 0);
      this.SPI = uvm_reg_field::type_id::create("SPI",,get_full_name());
      this.SPI.configure(this, 1, 3, "RO", 0, 0, 1, 0, 0);
      this.BUF = uvm_reg_field::type_id::create("BUF",,get_full_name());
      this.BUF.configure(this, 1, 4, "RO", 0, 0, 1, 0, 0);
      this.DSI = uvm_reg_field::type_id::create("DSI",,get_full_name());
      this.DSI.configure(this, 2, 5, "RO", 0, 0, 1, 0, 0);
      this.SUPPLY = uvm_reg_field::type_id::create("SUPPLY",,get_full_name());
      this.SUPPLY.configure(this, 1, 9, "RO", 0, 0, 1, 0, 0);
      this.ECC_FAIL = uvm_reg_field::type_id::create("ECC_FAIL",,get_full_name());
      this.ECC_FAIL.configure(this, 1, 10, "RO", 0, 0, 1, 0, 0);
      this.RESERVED = uvm_reg_field::type_id::create("RESERVED",,get_full_name());
      this.RESERVED.configure(this, 1, 11, "RO", 0, 0, 1, 0, 0);
      this.HW_FAIL = uvm_reg_field::type_id::create("HW_FAIL",,get_full_name());
      this.HW_FAIL.configure(this, 1, 12, "W1C", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_Interrupt_Registers_IRQ_STAT)

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
endclass : ral_reg_Interrupt_Registers_IRQ_STAT


class ral_reg_Interrupt_Registers_IRQ_MASK extends uvm_reg;
	rand uvm_reg_field OTPFAIL;
	rand uvm_reg_field CLKREF;
	rand uvm_reg_field RESET;
	rand uvm_reg_field SPI;
	rand uvm_reg_field BUF;
	rand uvm_reg_field DSI;
	rand uvm_reg_field SUPPLY;
	rand uvm_reg_field ECC_FAIL;
	rand uvm_reg_field RESERVED;
	rand uvm_reg_field HW_FAIL;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OTPFAIL: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CLKREF: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RESET: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SPI: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   BUF: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   DSI: coverpoint {m_data[6:5], m_is_read} iff(m_be != 0) {
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
	   SUPPLY: coverpoint {m_data[9:9], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ECC_FAIL: coverpoint {m_data[10:10], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RESERVED: coverpoint {m_data[11:11], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   HW_FAIL: coverpoint {m_data[12:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "Interrupt_Registers_IRQ_MASK");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OTPFAIL = uvm_reg_field::type_id::create("OTPFAIL",,get_full_name());
      this.OTPFAIL.configure(this, 1, 0, "RW", 0, 1, 1, 0, 0);
      this.CLKREF = uvm_reg_field::type_id::create("CLKREF",,get_full_name());
      this.CLKREF.configure(this, 1, 1, "RW", 0, 1, 1, 0, 0);
      this.RESET = uvm_reg_field::type_id::create("RESET",,get_full_name());
      this.RESET.configure(this, 1, 2, "RW", 0, 1, 1, 0, 0);
      this.SPI = uvm_reg_field::type_id::create("SPI",,get_full_name());
      this.SPI.configure(this, 1, 3, "RW", 0, 1, 1, 0, 0);
      this.BUF = uvm_reg_field::type_id::create("BUF",,get_full_name());
      this.BUF.configure(this, 1, 4, "RW", 0, 1, 1, 0, 0);
      this.DSI = uvm_reg_field::type_id::create("DSI",,get_full_name());
      this.DSI.configure(this, 2, 5, "RW", 0, 3, 1, 0, 0);
      this.SUPPLY = uvm_reg_field::type_id::create("SUPPLY",,get_full_name());
      this.SUPPLY.configure(this, 1, 9, "RW", 0, 1, 1, 0, 0);
      this.ECC_FAIL = uvm_reg_field::type_id::create("ECC_FAIL",,get_full_name());
      this.ECC_FAIL.configure(this, 1, 10, "RW", 0, 1, 1, 0, 0);
      this.RESERVED = uvm_reg_field::type_id::create("RESERVED",,get_full_name());
      this.RESERVED.configure(this, 1, 11, "RW", 0, 0, 1, 0, 0);
      this.HW_FAIL = uvm_reg_field::type_id::create("HW_FAIL",,get_full_name());
      this.HW_FAIL.configure(this, 1, 12, "RW", 0, 1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_Interrupt_Registers_IRQ_MASK)

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
endclass : ral_reg_Interrupt_Registers_IRQ_MASK


class ral_reg_Interrupt_Registers_ECC_IRQ_STAT extends uvm_reg;
	rand uvm_reg_field DSI_CRM_DATA_BUF;
	rand uvm_reg_field DSI_PDCM_DATA_BUF;
	rand uvm_reg_field DSI_CMD_BUF;
	rand uvm_reg_field DSI_TDMA;
	rand uvm_reg_field DSI_CMD;
	rand uvm_reg_field SPI_CMD_BUF;
	rand uvm_reg_field SPI_CMD;
	rand uvm_reg_field SPI_DATA;
	rand uvm_reg_field RAM;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DSI_CRM_DATA_BUF: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	   DSI_PDCM_DATA_BUF: coverpoint {m_data[3:2], m_is_read} iff(m_be != 0) {
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
	   DSI_CMD_BUF: coverpoint {m_data[5:4], m_is_read} iff(m_be != 0) {
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
	   DSI_TDMA: coverpoint {m_data[7:6], m_is_read} iff(m_be != 0) {
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
	   DSI_CMD: coverpoint {m_data[9:8], m_is_read} iff(m_be != 0) {
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
	   SPI_CMD_BUF: coverpoint {m_data[12:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SPI_CMD: coverpoint {m_data[13:13], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SPI_DATA: coverpoint {m_data[14:14], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RAM: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "Interrupt_Registers_ECC_IRQ_STAT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DSI_CRM_DATA_BUF = uvm_reg_field::type_id::create("DSI_CRM_DATA_BUF",,get_full_name());
      this.DSI_CRM_DATA_BUF.configure(this, 2, 0, "W1C", 0, 0, 1, 0, 0);
      this.DSI_PDCM_DATA_BUF = uvm_reg_field::type_id::create("DSI_PDCM_DATA_BUF",,get_full_name());
      this.DSI_PDCM_DATA_BUF.configure(this, 2, 2, "W1C", 0, 0, 1, 0, 0);
      this.DSI_CMD_BUF = uvm_reg_field::type_id::create("DSI_CMD_BUF",,get_full_name());
      this.DSI_CMD_BUF.configure(this, 2, 4, "W1C", 0, 0, 1, 0, 0);
      this.DSI_TDMA = uvm_reg_field::type_id::create("DSI_TDMA",,get_full_name());
      this.DSI_TDMA.configure(this, 2, 6, "W1C", 0, 0, 1, 0, 0);
      this.DSI_CMD = uvm_reg_field::type_id::create("DSI_CMD",,get_full_name());
      this.DSI_CMD.configure(this, 2, 8, "W1C", 0, 0, 1, 0, 0);
      this.SPI_CMD_BUF = uvm_reg_field::type_id::create("SPI_CMD_BUF",,get_full_name());
      this.SPI_CMD_BUF.configure(this, 1, 12, "W1C", 0, 0, 1, 0, 0);
      this.SPI_CMD = uvm_reg_field::type_id::create("SPI_CMD",,get_full_name());
      this.SPI_CMD.configure(this, 1, 13, "W1C", 0, 0, 1, 0, 0);
      this.SPI_DATA = uvm_reg_field::type_id::create("SPI_DATA",,get_full_name());
      this.SPI_DATA.configure(this, 1, 14, "W1C", 0, 0, 1, 0, 0);
      this.RAM = uvm_reg_field::type_id::create("RAM",,get_full_name());
      this.RAM.configure(this, 1, 15, "W1C", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_Interrupt_Registers_ECC_IRQ_STAT)

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
endclass : ral_reg_Interrupt_Registers_ECC_IRQ_STAT


class ral_reg_Interrupt_Registers_ECC_IRQ_MASK extends uvm_reg;
	rand uvm_reg_field DSI_CRM_DATA_BUF;
	rand uvm_reg_field DSI_PDCM_DATA_BUF;
	rand uvm_reg_field DSI_CMD_BUF;
	rand uvm_reg_field DSI_TDMA;
	rand uvm_reg_field DSI_CMD;
	rand uvm_reg_field SPI_CMD_BUF;
	rand uvm_reg_field SPI_CMD;
	rand uvm_reg_field SPI_DATA;
	rand uvm_reg_field RAM;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DSI_CRM_DATA_BUF: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	   DSI_PDCM_DATA_BUF: coverpoint {m_data[3:2], m_is_read} iff(m_be != 0) {
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
	   DSI_CMD_BUF: coverpoint {m_data[5:4], m_is_read} iff(m_be != 0) {
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
	   DSI_TDMA: coverpoint {m_data[7:6], m_is_read} iff(m_be != 0) {
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
	   DSI_CMD: coverpoint {m_data[9:8], m_is_read} iff(m_be != 0) {
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
	   SPI_CMD_BUF: coverpoint {m_data[12:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SPI_CMD: coverpoint {m_data[13:13], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SPI_DATA: coverpoint {m_data[14:14], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RAM: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "Interrupt_Registers_ECC_IRQ_MASK");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DSI_CRM_DATA_BUF = uvm_reg_field::type_id::create("DSI_CRM_DATA_BUF",,get_full_name());
      this.DSI_CRM_DATA_BUF.configure(this, 2, 0, "RW", 0, 3, 1, 0, 0);
      this.DSI_PDCM_DATA_BUF = uvm_reg_field::type_id::create("DSI_PDCM_DATA_BUF",,get_full_name());
      this.DSI_PDCM_DATA_BUF.configure(this, 2, 2, "RW", 0, 3, 1, 0, 0);
      this.DSI_CMD_BUF = uvm_reg_field::type_id::create("DSI_CMD_BUF",,get_full_name());
      this.DSI_CMD_BUF.configure(this, 2, 4, "RW", 0, 3, 1, 0, 0);
      this.DSI_TDMA = uvm_reg_field::type_id::create("DSI_TDMA",,get_full_name());
      this.DSI_TDMA.configure(this, 2, 6, "RW", 0, 3, 1, 0, 0);
      this.DSI_CMD = uvm_reg_field::type_id::create("DSI_CMD",,get_full_name());
      this.DSI_CMD.configure(this, 2, 8, "RW", 0, 3, 1, 0, 0);
      this.SPI_CMD_BUF = uvm_reg_field::type_id::create("SPI_CMD_BUF",,get_full_name());
      this.SPI_CMD_BUF.configure(this, 1, 12, "RW", 0, 1, 1, 0, 0);
      this.SPI_CMD = uvm_reg_field::type_id::create("SPI_CMD",,get_full_name());
      this.SPI_CMD.configure(this, 1, 13, "RW", 0, 1, 1, 0, 0);
      this.SPI_DATA = uvm_reg_field::type_id::create("SPI_DATA",,get_full_name());
      this.SPI_DATA.configure(this, 1, 14, "RW", 0, 1, 1, 0, 0);
      this.RAM = uvm_reg_field::type_id::create("RAM",,get_full_name());
      this.RAM.configure(this, 1, 15, "RW", 0, 1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_Interrupt_Registers_ECC_IRQ_MASK)

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
endclass : ral_reg_Interrupt_Registers_ECC_IRQ_MASK


class ral_reg_Interrupt_Registers_ECC_CORR_IRQ_STAT extends uvm_reg;
	rand uvm_reg_field DSI_CRM_DATA_BUF;
	rand uvm_reg_field DSI_PDCM_DATA_BUF;
	rand uvm_reg_field DSI_CMD_BUF;
	rand uvm_reg_field DSI_TDMA;
	rand uvm_reg_field DSI_CMD;
	rand uvm_reg_field SPI_CMD_BUF;
	rand uvm_reg_field SPI_CMD;
	rand uvm_reg_field SPI_DATA;
	rand uvm_reg_field RAM;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DSI_CRM_DATA_BUF: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	   DSI_PDCM_DATA_BUF: coverpoint {m_data[3:2], m_is_read} iff(m_be != 0) {
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
	   DSI_CMD_BUF: coverpoint {m_data[5:4], m_is_read} iff(m_be != 0) {
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
	   DSI_TDMA: coverpoint {m_data[7:6], m_is_read} iff(m_be != 0) {
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
	   DSI_CMD: coverpoint {m_data[9:8], m_is_read} iff(m_be != 0) {
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
	   SPI_CMD_BUF: coverpoint {m_data[12:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SPI_CMD: coverpoint {m_data[13:13], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SPI_DATA: coverpoint {m_data[14:14], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RAM: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "Interrupt_Registers_ECC_CORR_IRQ_STAT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DSI_CRM_DATA_BUF = uvm_reg_field::type_id::create("DSI_CRM_DATA_BUF",,get_full_name());
      this.DSI_CRM_DATA_BUF.configure(this, 2, 0, "W1C", 0, 0, 1, 0, 0);
      this.DSI_PDCM_DATA_BUF = uvm_reg_field::type_id::create("DSI_PDCM_DATA_BUF",,get_full_name());
      this.DSI_PDCM_DATA_BUF.configure(this, 2, 2, "W1C", 0, 0, 1, 0, 0);
      this.DSI_CMD_BUF = uvm_reg_field::type_id::create("DSI_CMD_BUF",,get_full_name());
      this.DSI_CMD_BUF.configure(this, 2, 4, "W1C", 0, 0, 1, 0, 0);
      this.DSI_TDMA = uvm_reg_field::type_id::create("DSI_TDMA",,get_full_name());
      this.DSI_TDMA.configure(this, 2, 6, "W1C", 0, 0, 1, 0, 0);
      this.DSI_CMD = uvm_reg_field::type_id::create("DSI_CMD",,get_full_name());
      this.DSI_CMD.configure(this, 2, 8, "W1C", 0, 0, 1, 0, 0);
      this.SPI_CMD_BUF = uvm_reg_field::type_id::create("SPI_CMD_BUF",,get_full_name());
      this.SPI_CMD_BUF.configure(this, 1, 12, "W1C", 0, 0, 1, 0, 0);
      this.SPI_CMD = uvm_reg_field::type_id::create("SPI_CMD",,get_full_name());
      this.SPI_CMD.configure(this, 1, 13, "W1C", 0, 0, 1, 0, 0);
      this.SPI_DATA = uvm_reg_field::type_id::create("SPI_DATA",,get_full_name());
      this.SPI_DATA.configure(this, 1, 14, "W1C", 0, 0, 1, 0, 0);
      this.RAM = uvm_reg_field::type_id::create("RAM",,get_full_name());
      this.RAM.configure(this, 1, 15, "W1C", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_Interrupt_Registers_ECC_CORR_IRQ_STAT)

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
endclass : ral_reg_Interrupt_Registers_ECC_CORR_IRQ_STAT


class ral_reg_Interrupt_Registers_ECC_CORR_IRQ_MASK extends uvm_reg;
	rand uvm_reg_field DSI_CRM_DATA_BUF;
	rand uvm_reg_field DSI_PDCM_DATA_BUF;
	rand uvm_reg_field DSI_CMD_BUF;
	rand uvm_reg_field DSI_TDMA;
	rand uvm_reg_field DSI_CMD;
	rand uvm_reg_field SPI_CMD_BUF;
	rand uvm_reg_field SPI_CMD;
	rand uvm_reg_field SPI_DATA;
	rand uvm_reg_field RAM;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DSI_CRM_DATA_BUF: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	   DSI_PDCM_DATA_BUF: coverpoint {m_data[3:2], m_is_read} iff(m_be != 0) {
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
	   DSI_CMD_BUF: coverpoint {m_data[5:4], m_is_read} iff(m_be != 0) {
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
	   DSI_TDMA: coverpoint {m_data[7:6], m_is_read} iff(m_be != 0) {
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
	   DSI_CMD: coverpoint {m_data[9:8], m_is_read} iff(m_be != 0) {
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
	   SPI_CMD_BUF: coverpoint {m_data[12:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SPI_CMD: coverpoint {m_data[13:13], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SPI_DATA: coverpoint {m_data[14:14], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RAM: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "Interrupt_Registers_ECC_CORR_IRQ_MASK");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DSI_CRM_DATA_BUF = uvm_reg_field::type_id::create("DSI_CRM_DATA_BUF",,get_full_name());
      this.DSI_CRM_DATA_BUF.configure(this, 2, 0, "RW", 0, 3, 1, 0, 0);
      this.DSI_PDCM_DATA_BUF = uvm_reg_field::type_id::create("DSI_PDCM_DATA_BUF",,get_full_name());
      this.DSI_PDCM_DATA_BUF.configure(this, 2, 2, "RW", 0, 3, 1, 0, 0);
      this.DSI_CMD_BUF = uvm_reg_field::type_id::create("DSI_CMD_BUF",,get_full_name());
      this.DSI_CMD_BUF.configure(this, 2, 4, "RW", 0, 3, 1, 0, 0);
      this.DSI_TDMA = uvm_reg_field::type_id::create("DSI_TDMA",,get_full_name());
      this.DSI_TDMA.configure(this, 2, 6, "RW", 0, 3, 1, 0, 0);
      this.DSI_CMD = uvm_reg_field::type_id::create("DSI_CMD",,get_full_name());
      this.DSI_CMD.configure(this, 2, 8, "RW", 0, 3, 1, 0, 0);
      this.SPI_CMD_BUF = uvm_reg_field::type_id::create("SPI_CMD_BUF",,get_full_name());
      this.SPI_CMD_BUF.configure(this, 1, 12, "RW", 0, 1, 1, 0, 0);
      this.SPI_CMD = uvm_reg_field::type_id::create("SPI_CMD",,get_full_name());
      this.SPI_CMD.configure(this, 1, 13, "RW", 0, 1, 1, 0, 0);
      this.SPI_DATA = uvm_reg_field::type_id::create("SPI_DATA",,get_full_name());
      this.SPI_DATA.configure(this, 1, 14, "RW", 0, 1, 1, 0, 0);
      this.RAM = uvm_reg_field::type_id::create("RAM",,get_full_name());
      this.RAM.configure(this, 1, 15, "RW", 0, 1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_Interrupt_Registers_ECC_CORR_IRQ_MASK)

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
endclass : ral_reg_Interrupt_Registers_ECC_CORR_IRQ_MASK


class ral_regfile_Interrupt_Registers extends uvm_reg_file;

	rand ral_reg_Interrupt_Registers_IRQ_STAT IRQ_STAT;
	rand ral_reg_Interrupt_Registers_IRQ_MASK IRQ_MASK;
	rand ral_reg_Interrupt_Registers_ECC_IRQ_STAT ECC_IRQ_STAT;
	rand ral_reg_Interrupt_Registers_ECC_IRQ_MASK ECC_IRQ_MASK;
	rand ral_reg_Interrupt_Registers_ECC_CORR_IRQ_STAT ECC_CORR_IRQ_STAT;
	rand ral_reg_Interrupt_Registers_ECC_CORR_IRQ_MASK ECC_CORR_IRQ_MASK;


	function new(string name = "Interrupt_Registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.IRQ_STAT = ral_reg_Interrupt_Registers_IRQ_STAT::type_id::create("IRQ_STAT",,get_full_name());
		if(this.IRQ_STAT.has_coverage(UVM_CVR_REG_BITS))
			this.IRQ_STAT.cg_bits.option.name = {get_name(), ".IRQ_STAT_bits"};
		this.IRQ_STAT.configure(get_block(), this, "");
		this.IRQ_STAT.build();
		this.IRQ_STAT.add_hdl_path('{
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_STAT.OTPFAIL", 0, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_STAT.CLKREF", 1, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_STAT.RESET", 2, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_STAT.SPI", 3, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_STAT.BUF", 4, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_STAT.DSI", 5, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_STAT.SUPPLY", 9, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_STAT.ECC_FAIL", 10, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_STAT.RESERVED", 11, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_STAT.HW_FAIL", 12, 1}
		});

		this.IRQ_MASK = ral_reg_Interrupt_Registers_IRQ_MASK::type_id::create("IRQ_MASK",,get_full_name());
		if(this.IRQ_MASK.has_coverage(UVM_CVR_REG_BITS))
			this.IRQ_MASK.cg_bits.option.name = {get_name(), ".IRQ_MASK_bits"};
		this.IRQ_MASK.configure(get_block(), this, "");
		this.IRQ_MASK.build();
		this.IRQ_MASK.add_hdl_path('{
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_MASK.OTPFAIL", 0, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_MASK.CLKREF", 1, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_MASK.RESET", 2, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_MASK.SPI", 3, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_MASK.BUF", 4, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_MASK.DSI", 5, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_MASK.SUPPLY", 9, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_MASK.ECC_FAIL", 10, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_MASK.RESERVED", 11, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_IRQ_MASK.HW_FAIL", 12, 1}
		});

		this.ECC_IRQ_STAT = ral_reg_Interrupt_Registers_ECC_IRQ_STAT::type_id::create("ECC_IRQ_STAT",,get_full_name());
		if(this.ECC_IRQ_STAT.has_coverage(UVM_CVR_REG_BITS))
			this.ECC_IRQ_STAT.cg_bits.option.name = {get_name(), ".ECC_IRQ_STAT_bits"};
		this.ECC_IRQ_STAT.configure(get_block(), this, "");
		this.ECC_IRQ_STAT.build();
		this.ECC_IRQ_STAT.add_hdl_path('{
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_STAT.DSI_CRM_DATA_BUF", 0, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_STAT.DSI_PDCM_DATA_BUF", 2, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD_BUF", 4, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_STAT.DSI_TDMA", 6, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_STAT.DSI_CMD", 8, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD_BUF", 12, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_STAT.SPI_CMD", 13, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_STAT.SPI_DATA", 14, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_STAT.RAM", 15, 1}
		});

		this.ECC_IRQ_MASK = ral_reg_Interrupt_Registers_ECC_IRQ_MASK::type_id::create("ECC_IRQ_MASK",,get_full_name());
		if(this.ECC_IRQ_MASK.has_coverage(UVM_CVR_REG_BITS))
			this.ECC_IRQ_MASK.cg_bits.option.name = {get_name(), ".ECC_IRQ_MASK_bits"};
		this.ECC_IRQ_MASK.configure(get_block(), this, "");
		this.ECC_IRQ_MASK.build();
		this.ECC_IRQ_MASK.add_hdl_path('{
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_MASK.DSI_CRM_DATA_BUF", 0, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_MASK.DSI_PDCM_DATA_BUF", 2, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_MASK.DSI_CMD_BUF", 4, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_MASK.DSI_TDMA", 6, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_MASK.DSI_CMD", 8, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_MASK.SPI_CMD_BUF", 12, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_MASK.SPI_CMD", 13, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_MASK.SPI_DATA", 14, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_IRQ_MASK.RAM", 15, 1}
		});

		this.ECC_CORR_IRQ_STAT = ral_reg_Interrupt_Registers_ECC_CORR_IRQ_STAT::type_id::create("ECC_CORR_IRQ_STAT",,get_full_name());
		if(this.ECC_CORR_IRQ_STAT.has_coverage(UVM_CVR_REG_BITS))
			this.ECC_CORR_IRQ_STAT.cg_bits.option.name = {get_name(), ".ECC_CORR_IRQ_STAT_bits"};
		this.ECC_CORR_IRQ_STAT.configure(get_block(), this, "");
		this.ECC_CORR_IRQ_STAT.build();
		this.ECC_CORR_IRQ_STAT.add_hdl_path('{
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CRM_DATA_BUF", 0, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_PDCM_DATA_BUF", 2, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD_BUF", 4, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_TDMA", 6, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_STAT.DSI_CMD", 8, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD_BUF", 12, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_CMD", 13, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_STAT.SPI_DATA", 14, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_STAT.RAM", 15, 1}
		});

		this.ECC_CORR_IRQ_MASK = ral_reg_Interrupt_Registers_ECC_CORR_IRQ_MASK::type_id::create("ECC_CORR_IRQ_MASK",,get_full_name());
		if(this.ECC_CORR_IRQ_MASK.has_coverage(UVM_CVR_REG_BITS))
			this.ECC_CORR_IRQ_MASK.cg_bits.option.name = {get_name(), ".ECC_CORR_IRQ_MASK_bits"};
		this.ECC_CORR_IRQ_MASK.configure(get_block(), this, "");
		this.ECC_CORR_IRQ_MASK.build();
		this.ECC_CORR_IRQ_MASK.add_hdl_path('{
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_MASK.DSI_CRM_DATA_BUF", 0, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_MASK.DSI_PDCM_DATA_BUF", 2, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_MASK.DSI_CMD_BUF", 4, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_MASK.DSI_TDMA", 6, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_MASK.DSI_CMD", 8, 2},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_MASK.SPI_CMD_BUF", 12, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_MASK.SPI_CMD", 13, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_MASK.SPI_DATA", 14, 1},
            '{"i_Interrupt_Registers.i_Interrupt_Registers_ECC_CORR_IRQ_MASK.RAM", 15, 1}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(IRQ_STAT, offset+`UVM_REG_ADDR_WIDTH'h50);
	  mp.add_reg(IRQ_MASK, offset+`UVM_REG_ADDR_WIDTH'h51);
	  mp.add_reg(ECC_IRQ_STAT, offset+`UVM_REG_ADDR_WIDTH'h52);
	  mp.add_reg(ECC_IRQ_MASK, offset+`UVM_REG_ADDR_WIDTH'h53);
	  mp.add_reg(ECC_CORR_IRQ_STAT, offset+`UVM_REG_ADDR_WIDTH'h54);
	  mp.add_reg(ECC_CORR_IRQ_MASK, offset+`UVM_REG_ADDR_WIDTH'h55);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  IRQ_STAT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h50);
	  IRQ_MASK.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h51);
	  ECC_IRQ_STAT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h52);
	  ECC_IRQ_MASK.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h53);
	  ECC_CORR_IRQ_STAT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h54);
	  ECC_CORR_IRQ_MASK.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h55);

	endfunction

	`uvm_object_utils(ral_regfile_Interrupt_Registers)
endclass : ral_regfile_Interrupt_Registers




class ral_block_interrupt extends uvm_reg_block;
	rand ral_regfile_Interrupt_Registers Interrupt_Registers;

	function new(string name = "interrupt");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 2, UVM_LITTLE_ENDIAN, 0);
      this.Interrupt_Registers = ral_regfile_Interrupt_Registers::type_id::create("Interrupt_Registers",,get_full_name());
      this.Interrupt_Registers.configure(this, null, "");
      this.Interrupt_Registers.build();
      this.Interrupt_Registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_interrupt)

endclass : ral_block_interrupt


class ral_reg_buffer_interrupt_registers_BUF_IRQ_STAT extends uvm_reg;
	rand uvm_reg_field DSI_CRM_FE;
	rand uvm_reg_field DSI_PDCM_FE;
	rand uvm_reg_field DSI_CMD_FE;
	rand uvm_reg_field SPI_CMD_FE;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DSI_CRM_FE: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	   DSI_PDCM_FE: coverpoint {m_data[3:2], m_is_read} iff(m_be != 0) {
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
	   DSI_CMD_FE: coverpoint {m_data[5:4], m_is_read} iff(m_be != 0) {
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
	   SPI_CMD_FE: coverpoint {m_data[6:6], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "buffer_interrupt_registers_BUF_IRQ_STAT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DSI_CRM_FE = uvm_reg_field::type_id::create("DSI_CRM_FE",,get_full_name());
      this.DSI_CRM_FE.configure(this, 2, 0, "W1C", 0, 0, 1, 0, 0);
      this.DSI_PDCM_FE = uvm_reg_field::type_id::create("DSI_PDCM_FE",,get_full_name());
      this.DSI_PDCM_FE.configure(this, 2, 2, "W1C", 0, 0, 1, 0, 0);
      this.DSI_CMD_FE = uvm_reg_field::type_id::create("DSI_CMD_FE",,get_full_name());
      this.DSI_CMD_FE.configure(this, 2, 4, "W1C", 0, 0, 1, 0, 0);
      this.SPI_CMD_FE = uvm_reg_field::type_id::create("SPI_CMD_FE",,get_full_name());
      this.SPI_CMD_FE.configure(this, 1, 6, "W1C", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_buffer_interrupt_registers_BUF_IRQ_STAT)

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
endclass : ral_reg_buffer_interrupt_registers_BUF_IRQ_STAT


class ral_reg_buffer_interrupt_registers_BUF_IRQ_MASK extends uvm_reg;
	rand uvm_reg_field DSI_CRM_FE;
	rand uvm_reg_field DSI_PDCM_FE;
	rand uvm_reg_field DSI_CMD_FE;
	rand uvm_reg_field SPI_CMD_FE;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DSI_CRM_FE: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	   DSI_PDCM_FE: coverpoint {m_data[3:2], m_is_read} iff(m_be != 0) {
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
	   DSI_CMD_FE: coverpoint {m_data[5:4], m_is_read} iff(m_be != 0) {
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
	   SPI_CMD_FE: coverpoint {m_data[6:6], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "buffer_interrupt_registers_BUF_IRQ_MASK");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DSI_CRM_FE = uvm_reg_field::type_id::create("DSI_CRM_FE",,get_full_name());
      this.DSI_CRM_FE.configure(this, 2, 0, "RW", 0, 3, 1, 0, 0);
      this.DSI_PDCM_FE = uvm_reg_field::type_id::create("DSI_PDCM_FE",,get_full_name());
      this.DSI_PDCM_FE.configure(this, 2, 2, "RW", 0, 3, 1, 0, 0);
      this.DSI_CMD_FE = uvm_reg_field::type_id::create("DSI_CMD_FE",,get_full_name());
      this.DSI_CMD_FE.configure(this, 2, 4, "RW", 0, 3, 1, 0, 0);
      this.SPI_CMD_FE = uvm_reg_field::type_id::create("SPI_CMD_FE",,get_full_name());
      this.SPI_CMD_FE.configure(this, 1, 6, "RW", 0, 1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_buffer_interrupt_registers_BUF_IRQ_MASK)

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
endclass : ral_reg_buffer_interrupt_registers_BUF_IRQ_MASK


class ral_reg_buffer_interrupt_registers_BUF_FILL_WARN extends uvm_reg;
	uvm_reg_field DSI_CRM_FW;
	uvm_reg_field DSI_PDCM_FW;
	uvm_reg_field DSI_CMD_FW;
	uvm_reg_field SPI_CMD_FW;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DSI_CRM_FW: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	   DSI_PDCM_FW: coverpoint {m_data[3:2], m_is_read} iff(m_be != 0) {
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
	   DSI_CMD_FW: coverpoint {m_data[5:4], m_is_read} iff(m_be != 0) {
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
	   SPI_CMD_FW: coverpoint {m_data[6:6], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "buffer_interrupt_registers_BUF_FILL_WARN");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DSI_CRM_FW = uvm_reg_field::type_id::create("DSI_CRM_FW",,get_full_name());
      this.DSI_CRM_FW.configure(this, 2, 0, "RO", 0, 0, 1, 0, 0);
      this.DSI_PDCM_FW = uvm_reg_field::type_id::create("DSI_PDCM_FW",,get_full_name());
      this.DSI_PDCM_FW.configure(this, 2, 2, "RO", 0, 0, 1, 0, 0);
      this.DSI_CMD_FW = uvm_reg_field::type_id::create("DSI_CMD_FW",,get_full_name());
      this.DSI_CMD_FW.configure(this, 2, 4, "RO", 0, 0, 1, 0, 0);
      this.SPI_CMD_FW = uvm_reg_field::type_id::create("SPI_CMD_FW",,get_full_name());
      this.SPI_CMD_FW.configure(this, 1, 6, "RO", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_buffer_interrupt_registers_BUF_FILL_WARN)

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
endclass : ral_reg_buffer_interrupt_registers_BUF_FILL_WARN


class ral_regfile_buffer_interrupt_registers extends uvm_reg_file;

	rand ral_reg_buffer_interrupt_registers_BUF_IRQ_STAT BUF_IRQ_STAT;
	rand ral_reg_buffer_interrupt_registers_BUF_IRQ_MASK BUF_IRQ_MASK;
	rand ral_reg_buffer_interrupt_registers_BUF_FILL_WARN BUF_FILL_WARN;


	function new(string name = "buffer_interrupt_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.BUF_IRQ_STAT = ral_reg_buffer_interrupt_registers_BUF_IRQ_STAT::type_id::create("BUF_IRQ_STAT",,get_full_name());
		if(this.BUF_IRQ_STAT.has_coverage(UVM_CVR_REG_BITS))
			this.BUF_IRQ_STAT.cg_bits.option.name = {get_name(), ".BUF_IRQ_STAT_bits"};
		this.BUF_IRQ_STAT.configure(get_block(), this, "");
		this.BUF_IRQ_STAT.build();
		this.BUF_IRQ_STAT.add_hdl_path('{
            '{"i_buffer_interrupt_registers.i_buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CRM_FE", 0, 2},
            '{"i_buffer_interrupt_registers.i_buffer_interrupt_registers_BUF_IRQ_STAT.DSI_PDCM_FE", 2, 2},
            '{"i_buffer_interrupt_registers.i_buffer_interrupt_registers_BUF_IRQ_STAT.DSI_CMD_FE", 4, 2},
            '{"i_buffer_interrupt_registers.i_buffer_interrupt_registers_BUF_IRQ_STAT.SPI_CMD_FE", 6, 1}
		});

		this.BUF_IRQ_MASK = ral_reg_buffer_interrupt_registers_BUF_IRQ_MASK::type_id::create("BUF_IRQ_MASK",,get_full_name());
		if(this.BUF_IRQ_MASK.has_coverage(UVM_CVR_REG_BITS))
			this.BUF_IRQ_MASK.cg_bits.option.name = {get_name(), ".BUF_IRQ_MASK_bits"};
		this.BUF_IRQ_MASK.configure(get_block(), this, "");
		this.BUF_IRQ_MASK.build();
		this.BUF_IRQ_MASK.add_hdl_path('{
            '{"i_buffer_interrupt_registers.i_buffer_interrupt_registers_BUF_IRQ_MASK.DSI_CRM_FE", 0, 2},
            '{"i_buffer_interrupt_registers.i_buffer_interrupt_registers_BUF_IRQ_MASK.DSI_PDCM_FE", 2, 2},
            '{"i_buffer_interrupt_registers.i_buffer_interrupt_registers_BUF_IRQ_MASK.DSI_CMD_FE", 4, 2},
            '{"i_buffer_interrupt_registers.i_buffer_interrupt_registers_BUF_IRQ_MASK.SPI_CMD_FE", 6, 1}
		});

		this.BUF_FILL_WARN = ral_reg_buffer_interrupt_registers_BUF_FILL_WARN::type_id::create("BUF_FILL_WARN",,get_full_name());
		if(this.BUF_FILL_WARN.has_coverage(UVM_CVR_REG_BITS))
			this.BUF_FILL_WARN.cg_bits.option.name = {get_name(), ".BUF_FILL_WARN_bits"};
		this.BUF_FILL_WARN.configure(get_block(), this, "");
		this.BUF_FILL_WARN.build();
		this.BUF_FILL_WARN.add_hdl_path('{
            '{"i_buffer_interrupt_registers.i_buffer_interrupt_registers_BUF_FILL_WARN.DSI_CRM_FW", 0, 2},
            '{"i_buffer_interrupt_registers.i_buffer_interrupt_registers_BUF_FILL_WARN.DSI_PDCM_FW", 2, 2},
            '{"i_buffer_interrupt_registers.i_buffer_interrupt_registers_BUF_FILL_WARN.DSI_CMD_FW", 4, 2},
            '{"i_buffer_interrupt_registers.i_buffer_interrupt_registers_BUF_FILL_WARN.SPI_CMD_FW", 6, 1}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(BUF_IRQ_STAT, offset+`UVM_REG_ADDR_WIDTH'h61);
	  mp.add_reg(BUF_IRQ_MASK, offset+`UVM_REG_ADDR_WIDTH'h62);
	  mp.add_reg(BUF_FILL_WARN, offset+`UVM_REG_ADDR_WIDTH'h63);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  BUF_IRQ_STAT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h61);
	  BUF_IRQ_MASK.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h62);
	  BUF_FILL_WARN.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h63);

	endfunction

	`uvm_object_utils(ral_regfile_buffer_interrupt_registers)
endclass : ral_regfile_buffer_interrupt_registers




class ral_block_ring_buffer_interrupt extends uvm_reg_block;
	rand ral_regfile_buffer_interrupt_registers buffer_interrupt_registers;

	function new(string name = "ring_buffer_interrupt");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 2, UVM_LITTLE_ENDIAN, 0);
      this.buffer_interrupt_registers = ral_regfile_buffer_interrupt_registers::type_id::create("buffer_interrupt_registers",,get_full_name());
      this.buffer_interrupt_registers.configure(this, null, "");
      this.buffer_interrupt_registers.build();
      this.buffer_interrupt_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_ring_buffer_interrupt)

endclass : ral_block_ring_buffer_interrupt


class ral_reg_SPI_registers_SPI_IRQ_STAT extends uvm_reg;
	rand uvm_reg_field CMD_INC;
	rand uvm_reg_field CRC_ERR;
	rand uvm_reg_field ALI_ERR;
	rand uvm_reg_field HW_FAIL;
	rand uvm_reg_field CMD_IGN;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CMD_INC: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CRC_ERR: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ALI_ERR: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   HW_FAIL: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CMD_IGN: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "SPI_registers_SPI_IRQ_STAT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CMD_INC = uvm_reg_field::type_id::create("CMD_INC",,get_full_name());
      this.CMD_INC.configure(this, 1, 0, "W1C", 0, 0, 1, 0, 0);
      this.CRC_ERR = uvm_reg_field::type_id::create("CRC_ERR",,get_full_name());
      this.CRC_ERR.configure(this, 1, 1, "W1C", 0, 0, 1, 0, 0);
      this.ALI_ERR = uvm_reg_field::type_id::create("ALI_ERR",,get_full_name());
      this.ALI_ERR.configure(this, 1, 2, "W1C", 0, 0, 1, 0, 0);
      this.HW_FAIL = uvm_reg_field::type_id::create("HW_FAIL",,get_full_name());
      this.HW_FAIL.configure(this, 1, 3, "W1C", 0, 0, 1, 0, 0);
      this.CMD_IGN = uvm_reg_field::type_id::create("CMD_IGN",,get_full_name());
      this.CMD_IGN.configure(this, 1, 4, "W1C", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_SPI_registers_SPI_IRQ_STAT)

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
endclass : ral_reg_SPI_registers_SPI_IRQ_STAT


class ral_reg_SPI_registers_SPI_IRQ_MASK extends uvm_reg;
	rand uvm_reg_field CMD_INC;
	rand uvm_reg_field CRC_ERR;
	rand uvm_reg_field ALI_ERR;
	rand uvm_reg_field HW_FAIL;
	rand uvm_reg_field CMD_IGN;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CMD_INC: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CRC_ERR: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ALI_ERR: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   HW_FAIL: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CMD_IGN: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "SPI_registers_SPI_IRQ_MASK");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CMD_INC = uvm_reg_field::type_id::create("CMD_INC",,get_full_name());
      this.CMD_INC.configure(this, 1, 0, "RW", 0, 1, 1, 0, 0);
      this.CRC_ERR = uvm_reg_field::type_id::create("CRC_ERR",,get_full_name());
      this.CRC_ERR.configure(this, 1, 1, "RW", 0, 1, 1, 0, 0);
      this.ALI_ERR = uvm_reg_field::type_id::create("ALI_ERR",,get_full_name());
      this.ALI_ERR.configure(this, 1, 2, "RW", 0, 1, 1, 0, 0);
      this.HW_FAIL = uvm_reg_field::type_id::create("HW_FAIL",,get_full_name());
      this.HW_FAIL.configure(this, 1, 3, "RW", 0, 1, 1, 0, 0);
      this.CMD_IGN = uvm_reg_field::type_id::create("CMD_IGN",,get_full_name());
      this.CMD_IGN.configure(this, 1, 4, "RW", 0, 1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_SPI_registers_SPI_IRQ_MASK)

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
endclass : ral_reg_SPI_registers_SPI_IRQ_MASK


class ral_reg_SPI_registers_STATUS_WORD extends uvm_reg;
	uvm_reg_field CR;
	uvm_reg_field PD;
	uvm_reg_field NT;
	uvm_reg_field CRC;
	uvm_reg_field SCE;
	uvm_reg_field BF;
	uvm_reg_field HE;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CR: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	   PD: coverpoint {m_data[3:2], m_is_read} iff(m_be != 0) {
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
	   NT: coverpoint {m_data[11:10], m_is_read} iff(m_be != 0) {
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
	   CRC: coverpoint {m_data[12:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SCE: coverpoint {m_data[13:13], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   BF: coverpoint {m_data[14:14], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   HE: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "SPI_registers_STATUS_WORD");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CR = uvm_reg_field::type_id::create("CR",,get_full_name());
      this.CR.configure(this, 2, 0, "RO", 0, 0, 1, 0, 0);
      this.PD = uvm_reg_field::type_id::create("PD",,get_full_name());
      this.PD.configure(this, 2, 2, "RO", 0, 0, 1, 0, 0);
      this.NT = uvm_reg_field::type_id::create("NT",,get_full_name());
      this.NT.configure(this, 2, 10, "RO", 0, 3, 1, 0, 0);
      this.CRC = uvm_reg_field::type_id::create("CRC",,get_full_name());
      this.CRC.configure(this, 1, 12, "RO", 0, 0, 1, 0, 0);
      this.SCE = uvm_reg_field::type_id::create("SCE",,get_full_name());
      this.SCE.configure(this, 1, 13, "RO", 0, 0, 1, 0, 0);
      this.BF = uvm_reg_field::type_id::create("BF",,get_full_name());
      this.BF.configure(this, 1, 14, "RO", 0, 0, 1, 0, 0);
      this.HE = uvm_reg_field::type_id::create("HE",,get_full_name());
      this.HE.configure(this, 1, 15, "RO", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_SPI_registers_STATUS_WORD)

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
endclass : ral_reg_SPI_registers_STATUS_WORD


class ral_regfile_SPI_registers extends uvm_reg_file;

	rand ral_reg_SPI_registers_SPI_IRQ_STAT SPI_IRQ_STAT;
	rand ral_reg_SPI_registers_SPI_IRQ_MASK SPI_IRQ_MASK;
	rand ral_reg_SPI_registers_STATUS_WORD STATUS_WORD;


	function new(string name = "SPI_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.SPI_IRQ_STAT = ral_reg_SPI_registers_SPI_IRQ_STAT::type_id::create("SPI_IRQ_STAT",,get_full_name());
		if(this.SPI_IRQ_STAT.has_coverage(UVM_CVR_REG_BITS))
			this.SPI_IRQ_STAT.cg_bits.option.name = {get_name(), ".SPI_IRQ_STAT_bits"};
		this.SPI_IRQ_STAT.configure(get_block(), this, "");
		this.SPI_IRQ_STAT.build();
		this.SPI_IRQ_STAT.add_hdl_path('{
            '{"i_SPI_registers.i_SPI_registers_SPI_IRQ_STAT.CMD_INC", 0, 1},
            '{"i_SPI_registers.i_SPI_registers_SPI_IRQ_STAT.CRC_ERR", 1, 1},
            '{"i_SPI_registers.i_SPI_registers_SPI_IRQ_STAT.ALI_ERR", 2, 1},
            '{"i_SPI_registers.i_SPI_registers_SPI_IRQ_STAT.HW_FAIL", 3, 1},
            '{"i_SPI_registers.i_SPI_registers_SPI_IRQ_STAT.CMD_IGN", 4, 1}
		});

		this.SPI_IRQ_MASK = ral_reg_SPI_registers_SPI_IRQ_MASK::type_id::create("SPI_IRQ_MASK",,get_full_name());
		if(this.SPI_IRQ_MASK.has_coverage(UVM_CVR_REG_BITS))
			this.SPI_IRQ_MASK.cg_bits.option.name = {get_name(), ".SPI_IRQ_MASK_bits"};
		this.SPI_IRQ_MASK.configure(get_block(), this, "");
		this.SPI_IRQ_MASK.build();
		this.SPI_IRQ_MASK.add_hdl_path('{
            '{"i_SPI_registers.i_SPI_registers_SPI_IRQ_MASK.CMD_INC", 0, 1},
            '{"i_SPI_registers.i_SPI_registers_SPI_IRQ_MASK.CRC_ERR", 1, 1},
            '{"i_SPI_registers.i_SPI_registers_SPI_IRQ_MASK.ALI_ERR", 2, 1},
            '{"i_SPI_registers.i_SPI_registers_SPI_IRQ_MASK.HW_FAIL", 3, 1},
            '{"i_SPI_registers.i_SPI_registers_SPI_IRQ_MASK.CMD_IGN", 4, 1}
		});

		this.STATUS_WORD = ral_reg_SPI_registers_STATUS_WORD::type_id::create("STATUS_WORD",,get_full_name());
		if(this.STATUS_WORD.has_coverage(UVM_CVR_REG_BITS))
			this.STATUS_WORD.cg_bits.option.name = {get_name(), ".STATUS_WORD_bits"};
		this.STATUS_WORD.configure(get_block(), this, "");
		this.STATUS_WORD.build();
		this.STATUS_WORD.add_hdl_path('{
            '{"i_SPI_registers.i_SPI_registers_STATUS_WORD.CR", 0, 2},
            '{"i_SPI_registers.i_SPI_registers_STATUS_WORD.PD", 2, 2},
            '{"i_SPI_registers.i_SPI_registers_STATUS_WORD.NT", 10, 2},
            '{"i_SPI_registers.i_SPI_registers_STATUS_WORD.CRC", 12, 1},
            '{"i_SPI_registers.i_SPI_registers_STATUS_WORD.SCE", 13, 1},
            '{"i_SPI_registers.i_SPI_registers_STATUS_WORD.BF", 14, 1},
            '{"i_SPI_registers.i_SPI_registers_STATUS_WORD.HE", 15, 1}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(SPI_IRQ_STAT, offset+`UVM_REG_ADDR_WIDTH'h80);
	  mp.add_reg(SPI_IRQ_MASK, offset+`UVM_REG_ADDR_WIDTH'h81);
	  mp.add_reg(STATUS_WORD, offset+`UVM_REG_ADDR_WIDTH'h85);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  SPI_IRQ_STAT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h80);
	  SPI_IRQ_MASK.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h81);
	  STATUS_WORD.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h85);

	endfunction

	`uvm_object_utils(ral_regfile_SPI_registers)
endclass : ral_regfile_SPI_registers




class ral_block_spi extends uvm_reg_block;
	rand ral_regfile_SPI_registers SPI_registers;

	function new(string name = "spi");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 2, UVM_LITTLE_ENDIAN, 0);
      this.SPI_registers = ral_regfile_SPI_registers::type_id::create("SPI_registers",,get_full_name());
      this.SPI_registers.configure(this, null, "");
      this.SPI_registers.build();
      this.SPI_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_spi)

endclass : ral_block_spi


class ral_reg_common_DSI3_block_registers_DSI_ENABLE extends uvm_reg;
	rand uvm_reg_field TRE;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TRE: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "common_DSI3_block_registers_DSI_ENABLE");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TRE = uvm_reg_field::type_id::create("TRE",,get_full_name());
      this.TRE.configure(this, 2, 0, "RW", 0, 3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_common_DSI3_block_registers_DSI_ENABLE)

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
endclass : ral_reg_common_DSI3_block_registers_DSI_ENABLE


class ral_reg_common_DSI3_block_registers_DSI_CFG extends uvm_reg;
	rand uvm_reg_field CHIPTIME;
	rand uvm_reg_field BITTIME;
	rand uvm_reg_field CRC_EN;
	rand uvm_reg_field SYNC_PDCM;
	rand uvm_reg_field SYNC_MASTER;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CHIPTIME: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	   BITTIME: coverpoint {m_data[3:2], m_is_read} iff(m_be != 0) {
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
	   CRC_EN: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SYNC_PDCM: coverpoint {m_data[5:5], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SYNC_MASTER: coverpoint {m_data[6:6], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "common_DSI3_block_registers_DSI_CFG");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CHIPTIME = uvm_reg_field::type_id::create("CHIPTIME",,get_full_name());
      this.CHIPTIME.configure(this, 2, 0, "RW", 0, 1, 1, 0, 0);
      this.BITTIME = uvm_reg_field::type_id::create("BITTIME",,get_full_name());
      this.BITTIME.configure(this, 2, 2, "RW", 0, 0, 1, 0, 0);
      this.CRC_EN = uvm_reg_field::type_id::create("CRC_EN",,get_full_name());
      this.CRC_EN.configure(this, 1, 4, "RW", 0, 1, 1, 0, 0);
      this.SYNC_PDCM = uvm_reg_field::type_id::create("SYNC_PDCM",,get_full_name());
      this.SYNC_PDCM.configure(this, 1, 5, "RW", 0, 1, 1, 0, 0);
      this.SYNC_MASTER = uvm_reg_field::type_id::create("SYNC_MASTER",,get_full_name());
      this.SYNC_MASTER.configure(this, 1, 6, "RW", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_common_DSI3_block_registers_DSI_CFG)

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
endclass : ral_reg_common_DSI3_block_registers_DSI_CFG


class ral_reg_common_DSI3_block_registers_DSI_TX_SHIFT extends uvm_reg;
	rand uvm_reg_field SHIFT;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   SHIFT: coverpoint {m_data[6:0], m_is_read} iff(m_be != 0) {
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
	endgroup
	function new(string name = "common_DSI3_block_registers_DSI_TX_SHIFT");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.SHIFT = uvm_reg_field::type_id::create("SHIFT",,get_full_name());
      this.SHIFT.configure(this, 7, 0, "RW", 0, 36, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_common_DSI3_block_registers_DSI_TX_SHIFT)

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
endclass : ral_reg_common_DSI3_block_registers_DSI_TX_SHIFT


class ral_reg_common_DSI3_block_registers_SYNC_IDLE_REG extends uvm_reg;
	uvm_reg_field DSI;
	uvm_reg_field PIN;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DSI: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	   PIN: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "common_DSI3_block_registers_SYNC_IDLE_REG");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DSI = uvm_reg_field::type_id::create("DSI",,get_full_name());
      this.DSI.configure(this, 2, 0, "RO", 0, 0, 1, 0, 1);
      this.PIN = uvm_reg_field::type_id::create("PIN",,get_full_name());
      this.PIN.configure(this, 1, 15, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_common_DSI3_block_registers_SYNC_IDLE_REG)

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
endclass : ral_reg_common_DSI3_block_registers_SYNC_IDLE_REG


class ral_reg_common_DSI3_block_registers_CRM_TIME extends uvm_reg;
	rand uvm_reg_field TIME;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TIME: coverpoint {m_data[10:0], m_is_read} iff(m_be != 0) {
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
	endgroup
	function new(string name = "common_DSI3_block_registers_CRM_TIME");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TIME = uvm_reg_field::type_id::create("TIME",,get_full_name());
      this.TIME.configure(this, 11, 0, "RW", 0, 450, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_common_DSI3_block_registers_CRM_TIME)

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
endclass : ral_reg_common_DSI3_block_registers_CRM_TIME


class ral_reg_common_DSI3_block_registers_CRM_TIME_NR extends uvm_reg;
	rand uvm_reg_field TIME;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TIME: coverpoint {m_data[10:0], m_is_read} iff(m_be != 0) {
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
	endgroup
	function new(string name = "common_DSI3_block_registers_CRM_TIME_NR");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TIME = uvm_reg_field::type_id::create("TIME",,get_full_name());
      this.TIME.configure(this, 11, 0, "RW", 0, 300, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_common_DSI3_block_registers_CRM_TIME_NR)

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
endclass : ral_reg_common_DSI3_block_registers_CRM_TIME_NR


class ral_regfile_common_DSI3_block_registers extends uvm_reg_file;

	rand ral_reg_common_DSI3_block_registers_DSI_ENABLE DSI_ENABLE;
	rand ral_reg_common_DSI3_block_registers_DSI_CFG DSI_CFG;
	rand ral_reg_common_DSI3_block_registers_DSI_TX_SHIFT DSI_TX_SHIFT;
	rand ral_reg_common_DSI3_block_registers_SYNC_IDLE_REG SYNC_IDLE_REG;
	rand ral_reg_common_DSI3_block_registers_CRM_TIME CRM_TIME;
	rand ral_reg_common_DSI3_block_registers_CRM_TIME_NR CRM_TIME_NR;


	function new(string name = "common_DSI3_block_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.DSI_ENABLE = ral_reg_common_DSI3_block_registers_DSI_ENABLE::type_id::create("DSI_ENABLE",,get_full_name());
		if(this.DSI_ENABLE.has_coverage(UVM_CVR_REG_BITS))
			this.DSI_ENABLE.cg_bits.option.name = {get_name(), ".DSI_ENABLE_bits"};
		this.DSI_ENABLE.configure(get_block(), this, "");
		this.DSI_ENABLE.build();
		this.DSI_ENABLE.add_hdl_path('{
            '{"i_common_DSI3_block_registers.i_common_DSI3_block_registers_DSI_ENABLE.TRE", 0, 2}
		});

		this.DSI_CFG = ral_reg_common_DSI3_block_registers_DSI_CFG::type_id::create("DSI_CFG",,get_full_name());
		if(this.DSI_CFG.has_coverage(UVM_CVR_REG_BITS))
			this.DSI_CFG.cg_bits.option.name = {get_name(), ".DSI_CFG_bits"};
		this.DSI_CFG.configure(get_block(), this, "");
		this.DSI_CFG.build();
		this.DSI_CFG.add_hdl_path('{
            '{"i_common_DSI3_block_registers.i_common_DSI3_block_registers_DSI_CFG.CHIPTIME", 0, 2},
            '{"i_common_DSI3_block_registers.i_common_DSI3_block_registers_DSI_CFG.BITTIME", 2, 2},
            '{"i_common_DSI3_block_registers.i_common_DSI3_block_registers_DSI_CFG.CRC_EN", 4, 1},
            '{"i_common_DSI3_block_registers.i_common_DSI3_block_registers_DSI_CFG.SYNC_PDCM", 5, 1},
            '{"i_common_DSI3_block_registers.i_common_DSI3_block_registers_DSI_CFG.SYNC_MASTER", 6, 1}
		});

		this.DSI_TX_SHIFT = ral_reg_common_DSI3_block_registers_DSI_TX_SHIFT::type_id::create("DSI_TX_SHIFT",,get_full_name());
		if(this.DSI_TX_SHIFT.has_coverage(UVM_CVR_REG_BITS))
			this.DSI_TX_SHIFT.cg_bits.option.name = {get_name(), ".DSI_TX_SHIFT_bits"};
		this.DSI_TX_SHIFT.configure(get_block(), this, "");
		this.DSI_TX_SHIFT.build();
		this.DSI_TX_SHIFT.add_hdl_path('{
            '{"i_common_DSI3_block_registers.i_common_DSI3_block_registers_DSI_TX_SHIFT.SHIFT", 0, 7}
		});

		this.SYNC_IDLE_REG = ral_reg_common_DSI3_block_registers_SYNC_IDLE_REG::type_id::create("SYNC_IDLE_REG",,get_full_name());
		if(this.SYNC_IDLE_REG.has_coverage(UVM_CVR_REG_BITS))
			this.SYNC_IDLE_REG.cg_bits.option.name = {get_name(), ".SYNC_IDLE_REG_bits"};
		this.SYNC_IDLE_REG.configure(get_block(), this, "");
		this.SYNC_IDLE_REG.build();
		this.SYNC_IDLE_REG.add_hdl_path('{
            '{"i_common_DSI3_block_registers.i_common_DSI3_block_registers_SYNC_IDLE_REG.DSI", 0, 2},
            '{"i_common_DSI3_block_registers.i_common_DSI3_block_registers_SYNC_IDLE_REG.PIN", 15, 1}
		});

		this.CRM_TIME = ral_reg_common_DSI3_block_registers_CRM_TIME::type_id::create("CRM_TIME",,get_full_name());
		if(this.CRM_TIME.has_coverage(UVM_CVR_REG_BITS))
			this.CRM_TIME.cg_bits.option.name = {get_name(), ".CRM_TIME_bits"};
		this.CRM_TIME.configure(get_block(), this, "");
		this.CRM_TIME.build();
		this.CRM_TIME.add_hdl_path('{
            '{"i_common_DSI3_block_registers.i_common_DSI3_block_registers_CRM_TIME.TIME", 0, 11}
		});

		this.CRM_TIME_NR = ral_reg_common_DSI3_block_registers_CRM_TIME_NR::type_id::create("CRM_TIME_NR",,get_full_name());
		if(this.CRM_TIME_NR.has_coverage(UVM_CVR_REG_BITS))
			this.CRM_TIME_NR.cg_bits.option.name = {get_name(), ".CRM_TIME_NR_bits"};
		this.CRM_TIME_NR.configure(get_block(), this, "");
		this.CRM_TIME_NR.build();
		this.CRM_TIME_NR.add_hdl_path('{
            '{"i_common_DSI3_block_registers.i_common_DSI3_block_registers_CRM_TIME_NR.TIME", 0, 11}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(DSI_ENABLE, offset+`UVM_REG_ADDR_WIDTH'h91);
	  mp.add_reg(DSI_CFG, offset+`UVM_REG_ADDR_WIDTH'h92);
	  mp.add_reg(DSI_TX_SHIFT, offset+`UVM_REG_ADDR_WIDTH'h94);
	  mp.add_reg(SYNC_IDLE_REG, offset+`UVM_REG_ADDR_WIDTH'h95);
	  mp.add_reg(CRM_TIME, offset+`UVM_REG_ADDR_WIDTH'h98);
	  mp.add_reg(CRM_TIME_NR, offset+`UVM_REG_ADDR_WIDTH'h99);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  DSI_ENABLE.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h91);
	  DSI_CFG.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h92);
	  DSI_TX_SHIFT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h94);
	  SYNC_IDLE_REG.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h95);
	  CRM_TIME.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h98);
	  CRM_TIME_NR.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h99);

	endfunction

	`uvm_object_utils(ral_regfile_common_DSI3_block_registers)
endclass : ral_regfile_common_DSI3_block_registers




class ral_block_dsi3 extends uvm_reg_block;
	rand ral_regfile_common_DSI3_block_registers common_DSI3_block_registers;

	function new(string name = "dsi3");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 2, UVM_LITTLE_ENDIAN, 0);
      this.common_DSI3_block_registers = ral_regfile_common_DSI3_block_registers::type_id::create("common_DSI3_block_registers",,get_full_name());
      this.common_DSI3_block_registers.configure(this, null, "");
      this.common_DSI3_block_registers.build();
      this.common_DSI3_block_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_dsi3)

endclass : ral_block_dsi3


class ral_reg_OTP_readout_register_OTP_READ_ADDRESS extends uvm_reg;
	rand uvm_reg_field ADDR;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ADDR: coverpoint {m_data[11:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "OTP_readout_register_OTP_READ_ADDRESS");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ADDR = uvm_reg_field::type_id::create("ADDR",,get_full_name());
      this.ADDR.configure(this, 12, 0, "RW", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_OTP_readout_register_OTP_READ_ADDRESS)

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
endclass : ral_reg_OTP_readout_register_OTP_READ_ADDRESS


class ral_reg_OTP_readout_register_OTP_READ_VALUE extends uvm_reg;
	uvm_reg_field VALUE;
	uvm_reg_field ECC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   VALUE: coverpoint {m_data[7:0], m_is_read} iff(m_be != 0) {
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
	   ECC: coverpoint {m_data[11:8], m_is_read} iff(m_be != 0) {
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
	function new(string name = "OTP_readout_register_OTP_READ_VALUE");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.VALUE = uvm_reg_field::type_id::create("VALUE",,get_full_name());
      this.VALUE.configure(this, 8, 0, "RO", 0, 0, 1, 0, 1);
      this.ECC = uvm_reg_field::type_id::create("ECC",,get_full_name());
      this.ECC.configure(this, 4, 8, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_OTP_readout_register_OTP_READ_VALUE)

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
endclass : ral_reg_OTP_readout_register_OTP_READ_VALUE


class ral_reg_OTP_readout_register_OTP_READ_STATUS extends uvm_reg;
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
	function new(string name = "OTP_readout_register_OTP_READ_STATUS");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.STATUS = uvm_reg_field::type_id::create("STATUS",,get_full_name());
      this.STATUS.configure(this, 2, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_OTP_readout_register_OTP_READ_STATUS)

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
endclass : ral_reg_OTP_readout_register_OTP_READ_STATUS


class ral_regfile_OTP_readout_register extends uvm_reg_file;

	rand ral_reg_OTP_readout_register_OTP_READ_ADDRESS OTP_READ_ADDRESS;
	rand ral_reg_OTP_readout_register_OTP_READ_VALUE OTP_READ_VALUE;
	rand ral_reg_OTP_readout_register_OTP_READ_STATUS OTP_READ_STATUS;


	function new(string name = "OTP_readout_register");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.OTP_READ_ADDRESS = ral_reg_OTP_readout_register_OTP_READ_ADDRESS::type_id::create("OTP_READ_ADDRESS",,get_full_name());
		if(this.OTP_READ_ADDRESS.has_coverage(UVM_CVR_REG_BITS))
			this.OTP_READ_ADDRESS.cg_bits.option.name = {get_name(), ".OTP_READ_ADDRESS_bits"};
		this.OTP_READ_ADDRESS.configure(get_block(), this, "");
		this.OTP_READ_ADDRESS.build();
		this.OTP_READ_ADDRESS.add_hdl_path('{
            '{"i_OTP_readout_register.i_OTP_readout_register_OTP_READ_ADDRESS.ADDR", 0, 12}
		});

		this.OTP_READ_VALUE = ral_reg_OTP_readout_register_OTP_READ_VALUE::type_id::create("OTP_READ_VALUE",,get_full_name());
		if(this.OTP_READ_VALUE.has_coverage(UVM_CVR_REG_BITS))
			this.OTP_READ_VALUE.cg_bits.option.name = {get_name(), ".OTP_READ_VALUE_bits"};
		this.OTP_READ_VALUE.configure(get_block(), this, "");
		this.OTP_READ_VALUE.build();
		this.OTP_READ_VALUE.add_hdl_path('{
            '{"i_OTP_readout_register.i_OTP_readout_register_OTP_READ_VALUE.VALUE", 0, 8},
            '{"i_OTP_readout_register.i_OTP_readout_register_OTP_READ_VALUE.ECC", 8, 4}
		});

		this.OTP_READ_STATUS = ral_reg_OTP_readout_register_OTP_READ_STATUS::type_id::create("OTP_READ_STATUS",,get_full_name());
		if(this.OTP_READ_STATUS.has_coverage(UVM_CVR_REG_BITS))
			this.OTP_READ_STATUS.cg_bits.option.name = {get_name(), ".OTP_READ_STATUS_bits"};
		this.OTP_READ_STATUS.configure(get_block(), this, "");
		this.OTP_READ_STATUS.build();
		this.OTP_READ_STATUS.add_hdl_path('{
            '{"i_OTP_readout_register.i_OTP_readout_register_OTP_READ_STATUS.STATUS", 0, 2}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(OTP_READ_ADDRESS, offset+`UVM_REG_ADDR_WIDTH'h70);
	  mp.add_reg(OTP_READ_VALUE, offset+`UVM_REG_ADDR_WIDTH'h71);
	  mp.add_reg(OTP_READ_STATUS, offset+`UVM_REG_ADDR_WIDTH'h72);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  OTP_READ_ADDRESS.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h70);
	  OTP_READ_VALUE.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h71);
	  OTP_READ_STATUS.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h72);

	endfunction

	`uvm_object_utils(ral_regfile_OTP_readout_register)
endclass : ral_regfile_OTP_readout_register




class ral_block_otp_reader extends uvm_reg_block;
	rand ral_regfile_OTP_readout_register OTP_readout_register;

	function new(string name = "otp_reader");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 2, UVM_LITTLE_ENDIAN, 0);
      this.OTP_readout_register = ral_regfile_OTP_readout_register::type_id::create("OTP_readout_register",,get_full_name());
      this.OTP_readout_register.configure(this, null, "");
      this.OTP_readout_register.build();
      this.OTP_readout_register.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_otp_reader)

endclass : ral_block_otp_reader


class ral_reg_DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL extends uvm_reg;
	uvm_reg_field TRIM_REC1;
	uvm_reg_field TRIM_REC2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TRIM_REC1: coverpoint {m_data[3:0], m_is_read} iff(m_be != 0) {
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
	   TRIM_REC2: coverpoint {m_data[7:4], m_is_read} iff(m_be != 0) {
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
	function new(string name = "DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TRIM_REC1 = uvm_reg_field::type_id::create("TRIM_REC1",,get_full_name());
      this.TRIM_REC1.configure(this, 4, 0, "RO", 0, 0, 1, 0, 0);
      this.TRIM_REC2 = uvm_reg_field::type_id::create("TRIM_REC2",,get_full_name());
      this.TRIM_REC2.configure(this, 4, 4, "RO", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL)

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
endclass : ral_reg_DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL


class ral_reg_DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE extends uvm_reg;
	uvm_reg_field TRIM_REC1;
	uvm_reg_field TRIM_REC2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TRIM_REC1: coverpoint {m_data[3:0], m_is_read} iff(m_be != 0) {
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
	   TRIM_REC2: coverpoint {m_data[7:4], m_is_read} iff(m_be != 0) {
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
	function new(string name = "DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TRIM_REC1 = uvm_reg_field::type_id::create("TRIM_REC1",,get_full_name());
      this.TRIM_REC1.configure(this, 4, 0, "RO", 0, 0, 1, 0, 0);
      this.TRIM_REC2 = uvm_reg_field::type_id::create("TRIM_REC2",,get_full_name());
      this.TRIM_REC2.configure(this, 4, 4, "RO", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE)

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
endclass : ral_reg_DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE


class ral_regfile_DSI3_channel_trimming_registers extends uvm_reg_file;

	rand ral_reg_DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL TRIM_DSI_REC_FALL;
	rand ral_reg_DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE TRIM_DSI_REC_RISE;


	function new(string name = "DSI3_channel_trimming_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.TRIM_DSI_REC_FALL = ral_reg_DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL::type_id::create("TRIM_DSI_REC_FALL",,get_full_name());
		if(this.TRIM_DSI_REC_FALL.has_coverage(UVM_CVR_REG_BITS))
			this.TRIM_DSI_REC_FALL.cg_bits.option.name = {get_name(), ".TRIM_DSI_REC_FALL_bits"};
		this.TRIM_DSI_REC_FALL.configure(get_block(), this, "");
		this.TRIM_DSI_REC_FALL.build();
		this.TRIM_DSI_REC_FALL.add_hdl_path('{
            '{"i_DSI3_channel_trimming_registers.i_DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL.TRIM_REC1", 0, 4},
            '{"i_DSI3_channel_trimming_registers.i_DSI3_channel_trimming_registers_TRIM_DSI_REC_FALL.TRIM_REC2", 4, 4}
		});

		this.TRIM_DSI_REC_RISE = ral_reg_DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE::type_id::create("TRIM_DSI_REC_RISE",,get_full_name());
		if(this.TRIM_DSI_REC_RISE.has_coverage(UVM_CVR_REG_BITS))
			this.TRIM_DSI_REC_RISE.cg_bits.option.name = {get_name(), ".TRIM_DSI_REC_RISE_bits"};
		this.TRIM_DSI_REC_RISE.configure(get_block(), this, "");
		this.TRIM_DSI_REC_RISE.build();
		this.TRIM_DSI_REC_RISE.add_hdl_path('{
            '{"i_DSI3_channel_trimming_registers.i_DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE.TRIM_REC1", 0, 4},
            '{"i_DSI3_channel_trimming_registers.i_DSI3_channel_trimming_registers_TRIM_DSI_REC_RISE.TRIM_REC2", 4, 4}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(TRIM_DSI_REC_FALL, offset+`UVM_REG_ADDR_WIDTH'h0);
	  mp.add_reg(TRIM_DSI_REC_RISE, offset+`UVM_REG_ADDR_WIDTH'h1);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  TRIM_DSI_REC_FALL.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h0);
	  TRIM_DSI_REC_RISE.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h1);

	endfunction

	`uvm_object_utils(ral_regfile_DSI3_channel_trimming_registers)
endclass : ral_regfile_DSI3_channel_trimming_registers




class ral_block_dsi3_trim extends uvm_reg_block;
	rand ral_regfile_DSI3_channel_trimming_registers DSI3_channel_trimming_registers;

	function new(string name = "dsi3_trim");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 2, UVM_LITTLE_ENDIAN, 0);
      this.DSI3_channel_trimming_registers = ral_regfile_DSI3_channel_trimming_registers::type_id::create("DSI3_channel_trimming_registers",,get_full_name());
      this.DSI3_channel_trimming_registers.configure(this, null, "");
      this.DSI3_channel_trimming_registers.build();
      this.DSI3_channel_trimming_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_dsi3_trim)

endclass : ral_block_dsi3_trim


class ral_reg_DSI3_channel_registers_DSI_STAT extends uvm_reg;
	uvm_reg_field PULSECNT;
	uvm_reg_field DSIOV;
	uvm_reg_field DSIUV;
	uvm_reg_field SYNC;
	uvm_reg_field SLAVES;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PULSECNT: coverpoint {m_data[7:0], m_is_read} iff(m_be != 0) {
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
	   DSIOV: coverpoint {m_data[8:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   DSIUV: coverpoint {m_data[9:9], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SYNC: coverpoint {m_data[10:10], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SLAVES: coverpoint {m_data[14:11], m_is_read} iff(m_be != 0) {
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
	function new(string name = "DSI3_channel_registers_DSI_STAT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PULSECNT = uvm_reg_field::type_id::create("PULSECNT",,get_full_name());
      this.PULSECNT.configure(this, 8, 0, "RO", 0, 0, 1, 0, 1);
      this.DSIOV = uvm_reg_field::type_id::create("DSIOV",,get_full_name());
      this.DSIOV.configure(this, 1, 8, "RO", 0, 0, 1, 0, 0);
      this.DSIUV = uvm_reg_field::type_id::create("DSIUV",,get_full_name());
      this.DSIUV.configure(this, 1, 9, "RO", 0, 0, 1, 0, 0);
      this.SYNC = uvm_reg_field::type_id::create("SYNC",,get_full_name());
      this.SYNC.configure(this, 1, 10, "RO", 0, 0, 1, 0, 0);
      this.SLAVES = uvm_reg_field::type_id::create("SLAVES",,get_full_name());
      this.SLAVES.configure(this, 4, 11, "RO", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_registers_DSI_STAT)

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
endclass : ral_reg_DSI3_channel_registers_DSI_STAT


class ral_reg_DSI3_channel_registers_PDCM_PERIOD extends uvm_reg;
	uvm_reg_field PDCMPER;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PDCMPER: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "DSI3_channel_registers_PDCM_PERIOD");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PDCMPER = uvm_reg_field::type_id::create("PDCMPER",,get_full_name());
      this.PDCMPER.configure(this, 16, 0, "RO", 0, 1000, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_registers_PDCM_PERIOD)

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
endclass : ral_reg_DSI3_channel_registers_PDCM_PERIOD


class ral_reg_DSI3_channel_registers_DSI_LOAD extends uvm_reg;
	rand uvm_reg_field LOAD;
	uvm_reg_field IDLE;
	uvm_reg_field START_MEASUREMENT;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LOAD: coverpoint {m_data[4:0], m_is_read} iff(m_be != 0) {
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
	   IDLE: coverpoint {m_data[14:14], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   START_MEASUREMENT: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DSI3_channel_registers_DSI_LOAD");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LOAD = uvm_reg_field::type_id::create("LOAD",,get_full_name());
      this.LOAD.configure(this, 5, 0, "RW", 0, 0, 1, 0, 1);
      this.IDLE = uvm_reg_field::type_id::create("IDLE",,get_full_name());
      this.IDLE.configure(this, 1, 14, "RO", 0, 1, 1, 0, 0);
      this.START_MEASUREMENT = uvm_reg_field::type_id::create("START_MEASUREMENT",,get_full_name());
      this.START_MEASUREMENT.configure(this, 1, 15, "RO", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_registers_DSI_LOAD)

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
endclass : ral_reg_DSI3_channel_registers_DSI_LOAD


class ral_reg_DSI3_channel_registers_DSI_IRQ_STAT extends uvm_reg;
	rand uvm_reg_field DSIOV;
	rand uvm_reg_field DSIUV;
	rand uvm_reg_field SYNC_ERR;
	rand uvm_reg_field HW_FAIL;
	rand uvm_reg_field DMOF;
	rand uvm_reg_field COM_ERR;
	rand uvm_reg_field IQ_ERR;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DSIOV: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   DSIUV: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SYNC_ERR: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   HW_FAIL: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   DMOF: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   COM_ERR: coverpoint {m_data[5:5], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   IQ_ERR: coverpoint {m_data[6:6], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DSI3_channel_registers_DSI_IRQ_STAT");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DSIOV = uvm_reg_field::type_id::create("DSIOV",,get_full_name());
      this.DSIOV.configure(this, 1, 0, "W1C", 0, 0, 1, 0, 0);
      this.DSIUV = uvm_reg_field::type_id::create("DSIUV",,get_full_name());
      this.DSIUV.configure(this, 1, 1, "W1C", 0, 0, 1, 0, 0);
      this.SYNC_ERR = uvm_reg_field::type_id::create("SYNC_ERR",,get_full_name());
      this.SYNC_ERR.configure(this, 1, 2, "W1C", 0, 0, 1, 0, 0);
      this.HW_FAIL = uvm_reg_field::type_id::create("HW_FAIL",,get_full_name());
      this.HW_FAIL.configure(this, 1, 3, "W1C", 0, 0, 1, 0, 0);
      this.DMOF = uvm_reg_field::type_id::create("DMOF",,get_full_name());
      this.DMOF.configure(this, 1, 4, "W1C", 0, 0, 1, 0, 0);
      this.COM_ERR = uvm_reg_field::type_id::create("COM_ERR",,get_full_name());
      this.COM_ERR.configure(this, 1, 5, "W1C", 0, 0, 1, 0, 0);
      this.IQ_ERR = uvm_reg_field::type_id::create("IQ_ERR",,get_full_name());
      this.IQ_ERR.configure(this, 1, 6, "W1C", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_registers_DSI_IRQ_STAT)

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
endclass : ral_reg_DSI3_channel_registers_DSI_IRQ_STAT


class ral_reg_DSI3_channel_registers_DSI_IRQ_MASK extends uvm_reg;
	rand uvm_reg_field DSIOV;
	rand uvm_reg_field DSIUV;
	rand uvm_reg_field SYNC_ERR;
	rand uvm_reg_field HW_FAIL;
	rand uvm_reg_field DMOF;
	rand uvm_reg_field COM_ERR;
	rand uvm_reg_field IQ_ERR;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DSIOV: coverpoint {m_data[0:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   DSIUV: coverpoint {m_data[1:1], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SYNC_ERR: coverpoint {m_data[2:2], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   HW_FAIL: coverpoint {m_data[3:3], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   DMOF: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   COM_ERR: coverpoint {m_data[5:5], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   IQ_ERR: coverpoint {m_data[6:6], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DSI3_channel_registers_DSI_IRQ_MASK");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DSIOV = uvm_reg_field::type_id::create("DSIOV",,get_full_name());
      this.DSIOV.configure(this, 1, 0, "RW", 0, 1, 1, 0, 0);
      this.DSIUV = uvm_reg_field::type_id::create("DSIUV",,get_full_name());
      this.DSIUV.configure(this, 1, 1, "RW", 0, 1, 1, 0, 0);
      this.SYNC_ERR = uvm_reg_field::type_id::create("SYNC_ERR",,get_full_name());
      this.SYNC_ERR.configure(this, 1, 2, "RW", 0, 1, 1, 0, 0);
      this.HW_FAIL = uvm_reg_field::type_id::create("HW_FAIL",,get_full_name());
      this.HW_FAIL.configure(this, 1, 3, "RW", 0, 1, 1, 0, 0);
      this.DMOF = uvm_reg_field::type_id::create("DMOF",,get_full_name());
      this.DMOF.configure(this, 1, 4, "RW", 0, 1, 1, 0, 0);
      this.COM_ERR = uvm_reg_field::type_id::create("COM_ERR",,get_full_name());
      this.COM_ERR.configure(this, 1, 5, "RW", 0, 1, 1, 0, 0);
      this.IQ_ERR = uvm_reg_field::type_id::create("IQ_ERR",,get_full_name());
      this.IQ_ERR.configure(this, 1, 6, "RW", 0, 1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_registers_DSI_IRQ_MASK)

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
endclass : ral_reg_DSI3_channel_registers_DSI_IRQ_MASK


class ral_reg_DSI3_channel_registers_DSI_CMD extends uvm_reg;
	uvm_reg_field DATA;
	uvm_reg_field CMD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DATA: coverpoint {m_data[11:0], m_is_read} iff(m_be != 0) {
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
	   CMD: coverpoint {m_data[15:12], m_is_read} iff(m_be != 0) {
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
	function new(string name = "DSI3_channel_registers_DSI_CMD");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DATA = uvm_reg_field::type_id::create("DATA",,get_full_name());
      this.DATA.configure(this, 12, 0, "RO", 0, 0, 1, 0, 0);
      this.CMD = uvm_reg_field::type_id::create("CMD",,get_full_name());
      this.CMD.configure(this, 4, 12, "RO", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_registers_DSI_CMD)

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
endclass : ral_reg_DSI3_channel_registers_DSI_CMD


class ral_reg_DSI3_channel_registers_CRM_WORD2 extends uvm_reg;
	uvm_reg_field CRM_WORD2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CRM_WORD2: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "DSI3_channel_registers_CRM_WORD2");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CRM_WORD2 = uvm_reg_field::type_id::create("CRM_WORD2",,get_full_name());
      this.CRM_WORD2.configure(this, 16, 0, "RO", 0, 255, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_registers_CRM_WORD2)

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
endclass : ral_reg_DSI3_channel_registers_CRM_WORD2


class ral_reg_DSI3_channel_registers_CRM_WORD1 extends uvm_reg;
	uvm_reg_field CRM_WORD1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CRM_WORD1: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "DSI3_channel_registers_CRM_WORD1");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CRM_WORD1 = uvm_reg_field::type_id::create("CRM_WORD1",,get_full_name());
      this.CRM_WORD1.configure(this, 16, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_registers_CRM_WORD1)

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
endclass : ral_reg_DSI3_channel_registers_CRM_WORD1


class ral_reg_DSI3_channel_registers_PACKET_STAT extends uvm_reg;
	uvm_reg_field SYMBOL_COUNT;
	uvm_reg_field CLK_ERR;
	uvm_reg_field VDSI_ERR;
	uvm_reg_field SYMBOL_ERROR;
	uvm_reg_field TE;
	uvm_reg_field CRC_ERR;
	uvm_reg_field SCE;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   SYMBOL_COUNT: coverpoint {m_data[7:0], m_is_read} iff(m_be != 0) {
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
	   CLK_ERR: coverpoint {m_data[8:8], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   VDSI_ERR: coverpoint {m_data[9:9], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SYMBOL_ERROR: coverpoint {m_data[10:10], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   TE: coverpoint {m_data[11:11], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CRC_ERR: coverpoint {m_data[12:12], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   SCE: coverpoint {m_data[13:13], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DSI3_channel_registers_PACKET_STAT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.SYMBOL_COUNT = uvm_reg_field::type_id::create("SYMBOL_COUNT",,get_full_name());
      this.SYMBOL_COUNT.configure(this, 8, 0, "RO", 0, 0, 1, 0, 1);
      this.CLK_ERR = uvm_reg_field::type_id::create("CLK_ERR",,get_full_name());
      this.CLK_ERR.configure(this, 1, 8, "RO", 0, 0, 1, 0, 0);
      this.VDSI_ERR = uvm_reg_field::type_id::create("VDSI_ERR",,get_full_name());
      this.VDSI_ERR.configure(this, 1, 9, "RO", 0, 0, 1, 0, 0);
      this.SYMBOL_ERROR = uvm_reg_field::type_id::create("SYMBOL_ERROR",,get_full_name());
      this.SYMBOL_ERROR.configure(this, 1, 10, "RO", 0, 0, 1, 0, 0);
      this.TE = uvm_reg_field::type_id::create("TE",,get_full_name());
      this.TE.configure(this, 1, 11, "RO", 0, 0, 1, 0, 0);
      this.CRC_ERR = uvm_reg_field::type_id::create("CRC_ERR",,get_full_name());
      this.CRC_ERR.configure(this, 1, 12, "RO", 0, 0, 1, 0, 0);
      this.SCE = uvm_reg_field::type_id::create("SCE",,get_full_name());
      this.SCE.configure(this, 1, 13, "RO", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_registers_PACKET_STAT)

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
endclass : ral_reg_DSI3_channel_registers_PACKET_STAT


class ral_reg_DSI3_channel_registers_FRAME_STAT extends uvm_reg;
	uvm_reg_field PACKET_COUNT;
	uvm_reg_field PC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PACKET_COUNT: coverpoint {m_data[7:0], m_is_read} iff(m_be != 0) {
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
	   PC: coverpoint {m_data[15:15], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DSI3_channel_registers_FRAME_STAT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PACKET_COUNT = uvm_reg_field::type_id::create("PACKET_COUNT",,get_full_name());
      this.PACKET_COUNT.configure(this, 8, 0, "RO", 0, 0, 1, 0, 1);
      this.PC = uvm_reg_field::type_id::create("PC",,get_full_name());
      this.PC.configure(this, 1, 15, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_registers_FRAME_STAT)

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
endclass : ral_reg_DSI3_channel_registers_FRAME_STAT


class ral_reg_DSI3_channel_registers_WAIT_TIME extends uvm_reg;
	uvm_reg_field TIME;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TIME: coverpoint {m_data[14:0], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {16'b??????????????00};
	      wildcard bins bit_0_wr_as_1 = {16'b??????????????10};
	      wildcard bins bit_0_rd_as_0 = {16'b??????????????01};
	      wildcard bins bit_0_rd_as_1 = {16'b??????????????11};
	      wildcard bins bit_1_wr_as_0 = {16'b?????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {16'b?????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {16'b?????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {16'b?????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {16'b????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {16'b????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {16'b????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {16'b????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {16'b???????????0???0};
	      wildcard bins bit_3_wr_as_1 = {16'b???????????1???0};
	      wildcard bins bit_3_rd_as_0 = {16'b???????????0???1};
	      wildcard bins bit_3_rd_as_1 = {16'b???????????1???1};
	      wildcard bins bit_4_wr_as_0 = {16'b??????????0????0};
	      wildcard bins bit_4_wr_as_1 = {16'b??????????1????0};
	      wildcard bins bit_4_rd_as_0 = {16'b??????????0????1};
	      wildcard bins bit_4_rd_as_1 = {16'b??????????1????1};
	      wildcard bins bit_5_wr_as_0 = {16'b?????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {16'b?????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {16'b?????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {16'b?????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {16'b????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {16'b????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {16'b????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {16'b????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {16'b???????0???????0};
	      wildcard bins bit_7_wr_as_1 = {16'b???????1???????0};
	      wildcard bins bit_7_rd_as_0 = {16'b???????0???????1};
	      wildcard bins bit_7_rd_as_1 = {16'b???????1???????1};
	      wildcard bins bit_8_wr_as_0 = {16'b??????0????????0};
	      wildcard bins bit_8_wr_as_1 = {16'b??????1????????0};
	      wildcard bins bit_8_rd_as_0 = {16'b??????0????????1};
	      wildcard bins bit_8_rd_as_1 = {16'b??????1????????1};
	      wildcard bins bit_9_wr_as_0 = {16'b?????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {16'b?????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {16'b?????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {16'b?????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {16'b????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {16'b????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {16'b????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {16'b????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {16'b???0???????????0};
	      wildcard bins bit_11_wr_as_1 = {16'b???1???????????0};
	      wildcard bins bit_11_rd_as_0 = {16'b???0???????????1};
	      wildcard bins bit_11_rd_as_1 = {16'b???1???????????1};
	      wildcard bins bit_12_wr_as_0 = {16'b??0????????????0};
	      wildcard bins bit_12_wr_as_1 = {16'b??1????????????0};
	      wildcard bins bit_12_rd_as_0 = {16'b??0????????????1};
	      wildcard bins bit_12_rd_as_1 = {16'b??1????????????1};
	      wildcard bins bit_13_wr_as_0 = {16'b?0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {16'b?1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {16'b?0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {16'b?1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {16'b0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {16'b1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {16'b0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {16'b1??????????????1};
	      option.weight = 60;
	   }
	endgroup
	function new(string name = "DSI3_channel_registers_WAIT_TIME");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TIME = uvm_reg_field::type_id::create("TIME",,get_full_name());
      this.TIME.configure(this, 15, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_registers_WAIT_TIME)

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
endclass : ral_reg_DSI3_channel_registers_WAIT_TIME


class ral_reg_DSI3_channel_registers_SYNC extends uvm_reg;
	uvm_reg_field CHANNELS;
	uvm_reg_field PIN;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CHANNELS: coverpoint {m_data[1:0], m_is_read} iff(m_be != 0) {
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
	   PIN: coverpoint {m_data[4:4], m_is_read} iff(m_be != 0) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DSI3_channel_registers_SYNC");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CHANNELS = uvm_reg_field::type_id::create("CHANNELS",,get_full_name());
      this.CHANNELS.configure(this, 2, 0, "RO", 0, 0, 1, 0, 0);
      this.PIN = uvm_reg_field::type_id::create("PIN",,get_full_name());
      this.PIN.configure(this, 1, 4, "RO", 0, 0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DSI3_channel_registers_SYNC)

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
endclass : ral_reg_DSI3_channel_registers_SYNC


class ral_regfile_DSI3_channel_registers extends uvm_reg_file;

	rand ral_reg_DSI3_channel_registers_DSI_STAT DSI_STAT;
	rand ral_reg_DSI3_channel_registers_PDCM_PERIOD PDCM_PERIOD;
	rand ral_reg_DSI3_channel_registers_DSI_LOAD DSI_LOAD;
	rand ral_reg_DSI3_channel_registers_DSI_IRQ_STAT DSI_IRQ_STAT;
	rand ral_reg_DSI3_channel_registers_DSI_IRQ_MASK DSI_IRQ_MASK;
	rand ral_reg_DSI3_channel_registers_DSI_CMD DSI_CMD;
	rand ral_reg_DSI3_channel_registers_CRM_WORD2 CRM_WORD2;
	rand ral_reg_DSI3_channel_registers_CRM_WORD1 CRM_WORD1;
	rand ral_reg_DSI3_channel_registers_PACKET_STAT PACKET_STAT;
	rand ral_reg_DSI3_channel_registers_FRAME_STAT FRAME_STAT;
	rand ral_reg_DSI3_channel_registers_WAIT_TIME WAIT_TIME;
	rand ral_reg_DSI3_channel_registers_SYNC SYNC;


	function new(string name = "DSI3_channel_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.DSI_STAT = ral_reg_DSI3_channel_registers_DSI_STAT::type_id::create("DSI_STAT",,get_full_name());
		if(this.DSI_STAT.has_coverage(UVM_CVR_REG_BITS))
			this.DSI_STAT.cg_bits.option.name = {get_name(), ".DSI_STAT_bits"};
		this.DSI_STAT.configure(get_block(), this, "");
		this.DSI_STAT.build();
		this.DSI_STAT.add_hdl_path('{
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_STAT.PULSECNT", 0, 8},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_STAT.DSIOV", 8, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_STAT.DSIUV", 9, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_STAT.SYNC", 10, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_STAT.SLAVES", 11, 4}
		});

		this.PDCM_PERIOD = ral_reg_DSI3_channel_registers_PDCM_PERIOD::type_id::create("PDCM_PERIOD",,get_full_name());
		if(this.PDCM_PERIOD.has_coverage(UVM_CVR_REG_BITS))
			this.PDCM_PERIOD.cg_bits.option.name = {get_name(), ".PDCM_PERIOD_bits"};
		this.PDCM_PERIOD.configure(get_block(), this, "");
		this.PDCM_PERIOD.build();
		this.PDCM_PERIOD.add_hdl_path('{
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_PDCM_PERIOD.PDCMPER", 0, 16}
		});

		this.DSI_LOAD = ral_reg_DSI3_channel_registers_DSI_LOAD::type_id::create("DSI_LOAD",,get_full_name());
		if(this.DSI_LOAD.has_coverage(UVM_CVR_REG_BITS))
			this.DSI_LOAD.cg_bits.option.name = {get_name(), ".DSI_LOAD_bits"};
		this.DSI_LOAD.configure(get_block(), this, "");
		this.DSI_LOAD.build();
		this.DSI_LOAD.add_hdl_path('{
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_LOAD.LOAD", 0, 5},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_LOAD.IDLE", 14, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_LOAD.START_MEASUREMENT", 15, 1}
		});

		this.DSI_IRQ_STAT = ral_reg_DSI3_channel_registers_DSI_IRQ_STAT::type_id::create("DSI_IRQ_STAT",,get_full_name());
		if(this.DSI_IRQ_STAT.has_coverage(UVM_CVR_REG_BITS))
			this.DSI_IRQ_STAT.cg_bits.option.name = {get_name(), ".DSI_IRQ_STAT_bits"};
		this.DSI_IRQ_STAT.configure(get_block(), this, "");
		this.DSI_IRQ_STAT.build();
		this.DSI_IRQ_STAT.add_hdl_path('{
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_STAT.DSIOV", 0, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_STAT.DSIUV", 1, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_STAT.SYNC_ERR", 2, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_STAT.HW_FAIL", 3, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_STAT.DMOF", 4, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_STAT.COM_ERR", 5, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_STAT.IQ_ERR", 6, 1}
		});

		this.DSI_IRQ_MASK = ral_reg_DSI3_channel_registers_DSI_IRQ_MASK::type_id::create("DSI_IRQ_MASK",,get_full_name());
		if(this.DSI_IRQ_MASK.has_coverage(UVM_CVR_REG_BITS))
			this.DSI_IRQ_MASK.cg_bits.option.name = {get_name(), ".DSI_IRQ_MASK_bits"};
		this.DSI_IRQ_MASK.configure(get_block(), this, "");
		this.DSI_IRQ_MASK.build();
		this.DSI_IRQ_MASK.add_hdl_path('{
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_MASK.DSIOV", 0, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_MASK.DSIUV", 1, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_MASK.SYNC_ERR", 2, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_MASK.HW_FAIL", 3, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_MASK.DMOF", 4, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_MASK.COM_ERR", 5, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_IRQ_MASK.IQ_ERR", 6, 1}
		});

		this.DSI_CMD = ral_reg_DSI3_channel_registers_DSI_CMD::type_id::create("DSI_CMD",,get_full_name());
		if(this.DSI_CMD.has_coverage(UVM_CVR_REG_BITS))
			this.DSI_CMD.cg_bits.option.name = {get_name(), ".DSI_CMD_bits"};
		this.DSI_CMD.configure(get_block(), this, "");
		this.DSI_CMD.build();
		this.DSI_CMD.add_hdl_path('{
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_CMD.DATA", 0, 12},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_DSI_CMD.CMD", 12, 4}
		});

		this.CRM_WORD2 = ral_reg_DSI3_channel_registers_CRM_WORD2::type_id::create("CRM_WORD2",,get_full_name());
		if(this.CRM_WORD2.has_coverage(UVM_CVR_REG_BITS))
			this.CRM_WORD2.cg_bits.option.name = {get_name(), ".CRM_WORD2_bits"};
		this.CRM_WORD2.configure(get_block(), this, "");
		this.CRM_WORD2.build();
		this.CRM_WORD2.add_hdl_path('{
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_CRM_WORD2.CRM_WORD2", 0, 16}
		});

		this.CRM_WORD1 = ral_reg_DSI3_channel_registers_CRM_WORD1::type_id::create("CRM_WORD1",,get_full_name());
		if(this.CRM_WORD1.has_coverage(UVM_CVR_REG_BITS))
			this.CRM_WORD1.cg_bits.option.name = {get_name(), ".CRM_WORD1_bits"};
		this.CRM_WORD1.configure(get_block(), this, "");
		this.CRM_WORD1.build();
		this.CRM_WORD1.add_hdl_path('{
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_CRM_WORD1.CRM_WORD1", 0, 16}
		});

		this.PACKET_STAT = ral_reg_DSI3_channel_registers_PACKET_STAT::type_id::create("PACKET_STAT",,get_full_name());
		if(this.PACKET_STAT.has_coverage(UVM_CVR_REG_BITS))
			this.PACKET_STAT.cg_bits.option.name = {get_name(), ".PACKET_STAT_bits"};
		this.PACKET_STAT.configure(get_block(), this, "");
		this.PACKET_STAT.build();
		this.PACKET_STAT.add_hdl_path('{
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_PACKET_STAT.SYMBOL_COUNT", 0, 8},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_PACKET_STAT.CLK_ERR", 8, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_PACKET_STAT.VDSI_ERR", 9, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_PACKET_STAT.SYMBOL_ERROR", 10, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_PACKET_STAT.TE", 11, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_PACKET_STAT.CRC_ERR", 12, 1},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_PACKET_STAT.SCE", 13, 1}
		});

		this.FRAME_STAT = ral_reg_DSI3_channel_registers_FRAME_STAT::type_id::create("FRAME_STAT",,get_full_name());
		if(this.FRAME_STAT.has_coverage(UVM_CVR_REG_BITS))
			this.FRAME_STAT.cg_bits.option.name = {get_name(), ".FRAME_STAT_bits"};
		this.FRAME_STAT.configure(get_block(), this, "");
		this.FRAME_STAT.build();
		this.FRAME_STAT.add_hdl_path('{
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_FRAME_STAT.PACKET_COUNT", 0, 8},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_FRAME_STAT.PC", 15, 1}
		});

		this.WAIT_TIME = ral_reg_DSI3_channel_registers_WAIT_TIME::type_id::create("WAIT_TIME",,get_full_name());
		if(this.WAIT_TIME.has_coverage(UVM_CVR_REG_BITS))
			this.WAIT_TIME.cg_bits.option.name = {get_name(), ".WAIT_TIME_bits"};
		this.WAIT_TIME.configure(get_block(), this, "");
		this.WAIT_TIME.build();
		this.WAIT_TIME.add_hdl_path('{
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_WAIT_TIME.TIME", 0, 15}
		});

		this.SYNC = ral_reg_DSI3_channel_registers_SYNC::type_id::create("SYNC",,get_full_name());
		if(this.SYNC.has_coverage(UVM_CVR_REG_BITS))
			this.SYNC.cg_bits.option.name = {get_name(), ".SYNC_bits"};
		this.SYNC.configure(get_block(), this, "");
		this.SYNC.build();
		this.SYNC.add_hdl_path('{
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_SYNC.CHANNELS", 0, 2},
            '{"i_DSI3_channel_registers.i_DSI3_channel_registers_SYNC.PIN", 4, 1}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(DSI_STAT, offset+`UVM_REG_ADDR_WIDTH'h0);
	  mp.add_reg(PDCM_PERIOD, offset+`UVM_REG_ADDR_WIDTH'h4);
	  mp.add_reg(DSI_LOAD, offset+`UVM_REG_ADDR_WIDTH'h5);
	  uvm_resource_db#(bit)::set({"REG::", DSI_LOAD.get_full_name()}, "NO_REG_ACCESS_TEST", 1, this);
	  uvm_resource_db#(bit)::set({"REG::", DSI_LOAD.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  mp.add_reg(DSI_IRQ_STAT, offset+`UVM_REG_ADDR_WIDTH'h8);
	  mp.add_reg(DSI_IRQ_MASK, offset+`UVM_REG_ADDR_WIDTH'h9);
	  mp.add_reg(DSI_CMD, offset+`UVM_REG_ADDR_WIDTH'h10);
	  mp.add_reg(CRM_WORD2, offset+`UVM_REG_ADDR_WIDTH'h11);
	  mp.add_reg(CRM_WORD1, offset+`UVM_REG_ADDR_WIDTH'h12);
	  mp.add_reg(PACKET_STAT, offset+`UVM_REG_ADDR_WIDTH'h18);
	  mp.add_reg(FRAME_STAT, offset+`UVM_REG_ADDR_WIDTH'h1B);
	  mp.add_reg(WAIT_TIME, offset+`UVM_REG_ADDR_WIDTH'h19);
	  mp.add_reg(SYNC, offset+`UVM_REG_ADDR_WIDTH'h1A);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  DSI_STAT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h0);
	  PDCM_PERIOD.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h4);
	  DSI_LOAD.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h5);
	  DSI_IRQ_STAT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h8);
	  DSI_IRQ_MASK.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h9);
	  DSI_CMD.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h10);
	  CRM_WORD2.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h11);
	  CRM_WORD1.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h12);
	  PACKET_STAT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h18);
	  FRAME_STAT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h1B);
	  WAIT_TIME.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h19);
	  SYNC.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h1A);

	endfunction

	`uvm_object_utils(ral_regfile_DSI3_channel_registers)
endclass : ral_regfile_DSI3_channel_registers




class ral_block_dsi3_block extends uvm_reg_block;
	rand ral_regfile_DSI3_channel_registers DSI3_channel_registers;

	function new(string name = "dsi3_block");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 2, UVM_LITTLE_ENDIAN, 0);
      this.DSI3_channel_registers = ral_regfile_DSI3_channel_registers::type_id::create("DSI3_channel_registers",,get_full_name());
      this.DSI3_channel_registers.configure(this, null, "");
      this.DSI3_channel_registers.build();
      this.DSI3_channel_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_dsi3_block)

endclass : ral_block_dsi3_block


class ral_reg_ring_buffer_registers_BUF_VALID_COUNT extends uvm_reg;
	uvm_reg_field VALID_COUNT;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   VALID_COUNT: coverpoint {m_data[11:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "ring_buffer_registers_BUF_VALID_COUNT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.VALID_COUNT = uvm_reg_field::type_id::create("VALID_COUNT",,get_full_name());
      this.VALID_COUNT.configure(this, 12, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_ring_buffer_registers_BUF_VALID_COUNT)

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
endclass : ral_reg_ring_buffer_registers_BUF_VALID_COUNT


class ral_reg_ring_buffer_registers_BUF_FREE extends uvm_reg;
	uvm_reg_field FREE;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   FREE: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "ring_buffer_registers_BUF_FREE");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.FREE = uvm_reg_field::type_id::create("FREE",,get_full_name());
      this.FREE.configure(this, 16, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_ring_buffer_registers_BUF_FREE)

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
endclass : ral_reg_ring_buffer_registers_BUF_FREE


class ral_reg_ring_buffer_registers_BUF_READ_POINTER extends uvm_reg;
	uvm_reg_field READ_POINTER;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   READ_POINTER: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "ring_buffer_registers_BUF_READ_POINTER");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.READ_POINTER = uvm_reg_field::type_id::create("READ_POINTER",,get_full_name());
      this.READ_POINTER.configure(this, 16, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_ring_buffer_registers_BUF_READ_POINTER)

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
endclass : ral_reg_ring_buffer_registers_BUF_READ_POINTER


class ral_reg_ring_buffer_registers_BUF_WRITE_POINTER extends uvm_reg;
	uvm_reg_field WRITE_POINTER;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   WRITE_POINTER: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "ring_buffer_registers_BUF_WRITE_POINTER");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.WRITE_POINTER = uvm_reg_field::type_id::create("WRITE_POINTER",,get_full_name());
      this.WRITE_POINTER.configure(this, 16, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_ring_buffer_registers_BUF_WRITE_POINTER)

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
endclass : ral_reg_ring_buffer_registers_BUF_WRITE_POINTER


class ral_reg_ring_buffer_registers_BUF_VALID_POINTER extends uvm_reg;
	uvm_reg_field VALID_POINTER;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   VALID_POINTER: coverpoint {m_data[15:0], m_is_read} iff(m_be != 0) {
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
	function new(string name = "ring_buffer_registers_BUF_VALID_POINTER");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.VALID_POINTER = uvm_reg_field::type_id::create("VALID_POINTER",,get_full_name());
      this.VALID_POINTER.configure(this, 16, 0, "RO", 0, 0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_ring_buffer_registers_BUF_VALID_POINTER)

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
endclass : ral_reg_ring_buffer_registers_BUF_VALID_POINTER


class ral_regfile_ring_buffer_registers extends uvm_reg_file;

	rand ral_reg_ring_buffer_registers_BUF_VALID_COUNT BUF_VALID_COUNT;
	rand ral_reg_ring_buffer_registers_BUF_FREE BUF_FREE;
	rand ral_reg_ring_buffer_registers_BUF_READ_POINTER BUF_READ_POINTER;
	rand ral_reg_ring_buffer_registers_BUF_WRITE_POINTER BUF_WRITE_POINTER;
	rand ral_reg_ring_buffer_registers_BUF_VALID_POINTER BUF_VALID_POINTER;


	function new(string name = "ring_buffer_registers");
		super.new(name);
	endfunction : new

	virtual function void build();
		this.BUF_VALID_COUNT = ral_reg_ring_buffer_registers_BUF_VALID_COUNT::type_id::create("BUF_VALID_COUNT",,get_full_name());
		if(this.BUF_VALID_COUNT.has_coverage(UVM_CVR_REG_BITS))
			this.BUF_VALID_COUNT.cg_bits.option.name = {get_name(), ".BUF_VALID_COUNT_bits"};
		this.BUF_VALID_COUNT.configure(get_block(), this, "");
		this.BUF_VALID_COUNT.build();
		this.BUF_VALID_COUNT.add_hdl_path('{
            '{"i_ring_buffer_registers.i_ring_buffer_registers_BUF_VALID_COUNT.VALID_COUNT", 0, 12}
		});

		this.BUF_FREE = ral_reg_ring_buffer_registers_BUF_FREE::type_id::create("BUF_FREE",,get_full_name());
		if(this.BUF_FREE.has_coverage(UVM_CVR_REG_BITS))
			this.BUF_FREE.cg_bits.option.name = {get_name(), ".BUF_FREE_bits"};
		this.BUF_FREE.configure(get_block(), this, "");
		this.BUF_FREE.build();
		this.BUF_FREE.add_hdl_path('{
            '{"i_ring_buffer_registers.i_ring_buffer_registers_BUF_FREE.FREE", 0, 16}
		});

		this.BUF_READ_POINTER = ral_reg_ring_buffer_registers_BUF_READ_POINTER::type_id::create("BUF_READ_POINTER",,get_full_name());
		if(this.BUF_READ_POINTER.has_coverage(UVM_CVR_REG_BITS))
			this.BUF_READ_POINTER.cg_bits.option.name = {get_name(), ".BUF_READ_POINTER_bits"};
		this.BUF_READ_POINTER.configure(get_block(), this, "");
		this.BUF_READ_POINTER.build();
		this.BUF_READ_POINTER.add_hdl_path('{
            '{"i_ring_buffer_registers.i_ring_buffer_registers_BUF_READ_POINTER.READ_POINTER", 0, 16}
		});

		this.BUF_WRITE_POINTER = ral_reg_ring_buffer_registers_BUF_WRITE_POINTER::type_id::create("BUF_WRITE_POINTER",,get_full_name());
		if(this.BUF_WRITE_POINTER.has_coverage(UVM_CVR_REG_BITS))
			this.BUF_WRITE_POINTER.cg_bits.option.name = {get_name(), ".BUF_WRITE_POINTER_bits"};
		this.BUF_WRITE_POINTER.configure(get_block(), this, "");
		this.BUF_WRITE_POINTER.build();
		this.BUF_WRITE_POINTER.add_hdl_path('{
            '{"i_ring_buffer_registers.i_ring_buffer_registers_BUF_WRITE_POINTER.WRITE_POINTER", 0, 16}
		});

		this.BUF_VALID_POINTER = ral_reg_ring_buffer_registers_BUF_VALID_POINTER::type_id::create("BUF_VALID_POINTER",,get_full_name());
		if(this.BUF_VALID_POINTER.has_coverage(UVM_CVR_REG_BITS))
			this.BUF_VALID_POINTER.cg_bits.option.name = {get_name(), ".BUF_VALID_POINTER_bits"};
		this.BUF_VALID_POINTER.configure(get_block(), this, "");
		this.BUF_VALID_POINTER.build();
		this.BUF_VALID_POINTER.add_hdl_path('{
            '{"i_ring_buffer_registers.i_ring_buffer_registers_BUF_VALID_POINTER.VALID_POINTER", 0, 16}
		});

	endfunction : build

	virtual function void map(uvm_reg_map    mp,
	                          uvm_reg_addr_t offset);
	  mp.add_reg(BUF_VALID_COUNT, offset+`UVM_REG_ADDR_WIDTH'h0);
	  mp.add_reg(BUF_FREE, offset+`UVM_REG_ADDR_WIDTH'h2);
	  uvm_resource_db#(bit)::set({"REG::", BUF_FREE.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(bit)::set({"REG::", BUF_FREE.get_full_name()}, "NO_REG_HW_RESET_TEST", 1, this);
	  mp.add_reg(BUF_READ_POINTER, offset+`UVM_REG_ADDR_WIDTH'h8);
	  uvm_resource_db#(bit)::set({"REG::", BUF_READ_POINTER.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(bit)::set({"REG::", BUF_READ_POINTER.get_full_name()}, "NO_REG_HW_RESET_TEST", 1, this);
	  mp.add_reg(BUF_WRITE_POINTER, offset+`UVM_REG_ADDR_WIDTH'h9);
	  uvm_resource_db#(bit)::set({"REG::", BUF_WRITE_POINTER.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(bit)::set({"REG::", BUF_WRITE_POINTER.get_full_name()}, "NO_REG_HW_RESET_TEST", 1, this);
	  mp.add_reg(BUF_VALID_POINTER, offset+`UVM_REG_ADDR_WIDTH'hA);
	  uvm_resource_db#(bit)::set({"REG::", BUF_VALID_POINTER.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(bit)::set({"REG::", BUF_VALID_POINTER.get_full_name()}, "NO_REG_HW_RESET_TEST", 1, this);

	endfunction

	virtual function void set_offset(uvm_reg_map    mp,
	                                   uvm_reg_addr_t offset);
	  BUF_VALID_COUNT.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h0);
	  BUF_FREE.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h2);
	  BUF_READ_POINTER.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h8);
	  BUF_WRITE_POINTER.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'h9);
	  BUF_VALID_POINTER.set_offset(mp, offset+`UVM_REG_ADDR_WIDTH'hA);

	endfunction

	`uvm_object_utils(ral_regfile_ring_buffer_registers)
endclass : ral_regfile_ring_buffer_registers




class ral_block_buf_ctrl extends uvm_reg_block;
	rand ral_regfile_ring_buffer_registers ring_buffer_registers;

	function new(string name = "buf_ctrl");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 2, UVM_LITTLE_ENDIAN, 0);
      this.ring_buffer_registers = ral_regfile_ring_buffer_registers::type_id::create("ring_buffer_registers",,get_full_name());
      this.ring_buffer_registers.configure(this, null, "");
      this.ring_buffer_registers.build();
      this.ring_buffer_registers.map(default_map, `UVM_REG_ADDR_WIDTH'h0);
   endfunction : build

	`uvm_object_utils(ral_block_buf_ctrl)

endclass : ral_block_buf_ctrl


class ral_sys_device_registers extends uvm_reg_block;

   rand ral_block_info Info;
   rand ral_block_supply Supply;
   rand ral_block_timebase Timebase;
   rand ral_block_interrupt Interrupt;
   rand ral_block_ring_buffer_interrupt Buffer_IRQs;
   rand ral_block_spi SPI;
   rand ral_block_dsi3 DSI_common;
   rand ral_block_otp_reader OTP_CTRL;
   rand ral_block_dsi3_trim DSI_TRIMMING[2];
   rand ral_block_dsi3_block DSI[2];
   rand ral_block_buf_ctrl SPI_CMD_STAT;
   rand ral_block_buf_ctrl DSI_CMD_STAT[2];
   rand ral_block_buf_ctrl DSI_CRM_STAT[2];
   rand ral_block_buf_ctrl DSI_PDCM_STAT[2];

	function new(string name = "device_registers");
		super.new(name);
	endfunction: new

	function void build();
      this.default_map = create_map("", 0, 2, UVM_LITTLE_ENDIAN, 0);
      this.Info = ral_block_info::type_id::create("Info",,get_full_name());
      this.Info.configure(this, "i_main_control");
      this.Info.build();
      this.default_map.add_submap(this.Info.default_map, `UVM_REG_ADDR_WIDTH'h0);
      this.Supply = ral_block_supply::type_id::create("Supply",,get_full_name());
      this.Supply.configure(this, "i_main_control");
      this.Supply.build();
      this.default_map.add_submap(this.Supply.default_map, `UVM_REG_ADDR_WIDTH'h0);
      this.Timebase = ral_block_timebase::type_id::create("Timebase",,get_full_name());
      this.Timebase.configure(this, "i_timebase");
      this.Timebase.build();
      this.default_map.add_submap(this.Timebase.default_map, `UVM_REG_ADDR_WIDTH'h0);
      this.Interrupt = ral_block_interrupt::type_id::create("Interrupt",,get_full_name());
      this.Interrupt.configure(this, "i_main_control");
      this.Interrupt.build();
      this.default_map.add_submap(this.Interrupt.default_map, `UVM_REG_ADDR_WIDTH'h0);
      this.Buffer_IRQs = ral_block_ring_buffer_interrupt::type_id::create("Buffer_IRQs",,get_full_name());
      this.Buffer_IRQs.configure(this, "i_buffers");
      this.Buffer_IRQs.build();
      this.default_map.add_submap(this.Buffer_IRQs.default_map, `UVM_REG_ADDR_WIDTH'h0);
      this.SPI = ral_block_spi::type_id::create("SPI",,get_full_name());
      this.SPI.configure(this, "i_spi");
      this.SPI.build();
      this.default_map.add_submap(this.SPI.default_map, `UVM_REG_ADDR_WIDTH'h0);
      this.DSI_common = ral_block_dsi3::type_id::create("DSI_common",,get_full_name());
      this.DSI_common.configure(this, "i_dsi3");
      this.DSI_common.build();
      this.default_map.add_submap(this.DSI_common.default_map, `UVM_REG_ADDR_WIDTH'h0);
      this.OTP_CTRL = ral_block_otp_reader::type_id::create("OTP_CTRL",,get_full_name());
      this.OTP_CTRL.configure(this, "i_main_control.i_main_fsm.i_otp_reader");
      this.OTP_CTRL.build();
      this.default_map.add_submap(this.OTP_CTRL.default_map, `UVM_REG_ADDR_WIDTH'h0);
      foreach (this.DSI_TRIMMING[i]) begin
         int J = i;
         this.DSI_TRIMMING[J] = ral_block_dsi3_trim::type_id::create($psprintf("DSI_TRIMMING[%0d]", J),,get_full_name());
         this.DSI_TRIMMING[J].configure(this, $psprintf("i_dsi3.generate_dsi3_blocks[%0d].i_dsi3_block", J));
         this.DSI_TRIMMING[J].build();
         this.default_map.add_submap(this.DSI_TRIMMING[J].default_map, `UVM_REG_ADDR_WIDTH'h10+J*`UVM_REG_ADDR_WIDTH'h2);
      end
      foreach (this.DSI[i]) begin
         int J = i;
         this.DSI[J] = ral_block_dsi3_block::type_id::create($psprintf("DSI[%0d]", J),,get_full_name());
         this.DSI[J].configure(this, $psprintf("i_dsi3.generate_dsi3_blocks[%0d].i_dsi3_block", J));
         this.DSI[J].build();
         this.default_map.add_submap(this.DSI[J].default_map, `UVM_REG_ADDR_WIDTH'hA0+J*`UVM_REG_ADDR_WIDTH'h20);
      end
      this.SPI_CMD_STAT = ral_block_buf_ctrl::type_id::create("SPI_CMD_STAT",,get_full_name());
      this.SPI_CMD_STAT.configure(this, "i_buffers.i_command_buffer");
      this.SPI_CMD_STAT.build();
      this.default_map.add_submap(this.SPI_CMD_STAT.default_map, `UVM_REG_ADDR_WIDTH'h100);
      foreach (this.DSI_CMD_STAT[i]) begin
         int J = i;
         this.DSI_CMD_STAT[J] = ral_block_buf_ctrl::type_id::create($psprintf("DSI_CMD_STAT[%0d]", J),,get_full_name());
         this.DSI_CMD_STAT[J].configure(this, $psprintf("i_buffers.generate_dsi_buffers[%0d].i_dsi3_command_buffer", J));
         this.DSI_CMD_STAT[J].build();
         this.default_map.add_submap(this.DSI_CMD_STAT[J].default_map, `UVM_REG_ADDR_WIDTH'h110+J*`UVM_REG_ADDR_WIDTH'h10);
      end
      foreach (this.DSI_CRM_STAT[i]) begin
         int J = i;
         this.DSI_CRM_STAT[J] = ral_block_buf_ctrl::type_id::create($psprintf("DSI_CRM_STAT[%0d]", J),,get_full_name());
         this.DSI_CRM_STAT[J].configure(this, $psprintf("i_buffers.generate_dsi_buffers[%0d].i_dsi3_crm_data_buffer", J));
         this.DSI_CRM_STAT[J].build();
         this.default_map.add_submap(this.DSI_CRM_STAT[J].default_map, `UVM_REG_ADDR_WIDTH'h130+J*`UVM_REG_ADDR_WIDTH'h10);
      end
      foreach (this.DSI_PDCM_STAT[i]) begin
         int J = i;
         this.DSI_PDCM_STAT[J] = ral_block_buf_ctrl::type_id::create($psprintf("DSI_PDCM_STAT[%0d]", J),,get_full_name());
         this.DSI_PDCM_STAT[J].configure(this, $psprintf("i_buffers.generate_dsi_buffers[%0d].i_dsi3_pdcm_data_buffer", J));
         this.DSI_PDCM_STAT[J].build();
         this.default_map.add_submap(this.DSI_PDCM_STAT[J].default_map, `UVM_REG_ADDR_WIDTH'h150+J*`UVM_REG_ADDR_WIDTH'h10);
      end
	  uvm_config_db #(uvm_reg_block)::set(null,"","RegisterModel_Debug",this);
	endfunction : build

	`uvm_object_utils(ral_sys_device_registers)
endclass : ral_sys_device_registers



`endif

endpackage
