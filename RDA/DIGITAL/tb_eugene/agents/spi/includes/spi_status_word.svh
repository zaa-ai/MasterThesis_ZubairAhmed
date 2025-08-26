/**
 * SPI status word flags 
 */
typedef enum {
	/**
	 * any hardware error occurred 
	 */	 
	HE=15,
	/**
	 * any command queue or data buffer fill warning is active 
	 */
	BF=14, 
	/**
	 * previous SPI command had a SPI command error
	 */
	SCI=13,
	/**
	 * CRC error on previous SPI command
	 */
	SPICRC=12,
	/**
	 * No TDMA scheme defined
	 */
	NT1=11,
	NT0=10,
	/**
	 * PDCM data buffer contains unread data
	 */
	PD1=3,
	PD0=2,
	/**
	 * CRM data buffer contains unread data
	 */
	CR1=1,
	CR0=0
} spi_status_word_flags;

/**
 * Class: spi_status_word
 * 
 * Contains IC status information of SPI output
 */
class spi_status_word extends flags_container#(spi_status_word_flags);
	
	`uvm_object_utils(spi_status_word)
	
	covergroup cov_status_word;
		option.per_instance = 0;
		coverpoint flags[HE];
		coverpoint flags[BF];
		coverpoint flags[SCI];
		coverpoint flags[SPICRC];
		coverpoint flags[NT1];
		coverpoint flags[NT0];
		coverpoint flags[PD1];
		coverpoint flags[PD0];
		coverpoint flags[CR1];
		coverpoint flags[CR0];
	endgroup
	
	/************************ Methods declarations ************************/
	function new(string name="IC status" );
		super.new(name);
		cov_status_word = new();
	endfunction
	
	virtual function void do_copy(uvm_object rhs);
		spi_status_word rhs_;
		if (!$cast(rhs_, rhs)) `uvm_fatal(get_type_name(), "Cast of rhs object failed")
		super.do_copy(rhs);
		this.flags = rhs_.flags;
	endfunction
	
	virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
		bit result;
		spi_status_word rhs_;
		if (!$cast(rhs_, rhs)) begin
			`uvm_fatal(get_type_name(), "Cast of rhs object failed")
		end
		result = super.do_compare(rhs, comparer);
		result &= comparer.compare_field("status word", get_values(), rhs_.get_values(), 16);
		this.check_values(rhs_.get_values());
		return result;
	endfunction
	
	virtual function void set(logic [15:0] data);
		set_values(data);
	endfunction
	
	virtual function logic[15:0] get();
		return 16'(get_values());
	endfunction
		
	virtual function void sample_cov();
		cov_status_word.sample();
	endfunction
		
	function void do_record(uvm_recorder recorder);
		super.do_record(recorder);	
		`uvm_record_field("flags", convert2string_others())
	endfunction
	
	virtual function string convert2string_others();
		string s = "";
		spi_status_word_flags iterator = iterator.first();
		do begin
			s = (flags[iterator] == 1'b1) ? {s, $sformatf("|%s", iterator.name())} : {s, "|-"};
			iterator = iterator.next();
		end while (iterator != iterator.first());
		return s;
	endfunction
		
	virtual function void check_status_flags(spi_status_word_flags status_flags[$]);
		flags_container #(spi_status_word_flags) flags = new();
		flags.set_flags(status_flags);
		void'(check_flags_are_equal(flags, $sformatf("Unexpected SPI status word flags")));
	endfunction
endclass
