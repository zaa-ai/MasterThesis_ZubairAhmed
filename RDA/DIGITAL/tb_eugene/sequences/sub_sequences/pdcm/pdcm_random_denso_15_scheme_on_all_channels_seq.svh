class pdcm_random_denso_15_scheme_on_all_channels_seq extends pdcm_random_denso_scheme_on_all_channels_seq;
	
	`uvm_object_utils(pdcm_random_denso_15_scheme_on_all_channels_seq)
	
	function new(string name = "");
		super.new("pdcm_random_denso_15_scheme_on_all_channels");
	endfunction
	
	virtual function tdma_scheme_pdcm create_tdma_scheme();
		tdma_scheme_pdcm_denso_15 denso_scheme = new();
		return denso_scheme;
	endfunction
endclass