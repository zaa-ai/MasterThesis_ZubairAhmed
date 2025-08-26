

function logic[31:0] create_symbol_mask(int symbol_count);
	logic[31:0] mask;
	int unsigned tmp;
	int i;
	mask  = 32'd0;
	tmp = 0;
	if(symbol_count > 8) return 32'hFFFF_FFFF;
	for(i=0; i < symbol_count; i++) begin
		tmp = int'(4'hF << (4 * (8 - i - 1)));
		mask += 32'(tmp);
	end
	return mask;
endfunction
