function void post_randomize();
	value = convert2logic(_val);
endfunction : post_randomize

static function digital_signal_t convert2enum(logic in);
	digital_signal_t _return_val;
	case (in)
		1'b1: 		_return_val = H;
		1'b0: 		_return_val = L;
		1'bz: 		_return_val = Z;
		1'bx: 		_return_val = X;
		default: 	_return_val = X;
	endcase
	return _return_val;
endfunction : convert2enum

static function logic convert2logic(digital_signal_t in);
	logic _return_val;
	case (in)
		L, H:		_return_val = 1'(in);	
		X: 			_return_val = 1'bx;	
		Z: 			_return_val = 1'bz;	
		default:	_return_val = 1'bx;
	endcase
	return _return_val;
endfunction : convert2logic
