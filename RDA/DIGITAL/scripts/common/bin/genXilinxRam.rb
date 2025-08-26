#!/usr/bin/env ruby

#param0: identifier (including file-path ... example: ../src/myname)
#param1: init hex file

def num2width(num)

	ret = 1
	num /= 2
	while num != 0 do
		ret += 1
		num /= 2
	end
	ret
end


identifier      = ARGV[0];
init_hex_file   = ARGV[1];

if identifier =~ /\/([^\/]+)$/
	identifier_name = $1
else
	identifier_name = identifier
end

hex_file_content = IO.readlines(init_hex_file)

data_width = (hex_file_content[0].strip.length + 1) / 2  # number of bytes
addr_width = num2width(hex_file_content.length-1)

0.upto(data_width-1) { |n|
	system("genXilinxRam8.rb #{identifier}_xsram_#{n}.v #{identifier_name}_xsram_#{n} #{addr_width} #{init_hex_file} #{data_width-(1+n)} 0")
}

content = ""
content += <<VLOG

`timescale 1ns/1ns
`include "tech.v"

module #{identifier_name}_xsram(
		input             CLK,  // clk
		input             CEN,  // chip enable
		input       [#{data_width-1}:0] WEN,  // bytewise write enable  
		input      [#{addr_width-1}:0] A,    // address
		input      [#{8*data_width-1}:0] D,    // data in
		output     [#{8*data_width-1}:0] Q     // data out
	);

`ifdef target_technology_FPGA

VLOG

0.upto(data_width-1) { |n|
content += <<VLOG
	#{identifier_name}_xsram_#{n} #{identifier_name}_xsram_#{n}_inst(
		.clk      (CLK),
		.sp_write (!CEN & !WEN[#{n}]),
		.sp_addr  (A),
		.sp_din   (D[8 * #{n} +: 8]),
		.sp_dout  (Q[8 * #{n} +: 8])
	);

VLOG
}

content += <<VLOG
`else

	// SIMULATION MODEL ONLY => NOT APPLICABLE FOR ASIC SYNTHESIS !

	reg [#{8*data_width-1}:0] ram [0:#{hex_file_content.length-1}];

	reg [#{addr_width-1}:0] raddr;
	
	reg rcen;

	always @(posedge CLK)
	begin
		if (!CEN) begin
VLOG

0.upto(data_width-1) { |n|
content += <<VLOG
			if (!WEN[#{n}]) ram[A][8 * #{n} +: 8] <= D[8 * #{n} +: 8];
VLOG
}

content += <<VLOG
		end
		raddr <= A;
		rcen <= CEN;
	end

	assign Q = 
// synopsys translate_off
		rcen ? {#{8*data_width}{1'bz}} : 
// synopsys translate_on
		ram[raddr];

// synopsys translate_off
	initial begin
VLOG

0.upto(hex_file_content.length-1) { |n|
content += <<VLOG
		ram[#{n}] = #{8*data_width}'h#{hex_file_content[n].strip};
VLOG
}

content += <<VLOG
	end
// synopsys translate_on

`endif

endmodule

VLOG

File.open("#{identifier}_xsram.v", "w") { |file|
   file << content
}

