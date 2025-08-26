#!/usr/bin/env ruby
inside_test_setup = 0
inside_all_ports = 0

File.open(ARGV[0], 'r') { |f|
while line = f.gets
	# When reaching test_setup section set flag
	if line =~ /"test_setup"/
	inside_test_setup = 1 
	end
	# When reaching all_ports section set flag
	if line =~ /"all_ports"/
	inside_all_ports = 1
	end

	#remove the preceeding I_ and O_ from Pins
	line.sub!("I_", "")
	line.sub!("O_","")
	#rename Pins to T2000 interface pins and set BiDi pin SYNCB HighZ
	line.sub!("SCK","SCK__MDMA_DPIN")
    line.sub!("BFWB","BFWB_TCK__MDMA_DPIN")
	line.sub!("RESB","RESB__MDMA_DPIN")
	line.sub!("RFC","RFC__MDMA_DPIN")
	line.sub!("SDI","MOSI__MDMA_DPIN")
	line.sub!("SDO","MISO__MDMA_DPIN")
	line.sub!("DAB","DAB_TMS__MDMA_DPIN")
	line.sub!("INTB","INTB_TDO__MDMA_DPIN")
	line.sub!("CSB","CSB__MDMA_DPIN")
	# In all ports section SYNCB is two times existend because it was I_SYNCB and O_SYNCB
	# so we delete only one line (the first one) with SYNCB stuff
	if inside_all_ports == 1 && line =~ /"SYNCB"/
	line.sub!(/(\s*\+\s)("SYNCB")/,"")
	# First occurence of SYNCB stuff is replaced with empty line
	# so we reset flag to leave the second one inside.
	inside_all_ports = 0
	end
	# When we are in test_setup section, we dont wanna delete the lines where SYNCB is set to 0
	# because its SYNCB is TDI and is needed for test setup.
	if inside_test_setup == 0
		line.sub!(/("SYNCB"\s=\s)(0);/,"")
	end
	line.sub!(/("SYNCB"\s=\s)(X);/,"\\1Z;") 
	line.sub!(/("SYNCB"\s=\s)(N);/,"") 
	line.sub!(/("SYNCB"\s)(In);/,"") 
	line.sub!(/("SYNCB"\s)(Out);/,"\\1InOut;") 
	line.sub!("SYNCB","SYNCB_TDI__MDMA_DPIN")

# output lines ...
	puts line
end
}

