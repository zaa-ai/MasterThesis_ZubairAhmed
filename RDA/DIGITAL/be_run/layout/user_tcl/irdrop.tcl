
remove_fp_virtual_pad -all

# Creates virtual power or ground pads for power network analysis and power network synthesis.
# VDD
create_fp_virtual_pad \
    -nets VDD \
    -layer METAL4 \
    -point {1916 1755.000}

#create_fp_virtual_pad \
    -nets VDD \
    -layer METAL4 \
    -point {931.000 960.000}

#create_fp_virtual_pad \
    -nets VDD \
    -layer METAL4 \
    -point {931.000 1135.000}

#create_fp_virtual_pad \
    -nets VDD \
    -layer METAL4 \
    -point {60.000 905.000}

    # VSS
create_fp_virtual_pad \
    -nets VSS \
    -layer METAL5 \
    -point {1888 1755}

#create_fp_virtual_pad \
    -nets VSS \
    -layer METAL5 \
    -point {0.000 587.0}

#create_fp_virtual_pad \
    -nets VSS \
    -layer METAL5 \
    -point {0.000 587.0}


analyze_fp_rail \
	-use_pins_as_pads \
	-nets {VSS VDD} \
	-voltage_supply 1.8 \
	-power_budget 18 \
	-output_directory pna

	