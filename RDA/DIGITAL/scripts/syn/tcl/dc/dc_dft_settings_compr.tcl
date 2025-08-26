if {$OPTIMIZATION_FLOW != "rtm_exp"} {
    #############################################################################
    # DFTMAX Compression Configuration 
    #############################################################################

    # Starting with Reference Methodology Scripts version G-2012.06
    # DFTMAX Compression is enabled in the default flow configuration.

    # Comment out the following command or change the option to "-scan_compression disable"
    # to disable DFTMAX Compression during DFT insertion.

    set_dft_configuration -scan_compression enable

    # DFTMAX Compression Options:
    # 
    #  -min_power true
    #     This specifies that compressor inputs are to be gated for functional power
    #     saving. 
    #     It also reduces glitching during functional and capture operations
    #     Default for -min_power option is false. Recommend that you set this to
    #     true. 
    #
    #  -xtolerance: value is set to tool default. 
    #     Specify "high" to generate DFTMAX compression architecture that has 100% X-tolerance.
    #
    #  -minimum_compression: tool default is a target compression ratio of 10,
    #
    #  -location <compressor_decompressor_location>
    #      Specifies the instance name in which the compressor and decompressor 
    #      will be instantiated.
    #      The default location is the top level of the current design.
    # 
    # For details on these and other DFTMAX compression options, please refer to the
    # TestMAX DFT User Guide, Chapter 18, "Using DFTMAX Compression"
    # and Chapter 20, "Managing X Values in Scan Compression".
     
    set_scan_compression_configuration -xtolerance high -min_power true;

    # Use the following to define the test-mode signal to be used for DFTMAX  
    # compression. Ensure that that test mode signals to be used for clockgating have 
    # been configured with set_dft_signal -usage clock_gating.

    # set_dft_signal -view spec -type TestMode -port scan_compression_enable


    #############################################################################
    # Shift Power Groups Configuration
    #############################################################################

    # Starting L-2016.03-SP2 release, DFTMAX Compression supports insertion of Shift Power Groups
    # to reduce power consumption during scan shift.
    # Please refer to the TestMAX DFT User Guide, Chapter 18,
    # "Reducing Power Consumption in Compressed Scan Designs", 
    # "Reducing Scan Shift Power Using Shift Power Groups" section.
    # 
    # To insert Shift Power Groups, do the following:
    # 
    # If you do not insert On-Chip Clocking (OCC), specify:
   
    # set_scan_compression_configuration
    # -shift_power_groups true
    # -shift_power_chain_length <l> | -shift_power_chain_ratio <r>
    # -shift_power_clock <clk>
    # 
    # Specify only one of -shift_power_chain_length or -shift_power_chain_ratio but not both.
    # 
    # Specify the signal to disable the shift power groups
      
    # set_dft_signal -view spec -type TestControl -port <p>
    # set_scan_compression_configuration -shift_power_disable <p>
      
    # Specify the scan-in and scan-out signals to use for the Shift Power Control chain
    # Note the name of the chain specified in the set_scan_path command. This name needs to be specified
    # in TetraMAX set_drc command (refer to TMAX-RM for details) 
    # 
    # set_scan_path shift_power_control_chain -class spc \
    # -scan_data_in SPC_IN \
    # -scan_data_out SPC_OUT \ 
    # -test_mode all
    # 
    # 
    # If you insert On-Chip Clocking (OCC), then specify:
    # 
    # set_scan_compression_configuration
    # -shift_power_groups true
    # -shift_power_chain_length <l> | -shift_power_chain_ratio <r>
    # 
    # Specify only one of -shift_power_chain_length or -shift_power_chain_ratio but not both.
    # Do not specify -shift_power_clock option. In OCC flows, the clock chain clock is automatically used.
     
    # Specify an external clock chain if you plan to use On-Chip Clocking together with Shift Power Control chain
    
    # set_scan_path OCC -class occ \
    # -scan_data_in  OCC_IN \
    # -scan_data_out  OCC_OUT \
    # -test_mode all



    #############################################################################
    # DFT Pipelined Scan Data Configuration
    #############################################################################

   # Use set_pipeline_scan_data_configuration to control how Pipelined Scan Data Registers
   # should be inserted

   # We recommend that you use the head_scan_flop true option to create head pipeline registers that 
   # hold their state during the capture cycle. 
   # You should also constrain ScanEnable to its inactive value during capture in ScanCompression modes


   # Note: if you select the head_scan_flop true option, you can share the scan clock with the head_pipeline_clock. 
   #  If you do not select head_scan_flop true option, then you must use a dedicated head pipeline clock.


    # Options:
    #  -head_scan_flop true
    #  -head_pipeline_clock  <name of clock for head pipeline registers>
    #  -tail_pipeline_clock  <name of clock for tail pipeline registers>
    #  -head_pipeline_stages <desired number of head pipeline stages>
    #  -tail_pipeline_stages <desired number of tail pipeline stages>

    # Example:

    # set_pipeline_scan_data_configuration -head_pipeline_clock <clock_name> \
    #   -tail_pipeline_clock <clock_name> \
    #   -head_scan_flop true \
    #   -head_pipeline_stages <x> \
    #   -tail_pipeline_stages <y
    #############################################################################
    # DFT Additional Setup
    #############################################################################

    # Add any additional design-specific DFT constraints here

    #############################################################################
    # Defining Multiple Test modes
    #############################################################################
    
    # Use the define_test_mode command to define additional test modes that you wish to build.
    #
    # If you have enabled DFTMAX or DFTMAX Ultra Compression, the tool will build two test modes by 
    # default: ScanCompression_mode and Internal_scan. 
    #
    # If you wish to override the default test modes, you need to define the purpose of that test mode, 
    # then use the -base_mode and -test_mode options of set_scan_compression_configuration or 
    # set_streaming_compression_configuration command to define the correspondence between the two modes.
    #  
    # Design Compiler shell switches to that test mode after a define_test_mode command.
    #
    # To define DFT signals or scan configuration for a particular test mode, specify -test_mode option 
    # for each modes that you have defined.
    #  
    # At top level, use define_test_mode -target to specify the block level test mode that should be active in 
    # that mode. Please refer to the TestMAX DFT User Guide Chapter 18, 
    # "Using DFTMAX Compression", "DFTMAX Scan Compression and Multiple Test Modes" section.
    #
    # Block level Example with DFTMAX Compression:
    # Defining the test modes at block level
    # define_test_mode MY_internal_scan -usage scan 
    # define_test_mode MY_compression -usage scan_compression
    # 
    # Specifying the DFT signals for each mode using the -test_mode option:
    # set_dft_signal -port scan_input_port_1  -type ScanDataIn  -view spec -test_mode MY_internal_scan
    # set_dft_signal -port scan_input_port_1  -type ScanDataIn  -view spec -test_mode MY_compression
    # set_dft_signal -port scan_output_port_1 -type ScanDataOut -view spec -test_mode MY_internal_scan
    # set_dft_signal -port scan_output_port_1 -type ScanDataOut -view spec -test_mode MY_compression
    #
    # Specifying the scan configuration for each test mode:
    # set_scan_configuration -chain_count <scan mode chain count> -test_mode MY_internal_scan
    # set_scan_configuration -chain_count <compression mode chain count> -test_mode MY_compression
    #
    # Specify the correspondence between user-defined internal scan mode and user-defined compression mode
    # set_scan_compression_configuration -chain_count <compression mode chain count>  -base_mode MY_internal_scan -test_mode MY_compression

    # Top level example with DFTMAX Compression:
    # define_test_mode MY_top_internal_scan -usage scan -target [list core1:MY_internal_scan core2:MY_internal_scan top]
    # define_test_mode MY_top_compression -usage scan_compression -target [list core1:MY_compression core2:MY_compression top]
    #
}
