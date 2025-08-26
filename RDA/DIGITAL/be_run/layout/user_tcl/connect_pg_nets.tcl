derive_pg_connection 	-power_net $MW_POWER_NET \
			-power_pin $MW_POWER_PORT \
			-ground_net $MW_GROUND_NET \
			-ground_pin $MW_GROUND_PORT

derive_pg_connection -power_net VCC -power_pin VCC -reconnect 

derive_pg_connection -ground_net PSUB   -ground_pin VSS
derive_pg_connection -power_net VDD_NBL -power_pin VDD_NBL
derive_pg_connection -ground_net PSUB   -ground_pin PSUB -cells [get_flat_cells -all i_digital_iso]
derive_pg_connection -ground_net VSS    -ground_pin VSS -cells [get_flat_cells -all i_digital_iso]
derive_pg_connection -power_net VDD     -power_pin VDD -cells  [get_flat_cells -all i_digital_iso]
