remove_unconnected_ports -blast [get_cell -hier] -blast_buses

verify_zrt_route
verify_lvs -max_error 1000 
verify_lvs -check_short_locator 
