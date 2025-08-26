
# some reports to align output of check_syn_synopsys_errors.csh
puts "Flip Flops, which are not part of a scan chain:"
set scFF {}
foreach chain_name [get_scan_chain_names] {
  append_to_collection -unique scFF [get_scan_cells_of_chain -chain $chain_name]
}
set no_scFF [remove_from_collection [get_flat_cells * -filter "is_a_flip_flop == true"] $scFF]
foreach_in_collection inst $no_scFF {
  puts "  [get_object_name $inst]"
}
puts "Total: [sizeof_collection $no_scFF]"

report_timing -scenarios [all_active_scenarios]
report_clock_gating -ungated -nosplit > ${REPORTS_DIR}/${DCRM_FINAL_CLOCK_GATING_REPORT}
