
set_app_var droute_fillDataType 127

foreach ref_name {slp_b_tsmc180bcd50_4kx12_cm16d_ab_r20 ips_tsmc180bcd50_p1r_ad SRAM_3072X23U18 } {
  set inst [get_cells -hierarchical -filter "ref_name == $ref_name" *]
  set inst_llx  [get_attribute $inst bbox_llx]
  set inst_lly  [get_attribute $inst bbox_lly]
  set inst_urx  [get_attribute $inst bbox_urx]
  set inst_ury  [get_attribute $inst bbox_ury]
  create_route_guide -coordinate [list $inst_llx $inst_lly $inst_urx $inst_ury]     \
                     -no_signal_layers {METAL1 METAL2 METAL3 METAL4}
}
