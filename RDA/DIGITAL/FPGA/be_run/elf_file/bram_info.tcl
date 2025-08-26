#create_property bmm_info_memory_device cell -type string

#set_property bmm_info_memory_device {[ 3: 0][0:8191]} [get_cells -hierarchical -filter { NAME =~  "*sync_sram_inst/sync_sram_slice_inst[3]/ram_reg_0" && PRIMITIVE_TYPE =~ BMEM.bram.* } ]
#set_property bmm_info_memory_device {[ 7: 4][0:8191]} [get_cells -hierarchical -filter { NAME =~  "*sync_sram_inst/sync_sram_slice_inst[3]/ram_reg_1" && PRIMITIVE_TYPE =~ BMEM.bram.* } ]
#set_property bmm_info_memory_device {[ 11: 8][0:8191]} [get_cells -hierarchical -filter { NAME =~  "*sync_sram_inst/sync_sram_slice_inst[2]/ram_reg_0" && PRIMITIVE_TYPE =~ BMEM.bram.* } ]
#set_property bmm_info_memory_device {[ 15: 12][0:8191]} [get_cells -hierarchical -filter { NAME =~  "*sync_sram_inst/sync_sram_slice_inst[2]/ram_reg_1" && PRIMITIVE_TYPE =~ BMEM.bram.* } ]
#set_property bmm_info_memory_device {[ 19: 16][0:8191]} [get_cells -hierarchical -filter { NAME =~  "*sync_sram_inst/sync_sram_slice_inst[1]/ram_reg_0" && PRIMITIVE_TYPE =~ BMEM.bram.* } ]
#set_property bmm_info_memory_device {[ 23: 20][0:8191]} [get_cells -hierarchical -filter { NAME =~  "*sync_sram_inst/sync_sram_slice_inst[1]/ram_reg_1" && PRIMITIVE_TYPE =~ BMEM.bram.* } ]
#set_property bmm_info_memory_device {[ 27: 24][0:8191]} [get_cells -hierarchical -filter { NAME =~  "*sync_sram_inst/sync_sram_slice_inst[0]/ram_reg_0" && PRIMITIVE_TYPE =~ BMEM.bram.* } ]
#set_property bmm_info_memory_device {[ 31: 28][0:8191]} [get_cells -hierarchical -filter { NAME =~  "*sync_sram_inst/sync_sram_slice_inst[0]/ram_reg_1" && PRIMITIVE_TYPE =~ BMEM.bram.* } ]