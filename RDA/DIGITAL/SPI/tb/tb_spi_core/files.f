+incdir+${UVM_HOME}/src
+incdir+${UVM_HOME}/src/vcs
${UVM_HOME}/src/uvm_pkg.sv
${UVM_HOME}/src/vcs/uvm_custom_install_vcs_recorder.sv
+incdir+${SYNOPSYS}/dw/sim_ver/

+incdir+${DESIGN}/${DIGITAL}/config
+incdir+${DESIGN}/${DIGITAL}/tb
+incdir+${DESIGN}/${DIGITAL}/tb_easier_uvm/dut
+incdir+${DESIGN}/${DIGITAL}/tb_easier_uvm/dut/tdma_scheme
+incdir+${DESIGN}/${DIGITAL}/edf_registers
+incdir+${DESIGN}/${DIGITAL}/COMMON_LIB/rtl
+incdir+${SVUNIT_HOME}/svunit_base
+incdir+${SVUNIT_HOME}/svunit_base/uvm-mock
+incdir+${DESIGN}/${DIGITAL}/tb_easier_uvm/generated_testbench/tb/spi/sv
+incdir+${DESIGN}/${DIGITAL}/tb_easier_uvm/generated_testbench/tb/include/spi
+incdir+${DESIGN}/${DIGITAL}/tb_easier_uvm/include/
+incdir+${DESIGN}/${DIGITAL}/tb_easier_uvm/dut/
+incdir+${DESIGN}/${DIGITAL}/SPI/tb/tb_spi_core/uvm_environment/

// DEFINES
${SVUNIT_HOME}/svunit_base/svunit_defines.svh

// PACKAGES
${DESIGN}/${DIGITAL}/tb/common_test_pkg.sv
${DESIGN}/${DIGITAL}/tb_easier_uvm/registers/addresses_pkg.sv
${DESIGN}/${DIGITAL}/tb_easier_uvm/dut/common_pkg.sv
${SVUNIT_HOME}/svunit_base/svunit_pkg.sv
${SVUNIT_HOME}/svunit_base/uvm-mock/svunit_uvm_mock_pkg.sv
${DESIGN}/${DIGITAL}/rtl/project_pkg.sv
${DESIGN}/${DIGITAL}/DSI3_MASTER/rtl/dsi3_pkg.sv
${DESIGN}/${DIGITAL}/tb_easier_uvm/include/common_env_pkg.svh
${DESIGN}/${DIGITAL}/tb_easier_uvm/generated_testbench/tb/spi/sv/spi_pkg.sv
${DESIGN}/${DIGITAL}/SPI/tb/tb_spi_core/spi_unit_test_pkg.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_implementation_pkg.sv

// INTERFACES
${DESIGN}/${DIGITAL}/SPI/rtl/spi_int_if.sv
${DESIGN}/${DIGITAL}/tb_easier_uvm/generated_testbench/tb/spi/sv/spi_if.sv

// Modules
${DESIGN}/${DIGITAL}/SPI/rtl/buffer_writer_access_arbiter.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_tx_fifo.sv
${DESIGN}/${DIGITAL}/SPI/rtl/spi_core.sv
${DESIGN}/${DIGITAL}/SPI/tb/tb_spi_core/spi_core_test.sv
${DESIGN}/${DIGITAL}/SPI/tb/tb_spi_core/buffer_writer_access_arbiter_test.sv
${DESIGN}/${DIGITAL}/SPI/tb/tb_spi_core/spi_testsuite.sv
${DESIGN}/${DIGITAL}/SPI/tb/tb_spi_core/spi_testrunner.sv
