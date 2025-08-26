#!/bin/csh
set TARGET_PATH = $DESIGN/$DIGITAL/tb_eugene/registers
echo "#####   generate register model   #####"
ralgen -l sv -uvm -c s -t device_registers $TARGET_PATH/registers.ral -o $TARGET_PATH/register_model -single_plan  -flds_out_reg none
echo "#####   generate test register model   #####"
ralgen -l sv -uvm -c s -t jtag_test_registers $TARGET_PATH/test_registers.ral -o $TARGET_PATH/test_register_model -single_plan -flds_out_reg none

echo "#####   removing LINT warnings   #####"
sed -i 's/iff[(]m_be[)]/iff\(m_be \!= 0\)/g' $TARGET_PATH/register_model.sv
sed -i 's/iff[(]m_be[)]/iff\(m_be \!= 0\)/g' $TARGET_PATH/test_register_model.sv

echo "#####   removing unused regs queue   #####"
sed -i 's/^\s*uvm_reg regs\[\$\];//g' $TARGET_PATH/register_model.sv
sed -i 's/^\s*uvm_reg regs\[\$\];//g' $TARGET_PATH/test_register_model.sv
sed -i 's/^\s*this.regs.push_back.*;//g' $TARGET_PATH/register_model.sv
sed -i 's/^\s*this.regs.push_back.*;//g' $TARGET_PATH/test_register_model.sv

sed -i '/ifndef/apackage regmodel_pkg;\n\n`include "uvm_macros.svh"\n' $TARGET_PATH/register_model.sv
echo "\nendpackage" >> $TARGET_PATH/register_model.sv

sed -i '/ifndef/apackage test_regmodel_pkg;\n\n`include "uvm_macros.svh"\n' $TARGET_PATH/test_register_model.sv
echo "\nendpackage" >> $TARGET_PATH/test_register_model.sv
