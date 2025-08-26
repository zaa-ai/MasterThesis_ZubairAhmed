#!/bin/csh
set TARGET_PATH = $DESIGN/$DIGITAL/tb_eugene
cd $TARGET_PATH
eugene generate --testbench-definition testbench.xml --target-directory agents
