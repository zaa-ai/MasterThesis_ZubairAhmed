dump -file sram_bist_test.fsdb -type FSDB
dump -deltaCycle on

dump -add testrunner.ts.ut.dut* -depth 0 -fsdb_opt +all

