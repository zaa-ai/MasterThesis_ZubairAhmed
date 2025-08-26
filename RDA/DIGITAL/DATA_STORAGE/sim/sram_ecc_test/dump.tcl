dump -file sram_ecc_test.fsdb -type FSDB

dump -deltaCycle on
dump -msv on

dump -add testrunner.ts.ut -depth 0 -aggregates -fsdb_opt +all
