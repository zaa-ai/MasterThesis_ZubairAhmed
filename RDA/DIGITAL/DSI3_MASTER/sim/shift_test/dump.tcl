dump -file shift_test.fsdb -type FSDB

dump -deltaCycle on

dump -add testrunner.ts.ut.* -depth 0 -aggregates 
dump -add testrunner.ts.ut.dsi3_start_manager.* -depth 0 -aggregates 
