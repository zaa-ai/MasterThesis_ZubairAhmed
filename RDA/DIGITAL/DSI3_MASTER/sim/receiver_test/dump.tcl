dump -file receiver_test.fsdb -type FSDB

dump -deltaCycle on

dump -add testrunner.ts.ut -fsdb_opt +all
dump -add testrunner.ts.fut -fsdb_opt +all
