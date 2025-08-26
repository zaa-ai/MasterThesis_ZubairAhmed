dump -file spi_test.fsdb -type FSDB


dump -deltaCycle on

dump -add testrunner.spi_ts.spi_t -depth 0 -aggregates  -fsdb_opt +all
