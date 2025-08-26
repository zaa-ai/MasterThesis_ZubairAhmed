dump -file spi_core_test.fsdb -type FSDB


dump -deltaCycle on

dump -add testrunner.spi_ts.spi_ct.* -depth 0 -aggregates
