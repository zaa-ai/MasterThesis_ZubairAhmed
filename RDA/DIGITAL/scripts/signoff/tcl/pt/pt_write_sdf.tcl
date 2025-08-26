
# TSMC 180 nm - 7 track
write_sdf -context Verilog -version 3.0 -include {SETUPHOLD RECREM} -compress gzip \
          $RESULTS_DIR/$DESIGN_NAME.signoff.sdf.gz

# Samsung 130 nm

