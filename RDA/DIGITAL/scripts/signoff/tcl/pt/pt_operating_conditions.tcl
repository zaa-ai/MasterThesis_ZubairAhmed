###############################################################################
# Defines  the  operating conditions or environmental characteris-
# tics for the current design.
#
# Corner names and Library names are set in Makefile and are extracted from
# tech_config.xml
#
###############################################################################
set_operating_conditions \
    -analysis_type on_chip_variation \
    -min $env(CORNER_NAME_MIN) \
    -max $env(CORNER_NAME_MAX) \
    -min_library $env(LIBRARY_NAME_MIN) \
    -max_library $env(LIBRARY_NAME_MAX) 
