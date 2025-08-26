
# suppress some known project_dependend messages
suppress_message VER-26
# VER-26 (warning) %s The package %s has already been analyzed. It is being replaced.

# Information: Ungrouping hierarchy...
suppress_message OPT-772

# Information: Complementing Port...
suppress_message OPT-319

suppress_message AUTOREAD-100
suppress_message AUTOREAD-102
suppress_message AUTOREAD-105

suppress_message AUTOREAD-303
suppress_message AUTOREAD-304

suppress_message VHD-4
#Information: Skipping clock gating on...
suppress_message PWR-806
#Information: Performing clock-gating on---
suppress_message PWR-730
# comes up as warning but is just an information..
suppress_message DDB-72
suppress_message DDB-74

# We do not have data for all ip cells
# MV-017  (warning)  %s operating condition %s for instance %s has a dif-
# ferent temperature than top level %s operating  condition  %s.   Delays 
# may be inaccurate as a result.
suppress_message MV-017
    
#long instance names...
suppress_message LINK-26
# Warning: Defining design library .... (AUTOREAD-107)
suppress_message AUTOREAD-107

#Warning: In the design ... net ... is connecting multiple ports. (UCN-1)
#comes with change_names
suppress_message UCN-1

# SDC set_driving_cell -lib_cell $INPUT_DRIVER  [all_inputs]:
#Warning: Design rule attributes from the driving cell will be
# set on the port. (UID-401)
suppress_message UID-401
