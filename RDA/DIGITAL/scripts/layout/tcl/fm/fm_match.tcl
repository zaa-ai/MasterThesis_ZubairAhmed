
puts "RM-Info: Running script [info script]\n"

#################################################################################
# Match compare points and report unmatched points 
#################################################################################

match

report_unmatched_points > ${REPORTS_DIR_FORMALITY}/${DESIGN_NAME}.fmv_unmatched_points.rpt


#################################################################################
# Verify and Report
#
# If the verification is not successful, the session will be saved and reports
# will be generated to help debug the failed or inconclusive verification.
#################################################################################

if { ![verify] }  {  
  save_session -replace ${REPORTS_DIR_FORMALITY}/${DESIGN_NAME}
  report_failing_points > ${REPORTS_DIR_FORMALITY}/${DESIGN_NAME}.fmv_failing_points.rpt
  report_aborted > ${REPORTS_DIR_FORMALITY}/${DESIGN_NAME}.fmv_aborted_points.rpt
  # Use analyze_points to help determine the next step in resolving verification
  # issues. It runs heuristic analysis to determine if there are potential causes
  # other than logical differences for failing or hard verification points. 
  analyze_points -all > ${REPORTS_DIR_FORMALITY}/${DESIGN_NAME}.fmv_analyze_points.rpt
  set fm_passed FALSE
} else {
  set fm_passed TRUE
}

puts "RM-Info: Completed script [info script]\n"

# ELMOS: handled in main script
#exit

