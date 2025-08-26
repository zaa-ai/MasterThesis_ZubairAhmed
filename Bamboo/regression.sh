#!/usr/local/bin/tcsh
#!/bin/csh

# Load required modules
module use /common/department/design/tools/digitalDesignFlow/modules
source project_env.csh

# Move into the DIGITAL directory
cd DIGITAL

# Ensure required directories exist
mkdir -p logs/vcs/ logs/passing logs/failing logs/test-reports/

# Ensure the script has execution permissions
chmod 544 config/otp.compile

# Select one specific test (Change method here if needed)
#shuf -n 1 regression.list > selected_test.list   # Select randomly(temporarily disabled)

#Run all tests in selected.list
#project sim cov -tc=selected.list -JUnit -f -v -maxpar=12 -fast -elfilelist=$DESIGN/$DIGITAL/config/excludeList.el -excl_bypass_checks -forbiddenHosts=exsim01,exsim02

#puts test'upload_tdma' from regression.list to 'selected.list'
#grep -x 'upload_tdma' regression.list > selected_test.list

#puts the given tests into selected.list
grep -x -E 'upload_tdma|spi_errors|dsi3_crm|debounce_times|shut_off' regression.list > selected_test.list

# Run UVM register sequences (unchanged)
#project sim -tc=uvm_register_sequences -localhost -JUnit -f -maxpar=3 -fast -no_lint
# Debug: Print which test is selected
echo "Running the following test:"
cat selected_test.list

#runs selected.list
#project sim cov -tc=selected_test.list -JUnit -f -v -maxpar=12 -fast -no_gui -no_check -no_pop +UVM_VERBOSITY=UVM_MEDIUM +bus_conflict_off +warn=noFCICIO +fsdbfile+selected_test.list.fsdb +fsdbDumpAll +lca -elfilelist=$DESIGN/$DIGITAL/config/excludeList.el -excl_bypass_checks -forbiddenHosts=exsim01,exsim02
project sim cov -tc=selected_test.list -JUnit -f -v -maxpar=12  -fast -elfilelist=$DESIGN/$DIGITAL/config/excludeList.el -excl_bypass_checks -forbiddenHosts=exsim01,exsim02

#runs selected.list and generates all the given metadata
#project sim cov -tc=selected_test.list -JUnit -f -v -maxpar=12 -fast +fsdbfile+selected_test.list.fsdb +lca +fsdbDumpAll -elfilelist=$DESIGN/$DIGITAL/config/excludeList.el -excl_bypass_checks -forbiddenHosts=exsim01,exsim02
#project sim -tc=uvm_register_sequences -localhost -JUnit -f $DESIGN/$DIGITAL/config/el_filelist -F $DESIGN/$DIGITAL/config/model_filelist -F $DESIGN/$DIGITAL/config/spi_filelist -f -maxpar=3 +fsdbfile+uvm_register_sequences.fsdb +lca +fsdbDumpAll -no_lint +incdir+$DESIGN/$DIGITAL/model +incdir+$DESIGN/$DIGITAL/SPI/rtl
project sim -tc=uvm_register_sequences -localhost -JUnit -f -maxpar=3 +fsdbfile+uvm_register_sequences.fsdb +lca +fsdbDumpAll -no_lint

# Create directories for organized logs
mkdir -p logs/passing   # Inside logs/
mkdir -p logs/failing   # Inside logs/
mkdir -p passing        # Ensure `passing/` is also created in DIGITAL/
mkdir -p failing

# Identify passing tests and move logs (UVM_ERROR == 0)
echo "Identifying passing tests..."
grep -rl "UVM_ERROR :    0" logs/vcs/ | xargs -I {} mv {} logs/passing/
cp -r logs/passing/* passing/  # Copy passing logs to DIGITAL/passing/

# Identify failing tests and move logs (UVM_ERROR != 0)
echo "Identifying failing tests..."
grep -rL "UVM_ERROR :    0" logs/vcs/ | xargs -I {} mv {} logs/failing/
cp -r logs/failing/* failing/  # Copy  failing logs

# Debug: Print the number of passing & failing tests
echo "Total Passing Tests: `ls logs/passing/ | wc -l`"
echo "Total Failing Tests: `ls logs/failing/ | wc -l`"

# Store the list of passing test logs
find ./failing -type f -name "*.log" > vcs.txt

# Generate build timings
make times

# Archive logs, keeping the structured format
tar -cvzf logs.tar.gz logs/

# Last line must be empty
