.PHONY: help tdma rda_binning rda_analysis debug clean_logs regression load_verdi

# Use Bash 
SHELL := /bin/bash
# Location of your simulator and common options
SIM      := /common/department/design/tools/designflow/develop/bin/sim
SIM_OPTS := clean an elab run -f -no_dump -no_check -no_gui -no_pop -v +UVM_MAX_QUIT_COUNT=5,NO

# per-test limits
ERR_LIMIT  := 20        # max UVM_ERROR occurrences per test
TIME_LIMIT := 300       # max seconds per test (5 minutes)
TESTS := $(shell sed '/^\s*$$/d' selected_test.list)	# list of tests (non-blank lines)

rda_analysis:
	@echo "Running RDA analysis…"
	@./rda_analysis.sh	

rda_binning:
	@echo "Running Binning..."
	@autorca -cfg rca.yaml

debug:
	@autorca -load_report rda_report.json

demo:
	@echo "Running RDA Binning..."
	@autorca -cfg temp_1.yaml
	@echo "Running Binning Report..."
	@autorca -load_report rda_report.json

clean:
	@echo "Cleaning up RDA artifacts"
	@rm -f *.log                # top-level log files
	@rm -f vcs.txt                # text lists (like vcs.txt)
	@rm -f temp.yaml rca.yaml   # RDA YAMLs
	@rm -rf failing/ passing/   # log split dirs
	@rm -rf rca.work/           # RCA working directory
	@rm -f rda_report.json 		# remove the generated json file

clean_logs:
	@echo "Cleaning up generated logs"
	@rm -rf sim/*/simdir/logs/*.log logs/*.log               # top-level log files
	@echo "Completed!!"


regression:
	@echo "▶ Starting regression of $(words $(TESTS)) tests (5 min each)…"
	@for t in $(TESTS); do \
	  LOG_DIR="sim/$$t/simdir/logs"; \
	  mkdir -p "$$LOG_DIR"; \
	  echo; \
	  echo "→ Running test: $$t"; \
	  \
	  timeout $(TIME_LIMIT) $(SIM) $$t $(SIM_OPTS) +UVM_TESTNAME=$$t \
	    2>&1 | tee "$$LOG_DIR/simulation.log"; \
	  EXIT_CODE=$$?; \
	  if [ $$EXIT_CODE -eq 124 ]; then \
	    echo "[TIMEOUT] $$t exceeded $(TIME_LIMIT)s — moving on"; \
	  else \
	    echo "[PASS]  $$t finished under $(TIME_LIMIT)s"; \
	  fi; \
	done
	@echo; \
	echo "###### Regression complete ######"

$(TESTS):
	@echo "→ Running test: $@"
	$(SIM) $@ $(SIM_OPTS)

help:
	@echo "Available make targets, Follow the steps for the Regression Flow:"
	@echo "  -make clean           # Remove all generated outputs and build artifacts"
	@echo "  -make clean_logs      # Delete all log files from previous runs in cd DIGITAL"
	@echo "  -make regression      # 1.run all tests in selected_test.list"
	@echo "  -make rda_analysis    # 2.Execute the RDA analysis workflow, sorts the passing and failing logs and produces vcs.txt"
	@echo "  -source verdi.csh	 # 3. Will load the necessays verdi RDA module and the liscence"
	@echo "  -make rda_binning     # 4.Run the RDA binning step (autorca using rca.yaml)"
	@echo "  -make debug           # 5.Loads the GUI responsible from the report.json"
	@echo "  -make demo            # Run the demo workflow for quick verification,"
	@echo "  -make <testname>      # run a single test (must be in selected_test.list)"
	@echo
	@echo "Available tests to run:"
	@sed 's/^/  /' selected_test.list

