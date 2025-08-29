
#!/bin/bash

find ./logs/failing -type f -name "*.log" > vcs.txt

module load verdi/W-2024.09-SP1

export SNPSLMD_LICENSE_FILE=27020@license03:27020@aedlmgr

autorca -gen_cfg_template temp.yaml -gen_mode binning

cp temp.yaml rca.yaml

sed -i 's/^\( *user_defined_rule: .*\)$/#\1/' rca.yaml

sed -i 's|latest_fail_list: .*|latest_fail_list: ./vcs.txt|' rca.yaml

autorca -cfg rca.yaml

autorca -load_report rda_report.json
