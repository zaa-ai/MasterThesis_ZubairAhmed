#!/bin/bash
set -euo pipefail


# 1) Copy & rename the master log aand make passing and failing directories
mkdir -p failing passing
echo "=== Copying simulation.log for each test ==="

while IFS= read -r test; do
  # skip blank lines
  if [[ -z "$test" ]]; then
    continue
  fi

  src="sim/$test/simdir/logs/simulation.log"
  dest="$test.log"

  if [[ -f "$src" ]]; then
    echo "  → Copying $src → $dest"
    cp "$src" "$dest"
  else
    echo "  ⚠️  Warning: log not found for '$test' at $src" >&2
  fi
done < selected_test.list

echo "=== Done copying logs ==="

# 2) Sort logs into failing/ vs passing/
grep -L "UVM_ERROR" *.log | xargs -r -I {} mv {} passing/
grep -l "UVM_ERROR" *.log | xargs -r -I {} mv {} failing/


# 3) List all failing into vcs.txt
find ./failing -type f -name "*.log" > vcs.txt

# 4) Generate and tweak RDA config
autorca -gen_cfg_template temp.yaml -gen_mode binning
cp temp.yaml rca.yaml
sed -i 's/^\( *user_defined_rule: .*\)$/#\1/' rca.yaml
sed -i 's|latest_fail_list: .*|latest_fail_list: ./vcs.txt|' rca.yaml


