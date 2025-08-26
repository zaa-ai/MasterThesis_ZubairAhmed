# make_reqs.py
import yaml, re

with open('dbscan_environment.yaml') as f:
    env = yaml.safe_load(f)

pip_deps = []
for dep in env['dependencies']:
    # conda string entries
    if isinstance(dep, str):
        # drop build metadata: foo=1.2.3=build -> foo==1.2.3
        name, version, *_ = dep.split('=')
        pip_deps.append(f"{name}=={version}")
    # pip subsection
    elif isinstance(dep, dict) and 'pip' in dep:
        pip_deps += dep['pip']

# write out
with open('requirements.txt', 'w') as out:
    out.write('\n'.join(pip_deps))
print(f"Wrote {len(pip_deps)} packages to requirements.txt")
