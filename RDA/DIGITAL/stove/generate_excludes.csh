#!/bin/csh
set JSON = ${DESIGN}/${DIGITAL}/config/$PROJECT_STATE.json

stove edf-headers -p $JSON --template generate_excludes.vm --flat -o excludes.txt

sed -i 's/\s//' excludes.txt
tr -d '\n' < excludes.txt > excludes_tmp.txt
mv -f excludes_tmp.txt excludes.txt

