#!/bin/bash

if [ $# -eq 3 ]
 then
  WIN=$3
 else
  WIN=" "
 fi
######
# Extra check for eventually floating nets
#####

grep "1'b0" $1 > logs/NetlistErrors
grep "1'b1" $1 >> logs/NetlistErrors
grep "assign" $1 >> logs/NetlistErrors

ERR=($(wc -l logs/NetlistErrors))
ERR=${ERR[0]}
if [ $ERR -gt 0 ]
 then
   echo -e  "\\033[1;31mNetlist-Errors: " $ERR "\\033[0m"
  else
   echo -e "\\033[1;32mNo Errors\\033[0m"
fi

if  [ $ERR -gt 0  ] 
 then 
    xterm -vb +hold -bg black -fg red    -rightbar -fn fixed -geometry 120x35 -T $1 -e less logs/NetlistErrors &
    exit 1
 else
    date > $2
    exit 0
fi
echo "`date` $1 $ERR" >>flow.log


