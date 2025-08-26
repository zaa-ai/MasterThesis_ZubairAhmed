#!/bin/bash

if [ $# -eq 3 ]
 then
  WIN=$3
 else
  WIN=" "
 fi

LOGS_DIR=$(echo $1 | awk -F/ '{print $1}')

grep -i "^\s*Error:" $1 > $LOGS_DIR/Errors
grep -i "^\s*RM-Error:" $1 >> $LOGS_DIR/Errors
grep -i "^The tool has just encountered a fatal error:" $1 >> $LOGS_DIR/Errors
grep -i "^Stack trace for crashing thread" $1 >> $LOGS_DIR/Errors

grep -i "^\s*Warning:" $1 > $LOGS_DIR/Warning
grep -i "^\s*RM-Warning:" $1 >> $LOGS_DIR/Warning

ERR=($(wc -l $LOGS_DIR/Errors))
ERR=${ERR[0]}
if [ $ERR -gt 0 ]
 then
   echo -e  "\\033[1;31mErrors: " $ERR "\\033[0m"
  else
   echo -e "\\033[1;32mNo Errors\\033[0m"
fi

WARN=($(wc -l $LOGS_DIR/Warning))
WARN=${WARN[0]}
echo -e  "\\033[33mWarnings: " $WARN "\\033[0m"
if  [[ $WARN -gt 0  &&  $WIN != "-w" ]]
 then 
    xterm -vb +hold -bg black -fg yellow -rightbar -fn fixed -geometry 120x35 -T $1 -e less $LOGS_DIR/Warning &
fi
if  [ $ERR -gt 0  ] 
 then 
    xterm -vb +hold -bg black -fg red    -rightbar -fn fixed -geometry 120x35 -T $1 -e less $LOGS_DIR/Errors &
    exit 1
 else
    date > $2
    exit 0
 fi
echo "`date` $1 $ERR $WARN" >>flow.log


