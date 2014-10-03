#!/bin/sh

for file in gen/$1/*[0-9].ec; do
  if grep valid $file.result_2 >/dev/null 2>&1; then
    printf "$file valid:            "
    grep '] in' $file | grep -v input | grep -v '\[\]'
  elif ! grep Attack $file.result_2 >/dev/null 2>&1; then
    printf "$file unknown for 2-CMA:"
    grep '] in' $file | grep -v input | grep -v '\[\]'
  fi
done
