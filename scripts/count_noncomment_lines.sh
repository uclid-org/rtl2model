#!/usr/bin/env bash
# Counts the number of lines in the file that are not comment-only
grep -v -E "\s+#" "$1" | wc -l
