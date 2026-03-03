#!/usr/bin/env bash
set -euo pipefail

gcc -finput-charset=UTF-8 -fexec-charset=UTF-8 -fextended-identifiers \
  -I./includes -o main ./src/main.c ./src/tinyexpr.c
