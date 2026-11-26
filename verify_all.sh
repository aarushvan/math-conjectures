#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

echo "=== 1. Checking Lean 4 files for sorry/admit/unsafe/custom axioms ==="
if grep -rnE '\b(sorry|admit|axiom|unsafe)\b' 01-dihedral-shuffle-squares/DihedralShuffleDisproof.lean 02-oeis-a382427-a381717/WisemanA382427.lean 04-oeis-a384890/WisemanA384890.lean; then
  echo "ERROR: Forbidden proof placeholder or axiom keyword found!"
  exit 1
fi
echo "Clean: zero sorry/admit/axiom/unsafe tokens."

echo "=== 2. Kernel-checking Lean 4 proofs ==="
for f in \
  01-dihedral-shuffle-squares/DihedralShuffleDisproof.lean \
  02-oeis-a382427-a381717/WisemanA382427.lean \
  04-oeis-a384890/WisemanA384890.lean
do
  if ! OUT="$(lean "$f" 2>&1)"; then
    echo "$OUT"
    exit 1
  fi
  echo "$OUT"
  if echo "$OUT" | grep -q "sorryAx"; then
    echo "ERROR: sorryAx detected in $f!"
    exit 1
  fi
done
echo "All 3 Lean 4 files kernel-checked cleanly."

echo "=== 3. Running Python verifiers ==="
python3 01-dihedral-shuffle-squares/verify_dihedral.py
python3 02-oeis-a382427-a381717/verify_a382427.py
python3 04-oeis-a384890/verify_a384890.py
python3 05-mo476077-johnston/python/verify_mo476077.py --self-test

echo "=== 4. Compiling and running C / C++ verifiers ==="
clang -O3 -Wall -Wextra -Werror 03-oeis-a377090/verify_a377090.c -lm -o 03-oeis-a377090/verify_a377090
./03-oeis-a377090/verify_a377090

clang++ -O3 -std=c++20 -pthread -march=native 05-mo476077-johnston/cpp/mo476077_search.cpp -o 05-mo476077-johnston/cpp/mo476077_search
./05-mo476077-johnston/cpp/mo476077_search --blocks 3 12

echo "ALL CHECKS PASSED."
