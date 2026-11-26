#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

LEAN_FILES=(
  01-dihedral-shuffle-squares/DihedralShuffleDisproof.lean
  02-oeis-a382427-a381717/WisemanA382427.lean
  04-oeis-a384890/WisemanA384890.lean
  05-mo476077-johnston/JohnstonEsymmM345.lean
  06-berlow-stack-sorting/BerlowStackSorting.lean
  09-shuffle-antisquares/ShuffleAntiSquares.lean
)

echo "=== 1. Checking Lean 4 files for sorry/admit/unsafe/custom axioms ==="
if grep -rnE '\b(sorry|admit|axiom|unsafe)\b' "${LEAN_FILES[@]}"; then
  echo "ERROR: Forbidden proof placeholder or axiom keyword found!"
  exit 1
fi
echo "Clean: zero sorry/admit/axiom/unsafe tokens."

echo "=== 2. Checking repository for forbidden em dashes (U+2014) ==="
if grep -rn $'\xe2\x80\x94' --exclude-dir=.git --exclude="verify_a377090" --exclude="mo476077_search" .; then
  echo "ERROR: Forbidden U+2014 em dash found!"
  exit 1
fi
echo "Clean: zero em dashes across repository."

echo "=== 3. Kernel-checking all 6 Lean 4 proofs (leanprover/lean4:v4.36.0) ==="
for f in "${LEAN_FILES[@]}"; do
  echo "--- Compiling $f ---"
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
echo "All 6 Lean 4 files kernel-checked cleanly."

echo "=== 4. Running Python verifiers across Tracks 01..12 ==="
python3 01-dihedral-shuffle-squares/verify_dihedral.py
python3 02-oeis-a382427-a381717/verify_a382427.py
python3 04-oeis-a384890/verify_a384890.py
python3 05-mo476077-johnston/python/verify_mo476077.py --self-test
python3 05-mo476077-johnston/python/verify_identities_m345.py
python3 06-berlow-stack-sorting/verify_berlow.py
python3 07-oeis-a384350/verify_a384350.py
python3 08-oeis-a383093/verify_a383093.py
python3 09-shuffle-antisquares/verify_antisquares.py
python3 10-berlow-stack-sorting-132-213/verify_berlow_132_213.py --through-12
python3 11-mo475478-stanley-bivariate/stanley_verify.py --degree 8
python3 12-mo507835-phan-lattice/phan_periodic.py --dimensions 2 3 4 --periods 3 4 6 --steps 6000 --restarts 3

echo "=== 5. Compiling and running C / C++ verifiers ==="
clang -O3 -Wall -Wextra -Werror 03-oeis-a377090/verify_a377090.c -lm -o 03-oeis-a377090/verify_a377090
./03-oeis-a377090/verify_a377090

clang++ -O3 -std=c++20 -pthread -march=native 05-mo476077-johnston/cpp/mo476077_search.cpp -o 05-mo476077-johnston/cpp/mo476077_search
./05-mo476077-johnston/cpp/mo476077_search --blocks 3 12

echo "ALL CHECKS PASSED."