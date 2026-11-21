#!/usr/bin/env bash
# Text check for constructs that must not appear in the library. See AGENTS.md.
set -uo pipefail
cd "$(dirname "$0")/.."
# Never allowed.
forbidden='^[[:space:]]*(private |protected |noncomputable |unsafe )*(axiom|opaque)[[:space:]]|native_decide|decide[[:space:]]*\+native|bv_decide|ofReduceBool|trustCompiler|implemented_by|@\[extern|^[[:space:]]*unsafe[[:space:]]|set_option[[:space:]]+debug\.|skipKernelTC|sorryAx'
# Code that runs when the file is built. Vendored code under External/ is reviewed by hand instead.
buildtime='#eval|run_cmd|run_elab|run_meta|run_tac|by_elab|\\bd?simproc\\b|^[[:space:]]*(builtin_)?initialize\b|^[[:space:]]*(local |scoped )?elab(_rules)?\b|@\[(command_elab|term_elab|tactic|init)\b'
status=0
grep -rnE --include='*.lean' "$forbidden" RiemannMasullo Main.lean && status=1
grep -rnE --include='*.lean' --exclude-dir=External "$buildtime" RiemannMasullo Main.lean && status=1
if [ $status = 1 ]; then
  echo "lint: forbidden construct found (see AGENTS.md)" >&2
  exit 1
fi
echo "lint: ok"
