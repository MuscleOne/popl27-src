#!/bin/sh
set -eu
artifact_root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
mode=${1:-runtime}
example=${2:-pipeline}
if [ "$#" -gt 0 ]; then shift; fi
if [ "$#" -gt 0 ]; then shift; fi
case "$mode" in
  source|runtime) ;;
  *) printf '%s\n' 'usage: run.sh [source|runtime] [pipeline|checker-valid|checker-error] [interpreter options]' >&2; exit 2 ;;
esac
case "$example" in
  pipeline|checker-valid|checker-error) ;;
  *) printf '%s\n' "unknown example: $example" >&2; exit 2 ;;
esac
exec opam exec -- dune exec --root "$artifact_root/ocaml" \
  "bin/$mode.exe" -- "$@" "$artifact_root/examples/$example.async"
