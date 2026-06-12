import VersoManual
import Site

open Verso.Genre Manual

def main := manualMain (%doc Site) (config := {
  emitHtmlSingle := .no,
  emitHtmlMulti := .immediately,
  htmlDepth := 1,
  sourceLink := some "https://github.com/rkirov/jacobian-claude",
  issueLink := some "https://github.com/rkirov/jacobian-claude/issues"
})
