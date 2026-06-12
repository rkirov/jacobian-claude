import VersoManual
import Site

open Verso.Genre Manual

def main := manualMain (%doc Site) (config := {
  emitTeX := false,
  emitHtmlSingle := false,
  emitHtmlMulti := true,
  htmlDepth := 1
})
