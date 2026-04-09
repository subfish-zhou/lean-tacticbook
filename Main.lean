import VersoManual
import LeanAutoBook

open Verso.Genre Manual
open Verso Code External

def config : Config where
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1
  sourceLink := some "https://github.com/subfish-zhou/lean-tacticbook"
  issueLink := some "https://github.com/subfish-zhou/lean-tacticbook/issues"

def main := manualMain (%doc LeanAutoBook) (config := { config with })
