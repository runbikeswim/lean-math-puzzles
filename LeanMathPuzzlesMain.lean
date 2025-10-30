import LeanMathPuzzles
import VersoManual
import Verso.Output.Html

open Verso Doc
open Verso.Genre Manual

def config : Config where
  destination := "docs"
  emitTeX := false
  emitHtmlSingle := false
  emitHtmlMulti := true
  htmlDepth := 1

def main := manualMain (%doc LeanMathPuzzles) (config := config.addKaTeX)
