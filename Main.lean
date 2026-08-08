import VersoManual
import LeanTacticBook

open Verso.Genre Manual
open Verso Code External

-- htmlDepth := 1 → 整章塞进一页, 不按 section 拆子页 (2026-07-12 子鱼要求)
def main := manualMain (%doc LeanTacticBook) (config := { htmlDepth := 1 })
