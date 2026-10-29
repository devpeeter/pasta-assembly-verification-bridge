import MulMetadata
import MulFormatting
import Init.Data.String.Lemmas

namespace PastaBridge.MulPieceFormatting

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open MulStep
open MultiplicationArtifact (Piece renderPieces)

def sourcePieces : Source → List Piece
  | .operand i => [.operand i]
  | .zero => [.text "xzr"]

def triplePieces (mnemonic : String) (d : Operand) (a b : Source) : List Piece :=
  [.text (mnemonic ++ " "), .operand d, .text ", "] ++
    sourcePieces a ++ [.text ", "] ++ sourcePieces b

/-- Generic syntax of supported forms, applied to the actual decoded program. -/
def formatPieces : Instruction → List Piece
  | .adds d a b => triplePieces "adds" d a b
  | .adcs d a b => triplePieces "adcs" d a b
  | .adc d a b => triplePieces "adc" d a b
  | .subs d a b => triplePieces "subs" d a b
  | .sbcs d a b => triplePieces "sbcs" d a b
  | .cselLo d a b => triplePieces "csel" d a b ++ [.text ", lo"]
  | .mul d a b => triplePieces "mul" d a b
  | .umulh d a b => triplePieces "umulh" d a b
  | .lsl d a _ => [.text "lsl ", .operand d, .text ", "] ++ sourcePieces a ++ [.text ", #62"]
  | .lsr d a _ => [.text "lsr ", .operand d, .text ", "] ++ sourcePieces a ++ [.text ", #2"]
  | .subsOne a => [.text "subs xzr, ", .operand a, .text ", #1"]
  | .movMask d => [.text "mov ", .operand d, .text ", #0x4000000000000000"]

def programPieces : List Instruction → List Piece
  | [] => []
  | [operation] => formatPieces operation
  | operation :: remaining => formatPieces operation ++ [.text "\n"] ++ programPieces remaining

def prepend : Piece → List Piece → List Piece
  | .text left, .text right :: remaining => .text (left ++ right) :: remaining
  | piece, remaining => piece :: remaining

/-- Merge adjacent literal fragments without evaluating register names. -/
def normalize : List Piece → List Piece
  | [] => []
  | piece :: remaining => prepend piece (normalize remaining)

theorem render_append (binding : Binding) (left right : List Piece) :
    renderPieces binding (left ++ right) = renderPieces binding left ++ renderPieces binding right := by
  simp only [renderPieces, List.map_append, String.join_append]

theorem render_nil (binding : Binding) : renderPieces binding [] = "" := rfl

theorem render_text_cons (binding : Binding) (text : String) (tail : List Piece) :
    renderPieces binding (.text text :: tail) = text ++ renderPieces binding tail := by
  simp only [renderPieces, List.map_cons, String.join_cons]

theorem render_operand_cons (binding : Binding) (index : Operand) (tail : List Piece) :
    renderPieces binding (.operand index :: tail) = registerName (binding index) ++ renderPieces binding tail := by
  simp only [renderPieces, List.map_cons, String.join_cons]

theorem render_source (binding : Binding) (source : Source) :
    renderPieces binding (sourcePieces source) = MulFormatting.sourceName binding source := by
  cases source <;> simp [sourcePieces, renderPieces, MulFormatting.sourceName, String.join_cons]

theorem render_instruction (binding : Binding) (operation : Instruction) :
    renderPieces binding (formatPieces operation) = MulFormatting.format binding operation := by
  cases operation <;>
    simp [formatPieces, triplePieces, render_append, render_source, render_nil,
      render_text_cons, render_operand_cons, MulFormatting.format, MulFormatting.triple,
      String.append_assoc]

theorem render_program (binding : Binding) (program : List Instruction) :
    renderPieces binding (programPieces program) =
      String.intercalate "\n" (program.map (MulFormatting.format binding)) := by
  induction program with
  | nil => simp [programPieces, renderPieces]
  | cons operation remaining ih =>
    cases remaining with
    | nil => simp [programPieces, render_instruction]
    | cons next tail =>
      change renderPieces binding (formatPieces operation ++ [.text "\n"] ++
        programPieces (next :: tail)) = _
      rw [render_append, render_append, render_instruction, ih]
      simp [renderPieces, String.join_cons, String.intercalate_cons_cons, String.append_assoc]

theorem render_prepend (binding : Binding) (piece : Piece) (remaining : List Piece) :
    renderPieces binding (prepend piece remaining) = renderPieces binding (piece :: remaining) := by
  cases piece <;> cases remaining with
  | nil => rfl
  | cons head tail =>
    cases head <;> simp [prepend, renderPieces, String.join_cons, String.append_assoc]

theorem render_normalize (binding : Binding) (pieces : List Piece) :
    renderPieces binding (normalize pieces) = renderPieces binding pieces := by
  induction pieces with
  | nil => rfl
  | cons piece tail ih =>
    rw [normalize, render_prepend]
    cases piece with
    | text value =>
      simpa only [renderPieces, List.map_cons, String.join_cons] using
        congrArg (fun text => value ++ text) ih
    | operand index =>
      simpa only [renderPieces, List.map_cons, String.join_cons] using
        congrArg (fun text => registerName (binding index) ++ text) ih

#print axioms render_instruction
#print axioms render_program
#print axioms render_normalize

end PastaBridge.MulPieceFormatting
