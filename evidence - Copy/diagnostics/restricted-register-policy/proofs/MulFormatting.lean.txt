import MulProgramData

namespace PastaBridge.MulFormatting

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open MulStep

def sourceName (binding : Binding) : Source → String
  | .operand i => registerName (binding i)
  | .zero => "xzr"

def triple (mnemonic : String) (binding : Binding) (d : Operand) (a b : Source) : String :=
  mnemonic ++ " " ++ registerName (binding d) ++ ", " ++ sourceName binding a ++
    ", " ++ sourceName binding b

def format (binding : Binding) : Instruction → String
  | .adds d a b => triple "adds" binding d a b
  | .adcs d a b => triple "adcs" binding d a b
  | .adc d a b => triple "adc" binding d a b
  | .subs d a b => triple "subs" binding d a b
  | .sbcs d a b => triple "sbcs" binding d a b
  | .cselLo d a b => triple "csel" binding d a b ++ ", lo"
  | .mul d a b => triple "mul" binding d a b
  | .umulh d a b => triple "umulh" binding d a b
  | .lsl d a _ => "lsl " ++ registerName (binding d) ++ ", " ++ sourceName binding a ++ ", #62"
  | .lsr d a _ => "lsr " ++ registerName (binding d) ++ ", " ++ sourceName binding a ++ ", #2"
  | .subsOne a => "subs xzr, " ++ registerName (binding a) ++ ", #1"
  | .movMask d => "mov " ++ registerName (binding d) ++ ", #0x4000000000000000"

def supported : Instruction → Bool
  | .lsl _ _ n => n.val == 62
  | .lsr _ _ n => n.val == 2
  | _ => true

def serializeDirective : Directive → Except String String
  | .instr ⟨.W64, operation⟩ => MultiplicationArtifact.serializeOperation operation
  | _ => .error "unsupported directive or instruction width"

theorem register_allowed (r : XReg) (allowed : KrakenBinding.Allowed r) :
    register64 (.low (.reg r) .W64) = .ok (registerName r) := by
  cases r <;> simp_all [KrakenBinding.Allowed, register64] <;> decide +kernel

theorem source_allowed (binding : Binding) (allowed : ∀ i, KrakenBinding.Allowed (binding i))
    (source : Source) : register64 (sourceRegister binding source) = .ok (sourceName binding source) := by
  cases source
  case zero => rfl
  case operand i => exact register_allowed _ (allowed i)

theorem serialize_instruction (binding : Binding) (allowed : ∀ i, KrakenBinding.Allowed (binding i))
    (operation : Instruction) (isSupported : supported operation = true) :
    serializeDirective (.instr (instruction operation binding)) = .ok (format binding operation) := by
  have registers (i : Fin 21) :
      register64 (.low (.reg (binding i)) .W64) = .ok (registerName (binding i)) :=
    register_allowed _ (allowed i)
  have sources (source : Source) := source_allowed binding allowed source
  have arithmeticGuard : ((0 : Int64) != 0 || ShiftType.LSL != .LSL) = false := by decide +kernel
  have immediateGuard : ((1 : ConstExpr) != .int64 1 || ImmShift.S0 != .S0) = false := by decide +kernel
  have moveGuard : ((0x4000 : Int64) != 0x4000) = false := by decide +kernel
  have leftSelf : (ShiftType.LSL == ShiftType.LSL) = true := rfl
  have rightLeft : (ShiftType.LSR == ShiftType.LSL) = false := rfl
  cases operation
  case lsl d a n =>
    have h : n = ⟨62, by decide⟩ := Fin.ext (by simpa only [supported, beq_iff_eq] using isSupported)
    subst n
    simp (ground := true) only [serializeDirective, instruction,
      MultiplicationArtifact.serializeOperation, destinationRegister, format,
      sources, registers, Except.bind, Except.pure, Bind.bind, Pure.pure,
      leftSelf, Bool.false_eq_true, if_true, if_false]
    simp (ground := true) only [String.append_assoc]
  case lsr d a n =>
    have h : n = ⟨2, by decide⟩ := Fin.ext (by simpa only [supported, beq_iff_eq] using isSupported)
    subst n
    simp (ground := true) only [serializeDirective, instruction,
      MultiplicationArtifact.serializeOperation, destinationRegister, format,
      sources, registers, Except.bind, Except.pure, Bind.bind, Pure.pure,
      rightLeft, Bool.false_eq_true, if_true, if_false]
    simp (ground := true) only [String.append_assoc]
  case subsOne a =>
    change (do
      if ((1 : ConstExpr) != ConstExpr.int64 1 || ImmShift.S0 != ImmShift.S0) then
        throw "unsupported subtraction immediate"
      return "subs " ++ (← register64 (.low .XZR .W64)) ++ ", " ++
        (← MultiplicationArtifact.registerSp64 (.low (.reg (binding a)) .W64)) ++ ", #1") =
      .ok ("subs xzr, " ++ registerName (binding a) ++ ", #1")
    rw [immediateGuard]
    have zeroRegister : register64 (.low .XZR .W64) = .ok "xzr" := rfl
    simp (ground := true) only [Bool.false_eq_true, if_false,
      MultiplicationArtifact.registerSp64, registers, Except.bind, Except.pure, Bind.bind, Pure.pure,
      zeroRegister]
  all_goals
    simp (ground := true) only [serializeDirective, instruction,
      MultiplicationArtifact.serializeOperation, destinationRegister, format, triple, threeRegisters,
      sources, registers, Except.bind, Except.pure, Bind.bind, Pure.pure,
      ↓arithmeticGuard, ↓moveGuard, Bool.false_eq_true, if_false]

theorem serialize_program (binding : Binding) (allowed : ∀ i, KrakenBinding.Allowed (binding i))
    (program : List Instruction) (isSupported : ∀ operation ∈ program, supported operation = true) :
    MultiplicationArtifact.serializeProgram (MulMachine.encode binding program) =
      .ok (String.intercalate "\n" (program.map (format binding))) := by
  have mapped :
      (program.map (fun operation => Directive.instr (instruction operation binding))).mapM
        serializeDirective = .ok (program.map (format binding)) := by
    induction program with
    | nil => rfl
    | cons operation remaining ih =>
      have h := serialize_instruction binding allowed operation (isSupported operation (by simp))
      have tail := ih (by intro op hop; exact isSupported op (by simp [hop]))
      simp only [List.map_cons, List.mapM_cons, h, tail, Bind.bind, Pure.pure, Except.bind, Except.pure]
  unfold MultiplicationArtifact.serializeProgram MulMachine.encode
  change (do
    let lines ← (program.map (fun operation => Directive.instr (instruction operation binding))).mapM serializeDirective
    pure (String.intercalate "\n" lines)) = _
  rw [mapped]
  rfl

theorem retained_supported : MulProgramData.retainedInstructions.all supported = true := by
  decide +kernel

#print axioms serialize_instruction
#print axioms serialize_program
#print axioms retained_supported

end PastaBridge.MulFormatting
