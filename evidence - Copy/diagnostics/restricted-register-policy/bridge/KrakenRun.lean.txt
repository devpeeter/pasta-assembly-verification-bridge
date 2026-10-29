import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Lean

open Lean

namespace PastaBridge

def registerNames : List String := (List.range 31).map (fun n => s!"x{n}")

def readReg (s : Reg64s) (name : String) : Except String UInt64 := do
  if name == "sp" then return s.SP
  match Kraken.AArch64.Parser.parseXRegName name with
  | some (.W64, r) => return s.getXReg r
  | _ => throw s!"invalid 64-bit register: {name}"

def writeReg (s : Reg64s) (name : String) (value : Nat) : Except String Reg64s := do
  if value >= 2^64 then throw s!"register value exceeds 64 bits: {name}"
  if name == "sp" then return { s with SP := UInt64.ofNat value }
  match Kraken.AArch64.Parser.parseXRegName name with
  | some (.W64, r) => return s.setXReg r (BitVec.ofNat 64 value)
  | _ => throw s!"invalid 64-bit register: {name}"

def initState (j : Json) : Except String MachineData := do
  let obj ← (← j.getObjVal? "regs").getObj?
  let mut regs : Reg64s := {}
  for (name, value) in obj.toArray do
    regs ← writeReg regs name (← value.getNat?)
  let flags ← j.getObjVal? "flags"
  let status : StatusFlags := {
    n := ← (← flags.getObjVal? "n").getBool?
    z := ← (← flags.getObjVal? "z").getBool?
    c := ← (← flags.getObjVal? "c").getBool?
    v := ← (← flags.getObjVal? "v").getBool? }
  let memory := (∅ : DataMem).insert (BitVec.ofNat 64 4096) 165
  return { regs, status, dmem := memory }

def finishEffects : Nat → Effects → Except String MachineData
  | 0, _ => .error "effect budget exhausted"
  | _ + 1, .done (state, _) => .ok state
  | fuel + 1, .require_exec_access _ next => finishEffects fuel (next ())
  | _, .require_read_access _ _ _ => .error "unsupported memory read effect"
  | _, .require_write_access _ _ _ => .error "unsupported memory write effect"
  | _, .nonmem_load .. => .error "unsupported external memory read effect"
  | _, .nonmem_store .. => .error "unsupported external memory write effect"
  | _, @Effects.undefined _ _ _ => .error "undefined instruction behavior"
  | _, .unimplemented reason => .error reason

def run (program : Program) (state : MachineData) : Except String MachineData :=
  letI : Labels := { label _ := 0 }
  finishEffects (program.length + 1)
    (Directives.interp (program.map (fun i => (i, 4))) state 0
      (fun pc state => .done (state, pc)))

def stateJson (initial final : MachineData) : Except String Json := do
  let regs ← (registerNames ++ ["sp"]).mapM fun name => do
    return (name, toJson (← readReg final.regs name).toNat)
  return Json.mkObj [
    ("regs", Json.mkObj regs),
    ("flags", Json.mkObj [
      ("n", toJson final.status.n), ("z", toJson final.status.z),
      ("c", toJson final.status.c), ("v", toJson final.status.v)]),
    ("memory_preserved", toJson (final.dmem == initial.dmem)),
    ("sp_preserved", toJson (final.regs.SP == initial.regs.SP))]

def runCase (program : Program) (j : Json) : Except String Json := do
  let state ← initState j
  stateJson state (← run program state)

def runBatch (assembly cases : String) : Except String Json := do
  let program ← Kraken.AArch64.Parser.parse assembly
  if program.any (fun d => match d with | .instr _ => false | _ => true) then
    throw "unsupported non-instruction directive"
  let inputs ← (← Json.parse cases).getArr?
  let results ← inputs.mapM (runCase program)
  return Json.arr results

end PastaBridge

def main (args : List String) : IO UInt32 := do
  match args with
  | [assemblyPath, inputPath] =>
    let assembly ← IO.FS.readFile assemblyPath
    let inputs ← IO.FS.readFile inputPath
    match PastaBridge.runBatch assembly inputs with
    | .ok result => IO.println result.compress; return 0
    | .error reason => IO.eprintln reason; return 1
  | _ =>
    IO.eprintln "usage: KrakenRun.lean ASSEMBLY.S CASES.json"
    return 2
