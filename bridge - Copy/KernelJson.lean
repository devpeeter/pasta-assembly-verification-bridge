import Lean

namespace PastaBridge.KernelJson

inductive Value where
  | null
  | bool (value : Bool)
  | number (value : Int)
  | string (value : String)
  | array (values : List Value)
  | object (fields : List (String × Value))
  deriving Repr

def whitespace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\r' || c == '\t'
def skipSpace (chars : List Char) : List Char := chars.dropWhile whitespace

def parseString : Nat → List Char → List Char → Except String (String × List Char)
  | 0, _, _ => .error "JSON string budget exhausted"
  | _ + 1, [], _ => .error "unterminated JSON string"
  | _ + 1, '"' :: rest, acc => .ok (String.ofList acc.reverse, rest)
  | fuel + 1, '\\' :: escape :: rest, acc =>
    match escape with
    | '"' => parseString fuel rest ('"' :: acc)
    | '\\' => parseString fuel rest ('\\' :: acc)
    | '/' => parseString fuel rest ('/' :: acc)
    | 'n' => parseString fuel rest ('\n' :: acc)
    | 'r' => parseString fuel rest ('\r' :: acc)
    | 't' => parseString fuel rest ('\t' :: acc)
    | 'b' => parseString fuel rest (Char.ofNat 8 :: acc)
    | 'f' => parseString fuel rest (Char.ofNat 12 :: acc)
    | _ => .error "unsupported JSON escape"
  | fuel + 1, char :: rest, acc =>
    if char.toNat < 32 then .error "control character in JSON string"
    else parseString fuel rest (char :: acc)

def decimal (c : Char) : Bool := '0' <= c && c <= '9'

def parseNumber (chars : List Char) : Except String (Value × List Char) := do
  let (negative, chars) := match chars with
    | '-' :: rest => (true, rest)
    | _ => (false, chars)
  let digits := chars.takeWhile decimal
  if digits.isEmpty then throw "JSON integer expected"
  if digits.length > 1 && digits.head? == some '0' then throw "leading zero in JSON integer"
  let value := digits.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
  return (.number (if negative then -(Int.ofNat value) else Int.ofNat value), chars.drop digits.length)

mutual
  def parseValue : Nat → List Char → Except String (Value × List Char)
    | 0, _ => .error "JSON value budget exhausted"
    | fuel + 1, input =>
      match skipSpace input with
      | '"' :: rest => do
        let (value, rest) ← parseString fuel rest []
        return (.string value, rest)
      | '[' :: rest => do
        let (values, rest) ← parseArray fuel (skipSpace rest)
        return (.array values, rest)
      | '{' :: rest => do
        let (fields, rest) ← parseObject fuel (skipSpace rest)
        return (.object fields, rest)
      | 'n' :: 'u' :: 'l' :: 'l' :: rest => .ok (.null, rest)
      | 't' :: 'r' :: 'u' :: 'e' :: rest => .ok (.bool true, rest)
      | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => .ok (.bool false, rest)
      | chars => parseNumber chars

  def parseArray : Nat → List Char → Except String (List Value × List Char)
    | 0, _ => .error "JSON array budget exhausted"
    | _ + 1, ']' :: rest => .ok ([], rest)
    | fuel + 1, chars => do
      let (value, rest) ← parseValue fuel chars
      match skipSpace rest with
      | ']' :: rest => return ([value], rest)
      | ',' :: rest =>
        if (skipSpace rest).head? == some ']' then throw "trailing JSON array comma"
        let (values, rest) ← parseArray fuel (skipSpace rest)
        return (value :: values, rest)
      | _ => throw "JSON array delimiter expected"

  def parseObject : Nat → List Char → Except String (List (String × Value) × List Char)
    | 0, _ => .error "JSON object budget exhausted"
    | _ + 1, '}' :: rest => .ok ([], rest)
    | fuel + 1, '"' :: chars => do
      let (key, rest) ← parseString fuel chars []
      let rest ← match skipSpace rest with
        | ':' :: rest => pure rest
        | _ => throw "JSON object colon expected"
      let (value, rest) ← parseValue fuel rest
      match skipSpace rest with
      | '}' :: rest => return ([(key, value)], rest)
      | ',' :: rest =>
        if (skipSpace rest).head? == some '}' then throw "trailing JSON object comma"
        let (fields, rest) ← parseObject fuel (skipSpace rest)
        if fields.any (fun field => field.1 == key) then throw "duplicate JSON object key"
        return ((key, value) :: fields, rest)
      | _ => throw "JSON object delimiter expected"
    | _ + 1, _ => .error "JSON object key expected"
end

def parse (input : String) : Except String Value := do
  let chars := input.toList
  let (value, rest) ← parseValue (chars.length + 1) chars
  if !(skipSpace rest).isEmpty then throw "trailing JSON data"
  return value

def Value.field (value : Value) (key : String) : Except String Value :=
  match value with
  | .object fields => match fields.find? (fun field => field.1 == key) with
    | some (_, value) => .ok value
    | none => .error s!"missing JSON field {key}"
  | _ => .error "JSON object expected"

def Value.text (value : Value) : Except String String :=
  match value with
  | .string text => .ok text
  | _ => .error "JSON string expected"

def Value.nat (value : Value) : Except String Nat :=
  match value with
  | .number n => if n < 0 then .error "nonnegative integer expected" else .ok n.toNat
  | _ => .error "JSON integer expected"

def Value.items (value : Value) : Except String (List Value) :=
  match value with
  | .array values => .ok values
  | _ => .error "JSON array expected"

end PastaBridge.KernelJson
