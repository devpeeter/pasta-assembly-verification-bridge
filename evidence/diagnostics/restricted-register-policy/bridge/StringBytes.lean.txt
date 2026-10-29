import Init.Data.String.Lemmas.Intercalate
import Init.Data.ByteArray.Lemmas

namespace PastaBridge.StringBytes

def bytes (text : String) : List UInt8 := text.toByteArray.data.toList

theorem injective {first second : String} (same : bytes first = bytes second) :
    first = second := by
  apply String.toByteArray_inj.mp
  apply ByteArray.ext
  exact Array.toList_inj.mp same

theorem append (first second : String) :
    bytes (first ++ second) = bytes first ++ bytes second := by
  unfold bytes
  rw [String.toByteArray_append, ByteArray.toList_data_append]

theorem join (parts : List String) :
    bytes (String.join parts) = parts.flatMap bytes := by
  induction parts with
  | nil => rfl
  | cons first remaining ih =>
    rw [String.join_cons, append, ih]
    rfl

theorem intercalate (separator : String) (parts : List String) :
    bytes (String.intercalate separator parts) =
      (bytes separator).intercalate (parts.map bytes) := by
  induction parts with
  | nil => rfl
  | cons first remaining ih =>
    cases remaining with
    | nil =>
      rw [String.intercalate_singleton]
      simp only [List.map_cons, List.map_nil, List.intercalate_singleton]
    | cons second rest =>
      rw [String.intercalate_cons_cons, append, append, ih]
      simp only [List.map_cons, List.intercalate_cons_cons, List.append_assoc]

#print axioms injective
#print axioms append
#print axioms join
#print axioms intercalate

end PastaBridge.StringBytes
