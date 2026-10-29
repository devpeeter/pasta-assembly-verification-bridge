import MulArtifact

namespace PastaBridge

set_option maxRecDepth 100000

def retainedMultiplicationCharonArtifact : String := retainedText("../generated/mul-check.json")
def retainedMultiplicationArtifactBytes : List UInt8 := retainedByteList("../generated/mul-check.json")
def retainedMultiplicationArtifactChars : List Char := retainedMultiplicationCharonArtifact.toList
def retainedMultiplicationArtifactValue : KernelJson.Value := retainedJsonValue("../generated/mul-check.json")
def retainedMultiplicationAssembly : String := retainedText("../generated/mul.S")
def retainedMultiplicationProgram : Program := retainedProgram("../generated/mul.S")

end PastaBridge
