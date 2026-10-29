import Artifact

set_option maxRecDepth 100000

namespace PastaBridge

def retainedCharonArtifact : String := retainedText("../generated/add-check.json")
def retainedArtifactChars : List Char := retainedChars("../generated/add-check.json")
def retainedAdditionAssembly : String := retainedText("../generated/add.S")
def retainedAdditionProgram : Program := retainedProgram("../generated/add.S")

end PastaBridge
