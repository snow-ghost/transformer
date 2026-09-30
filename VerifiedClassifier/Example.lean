import VerifiedClassifier.Choice

namespace VerifiedClassifier.Example

def data : List (String × Fin 3) :=
  [("fruit",0),("fruit",0),("fruit",0),("fruit",0),("fruit",1),("other",2)]

def result : Choice.Result 3 := Choice.choose (Choice.learn data "fruit")
def unseen : Choice.Result 3 := Choice.choose (Choice.learn data "unseen")

end VerifiedClassifier.Example
