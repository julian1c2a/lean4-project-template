import FOL.FOL

def doubleNegAxiom (A : Formula) : Formula := .impl (neg (neg A)) A
def excludedMiddleAxiom (A : Formula) : Formula := .or A (neg A)
