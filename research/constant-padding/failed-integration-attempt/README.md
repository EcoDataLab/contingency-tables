# Preserved first public-scope integration failure

The fresh compile reached `Research.ReciprocalZeroPhysical` without making
its required `Research.AcceptancePadding` source available. The compiler
rejected the missing imported object; this was a runner dependency omission.
The later [successful scope](../results/verification.json) explicitly compiles
that shared source and `Math115.ReferenceEdgeAcceptance` first. No proof was
weakened. The failed attempt made no audit or acceptance claim.
