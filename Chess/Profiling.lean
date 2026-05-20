import Chess.Basic

def ProfilingTestBoard := FENtoBoard (parseFenString "4k3/2pp3p/4b3/1np1p1q1/1N1P3P/4BPP1/P3P3/R2QKBNR test")

def testMove : Move := .move (⟨1,3⟩, ⟨7, 2⟩)

def runCount := 1000
--- TODO funktioniert nicht gscheit wergen optimierung
def profileApplyMove := Id.run do
  for i in [:runCount] do
    let new_b <- ProfilingTestBoard.applyMove testMove
