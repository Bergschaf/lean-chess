import Chess.Basic
def BenchmarkBoard := FENtoBoard (parseFenString "1rb2bnr/2ppnkpp/p1p1p3/5pq1/8/BP2P1PB/P2P1P1P/RN1QK1NR w KQ - 2 10")


def getSystemTime : IO Nat := do
  let file <- IO.FS.readFile "/proc/uptime"
  let str := (file.split " ").toList[0]!.split "." |>.toList
  let seconds := str[0]!.toNat!
  let millis := str[1]!.toNat! * 10
  return seconds * 1000 + millis

/-- Serach depth as first argument -/
def main (args : List String) : IO Unit := do
  let depth : Nat := match args[0]? with
  | .none => 4
  | .some s => s.toNat!

  let startHeartBeats <- IO.getNumHeartbeats
  let startTime <- getSystemTime

  let bestMove := BenchmarkBoard.bestMove .White depth
  dbg_trace bestMove

  let endHeartBeats <- IO.getNumHeartbeats
  let endTime <- getSystemTime

  let stdout <- IO.getStdout

  stdout.putStrLn s!"ΔHeartbeats: {((endHeartBeats-startHeartBeats)).toFloat / 1000000}M"
  stdout.putStrLn s!"ΔTime: {endTime-startTime}ms"
