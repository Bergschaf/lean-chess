import Chess

def main : IO Unit := do
  let stdin <- IO.getStdin
  let stdout <- IO.getStdout

  stdout.putStr "FEN String: "
  --let fen <- stdin.getLine
  let fen := "1rb2bnr/2ppnkpp/p1p1p3/5pq1/8/BP2P1PB/P2P1P1P/RN1QK1NR w KQ - 2 10"
  let mut board := FENtoBoard (parseFenString fen)
  let mut turn := Turn.Black
  repeat

    stdout.putStr board.toString

    stdout.putStr "SearchDepth?"

    let depth <- stdin.getLine
    let depth := (depth.dropEnd 1).toNat!

    let bestMove := board.bestMove turn depth
    stdout.putStr (toString bestMove)
    board := board.applyMove bestMove.1
    stdout.putStr "------------------"
    stdout.putStr board.toString
    let mut playerMove := Move.empty
    repeat
      stdout.putStr "Your move?"
      let input <- stdin.getLine
      match Move.fromString (input.dropEnd 1).toString with
      | .none => continue
      | .some m =>
        if ((board.isValidMove turn.next m).run' ∅).run then
          playerMove := m
          break
        else
          --stdout.putStr (ToString.toString (board.possibleMoves turn.next))
          stdout.putStr <| (ToString.toString m).append "Is Invalid"
    board := board.applyMove playerMove
