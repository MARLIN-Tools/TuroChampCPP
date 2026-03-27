# TuroChampCPP

An easily-accessable and easy-to-use UCI-focused recreation of TuroChamp, the paper chess engine made by Alan Turing.

## Rules of TuroChamp (per ChessBase's article)

- Piece Values: Pawn=1, knight=3, bishop=3½, rook=5, queen=10.
- Mobility: For the Q,R,B,N, add the square root of the number of moves the piece can make; count each capture as two moves.
- Piece safety: For the R,B,N, add 1.0 point if it is defended, and 1.5 points if it is defended at least twice.
- King mobility: For the K, the same as (1) except for castling moves.
- King safety: For the K, deduct points for its vulnerability as follows: assume that a Queen of the same colour is on the King's square; calculate its mobility, and then subtract this value from the score.
- Castling: Add 1.0 point for the possibility of still being able to castle on a later move if a King or Rook move is being considered; add another point if castling can take place on the next move; finally add one more point for actually castling.
- Pawn credit: Add 0.2 point for each rank advanced, and 0.3 point for being defended by a non-Pawn.
- Mates and checks: Add 1.0 point for the threat of mate and 0.5 point for a check.

## Settings

- Depth: by default it is 3 to match Turing's original process, though it can be configured to be any value from 1-4, any higher value would be too slow without adding additional search features which would change evaluation.
- Q-Search Depth: by default is 8, for captures and checks. Can be set to any value from 0 to 32.
- ModernSearch: Enables an aggressive modern search mode with a transposition table, null-move pruning, move reductions, futility pruning, and SEE-based q-search pruning. It is much faster, but it is no longer evaluation-identical to the historical search.
- HashMB: The hash size of the transposition table... in MB.

## Sources used when researching and working on interpreting the rules:

- <https://www.chessprogramming.org/Turochamp>
- <https://en.wikipedia.org/wiki/Turochamp>
- <https://en.chessbase.com/post/reconstructing-turing-s-paper-machine>
- <https://github.com/pol-rivero/Turochamp-Chess-Challenge>
- <https://github.com/mdoege/PyTuroChamp>
