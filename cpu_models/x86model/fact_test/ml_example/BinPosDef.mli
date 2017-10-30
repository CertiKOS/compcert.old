module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg
 end
