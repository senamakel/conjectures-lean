def get0 : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: l, n + 1 => get0 l n

def addPre : List Nat → List Nat → List Nat
  | [], l => l
  | _ :: _, [] => []
  | x :: a, y :: l => (x + y) :: addPre a l

def stepAux (d : Nat) : Nat → List Nat → List Nat
  | 0, l => l
  | _ + 1, [] => []
  | f + 1, x :: l => (x :: l).take d ++ stepAux d f (addPre ((x :: l).take d) ((x :: l).drop d))

def iterPow (d : Nat) (F : Nat) : Nat → List Nat → List Nat
  | 0, l => l
  | k + 1, l => iterPow d F k (stepAux d F l)

def coeffList (m F : Nat) (l : List Nat) : Nat → List Nat
  | 0 => l
  | N + 1 => iterPow (2 ^ N) F m (coeffList m F l N)

def bList (m N L : Nat) : List Nat := coeffList m (L + 1) (1 :: List.replicate L 0) N

set_option maxRecDepth 100000 in
example : get0 (bList 15 8 128) 128 = 66243595743894015443321698798500 := by decide +kernel
set_option maxRecDepth 100000 in
example : get0 (bList 31 9 256) 256 = 3052369194453650254501535715298757541552490784809850699183520381604 := by decide +kernel
