import SunPi.Check
open SunPi.Check
set_option maxRecDepth 100000
set_option trace.profiler true in
theorem t : checkA 5 59 = true := by decide +kernel
