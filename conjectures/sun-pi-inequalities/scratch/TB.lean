import SunPi.Check
open SunPi.Check
set_option trace.profiler true in
theorem t : checkB 3 4 697 = true := by native_decide
