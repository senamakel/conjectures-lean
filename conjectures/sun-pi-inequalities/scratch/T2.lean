import SunPi.Check
open SunPi.Check
set_option maxRecDepth 100000
#eval checkA 5 59
example : checkA 5 59 = true := by decide +kernel
