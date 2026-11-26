import SunPi.Check
open SunPi.Check
set_option maxRecDepth 100000
#eval checkB 3 4 722
#eval checkA 512 5 507
example : checkB 3 4 100 = true := by decide +kernel
