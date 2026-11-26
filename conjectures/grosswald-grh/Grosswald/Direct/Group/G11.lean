import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0550
import Grosswald.Direct.Run.B0551
import Grosswald.Direct.Run.B0552
import Grosswald.Direct.Run.B0553
import Grosswald.Direct.Run.B0554
import Grosswald.Direct.Run.B0555
import Grosswald.Direct.Run.B0556
import Grosswald.Direct.Run.B0557
import Grosswald.Direct.Run.B0558
import Grosswald.Direct.Run.B0559
import Grosswald.Direct.Run.B0560
import Grosswald.Direct.Run.B0561
import Grosswald.Direct.Run.B0562
import Grosswald.Direct.Run.B0563
import Grosswald.Direct.Run.B0564
import Grosswald.Direct.Run.B0565
import Grosswald.Direct.Run.B0566
import Grosswald.Direct.Run.B0567
import Grosswald.Direct.Run.B0568
import Grosswald.Direct.Run.B0569
import Grosswald.Direct.Run.B0570
import Grosswald.Direct.Run.B0571
import Grosswald.Direct.Run.B0572
import Grosswald.Direct.Run.B0573
import Grosswald.Direct.Run.B0574
import Grosswald.Direct.Run.B0575
import Grosswald.Direct.Run.B0576
import Grosswald.Direct.Run.B0577
import Grosswald.Direct.Run.B0578
import Grosswald.Direct.Run.B0579
import Grosswald.Direct.Run.B0580
import Grosswald.Direct.Run.B0581
import Grosswald.Direct.Run.B0582
import Grosswald.Direct.Run.B0583
import Grosswald.Direct.Run.B0584
import Grosswald.Direct.Run.B0585
import Grosswald.Direct.Run.B0586
import Grosswald.Direct.Run.B0587
import Grosswald.Direct.Run.B0588
import Grosswald.Direct.Run.B0589
import Grosswald.Direct.Run.B0590
import Grosswald.Direct.Run.B0591
import Grosswald.Direct.Run.B0592
import Grosswald.Direct.Run.B0593
import Grosswald.Direct.Run.B0594
import Grosswald.Direct.Run.B0595
import Grosswald.Direct.Run.B0596
import Grosswald.Direct.Run.B0597
import Grosswald.Direct.Run.B0598
import Grosswald.Direct.Run.B0599

namespace Grosswald.Direct
open GrosswaldCompute
theorem g11 : segsOk 20000000 2200100000411 5000 = true := by
  have h0599 : segsOk 20000000 2396100000411 100 = true := Run.b0599
  have h0598 : segsOk 20000000 2392100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0598 h0599 (by norm_num)
  have h0597 : segsOk 20000000 2388100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0597 h0598 (by norm_num)
  have h0596 : segsOk 20000000 2384100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0596 h0597 (by norm_num)
  have h0595 : segsOk 20000000 2380100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0595 h0596 (by norm_num)
  have h0594 : segsOk 20000000 2376100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0594 h0595 (by norm_num)
  have h0593 : segsOk 20000000 2372100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0593 h0594 (by norm_num)
  have h0592 : segsOk 20000000 2368100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0592 h0593 (by norm_num)
  have h0591 : segsOk 20000000 2364100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0591 h0592 (by norm_num)
  have h0590 : segsOk 20000000 2360100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0590 h0591 (by norm_num)
  have h0589 : segsOk 20000000 2356100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0589 h0590 (by norm_num)
  have h0588 : segsOk 20000000 2352100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0588 h0589 (by norm_num)
  have h0587 : segsOk 20000000 2348100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0587 h0588 (by norm_num)
  have h0586 : segsOk 20000000 2344100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0586 h0587 (by norm_num)
  have h0585 : segsOk 20000000 2340100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0585 h0586 (by norm_num)
  have h0584 : segsOk 20000000 2336100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0584 h0585 (by norm_num)
  have h0583 : segsOk 20000000 2332100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0583 h0584 (by norm_num)
  have h0582 : segsOk 20000000 2328100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0582 h0583 (by norm_num)
  have h0581 : segsOk 20000000 2324100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0581 h0582 (by norm_num)
  have h0580 : segsOk 20000000 2320100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0580 h0581 (by norm_num)
  have h0579 : segsOk 20000000 2316100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0579 h0580 (by norm_num)
  have h0578 : segsOk 20000000 2312100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0578 h0579 (by norm_num)
  have h0577 : segsOk 20000000 2308100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0577 h0578 (by norm_num)
  have h0576 : segsOk 20000000 2304100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0576 h0577 (by norm_num)
  have h0575 : segsOk 20000000 2300100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0575 h0576 (by norm_num)
  have h0574 : segsOk 20000000 2296100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0574 h0575 (by norm_num)
  have h0573 : segsOk 20000000 2292100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0573 h0574 (by norm_num)
  have h0572 : segsOk 20000000 2288100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0572 h0573 (by norm_num)
  have h0571 : segsOk 20000000 2284100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0571 h0572 (by norm_num)
  have h0570 : segsOk 20000000 2280100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0570 h0571 (by norm_num)
  have h0569 : segsOk 20000000 2276100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0569 h0570 (by norm_num)
  have h0568 : segsOk 20000000 2272100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0568 h0569 (by norm_num)
  have h0567 : segsOk 20000000 2268100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0567 h0568 (by norm_num)
  have h0566 : segsOk 20000000 2264100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0566 h0567 (by norm_num)
  have h0565 : segsOk 20000000 2260100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0565 h0566 (by norm_num)
  have h0564 : segsOk 20000000 2256100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0564 h0565 (by norm_num)
  have h0563 : segsOk 20000000 2252100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0563 h0564 (by norm_num)
  have h0562 : segsOk 20000000 2248100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0562 h0563 (by norm_num)
  have h0561 : segsOk 20000000 2244100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0561 h0562 (by norm_num)
  have h0560 : segsOk 20000000 2240100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0560 h0561 (by norm_num)
  have h0559 : segsOk 20000000 2236100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0559 h0560 (by norm_num)
  have h0558 : segsOk 20000000 2232100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0558 h0559 (by norm_num)
  have h0557 : segsOk 20000000 2228100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0557 h0558 (by norm_num)
  have h0556 : segsOk 20000000 2224100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0556 h0557 (by norm_num)
  have h0555 : segsOk 20000000 2220100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0555 h0556 (by norm_num)
  have h0554 : segsOk 20000000 2216100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0554 h0555 (by norm_num)
  have h0553 : segsOk 20000000 2212100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0553 h0554 (by norm_num)
  have h0552 : segsOk 20000000 2208100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0552 h0553 (by norm_num)
  have h0551 : segsOk 20000000 2204100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0551 h0552 (by norm_num)
  have h0550 : segsOk 20000000 2200100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0550 h0551 (by norm_num)
  exact h0550
end Grosswald.Direct
