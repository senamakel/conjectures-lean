import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0600
import Grosswald.Direct.Run.B0601
import Grosswald.Direct.Run.B0602
import Grosswald.Direct.Run.B0603
import Grosswald.Direct.Run.B0604
import Grosswald.Direct.Run.B0605
import Grosswald.Direct.Run.B0606
import Grosswald.Direct.Run.B0607
import Grosswald.Direct.Run.B0608
import Grosswald.Direct.Run.B0609
import Grosswald.Direct.Run.B0610
import Grosswald.Direct.Run.B0611
import Grosswald.Direct.Run.B0612
import Grosswald.Direct.Run.B0613
import Grosswald.Direct.Run.B0614
import Grosswald.Direct.Run.B0615
import Grosswald.Direct.Run.B0616
import Grosswald.Direct.Run.B0617
import Grosswald.Direct.Run.B0618
import Grosswald.Direct.Run.B0619
import Grosswald.Direct.Run.B0620
import Grosswald.Direct.Run.B0621
import Grosswald.Direct.Run.B0622
import Grosswald.Direct.Run.B0623
import Grosswald.Direct.Run.B0624
import Grosswald.Direct.Run.B0625
import Grosswald.Direct.Run.B0626
import Grosswald.Direct.Run.B0627
import Grosswald.Direct.Run.B0628
import Grosswald.Direct.Run.B0629
import Grosswald.Direct.Run.B0630
import Grosswald.Direct.Run.B0631
import Grosswald.Direct.Run.B0632
import Grosswald.Direct.Run.B0633
import Grosswald.Direct.Run.B0634
import Grosswald.Direct.Run.B0635
import Grosswald.Direct.Run.B0636
import Grosswald.Direct.Run.B0637
import Grosswald.Direct.Run.B0638
import Grosswald.Direct.Run.B0639
import Grosswald.Direct.Run.B0640
import Grosswald.Direct.Run.B0641
import Grosswald.Direct.Run.B0642
import Grosswald.Direct.Run.B0643
import Grosswald.Direct.Run.B0644
import Grosswald.Direct.Run.B0645
import Grosswald.Direct.Run.B0646
import Grosswald.Direct.Run.B0647
import Grosswald.Direct.Run.B0648
import Grosswald.Direct.Run.B0649

namespace Grosswald.Direct
open GrosswaldCompute
theorem g12 : segsOk 20000000 2400100000411 5000 = true := by
  have h0649 : segsOk 20000000 2596100000411 100 = true := Run.b0649
  have h0648 : segsOk 20000000 2592100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0648 h0649 (by norm_num)
  have h0647 : segsOk 20000000 2588100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0647 h0648 (by norm_num)
  have h0646 : segsOk 20000000 2584100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0646 h0647 (by norm_num)
  have h0645 : segsOk 20000000 2580100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0645 h0646 (by norm_num)
  have h0644 : segsOk 20000000 2576100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0644 h0645 (by norm_num)
  have h0643 : segsOk 20000000 2572100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0643 h0644 (by norm_num)
  have h0642 : segsOk 20000000 2568100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0642 h0643 (by norm_num)
  have h0641 : segsOk 20000000 2564100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0641 h0642 (by norm_num)
  have h0640 : segsOk 20000000 2560100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0640 h0641 (by norm_num)
  have h0639 : segsOk 20000000 2556100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0639 h0640 (by norm_num)
  have h0638 : segsOk 20000000 2552100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0638 h0639 (by norm_num)
  have h0637 : segsOk 20000000 2548100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0637 h0638 (by norm_num)
  have h0636 : segsOk 20000000 2544100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0636 h0637 (by norm_num)
  have h0635 : segsOk 20000000 2540100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0635 h0636 (by norm_num)
  have h0634 : segsOk 20000000 2536100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0634 h0635 (by norm_num)
  have h0633 : segsOk 20000000 2532100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0633 h0634 (by norm_num)
  have h0632 : segsOk 20000000 2528100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0632 h0633 (by norm_num)
  have h0631 : segsOk 20000000 2524100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0631 h0632 (by norm_num)
  have h0630 : segsOk 20000000 2520100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0630 h0631 (by norm_num)
  have h0629 : segsOk 20000000 2516100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0629 h0630 (by norm_num)
  have h0628 : segsOk 20000000 2512100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0628 h0629 (by norm_num)
  have h0627 : segsOk 20000000 2508100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0627 h0628 (by norm_num)
  have h0626 : segsOk 20000000 2504100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0626 h0627 (by norm_num)
  have h0625 : segsOk 20000000 2500100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0625 h0626 (by norm_num)
  have h0624 : segsOk 20000000 2496100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0624 h0625 (by norm_num)
  have h0623 : segsOk 20000000 2492100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0623 h0624 (by norm_num)
  have h0622 : segsOk 20000000 2488100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0622 h0623 (by norm_num)
  have h0621 : segsOk 20000000 2484100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0621 h0622 (by norm_num)
  have h0620 : segsOk 20000000 2480100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0620 h0621 (by norm_num)
  have h0619 : segsOk 20000000 2476100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0619 h0620 (by norm_num)
  have h0618 : segsOk 20000000 2472100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0618 h0619 (by norm_num)
  have h0617 : segsOk 20000000 2468100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0617 h0618 (by norm_num)
  have h0616 : segsOk 20000000 2464100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0616 h0617 (by norm_num)
  have h0615 : segsOk 20000000 2460100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0615 h0616 (by norm_num)
  have h0614 : segsOk 20000000 2456100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0614 h0615 (by norm_num)
  have h0613 : segsOk 20000000 2452100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0613 h0614 (by norm_num)
  have h0612 : segsOk 20000000 2448100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0612 h0613 (by norm_num)
  have h0611 : segsOk 20000000 2444100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0611 h0612 (by norm_num)
  have h0610 : segsOk 20000000 2440100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0610 h0611 (by norm_num)
  have h0609 : segsOk 20000000 2436100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0609 h0610 (by norm_num)
  have h0608 : segsOk 20000000 2432100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0608 h0609 (by norm_num)
  have h0607 : segsOk 20000000 2428100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0607 h0608 (by norm_num)
  have h0606 : segsOk 20000000 2424100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0606 h0607 (by norm_num)
  have h0605 : segsOk 20000000 2420100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0605 h0606 (by norm_num)
  have h0604 : segsOk 20000000 2416100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0604 h0605 (by norm_num)
  have h0603 : segsOk 20000000 2412100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0603 h0604 (by norm_num)
  have h0602 : segsOk 20000000 2408100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0602 h0603 (by norm_num)
  have h0601 : segsOk 20000000 2404100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0601 h0602 (by norm_num)
  have h0600 : segsOk 20000000 2400100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0600 h0601 (by norm_num)
  exact h0600
end Grosswald.Direct
