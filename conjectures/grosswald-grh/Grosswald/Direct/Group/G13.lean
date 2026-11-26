import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0650
import Grosswald.Direct.Run.B0651
import Grosswald.Direct.Run.B0652
import Grosswald.Direct.Run.B0653
import Grosswald.Direct.Run.B0654
import Grosswald.Direct.Run.B0655
import Grosswald.Direct.Run.B0656
import Grosswald.Direct.Run.B0657
import Grosswald.Direct.Run.B0658
import Grosswald.Direct.Run.B0659
import Grosswald.Direct.Run.B0660
import Grosswald.Direct.Run.B0661
import Grosswald.Direct.Run.B0662
import Grosswald.Direct.Run.B0663
import Grosswald.Direct.Run.B0664
import Grosswald.Direct.Run.B0665
import Grosswald.Direct.Run.B0666
import Grosswald.Direct.Run.B0667
import Grosswald.Direct.Run.B0668
import Grosswald.Direct.Run.B0669
import Grosswald.Direct.Run.B0670
import Grosswald.Direct.Run.B0671
import Grosswald.Direct.Run.B0672
import Grosswald.Direct.Run.B0673
import Grosswald.Direct.Run.B0674
import Grosswald.Direct.Run.B0675
import Grosswald.Direct.Run.B0676
import Grosswald.Direct.Run.B0677
import Grosswald.Direct.Run.B0678
import Grosswald.Direct.Run.B0679
import Grosswald.Direct.Run.B0680
import Grosswald.Direct.Run.B0681
import Grosswald.Direct.Run.B0682
import Grosswald.Direct.Run.B0683
import Grosswald.Direct.Run.B0684
import Grosswald.Direct.Run.B0685
import Grosswald.Direct.Run.B0686
import Grosswald.Direct.Run.B0687
import Grosswald.Direct.Run.B0688
import Grosswald.Direct.Run.B0689
import Grosswald.Direct.Run.B0690
import Grosswald.Direct.Run.B0691
import Grosswald.Direct.Run.B0692
import Grosswald.Direct.Run.B0693
import Grosswald.Direct.Run.B0694
import Grosswald.Direct.Run.B0695
import Grosswald.Direct.Run.B0696
import Grosswald.Direct.Run.B0697
import Grosswald.Direct.Run.B0698
import Grosswald.Direct.Run.B0699

namespace Grosswald.Direct
open GrosswaldCompute
theorem g13 : segsOk 20000000 2600100000411 5000 = true := by
  have h0699 : segsOk 20000000 2796100000411 100 = true := Run.b0699
  have h0698 : segsOk 20000000 2792100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0698 h0699 (by norm_num)
  have h0697 : segsOk 20000000 2788100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0697 h0698 (by norm_num)
  have h0696 : segsOk 20000000 2784100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0696 h0697 (by norm_num)
  have h0695 : segsOk 20000000 2780100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0695 h0696 (by norm_num)
  have h0694 : segsOk 20000000 2776100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0694 h0695 (by norm_num)
  have h0693 : segsOk 20000000 2772100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0693 h0694 (by norm_num)
  have h0692 : segsOk 20000000 2768100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0692 h0693 (by norm_num)
  have h0691 : segsOk 20000000 2764100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0691 h0692 (by norm_num)
  have h0690 : segsOk 20000000 2760100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0690 h0691 (by norm_num)
  have h0689 : segsOk 20000000 2756100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0689 h0690 (by norm_num)
  have h0688 : segsOk 20000000 2752100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0688 h0689 (by norm_num)
  have h0687 : segsOk 20000000 2748100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0687 h0688 (by norm_num)
  have h0686 : segsOk 20000000 2744100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0686 h0687 (by norm_num)
  have h0685 : segsOk 20000000 2740100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0685 h0686 (by norm_num)
  have h0684 : segsOk 20000000 2736100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0684 h0685 (by norm_num)
  have h0683 : segsOk 20000000 2732100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0683 h0684 (by norm_num)
  have h0682 : segsOk 20000000 2728100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0682 h0683 (by norm_num)
  have h0681 : segsOk 20000000 2724100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0681 h0682 (by norm_num)
  have h0680 : segsOk 20000000 2720100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0680 h0681 (by norm_num)
  have h0679 : segsOk 20000000 2716100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0679 h0680 (by norm_num)
  have h0678 : segsOk 20000000 2712100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0678 h0679 (by norm_num)
  have h0677 : segsOk 20000000 2708100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0677 h0678 (by norm_num)
  have h0676 : segsOk 20000000 2704100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0676 h0677 (by norm_num)
  have h0675 : segsOk 20000000 2700100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0675 h0676 (by norm_num)
  have h0674 : segsOk 20000000 2696100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0674 h0675 (by norm_num)
  have h0673 : segsOk 20000000 2692100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0673 h0674 (by norm_num)
  have h0672 : segsOk 20000000 2688100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0672 h0673 (by norm_num)
  have h0671 : segsOk 20000000 2684100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0671 h0672 (by norm_num)
  have h0670 : segsOk 20000000 2680100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0670 h0671 (by norm_num)
  have h0669 : segsOk 20000000 2676100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0669 h0670 (by norm_num)
  have h0668 : segsOk 20000000 2672100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0668 h0669 (by norm_num)
  have h0667 : segsOk 20000000 2668100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0667 h0668 (by norm_num)
  have h0666 : segsOk 20000000 2664100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0666 h0667 (by norm_num)
  have h0665 : segsOk 20000000 2660100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0665 h0666 (by norm_num)
  have h0664 : segsOk 20000000 2656100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0664 h0665 (by norm_num)
  have h0663 : segsOk 20000000 2652100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0663 h0664 (by norm_num)
  have h0662 : segsOk 20000000 2648100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0662 h0663 (by norm_num)
  have h0661 : segsOk 20000000 2644100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0661 h0662 (by norm_num)
  have h0660 : segsOk 20000000 2640100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0660 h0661 (by norm_num)
  have h0659 : segsOk 20000000 2636100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0659 h0660 (by norm_num)
  have h0658 : segsOk 20000000 2632100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0658 h0659 (by norm_num)
  have h0657 : segsOk 20000000 2628100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0657 h0658 (by norm_num)
  have h0656 : segsOk 20000000 2624100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0656 h0657 (by norm_num)
  have h0655 : segsOk 20000000 2620100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0655 h0656 (by norm_num)
  have h0654 : segsOk 20000000 2616100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0654 h0655 (by norm_num)
  have h0653 : segsOk 20000000 2612100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0653 h0654 (by norm_num)
  have h0652 : segsOk 20000000 2608100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0652 h0653 (by norm_num)
  have h0651 : segsOk 20000000 2604100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0651 h0652 (by norm_num)
  have h0650 : segsOk 20000000 2600100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0650 h0651 (by norm_num)
  exact h0650
end Grosswald.Direct
