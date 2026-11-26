import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0700
import Grosswald.Direct.Run.B0701
import Grosswald.Direct.Run.B0702
import Grosswald.Direct.Run.B0703
import Grosswald.Direct.Run.B0704
import Grosswald.Direct.Run.B0705
import Grosswald.Direct.Run.B0706
import Grosswald.Direct.Run.B0707
import Grosswald.Direct.Run.B0708
import Grosswald.Direct.Run.B0709
import Grosswald.Direct.Run.B0710
import Grosswald.Direct.Run.B0711
import Grosswald.Direct.Run.B0712
import Grosswald.Direct.Run.B0713
import Grosswald.Direct.Run.B0714
import Grosswald.Direct.Run.B0715
import Grosswald.Direct.Run.B0716
import Grosswald.Direct.Run.B0717
import Grosswald.Direct.Run.B0718
import Grosswald.Direct.Run.B0719
import Grosswald.Direct.Run.B0720
import Grosswald.Direct.Run.B0721
import Grosswald.Direct.Run.B0722
import Grosswald.Direct.Run.B0723
import Grosswald.Direct.Run.B0724
import Grosswald.Direct.Run.B0725
import Grosswald.Direct.Run.B0726
import Grosswald.Direct.Run.B0727
import Grosswald.Direct.Run.B0728
import Grosswald.Direct.Run.B0729
import Grosswald.Direct.Run.B0730
import Grosswald.Direct.Run.B0731
import Grosswald.Direct.Run.B0732
import Grosswald.Direct.Run.B0733
import Grosswald.Direct.Run.B0734
import Grosswald.Direct.Run.B0735
import Grosswald.Direct.Run.B0736
import Grosswald.Direct.Run.B0737
import Grosswald.Direct.Run.B0738
import Grosswald.Direct.Run.B0739
import Grosswald.Direct.Run.B0740
import Grosswald.Direct.Run.B0741
import Grosswald.Direct.Run.B0742
import Grosswald.Direct.Run.B0743
import Grosswald.Direct.Run.B0744
import Grosswald.Direct.Run.B0745
import Grosswald.Direct.Run.B0746
import Grosswald.Direct.Run.B0747
import Grosswald.Direct.Run.B0748
import Grosswald.Direct.Run.B0749

namespace Grosswald.Direct
open GrosswaldCompute
theorem g14 : segsOk 20000000 2800100000411 5000 = true := by
  have h0749 : segsOk 20000000 2996100000411 100 = true := Run.b0749
  have h0748 : segsOk 20000000 2992100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0748 h0749 (by norm_num)
  have h0747 : segsOk 20000000 2988100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0747 h0748 (by norm_num)
  have h0746 : segsOk 20000000 2984100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0746 h0747 (by norm_num)
  have h0745 : segsOk 20000000 2980100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0745 h0746 (by norm_num)
  have h0744 : segsOk 20000000 2976100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0744 h0745 (by norm_num)
  have h0743 : segsOk 20000000 2972100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0743 h0744 (by norm_num)
  have h0742 : segsOk 20000000 2968100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0742 h0743 (by norm_num)
  have h0741 : segsOk 20000000 2964100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0741 h0742 (by norm_num)
  have h0740 : segsOk 20000000 2960100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0740 h0741 (by norm_num)
  have h0739 : segsOk 20000000 2956100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0739 h0740 (by norm_num)
  have h0738 : segsOk 20000000 2952100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0738 h0739 (by norm_num)
  have h0737 : segsOk 20000000 2948100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0737 h0738 (by norm_num)
  have h0736 : segsOk 20000000 2944100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0736 h0737 (by norm_num)
  have h0735 : segsOk 20000000 2940100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0735 h0736 (by norm_num)
  have h0734 : segsOk 20000000 2936100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0734 h0735 (by norm_num)
  have h0733 : segsOk 20000000 2932100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0733 h0734 (by norm_num)
  have h0732 : segsOk 20000000 2928100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0732 h0733 (by norm_num)
  have h0731 : segsOk 20000000 2924100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0731 h0732 (by norm_num)
  have h0730 : segsOk 20000000 2920100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0730 h0731 (by norm_num)
  have h0729 : segsOk 20000000 2916100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0729 h0730 (by norm_num)
  have h0728 : segsOk 20000000 2912100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0728 h0729 (by norm_num)
  have h0727 : segsOk 20000000 2908100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0727 h0728 (by norm_num)
  have h0726 : segsOk 20000000 2904100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0726 h0727 (by norm_num)
  have h0725 : segsOk 20000000 2900100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0725 h0726 (by norm_num)
  have h0724 : segsOk 20000000 2896100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0724 h0725 (by norm_num)
  have h0723 : segsOk 20000000 2892100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0723 h0724 (by norm_num)
  have h0722 : segsOk 20000000 2888100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0722 h0723 (by norm_num)
  have h0721 : segsOk 20000000 2884100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0721 h0722 (by norm_num)
  have h0720 : segsOk 20000000 2880100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0720 h0721 (by norm_num)
  have h0719 : segsOk 20000000 2876100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0719 h0720 (by norm_num)
  have h0718 : segsOk 20000000 2872100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0718 h0719 (by norm_num)
  have h0717 : segsOk 20000000 2868100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0717 h0718 (by norm_num)
  have h0716 : segsOk 20000000 2864100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0716 h0717 (by norm_num)
  have h0715 : segsOk 20000000 2860100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0715 h0716 (by norm_num)
  have h0714 : segsOk 20000000 2856100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0714 h0715 (by norm_num)
  have h0713 : segsOk 20000000 2852100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0713 h0714 (by norm_num)
  have h0712 : segsOk 20000000 2848100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0712 h0713 (by norm_num)
  have h0711 : segsOk 20000000 2844100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0711 h0712 (by norm_num)
  have h0710 : segsOk 20000000 2840100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0710 h0711 (by norm_num)
  have h0709 : segsOk 20000000 2836100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0709 h0710 (by norm_num)
  have h0708 : segsOk 20000000 2832100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0708 h0709 (by norm_num)
  have h0707 : segsOk 20000000 2828100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0707 h0708 (by norm_num)
  have h0706 : segsOk 20000000 2824100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0706 h0707 (by norm_num)
  have h0705 : segsOk 20000000 2820100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0705 h0706 (by norm_num)
  have h0704 : segsOk 20000000 2816100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0704 h0705 (by norm_num)
  have h0703 : segsOk 20000000 2812100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0703 h0704 (by norm_num)
  have h0702 : segsOk 20000000 2808100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0702 h0703 (by norm_num)
  have h0701 : segsOk 20000000 2804100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0701 h0702 (by norm_num)
  have h0700 : segsOk 20000000 2800100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0700 h0701 (by norm_num)
  exact h0700
end Grosswald.Direct
