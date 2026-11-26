import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0750
import Grosswald.Direct.Run.B0751
import Grosswald.Direct.Run.B0752
import Grosswald.Direct.Run.B0753
import Grosswald.Direct.Run.B0754
import Grosswald.Direct.Run.B0755
import Grosswald.Direct.Run.B0756
import Grosswald.Direct.Run.B0757
import Grosswald.Direct.Run.B0758
import Grosswald.Direct.Run.B0759
import Grosswald.Direct.Run.B0760
import Grosswald.Direct.Run.B0761
import Grosswald.Direct.Run.B0762
import Grosswald.Direct.Run.B0763
import Grosswald.Direct.Run.B0764
import Grosswald.Direct.Run.B0765
import Grosswald.Direct.Run.B0766
import Grosswald.Direct.Run.B0767
import Grosswald.Direct.Run.B0768
import Grosswald.Direct.Run.B0769
import Grosswald.Direct.Run.B0770
import Grosswald.Direct.Run.B0771
import Grosswald.Direct.Run.B0772
import Grosswald.Direct.Run.B0773
import Grosswald.Direct.Run.B0774
import Grosswald.Direct.Run.B0775
import Grosswald.Direct.Run.B0776
import Grosswald.Direct.Run.B0777
import Grosswald.Direct.Run.B0778
import Grosswald.Direct.Run.B0779
import Grosswald.Direct.Run.B0780
import Grosswald.Direct.Run.B0781
import Grosswald.Direct.Run.B0782
import Grosswald.Direct.Run.B0783
import Grosswald.Direct.Run.B0784
import Grosswald.Direct.Run.B0785
import Grosswald.Direct.Run.B0786
import Grosswald.Direct.Run.B0787
import Grosswald.Direct.Run.B0788
import Grosswald.Direct.Run.B0789
import Grosswald.Direct.Run.B0790
import Grosswald.Direct.Run.B0791
import Grosswald.Direct.Run.B0792
import Grosswald.Direct.Run.B0793
import Grosswald.Direct.Run.B0794
import Grosswald.Direct.Run.B0795
import Grosswald.Direct.Run.B0796
import Grosswald.Direct.Run.B0797
import Grosswald.Direct.Run.B0798
import Grosswald.Direct.Run.B0799

namespace Grosswald.Direct
open GrosswaldCompute
theorem g15 : segsOk 20000000 3000100000411 5000 = true := by
  have h0799 : segsOk 20000000 3196100000411 100 = true := Run.b0799
  have h0798 : segsOk 20000000 3192100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0798 h0799 (by norm_num)
  have h0797 : segsOk 20000000 3188100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0797 h0798 (by norm_num)
  have h0796 : segsOk 20000000 3184100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0796 h0797 (by norm_num)
  have h0795 : segsOk 20000000 3180100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0795 h0796 (by norm_num)
  have h0794 : segsOk 20000000 3176100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0794 h0795 (by norm_num)
  have h0793 : segsOk 20000000 3172100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0793 h0794 (by norm_num)
  have h0792 : segsOk 20000000 3168100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0792 h0793 (by norm_num)
  have h0791 : segsOk 20000000 3164100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0791 h0792 (by norm_num)
  have h0790 : segsOk 20000000 3160100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0790 h0791 (by norm_num)
  have h0789 : segsOk 20000000 3156100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0789 h0790 (by norm_num)
  have h0788 : segsOk 20000000 3152100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0788 h0789 (by norm_num)
  have h0787 : segsOk 20000000 3148100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0787 h0788 (by norm_num)
  have h0786 : segsOk 20000000 3144100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0786 h0787 (by norm_num)
  have h0785 : segsOk 20000000 3140100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0785 h0786 (by norm_num)
  have h0784 : segsOk 20000000 3136100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0784 h0785 (by norm_num)
  have h0783 : segsOk 20000000 3132100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0783 h0784 (by norm_num)
  have h0782 : segsOk 20000000 3128100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0782 h0783 (by norm_num)
  have h0781 : segsOk 20000000 3124100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0781 h0782 (by norm_num)
  have h0780 : segsOk 20000000 3120100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0780 h0781 (by norm_num)
  have h0779 : segsOk 20000000 3116100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0779 h0780 (by norm_num)
  have h0778 : segsOk 20000000 3112100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0778 h0779 (by norm_num)
  have h0777 : segsOk 20000000 3108100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0777 h0778 (by norm_num)
  have h0776 : segsOk 20000000 3104100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0776 h0777 (by norm_num)
  have h0775 : segsOk 20000000 3100100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0775 h0776 (by norm_num)
  have h0774 : segsOk 20000000 3096100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0774 h0775 (by norm_num)
  have h0773 : segsOk 20000000 3092100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0773 h0774 (by norm_num)
  have h0772 : segsOk 20000000 3088100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0772 h0773 (by norm_num)
  have h0771 : segsOk 20000000 3084100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0771 h0772 (by norm_num)
  have h0770 : segsOk 20000000 3080100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0770 h0771 (by norm_num)
  have h0769 : segsOk 20000000 3076100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0769 h0770 (by norm_num)
  have h0768 : segsOk 20000000 3072100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0768 h0769 (by norm_num)
  have h0767 : segsOk 20000000 3068100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0767 h0768 (by norm_num)
  have h0766 : segsOk 20000000 3064100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0766 h0767 (by norm_num)
  have h0765 : segsOk 20000000 3060100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0765 h0766 (by norm_num)
  have h0764 : segsOk 20000000 3056100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0764 h0765 (by norm_num)
  have h0763 : segsOk 20000000 3052100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0763 h0764 (by norm_num)
  have h0762 : segsOk 20000000 3048100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0762 h0763 (by norm_num)
  have h0761 : segsOk 20000000 3044100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0761 h0762 (by norm_num)
  have h0760 : segsOk 20000000 3040100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0760 h0761 (by norm_num)
  have h0759 : segsOk 20000000 3036100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0759 h0760 (by norm_num)
  have h0758 : segsOk 20000000 3032100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0758 h0759 (by norm_num)
  have h0757 : segsOk 20000000 3028100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0757 h0758 (by norm_num)
  have h0756 : segsOk 20000000 3024100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0756 h0757 (by norm_num)
  have h0755 : segsOk 20000000 3020100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0755 h0756 (by norm_num)
  have h0754 : segsOk 20000000 3016100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0754 h0755 (by norm_num)
  have h0753 : segsOk 20000000 3012100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0753 h0754 (by norm_num)
  have h0752 : segsOk 20000000 3008100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0752 h0753 (by norm_num)
  have h0751 : segsOk 20000000 3004100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0751 h0752 (by norm_num)
  have h0750 : segsOk 20000000 3000100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0750 h0751 (by norm_num)
  exact h0750
end Grosswald.Direct
