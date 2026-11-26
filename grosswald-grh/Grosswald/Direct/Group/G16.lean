import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0800
import Grosswald.Direct.Run.B0801
import Grosswald.Direct.Run.B0802
import Grosswald.Direct.Run.B0803
import Grosswald.Direct.Run.B0804
import Grosswald.Direct.Run.B0805
import Grosswald.Direct.Run.B0806
import Grosswald.Direct.Run.B0807
import Grosswald.Direct.Run.B0808
import Grosswald.Direct.Run.B0809
import Grosswald.Direct.Run.B0810
import Grosswald.Direct.Run.B0811
import Grosswald.Direct.Run.B0812
import Grosswald.Direct.Run.B0813
import Grosswald.Direct.Run.B0814
import Grosswald.Direct.Run.B0815
import Grosswald.Direct.Run.B0816
import Grosswald.Direct.Run.B0817
import Grosswald.Direct.Run.B0818
import Grosswald.Direct.Run.B0819
import Grosswald.Direct.Run.B0820
import Grosswald.Direct.Run.B0821
import Grosswald.Direct.Run.B0822
import Grosswald.Direct.Run.B0823
import Grosswald.Direct.Run.B0824
import Grosswald.Direct.Run.B0825
import Grosswald.Direct.Run.B0826
import Grosswald.Direct.Run.B0827
import Grosswald.Direct.Run.B0828
import Grosswald.Direct.Run.B0829
import Grosswald.Direct.Run.B0830
import Grosswald.Direct.Run.B0831
import Grosswald.Direct.Run.B0832
import Grosswald.Direct.Run.B0833
import Grosswald.Direct.Run.B0834
import Grosswald.Direct.Run.B0835
import Grosswald.Direct.Run.B0836
import Grosswald.Direct.Run.B0837
import Grosswald.Direct.Run.B0838
import Grosswald.Direct.Run.B0839
import Grosswald.Direct.Run.B0840
import Grosswald.Direct.Run.B0841
import Grosswald.Direct.Run.B0842
import Grosswald.Direct.Run.B0843
import Grosswald.Direct.Run.B0844
import Grosswald.Direct.Run.B0845
import Grosswald.Direct.Run.B0846
import Grosswald.Direct.Run.B0847
import Grosswald.Direct.Run.B0848
import Grosswald.Direct.Run.B0849

namespace Grosswald.Direct
open GrosswaldCompute
theorem g16 : segsOk 20000000 3200100000411 5000 = true := by
  have h0849 : segsOk 20000000 3396100000411 100 = true := Run.b0849
  have h0848 : segsOk 20000000 3392100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0848 h0849 (by norm_num)
  have h0847 : segsOk 20000000 3388100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0847 h0848 (by norm_num)
  have h0846 : segsOk 20000000 3384100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0846 h0847 (by norm_num)
  have h0845 : segsOk 20000000 3380100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0845 h0846 (by norm_num)
  have h0844 : segsOk 20000000 3376100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0844 h0845 (by norm_num)
  have h0843 : segsOk 20000000 3372100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0843 h0844 (by norm_num)
  have h0842 : segsOk 20000000 3368100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0842 h0843 (by norm_num)
  have h0841 : segsOk 20000000 3364100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0841 h0842 (by norm_num)
  have h0840 : segsOk 20000000 3360100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0840 h0841 (by norm_num)
  have h0839 : segsOk 20000000 3356100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0839 h0840 (by norm_num)
  have h0838 : segsOk 20000000 3352100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0838 h0839 (by norm_num)
  have h0837 : segsOk 20000000 3348100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0837 h0838 (by norm_num)
  have h0836 : segsOk 20000000 3344100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0836 h0837 (by norm_num)
  have h0835 : segsOk 20000000 3340100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0835 h0836 (by norm_num)
  have h0834 : segsOk 20000000 3336100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0834 h0835 (by norm_num)
  have h0833 : segsOk 20000000 3332100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0833 h0834 (by norm_num)
  have h0832 : segsOk 20000000 3328100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0832 h0833 (by norm_num)
  have h0831 : segsOk 20000000 3324100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0831 h0832 (by norm_num)
  have h0830 : segsOk 20000000 3320100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0830 h0831 (by norm_num)
  have h0829 : segsOk 20000000 3316100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0829 h0830 (by norm_num)
  have h0828 : segsOk 20000000 3312100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0828 h0829 (by norm_num)
  have h0827 : segsOk 20000000 3308100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0827 h0828 (by norm_num)
  have h0826 : segsOk 20000000 3304100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0826 h0827 (by norm_num)
  have h0825 : segsOk 20000000 3300100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0825 h0826 (by norm_num)
  have h0824 : segsOk 20000000 3296100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0824 h0825 (by norm_num)
  have h0823 : segsOk 20000000 3292100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0823 h0824 (by norm_num)
  have h0822 : segsOk 20000000 3288100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0822 h0823 (by norm_num)
  have h0821 : segsOk 20000000 3284100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0821 h0822 (by norm_num)
  have h0820 : segsOk 20000000 3280100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0820 h0821 (by norm_num)
  have h0819 : segsOk 20000000 3276100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0819 h0820 (by norm_num)
  have h0818 : segsOk 20000000 3272100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0818 h0819 (by norm_num)
  have h0817 : segsOk 20000000 3268100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0817 h0818 (by norm_num)
  have h0816 : segsOk 20000000 3264100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0816 h0817 (by norm_num)
  have h0815 : segsOk 20000000 3260100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0815 h0816 (by norm_num)
  have h0814 : segsOk 20000000 3256100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0814 h0815 (by norm_num)
  have h0813 : segsOk 20000000 3252100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0813 h0814 (by norm_num)
  have h0812 : segsOk 20000000 3248100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0812 h0813 (by norm_num)
  have h0811 : segsOk 20000000 3244100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0811 h0812 (by norm_num)
  have h0810 : segsOk 20000000 3240100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0810 h0811 (by norm_num)
  have h0809 : segsOk 20000000 3236100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0809 h0810 (by norm_num)
  have h0808 : segsOk 20000000 3232100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0808 h0809 (by norm_num)
  have h0807 : segsOk 20000000 3228100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0807 h0808 (by norm_num)
  have h0806 : segsOk 20000000 3224100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0806 h0807 (by norm_num)
  have h0805 : segsOk 20000000 3220100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0805 h0806 (by norm_num)
  have h0804 : segsOk 20000000 3216100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0804 h0805 (by norm_num)
  have h0803 : segsOk 20000000 3212100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0803 h0804 (by norm_num)
  have h0802 : segsOk 20000000 3208100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0802 h0803 (by norm_num)
  have h0801 : segsOk 20000000 3204100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0801 h0802 (by norm_num)
  have h0800 : segsOk 20000000 3200100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0800 h0801 (by norm_num)
  exact h0800
end Grosswald.Direct
