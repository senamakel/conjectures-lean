import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0900
import Grosswald.Direct.Run.B0901
import Grosswald.Direct.Run.B0902
import Grosswald.Direct.Run.B0903
import Grosswald.Direct.Run.B0904
import Grosswald.Direct.Run.B0905
import Grosswald.Direct.Run.B0906
import Grosswald.Direct.Run.B0907
import Grosswald.Direct.Run.B0908
import Grosswald.Direct.Run.B0909
import Grosswald.Direct.Run.B0910
import Grosswald.Direct.Run.B0911
import Grosswald.Direct.Run.B0912
import Grosswald.Direct.Run.B0913
import Grosswald.Direct.Run.B0914
import Grosswald.Direct.Run.B0915
import Grosswald.Direct.Run.B0916
import Grosswald.Direct.Run.B0917
import Grosswald.Direct.Run.B0918
import Grosswald.Direct.Run.B0919
import Grosswald.Direct.Run.B0920
import Grosswald.Direct.Run.B0921
import Grosswald.Direct.Run.B0922
import Grosswald.Direct.Run.B0923
import Grosswald.Direct.Run.B0924
import Grosswald.Direct.Run.B0925
import Grosswald.Direct.Run.B0926
import Grosswald.Direct.Run.B0927
import Grosswald.Direct.Run.B0928
import Grosswald.Direct.Run.B0929
import Grosswald.Direct.Run.B0930
import Grosswald.Direct.Run.B0931
import Grosswald.Direct.Run.B0932
import Grosswald.Direct.Run.B0933
import Grosswald.Direct.Run.B0934
import Grosswald.Direct.Run.B0935
import Grosswald.Direct.Run.B0936
import Grosswald.Direct.Run.B0937
import Grosswald.Direct.Run.B0938
import Grosswald.Direct.Run.B0939
import Grosswald.Direct.Run.B0940
import Grosswald.Direct.Run.B0941
import Grosswald.Direct.Run.B0942
import Grosswald.Direct.Run.B0943
import Grosswald.Direct.Run.B0944
import Grosswald.Direct.Run.B0945
import Grosswald.Direct.Run.B0946
import Grosswald.Direct.Run.B0947
import Grosswald.Direct.Run.B0948
import Grosswald.Direct.Run.B0949

namespace Grosswald.Direct
open GrosswaldCompute
theorem g18 : segsOk 20000000 3600100000411 5000 = true := by
  have h0949 : segsOk 20000000 3796100000411 100 = true := Run.b0949
  have h0948 : segsOk 20000000 3792100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0948 h0949 (by norm_num)
  have h0947 : segsOk 20000000 3788100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0947 h0948 (by norm_num)
  have h0946 : segsOk 20000000 3784100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0946 h0947 (by norm_num)
  have h0945 : segsOk 20000000 3780100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0945 h0946 (by norm_num)
  have h0944 : segsOk 20000000 3776100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0944 h0945 (by norm_num)
  have h0943 : segsOk 20000000 3772100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0943 h0944 (by norm_num)
  have h0942 : segsOk 20000000 3768100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0942 h0943 (by norm_num)
  have h0941 : segsOk 20000000 3764100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0941 h0942 (by norm_num)
  have h0940 : segsOk 20000000 3760100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0940 h0941 (by norm_num)
  have h0939 : segsOk 20000000 3756100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0939 h0940 (by norm_num)
  have h0938 : segsOk 20000000 3752100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0938 h0939 (by norm_num)
  have h0937 : segsOk 20000000 3748100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0937 h0938 (by norm_num)
  have h0936 : segsOk 20000000 3744100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0936 h0937 (by norm_num)
  have h0935 : segsOk 20000000 3740100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0935 h0936 (by norm_num)
  have h0934 : segsOk 20000000 3736100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0934 h0935 (by norm_num)
  have h0933 : segsOk 20000000 3732100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0933 h0934 (by norm_num)
  have h0932 : segsOk 20000000 3728100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0932 h0933 (by norm_num)
  have h0931 : segsOk 20000000 3724100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0931 h0932 (by norm_num)
  have h0930 : segsOk 20000000 3720100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0930 h0931 (by norm_num)
  have h0929 : segsOk 20000000 3716100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0929 h0930 (by norm_num)
  have h0928 : segsOk 20000000 3712100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0928 h0929 (by norm_num)
  have h0927 : segsOk 20000000 3708100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0927 h0928 (by norm_num)
  have h0926 : segsOk 20000000 3704100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0926 h0927 (by norm_num)
  have h0925 : segsOk 20000000 3700100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0925 h0926 (by norm_num)
  have h0924 : segsOk 20000000 3696100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0924 h0925 (by norm_num)
  have h0923 : segsOk 20000000 3692100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0923 h0924 (by norm_num)
  have h0922 : segsOk 20000000 3688100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0922 h0923 (by norm_num)
  have h0921 : segsOk 20000000 3684100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0921 h0922 (by norm_num)
  have h0920 : segsOk 20000000 3680100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0920 h0921 (by norm_num)
  have h0919 : segsOk 20000000 3676100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0919 h0920 (by norm_num)
  have h0918 : segsOk 20000000 3672100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0918 h0919 (by norm_num)
  have h0917 : segsOk 20000000 3668100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0917 h0918 (by norm_num)
  have h0916 : segsOk 20000000 3664100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0916 h0917 (by norm_num)
  have h0915 : segsOk 20000000 3660100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0915 h0916 (by norm_num)
  have h0914 : segsOk 20000000 3656100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0914 h0915 (by norm_num)
  have h0913 : segsOk 20000000 3652100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0913 h0914 (by norm_num)
  have h0912 : segsOk 20000000 3648100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0912 h0913 (by norm_num)
  have h0911 : segsOk 20000000 3644100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0911 h0912 (by norm_num)
  have h0910 : segsOk 20000000 3640100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0910 h0911 (by norm_num)
  have h0909 : segsOk 20000000 3636100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0909 h0910 (by norm_num)
  have h0908 : segsOk 20000000 3632100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0908 h0909 (by norm_num)
  have h0907 : segsOk 20000000 3628100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0907 h0908 (by norm_num)
  have h0906 : segsOk 20000000 3624100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0906 h0907 (by norm_num)
  have h0905 : segsOk 20000000 3620100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0905 h0906 (by norm_num)
  have h0904 : segsOk 20000000 3616100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0904 h0905 (by norm_num)
  have h0903 : segsOk 20000000 3612100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0903 h0904 (by norm_num)
  have h0902 : segsOk 20000000 3608100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0902 h0903 (by norm_num)
  have h0901 : segsOk 20000000 3604100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0901 h0902 (by norm_num)
  have h0900 : segsOk 20000000 3600100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0900 h0901 (by norm_num)
  exact h0900
end Grosswald.Direct
