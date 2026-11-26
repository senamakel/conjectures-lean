import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0850
import Grosswald.Direct.Run.B0851
import Grosswald.Direct.Run.B0852
import Grosswald.Direct.Run.B0853
import Grosswald.Direct.Run.B0854
import Grosswald.Direct.Run.B0855
import Grosswald.Direct.Run.B0856
import Grosswald.Direct.Run.B0857
import Grosswald.Direct.Run.B0858
import Grosswald.Direct.Run.B0859
import Grosswald.Direct.Run.B0860
import Grosswald.Direct.Run.B0861
import Grosswald.Direct.Run.B0862
import Grosswald.Direct.Run.B0863
import Grosswald.Direct.Run.B0864
import Grosswald.Direct.Run.B0865
import Grosswald.Direct.Run.B0866
import Grosswald.Direct.Run.B0867
import Grosswald.Direct.Run.B0868
import Grosswald.Direct.Run.B0869
import Grosswald.Direct.Run.B0870
import Grosswald.Direct.Run.B0871
import Grosswald.Direct.Run.B0872
import Grosswald.Direct.Run.B0873
import Grosswald.Direct.Run.B0874
import Grosswald.Direct.Run.B0875
import Grosswald.Direct.Run.B0876
import Grosswald.Direct.Run.B0877
import Grosswald.Direct.Run.B0878
import Grosswald.Direct.Run.B0879
import Grosswald.Direct.Run.B0880
import Grosswald.Direct.Run.B0881
import Grosswald.Direct.Run.B0882
import Grosswald.Direct.Run.B0883
import Grosswald.Direct.Run.B0884
import Grosswald.Direct.Run.B0885
import Grosswald.Direct.Run.B0886
import Grosswald.Direct.Run.B0887
import Grosswald.Direct.Run.B0888
import Grosswald.Direct.Run.B0889
import Grosswald.Direct.Run.B0890
import Grosswald.Direct.Run.B0891
import Grosswald.Direct.Run.B0892
import Grosswald.Direct.Run.B0893
import Grosswald.Direct.Run.B0894
import Grosswald.Direct.Run.B0895
import Grosswald.Direct.Run.B0896
import Grosswald.Direct.Run.B0897
import Grosswald.Direct.Run.B0898
import Grosswald.Direct.Run.B0899

namespace Grosswald.Direct
open GrosswaldCompute
theorem g17 : segsOk 20000000 3400100000411 5000 = true := by
  have h0899 : segsOk 20000000 3596100000411 100 = true := Run.b0899
  have h0898 : segsOk 20000000 3592100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0898 h0899 (by norm_num)
  have h0897 : segsOk 20000000 3588100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0897 h0898 (by norm_num)
  have h0896 : segsOk 20000000 3584100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0896 h0897 (by norm_num)
  have h0895 : segsOk 20000000 3580100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0895 h0896 (by norm_num)
  have h0894 : segsOk 20000000 3576100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0894 h0895 (by norm_num)
  have h0893 : segsOk 20000000 3572100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0893 h0894 (by norm_num)
  have h0892 : segsOk 20000000 3568100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0892 h0893 (by norm_num)
  have h0891 : segsOk 20000000 3564100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0891 h0892 (by norm_num)
  have h0890 : segsOk 20000000 3560100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0890 h0891 (by norm_num)
  have h0889 : segsOk 20000000 3556100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0889 h0890 (by norm_num)
  have h0888 : segsOk 20000000 3552100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0888 h0889 (by norm_num)
  have h0887 : segsOk 20000000 3548100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0887 h0888 (by norm_num)
  have h0886 : segsOk 20000000 3544100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0886 h0887 (by norm_num)
  have h0885 : segsOk 20000000 3540100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0885 h0886 (by norm_num)
  have h0884 : segsOk 20000000 3536100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0884 h0885 (by norm_num)
  have h0883 : segsOk 20000000 3532100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0883 h0884 (by norm_num)
  have h0882 : segsOk 20000000 3528100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0882 h0883 (by norm_num)
  have h0881 : segsOk 20000000 3524100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0881 h0882 (by norm_num)
  have h0880 : segsOk 20000000 3520100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0880 h0881 (by norm_num)
  have h0879 : segsOk 20000000 3516100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0879 h0880 (by norm_num)
  have h0878 : segsOk 20000000 3512100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0878 h0879 (by norm_num)
  have h0877 : segsOk 20000000 3508100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0877 h0878 (by norm_num)
  have h0876 : segsOk 20000000 3504100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0876 h0877 (by norm_num)
  have h0875 : segsOk 20000000 3500100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0875 h0876 (by norm_num)
  have h0874 : segsOk 20000000 3496100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0874 h0875 (by norm_num)
  have h0873 : segsOk 20000000 3492100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0873 h0874 (by norm_num)
  have h0872 : segsOk 20000000 3488100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0872 h0873 (by norm_num)
  have h0871 : segsOk 20000000 3484100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0871 h0872 (by norm_num)
  have h0870 : segsOk 20000000 3480100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0870 h0871 (by norm_num)
  have h0869 : segsOk 20000000 3476100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0869 h0870 (by norm_num)
  have h0868 : segsOk 20000000 3472100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0868 h0869 (by norm_num)
  have h0867 : segsOk 20000000 3468100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0867 h0868 (by norm_num)
  have h0866 : segsOk 20000000 3464100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0866 h0867 (by norm_num)
  have h0865 : segsOk 20000000 3460100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0865 h0866 (by norm_num)
  have h0864 : segsOk 20000000 3456100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0864 h0865 (by norm_num)
  have h0863 : segsOk 20000000 3452100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0863 h0864 (by norm_num)
  have h0862 : segsOk 20000000 3448100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0862 h0863 (by norm_num)
  have h0861 : segsOk 20000000 3444100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0861 h0862 (by norm_num)
  have h0860 : segsOk 20000000 3440100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0860 h0861 (by norm_num)
  have h0859 : segsOk 20000000 3436100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0859 h0860 (by norm_num)
  have h0858 : segsOk 20000000 3432100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0858 h0859 (by norm_num)
  have h0857 : segsOk 20000000 3428100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0857 h0858 (by norm_num)
  have h0856 : segsOk 20000000 3424100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0856 h0857 (by norm_num)
  have h0855 : segsOk 20000000 3420100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0855 h0856 (by norm_num)
  have h0854 : segsOk 20000000 3416100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0854 h0855 (by norm_num)
  have h0853 : segsOk 20000000 3412100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0853 h0854 (by norm_num)
  have h0852 : segsOk 20000000 3408100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0852 h0853 (by norm_num)
  have h0851 : segsOk 20000000 3404100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0851 h0852 (by norm_num)
  have h0850 : segsOk 20000000 3400100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0850 h0851 (by norm_num)
  exact h0850
end Grosswald.Direct
