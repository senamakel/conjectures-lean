import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0950
import Grosswald.Direct.Run.B0951
import Grosswald.Direct.Run.B0952
import Grosswald.Direct.Run.B0953
import Grosswald.Direct.Run.B0954
import Grosswald.Direct.Run.B0955
import Grosswald.Direct.Run.B0956
import Grosswald.Direct.Run.B0957
import Grosswald.Direct.Run.B0958
import Grosswald.Direct.Run.B0959
import Grosswald.Direct.Run.B0960
import Grosswald.Direct.Run.B0961
import Grosswald.Direct.Run.B0962
import Grosswald.Direct.Run.B0963
import Grosswald.Direct.Run.B0964
import Grosswald.Direct.Run.B0965
import Grosswald.Direct.Run.B0966
import Grosswald.Direct.Run.B0967
import Grosswald.Direct.Run.B0968
import Grosswald.Direct.Run.B0969
import Grosswald.Direct.Run.B0970
import Grosswald.Direct.Run.B0971
import Grosswald.Direct.Run.B0972
import Grosswald.Direct.Run.B0973
import Grosswald.Direct.Run.B0974
import Grosswald.Direct.Run.B0975
import Grosswald.Direct.Run.B0976
import Grosswald.Direct.Run.B0977
import Grosswald.Direct.Run.B0978
import Grosswald.Direct.Run.B0979
import Grosswald.Direct.Run.B0980
import Grosswald.Direct.Run.B0981
import Grosswald.Direct.Run.B0982
import Grosswald.Direct.Run.B0983
import Grosswald.Direct.Run.B0984
import Grosswald.Direct.Run.B0985
import Grosswald.Direct.Run.B0986
import Grosswald.Direct.Run.B0987
import Grosswald.Direct.Run.B0988
import Grosswald.Direct.Run.B0989
import Grosswald.Direct.Run.B0990
import Grosswald.Direct.Run.B0991
import Grosswald.Direct.Run.B0992
import Grosswald.Direct.Run.B0993
import Grosswald.Direct.Run.B0994
import Grosswald.Direct.Run.B0995
import Grosswald.Direct.Run.B0996
import Grosswald.Direct.Run.B0997
import Grosswald.Direct.Run.B0998
import Grosswald.Direct.Run.B0999

namespace Grosswald.Direct
open GrosswaldCompute
theorem g19 : segsOk 20000000 3800100000411 5000 = true := by
  have h0999 : segsOk 20000000 3996100000411 100 = true := Run.b0999
  have h0998 : segsOk 20000000 3992100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0998 h0999 (by norm_num)
  have h0997 : segsOk 20000000 3988100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0997 h0998 (by norm_num)
  have h0996 : segsOk 20000000 3984100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0996 h0997 (by norm_num)
  have h0995 : segsOk 20000000 3980100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0995 h0996 (by norm_num)
  have h0994 : segsOk 20000000 3976100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0994 h0995 (by norm_num)
  have h0993 : segsOk 20000000 3972100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0993 h0994 (by norm_num)
  have h0992 : segsOk 20000000 3968100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0992 h0993 (by norm_num)
  have h0991 : segsOk 20000000 3964100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0991 h0992 (by norm_num)
  have h0990 : segsOk 20000000 3960100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0990 h0991 (by norm_num)
  have h0989 : segsOk 20000000 3956100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0989 h0990 (by norm_num)
  have h0988 : segsOk 20000000 3952100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0988 h0989 (by norm_num)
  have h0987 : segsOk 20000000 3948100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0987 h0988 (by norm_num)
  have h0986 : segsOk 20000000 3944100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0986 h0987 (by norm_num)
  have h0985 : segsOk 20000000 3940100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0985 h0986 (by norm_num)
  have h0984 : segsOk 20000000 3936100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0984 h0985 (by norm_num)
  have h0983 : segsOk 20000000 3932100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0983 h0984 (by norm_num)
  have h0982 : segsOk 20000000 3928100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0982 h0983 (by norm_num)
  have h0981 : segsOk 20000000 3924100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0981 h0982 (by norm_num)
  have h0980 : segsOk 20000000 3920100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0980 h0981 (by norm_num)
  have h0979 : segsOk 20000000 3916100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0979 h0980 (by norm_num)
  have h0978 : segsOk 20000000 3912100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0978 h0979 (by norm_num)
  have h0977 : segsOk 20000000 3908100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0977 h0978 (by norm_num)
  have h0976 : segsOk 20000000 3904100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0976 h0977 (by norm_num)
  have h0975 : segsOk 20000000 3900100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0975 h0976 (by norm_num)
  have h0974 : segsOk 20000000 3896100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0974 h0975 (by norm_num)
  have h0973 : segsOk 20000000 3892100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0973 h0974 (by norm_num)
  have h0972 : segsOk 20000000 3888100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0972 h0973 (by norm_num)
  have h0971 : segsOk 20000000 3884100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0971 h0972 (by norm_num)
  have h0970 : segsOk 20000000 3880100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0970 h0971 (by norm_num)
  have h0969 : segsOk 20000000 3876100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0969 h0970 (by norm_num)
  have h0968 : segsOk 20000000 3872100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0968 h0969 (by norm_num)
  have h0967 : segsOk 20000000 3868100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0967 h0968 (by norm_num)
  have h0966 : segsOk 20000000 3864100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0966 h0967 (by norm_num)
  have h0965 : segsOk 20000000 3860100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0965 h0966 (by norm_num)
  have h0964 : segsOk 20000000 3856100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0964 h0965 (by norm_num)
  have h0963 : segsOk 20000000 3852100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0963 h0964 (by norm_num)
  have h0962 : segsOk 20000000 3848100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0962 h0963 (by norm_num)
  have h0961 : segsOk 20000000 3844100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0961 h0962 (by norm_num)
  have h0960 : segsOk 20000000 3840100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0960 h0961 (by norm_num)
  have h0959 : segsOk 20000000 3836100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0959 h0960 (by norm_num)
  have h0958 : segsOk 20000000 3832100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0958 h0959 (by norm_num)
  have h0957 : segsOk 20000000 3828100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0957 h0958 (by norm_num)
  have h0956 : segsOk 20000000 3824100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0956 h0957 (by norm_num)
  have h0955 : segsOk 20000000 3820100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0955 h0956 (by norm_num)
  have h0954 : segsOk 20000000 3816100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0954 h0955 (by norm_num)
  have h0953 : segsOk 20000000 3812100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0953 h0954 (by norm_num)
  have h0952 : segsOk 20000000 3808100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0952 h0953 (by norm_num)
  have h0951 : segsOk 20000000 3804100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0951 h0952 (by norm_num)
  have h0950 : segsOk 20000000 3800100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0950 h0951 (by norm_num)
  exact h0950
end Grosswald.Direct
