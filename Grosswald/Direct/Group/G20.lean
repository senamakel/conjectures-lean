import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1000
import Grosswald.Direct.Run.B1001
import Grosswald.Direct.Run.B1002
import Grosswald.Direct.Run.B1003
import Grosswald.Direct.Run.B1004
import Grosswald.Direct.Run.B1005
import Grosswald.Direct.Run.B1006
import Grosswald.Direct.Run.B1007
import Grosswald.Direct.Run.B1008
import Grosswald.Direct.Run.B1009
import Grosswald.Direct.Run.B1010
import Grosswald.Direct.Run.B1011
import Grosswald.Direct.Run.B1012
import Grosswald.Direct.Run.B1013
import Grosswald.Direct.Run.B1014
import Grosswald.Direct.Run.B1015
import Grosswald.Direct.Run.B1016
import Grosswald.Direct.Run.B1017
import Grosswald.Direct.Run.B1018
import Grosswald.Direct.Run.B1019
import Grosswald.Direct.Run.B1020
import Grosswald.Direct.Run.B1021
import Grosswald.Direct.Run.B1022
import Grosswald.Direct.Run.B1023
import Grosswald.Direct.Run.B1024
import Grosswald.Direct.Run.B1025
import Grosswald.Direct.Run.B1026
import Grosswald.Direct.Run.B1027
import Grosswald.Direct.Run.B1028
import Grosswald.Direct.Run.B1029
import Grosswald.Direct.Run.B1030
import Grosswald.Direct.Run.B1031
import Grosswald.Direct.Run.B1032
import Grosswald.Direct.Run.B1033
import Grosswald.Direct.Run.B1034
import Grosswald.Direct.Run.B1035
import Grosswald.Direct.Run.B1036
import Grosswald.Direct.Run.B1037
import Grosswald.Direct.Run.B1038
import Grosswald.Direct.Run.B1039
import Grosswald.Direct.Run.B1040
import Grosswald.Direct.Run.B1041
import Grosswald.Direct.Run.B1042
import Grosswald.Direct.Run.B1043
import Grosswald.Direct.Run.B1044
import Grosswald.Direct.Run.B1045
import Grosswald.Direct.Run.B1046
import Grosswald.Direct.Run.B1047
import Grosswald.Direct.Run.B1048
import Grosswald.Direct.Run.B1049

namespace Grosswald.Direct
open GrosswaldCompute
theorem g20 : segsOk 20000000 4000100000411 5000 = true := by
  have h1049 : segsOk 20000000 4196100000411 100 = true := Run.b1049
  have h1048 : segsOk 20000000 4192100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1048 h1049 (by norm_num)
  have h1047 : segsOk 20000000 4188100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1047 h1048 (by norm_num)
  have h1046 : segsOk 20000000 4184100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1046 h1047 (by norm_num)
  have h1045 : segsOk 20000000 4180100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1045 h1046 (by norm_num)
  have h1044 : segsOk 20000000 4176100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1044 h1045 (by norm_num)
  have h1043 : segsOk 20000000 4172100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1043 h1044 (by norm_num)
  have h1042 : segsOk 20000000 4168100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1042 h1043 (by norm_num)
  have h1041 : segsOk 20000000 4164100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1041 h1042 (by norm_num)
  have h1040 : segsOk 20000000 4160100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1040 h1041 (by norm_num)
  have h1039 : segsOk 20000000 4156100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1039 h1040 (by norm_num)
  have h1038 : segsOk 20000000 4152100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1038 h1039 (by norm_num)
  have h1037 : segsOk 20000000 4148100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1037 h1038 (by norm_num)
  have h1036 : segsOk 20000000 4144100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1036 h1037 (by norm_num)
  have h1035 : segsOk 20000000 4140100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1035 h1036 (by norm_num)
  have h1034 : segsOk 20000000 4136100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1034 h1035 (by norm_num)
  have h1033 : segsOk 20000000 4132100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1033 h1034 (by norm_num)
  have h1032 : segsOk 20000000 4128100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1032 h1033 (by norm_num)
  have h1031 : segsOk 20000000 4124100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1031 h1032 (by norm_num)
  have h1030 : segsOk 20000000 4120100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1030 h1031 (by norm_num)
  have h1029 : segsOk 20000000 4116100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1029 h1030 (by norm_num)
  have h1028 : segsOk 20000000 4112100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1028 h1029 (by norm_num)
  have h1027 : segsOk 20000000 4108100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1027 h1028 (by norm_num)
  have h1026 : segsOk 20000000 4104100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1026 h1027 (by norm_num)
  have h1025 : segsOk 20000000 4100100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1025 h1026 (by norm_num)
  have h1024 : segsOk 20000000 4096100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1024 h1025 (by norm_num)
  have h1023 : segsOk 20000000 4092100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1023 h1024 (by norm_num)
  have h1022 : segsOk 20000000 4088100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1022 h1023 (by norm_num)
  have h1021 : segsOk 20000000 4084100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1021 h1022 (by norm_num)
  have h1020 : segsOk 20000000 4080100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1020 h1021 (by norm_num)
  have h1019 : segsOk 20000000 4076100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1019 h1020 (by norm_num)
  have h1018 : segsOk 20000000 4072100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1018 h1019 (by norm_num)
  have h1017 : segsOk 20000000 4068100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1017 h1018 (by norm_num)
  have h1016 : segsOk 20000000 4064100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1016 h1017 (by norm_num)
  have h1015 : segsOk 20000000 4060100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1015 h1016 (by norm_num)
  have h1014 : segsOk 20000000 4056100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1014 h1015 (by norm_num)
  have h1013 : segsOk 20000000 4052100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1013 h1014 (by norm_num)
  have h1012 : segsOk 20000000 4048100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1012 h1013 (by norm_num)
  have h1011 : segsOk 20000000 4044100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1011 h1012 (by norm_num)
  have h1010 : segsOk 20000000 4040100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1010 h1011 (by norm_num)
  have h1009 : segsOk 20000000 4036100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1009 h1010 (by norm_num)
  have h1008 : segsOk 20000000 4032100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1008 h1009 (by norm_num)
  have h1007 : segsOk 20000000 4028100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1007 h1008 (by norm_num)
  have h1006 : segsOk 20000000 4024100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1006 h1007 (by norm_num)
  have h1005 : segsOk 20000000 4020100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1005 h1006 (by norm_num)
  have h1004 : segsOk 20000000 4016100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1004 h1005 (by norm_num)
  have h1003 : segsOk 20000000 4012100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1003 h1004 (by norm_num)
  have h1002 : segsOk 20000000 4008100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1002 h1003 (by norm_num)
  have h1001 : segsOk 20000000 4004100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1001 h1002 (by norm_num)
  have h1000 : segsOk 20000000 4000100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1000 h1001 (by norm_num)
  exact h1000
end Grosswald.Direct
