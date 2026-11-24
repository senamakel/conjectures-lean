import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1050
import Grosswald.Direct.Run.B1051
import Grosswald.Direct.Run.B1052
import Grosswald.Direct.Run.B1053
import Grosswald.Direct.Run.B1054
import Grosswald.Direct.Run.B1055
import Grosswald.Direct.Run.B1056
import Grosswald.Direct.Run.B1057
import Grosswald.Direct.Run.B1058
import Grosswald.Direct.Run.B1059
import Grosswald.Direct.Run.B1060
import Grosswald.Direct.Run.B1061
import Grosswald.Direct.Run.B1062
import Grosswald.Direct.Run.B1063
import Grosswald.Direct.Run.B1064
import Grosswald.Direct.Run.B1065
import Grosswald.Direct.Run.B1066
import Grosswald.Direct.Run.B1067
import Grosswald.Direct.Run.B1068
import Grosswald.Direct.Run.B1069
import Grosswald.Direct.Run.B1070
import Grosswald.Direct.Run.B1071
import Grosswald.Direct.Run.B1072
import Grosswald.Direct.Run.B1073
import Grosswald.Direct.Run.B1074
import Grosswald.Direct.Run.B1075
import Grosswald.Direct.Run.B1076
import Grosswald.Direct.Run.B1077
import Grosswald.Direct.Run.B1078
import Grosswald.Direct.Run.B1079
import Grosswald.Direct.Run.B1080
import Grosswald.Direct.Run.B1081
import Grosswald.Direct.Run.B1082
import Grosswald.Direct.Run.B1083
import Grosswald.Direct.Run.B1084
import Grosswald.Direct.Run.B1085
import Grosswald.Direct.Run.B1086
import Grosswald.Direct.Run.B1087
import Grosswald.Direct.Run.B1088
import Grosswald.Direct.Run.B1089
import Grosswald.Direct.Run.B1090
import Grosswald.Direct.Run.B1091
import Grosswald.Direct.Run.B1092
import Grosswald.Direct.Run.B1093
import Grosswald.Direct.Run.B1094
import Grosswald.Direct.Run.B1095
import Grosswald.Direct.Run.B1096
import Grosswald.Direct.Run.B1097
import Grosswald.Direct.Run.B1098
import Grosswald.Direct.Run.B1099

namespace Grosswald.Direct
open GrosswaldCompute
theorem g21 : segsOk 20000000 4200100000411 5000 = true := by
  have h1099 : segsOk 20000000 4396100000411 100 = true := Run.b1099
  have h1098 : segsOk 20000000 4392100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1098 h1099 (by norm_num)
  have h1097 : segsOk 20000000 4388100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1097 h1098 (by norm_num)
  have h1096 : segsOk 20000000 4384100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1096 h1097 (by norm_num)
  have h1095 : segsOk 20000000 4380100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1095 h1096 (by norm_num)
  have h1094 : segsOk 20000000 4376100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1094 h1095 (by norm_num)
  have h1093 : segsOk 20000000 4372100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1093 h1094 (by norm_num)
  have h1092 : segsOk 20000000 4368100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1092 h1093 (by norm_num)
  have h1091 : segsOk 20000000 4364100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1091 h1092 (by norm_num)
  have h1090 : segsOk 20000000 4360100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1090 h1091 (by norm_num)
  have h1089 : segsOk 20000000 4356100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1089 h1090 (by norm_num)
  have h1088 : segsOk 20000000 4352100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1088 h1089 (by norm_num)
  have h1087 : segsOk 20000000 4348100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1087 h1088 (by norm_num)
  have h1086 : segsOk 20000000 4344100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1086 h1087 (by norm_num)
  have h1085 : segsOk 20000000 4340100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1085 h1086 (by norm_num)
  have h1084 : segsOk 20000000 4336100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1084 h1085 (by norm_num)
  have h1083 : segsOk 20000000 4332100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1083 h1084 (by norm_num)
  have h1082 : segsOk 20000000 4328100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1082 h1083 (by norm_num)
  have h1081 : segsOk 20000000 4324100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1081 h1082 (by norm_num)
  have h1080 : segsOk 20000000 4320100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1080 h1081 (by norm_num)
  have h1079 : segsOk 20000000 4316100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1079 h1080 (by norm_num)
  have h1078 : segsOk 20000000 4312100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1078 h1079 (by norm_num)
  have h1077 : segsOk 20000000 4308100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1077 h1078 (by norm_num)
  have h1076 : segsOk 20000000 4304100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1076 h1077 (by norm_num)
  have h1075 : segsOk 20000000 4300100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1075 h1076 (by norm_num)
  have h1074 : segsOk 20000000 4296100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1074 h1075 (by norm_num)
  have h1073 : segsOk 20000000 4292100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1073 h1074 (by norm_num)
  have h1072 : segsOk 20000000 4288100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1072 h1073 (by norm_num)
  have h1071 : segsOk 20000000 4284100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1071 h1072 (by norm_num)
  have h1070 : segsOk 20000000 4280100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1070 h1071 (by norm_num)
  have h1069 : segsOk 20000000 4276100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1069 h1070 (by norm_num)
  have h1068 : segsOk 20000000 4272100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1068 h1069 (by norm_num)
  have h1067 : segsOk 20000000 4268100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1067 h1068 (by norm_num)
  have h1066 : segsOk 20000000 4264100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1066 h1067 (by norm_num)
  have h1065 : segsOk 20000000 4260100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1065 h1066 (by norm_num)
  have h1064 : segsOk 20000000 4256100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1064 h1065 (by norm_num)
  have h1063 : segsOk 20000000 4252100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1063 h1064 (by norm_num)
  have h1062 : segsOk 20000000 4248100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1062 h1063 (by norm_num)
  have h1061 : segsOk 20000000 4244100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1061 h1062 (by norm_num)
  have h1060 : segsOk 20000000 4240100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1060 h1061 (by norm_num)
  have h1059 : segsOk 20000000 4236100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1059 h1060 (by norm_num)
  have h1058 : segsOk 20000000 4232100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1058 h1059 (by norm_num)
  have h1057 : segsOk 20000000 4228100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1057 h1058 (by norm_num)
  have h1056 : segsOk 20000000 4224100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1056 h1057 (by norm_num)
  have h1055 : segsOk 20000000 4220100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1055 h1056 (by norm_num)
  have h1054 : segsOk 20000000 4216100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1054 h1055 (by norm_num)
  have h1053 : segsOk 20000000 4212100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1053 h1054 (by norm_num)
  have h1052 : segsOk 20000000 4208100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1052 h1053 (by norm_num)
  have h1051 : segsOk 20000000 4204100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1051 h1052 (by norm_num)
  have h1050 : segsOk 20000000 4200100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1050 h1051 (by norm_num)
  exact h1050
end Grosswald.Direct
