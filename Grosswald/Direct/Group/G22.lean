import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1100
import Grosswald.Direct.Run.B1101
import Grosswald.Direct.Run.B1102
import Grosswald.Direct.Run.B1103
import Grosswald.Direct.Run.B1104
import Grosswald.Direct.Run.B1105
import Grosswald.Direct.Run.B1106
import Grosswald.Direct.Run.B1107
import Grosswald.Direct.Run.B1108
import Grosswald.Direct.Run.B1109
import Grosswald.Direct.Run.B1110
import Grosswald.Direct.Run.B1111
import Grosswald.Direct.Run.B1112
import Grosswald.Direct.Run.B1113
import Grosswald.Direct.Run.B1114
import Grosswald.Direct.Run.B1115
import Grosswald.Direct.Run.B1116
import Grosswald.Direct.Run.B1117
import Grosswald.Direct.Run.B1118
import Grosswald.Direct.Run.B1119
import Grosswald.Direct.Run.B1120
import Grosswald.Direct.Run.B1121
import Grosswald.Direct.Run.B1122
import Grosswald.Direct.Run.B1123
import Grosswald.Direct.Run.B1124
import Grosswald.Direct.Run.B1125
import Grosswald.Direct.Run.B1126
import Grosswald.Direct.Run.B1127
import Grosswald.Direct.Run.B1128
import Grosswald.Direct.Run.B1129
import Grosswald.Direct.Run.B1130
import Grosswald.Direct.Run.B1131
import Grosswald.Direct.Run.B1132
import Grosswald.Direct.Run.B1133
import Grosswald.Direct.Run.B1134
import Grosswald.Direct.Run.B1135
import Grosswald.Direct.Run.B1136
import Grosswald.Direct.Run.B1137
import Grosswald.Direct.Run.B1138
import Grosswald.Direct.Run.B1139
import Grosswald.Direct.Run.B1140
import Grosswald.Direct.Run.B1141
import Grosswald.Direct.Run.B1142
import Grosswald.Direct.Run.B1143
import Grosswald.Direct.Run.B1144
import Grosswald.Direct.Run.B1145
import Grosswald.Direct.Run.B1146
import Grosswald.Direct.Run.B1147
import Grosswald.Direct.Run.B1148
import Grosswald.Direct.Run.B1149

namespace Grosswald.Direct
open GrosswaldCompute
theorem g22 : segsOk 20000000 4400100000411 5000 = true := by
  have h1149 : segsOk 20000000 4596100000411 100 = true := Run.b1149
  have h1148 : segsOk 20000000 4592100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1148 h1149 (by norm_num)
  have h1147 : segsOk 20000000 4588100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1147 h1148 (by norm_num)
  have h1146 : segsOk 20000000 4584100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1146 h1147 (by norm_num)
  have h1145 : segsOk 20000000 4580100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1145 h1146 (by norm_num)
  have h1144 : segsOk 20000000 4576100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1144 h1145 (by norm_num)
  have h1143 : segsOk 20000000 4572100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1143 h1144 (by norm_num)
  have h1142 : segsOk 20000000 4568100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1142 h1143 (by norm_num)
  have h1141 : segsOk 20000000 4564100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1141 h1142 (by norm_num)
  have h1140 : segsOk 20000000 4560100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1140 h1141 (by norm_num)
  have h1139 : segsOk 20000000 4556100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1139 h1140 (by norm_num)
  have h1138 : segsOk 20000000 4552100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1138 h1139 (by norm_num)
  have h1137 : segsOk 20000000 4548100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1137 h1138 (by norm_num)
  have h1136 : segsOk 20000000 4544100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1136 h1137 (by norm_num)
  have h1135 : segsOk 20000000 4540100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1135 h1136 (by norm_num)
  have h1134 : segsOk 20000000 4536100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1134 h1135 (by norm_num)
  have h1133 : segsOk 20000000 4532100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1133 h1134 (by norm_num)
  have h1132 : segsOk 20000000 4528100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1132 h1133 (by norm_num)
  have h1131 : segsOk 20000000 4524100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1131 h1132 (by norm_num)
  have h1130 : segsOk 20000000 4520100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1130 h1131 (by norm_num)
  have h1129 : segsOk 20000000 4516100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1129 h1130 (by norm_num)
  have h1128 : segsOk 20000000 4512100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1128 h1129 (by norm_num)
  have h1127 : segsOk 20000000 4508100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1127 h1128 (by norm_num)
  have h1126 : segsOk 20000000 4504100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1126 h1127 (by norm_num)
  have h1125 : segsOk 20000000 4500100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1125 h1126 (by norm_num)
  have h1124 : segsOk 20000000 4496100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1124 h1125 (by norm_num)
  have h1123 : segsOk 20000000 4492100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1123 h1124 (by norm_num)
  have h1122 : segsOk 20000000 4488100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1122 h1123 (by norm_num)
  have h1121 : segsOk 20000000 4484100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1121 h1122 (by norm_num)
  have h1120 : segsOk 20000000 4480100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1120 h1121 (by norm_num)
  have h1119 : segsOk 20000000 4476100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1119 h1120 (by norm_num)
  have h1118 : segsOk 20000000 4472100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1118 h1119 (by norm_num)
  have h1117 : segsOk 20000000 4468100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1117 h1118 (by norm_num)
  have h1116 : segsOk 20000000 4464100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1116 h1117 (by norm_num)
  have h1115 : segsOk 20000000 4460100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1115 h1116 (by norm_num)
  have h1114 : segsOk 20000000 4456100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1114 h1115 (by norm_num)
  have h1113 : segsOk 20000000 4452100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1113 h1114 (by norm_num)
  have h1112 : segsOk 20000000 4448100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1112 h1113 (by norm_num)
  have h1111 : segsOk 20000000 4444100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1111 h1112 (by norm_num)
  have h1110 : segsOk 20000000 4440100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1110 h1111 (by norm_num)
  have h1109 : segsOk 20000000 4436100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1109 h1110 (by norm_num)
  have h1108 : segsOk 20000000 4432100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1108 h1109 (by norm_num)
  have h1107 : segsOk 20000000 4428100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1107 h1108 (by norm_num)
  have h1106 : segsOk 20000000 4424100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1106 h1107 (by norm_num)
  have h1105 : segsOk 20000000 4420100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1105 h1106 (by norm_num)
  have h1104 : segsOk 20000000 4416100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1104 h1105 (by norm_num)
  have h1103 : segsOk 20000000 4412100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1103 h1104 (by norm_num)
  have h1102 : segsOk 20000000 4408100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1102 h1103 (by norm_num)
  have h1101 : segsOk 20000000 4404100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1101 h1102 (by norm_num)
  have h1100 : segsOk 20000000 4400100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1100 h1101 (by norm_num)
  exact h1100
end Grosswald.Direct
