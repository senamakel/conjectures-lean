import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1150
import Grosswald.Direct.Run.B1151
import Grosswald.Direct.Run.B1152
import Grosswald.Direct.Run.B1153
import Grosswald.Direct.Run.B1154
import Grosswald.Direct.Run.B1155
import Grosswald.Direct.Run.B1156
import Grosswald.Direct.Run.B1157
import Grosswald.Direct.Run.B1158
import Grosswald.Direct.Run.B1159
import Grosswald.Direct.Run.B1160
import Grosswald.Direct.Run.B1161
import Grosswald.Direct.Run.B1162
import Grosswald.Direct.Run.B1163
import Grosswald.Direct.Run.B1164
import Grosswald.Direct.Run.B1165
import Grosswald.Direct.Run.B1166
import Grosswald.Direct.Run.B1167
import Grosswald.Direct.Run.B1168
import Grosswald.Direct.Run.B1169
import Grosswald.Direct.Run.B1170
import Grosswald.Direct.Run.B1171
import Grosswald.Direct.Run.B1172
import Grosswald.Direct.Run.B1173
import Grosswald.Direct.Run.B1174
import Grosswald.Direct.Run.B1175
import Grosswald.Direct.Run.B1176
import Grosswald.Direct.Run.B1177
import Grosswald.Direct.Run.B1178
import Grosswald.Direct.Run.B1179
import Grosswald.Direct.Run.B1180
import Grosswald.Direct.Run.B1181
import Grosswald.Direct.Run.B1182
import Grosswald.Direct.Run.B1183
import Grosswald.Direct.Run.B1184
import Grosswald.Direct.Run.B1185
import Grosswald.Direct.Run.B1186
import Grosswald.Direct.Run.B1187
import Grosswald.Direct.Run.B1188
import Grosswald.Direct.Run.B1189
import Grosswald.Direct.Run.B1190
import Grosswald.Direct.Run.B1191
import Grosswald.Direct.Run.B1192
import Grosswald.Direct.Run.B1193
import Grosswald.Direct.Run.B1194
import Grosswald.Direct.Run.B1195
import Grosswald.Direct.Run.B1196
import Grosswald.Direct.Run.B1197
import Grosswald.Direct.Run.B1198
import Grosswald.Direct.Run.B1199

namespace Grosswald.Direct
open GrosswaldCompute
theorem g23 : segsOk 20000000 4600100000411 5000 = true := by
  have h1199 : segsOk 20000000 4796100000411 100 = true := Run.b1199
  have h1198 : segsOk 20000000 4792100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1198 h1199 (by norm_num)
  have h1197 : segsOk 20000000 4788100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1197 h1198 (by norm_num)
  have h1196 : segsOk 20000000 4784100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1196 h1197 (by norm_num)
  have h1195 : segsOk 20000000 4780100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1195 h1196 (by norm_num)
  have h1194 : segsOk 20000000 4776100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1194 h1195 (by norm_num)
  have h1193 : segsOk 20000000 4772100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1193 h1194 (by norm_num)
  have h1192 : segsOk 20000000 4768100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1192 h1193 (by norm_num)
  have h1191 : segsOk 20000000 4764100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1191 h1192 (by norm_num)
  have h1190 : segsOk 20000000 4760100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1190 h1191 (by norm_num)
  have h1189 : segsOk 20000000 4756100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1189 h1190 (by norm_num)
  have h1188 : segsOk 20000000 4752100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1188 h1189 (by norm_num)
  have h1187 : segsOk 20000000 4748100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1187 h1188 (by norm_num)
  have h1186 : segsOk 20000000 4744100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1186 h1187 (by norm_num)
  have h1185 : segsOk 20000000 4740100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1185 h1186 (by norm_num)
  have h1184 : segsOk 20000000 4736100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1184 h1185 (by norm_num)
  have h1183 : segsOk 20000000 4732100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1183 h1184 (by norm_num)
  have h1182 : segsOk 20000000 4728100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1182 h1183 (by norm_num)
  have h1181 : segsOk 20000000 4724100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1181 h1182 (by norm_num)
  have h1180 : segsOk 20000000 4720100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1180 h1181 (by norm_num)
  have h1179 : segsOk 20000000 4716100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1179 h1180 (by norm_num)
  have h1178 : segsOk 20000000 4712100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1178 h1179 (by norm_num)
  have h1177 : segsOk 20000000 4708100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1177 h1178 (by norm_num)
  have h1176 : segsOk 20000000 4704100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1176 h1177 (by norm_num)
  have h1175 : segsOk 20000000 4700100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1175 h1176 (by norm_num)
  have h1174 : segsOk 20000000 4696100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1174 h1175 (by norm_num)
  have h1173 : segsOk 20000000 4692100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1173 h1174 (by norm_num)
  have h1172 : segsOk 20000000 4688100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1172 h1173 (by norm_num)
  have h1171 : segsOk 20000000 4684100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1171 h1172 (by norm_num)
  have h1170 : segsOk 20000000 4680100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1170 h1171 (by norm_num)
  have h1169 : segsOk 20000000 4676100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1169 h1170 (by norm_num)
  have h1168 : segsOk 20000000 4672100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1168 h1169 (by norm_num)
  have h1167 : segsOk 20000000 4668100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1167 h1168 (by norm_num)
  have h1166 : segsOk 20000000 4664100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1166 h1167 (by norm_num)
  have h1165 : segsOk 20000000 4660100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1165 h1166 (by norm_num)
  have h1164 : segsOk 20000000 4656100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1164 h1165 (by norm_num)
  have h1163 : segsOk 20000000 4652100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1163 h1164 (by norm_num)
  have h1162 : segsOk 20000000 4648100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1162 h1163 (by norm_num)
  have h1161 : segsOk 20000000 4644100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1161 h1162 (by norm_num)
  have h1160 : segsOk 20000000 4640100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1160 h1161 (by norm_num)
  have h1159 : segsOk 20000000 4636100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1159 h1160 (by norm_num)
  have h1158 : segsOk 20000000 4632100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1158 h1159 (by norm_num)
  have h1157 : segsOk 20000000 4628100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1157 h1158 (by norm_num)
  have h1156 : segsOk 20000000 4624100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1156 h1157 (by norm_num)
  have h1155 : segsOk 20000000 4620100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1155 h1156 (by norm_num)
  have h1154 : segsOk 20000000 4616100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1154 h1155 (by norm_num)
  have h1153 : segsOk 20000000 4612100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1153 h1154 (by norm_num)
  have h1152 : segsOk 20000000 4608100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1152 h1153 (by norm_num)
  have h1151 : segsOk 20000000 4604100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1151 h1152 (by norm_num)
  have h1150 : segsOk 20000000 4600100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1150 h1151 (by norm_num)
  exact h1150
end Grosswald.Direct
