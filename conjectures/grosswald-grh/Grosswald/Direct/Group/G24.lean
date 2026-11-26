import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1200
import Grosswald.Direct.Run.B1201
import Grosswald.Direct.Run.B1202
import Grosswald.Direct.Run.B1203
import Grosswald.Direct.Run.B1204
import Grosswald.Direct.Run.B1205
import Grosswald.Direct.Run.B1206
import Grosswald.Direct.Run.B1207
import Grosswald.Direct.Run.B1208
import Grosswald.Direct.Run.B1209
import Grosswald.Direct.Run.B1210
import Grosswald.Direct.Run.B1211
import Grosswald.Direct.Run.B1212
import Grosswald.Direct.Run.B1213
import Grosswald.Direct.Run.B1214
import Grosswald.Direct.Run.B1215
import Grosswald.Direct.Run.B1216
import Grosswald.Direct.Run.B1217
import Grosswald.Direct.Run.B1218
import Grosswald.Direct.Run.B1219
import Grosswald.Direct.Run.B1220
import Grosswald.Direct.Run.B1221
import Grosswald.Direct.Run.B1222
import Grosswald.Direct.Run.B1223
import Grosswald.Direct.Run.B1224
import Grosswald.Direct.Run.B1225
import Grosswald.Direct.Run.B1226
import Grosswald.Direct.Run.B1227
import Grosswald.Direct.Run.B1228
import Grosswald.Direct.Run.B1229
import Grosswald.Direct.Run.B1230
import Grosswald.Direct.Run.B1231
import Grosswald.Direct.Run.B1232
import Grosswald.Direct.Run.B1233
import Grosswald.Direct.Run.B1234
import Grosswald.Direct.Run.B1235
import Grosswald.Direct.Run.B1236
import Grosswald.Direct.Run.B1237
import Grosswald.Direct.Run.B1238
import Grosswald.Direct.Run.B1239
import Grosswald.Direct.Run.B1240
import Grosswald.Direct.Run.B1241
import Grosswald.Direct.Run.B1242
import Grosswald.Direct.Run.B1243
import Grosswald.Direct.Run.B1244
import Grosswald.Direct.Run.B1245
import Grosswald.Direct.Run.B1246
import Grosswald.Direct.Run.B1247
import Grosswald.Direct.Run.B1248
import Grosswald.Direct.Run.B1249

namespace Grosswald.Direct
open GrosswaldCompute
theorem g24 : segsOk 20000000 4800100000411 5000 = true := by
  have h1249 : segsOk 20000000 4996100000411 100 = true := Run.b1249
  have h1248 : segsOk 20000000 4992100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1248 h1249 (by norm_num)
  have h1247 : segsOk 20000000 4988100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1247 h1248 (by norm_num)
  have h1246 : segsOk 20000000 4984100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1246 h1247 (by norm_num)
  have h1245 : segsOk 20000000 4980100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1245 h1246 (by norm_num)
  have h1244 : segsOk 20000000 4976100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1244 h1245 (by norm_num)
  have h1243 : segsOk 20000000 4972100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1243 h1244 (by norm_num)
  have h1242 : segsOk 20000000 4968100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1242 h1243 (by norm_num)
  have h1241 : segsOk 20000000 4964100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1241 h1242 (by norm_num)
  have h1240 : segsOk 20000000 4960100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1240 h1241 (by norm_num)
  have h1239 : segsOk 20000000 4956100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1239 h1240 (by norm_num)
  have h1238 : segsOk 20000000 4952100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1238 h1239 (by norm_num)
  have h1237 : segsOk 20000000 4948100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1237 h1238 (by norm_num)
  have h1236 : segsOk 20000000 4944100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1236 h1237 (by norm_num)
  have h1235 : segsOk 20000000 4940100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1235 h1236 (by norm_num)
  have h1234 : segsOk 20000000 4936100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1234 h1235 (by norm_num)
  have h1233 : segsOk 20000000 4932100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1233 h1234 (by norm_num)
  have h1232 : segsOk 20000000 4928100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1232 h1233 (by norm_num)
  have h1231 : segsOk 20000000 4924100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1231 h1232 (by norm_num)
  have h1230 : segsOk 20000000 4920100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1230 h1231 (by norm_num)
  have h1229 : segsOk 20000000 4916100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1229 h1230 (by norm_num)
  have h1228 : segsOk 20000000 4912100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1228 h1229 (by norm_num)
  have h1227 : segsOk 20000000 4908100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1227 h1228 (by norm_num)
  have h1226 : segsOk 20000000 4904100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1226 h1227 (by norm_num)
  have h1225 : segsOk 20000000 4900100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1225 h1226 (by norm_num)
  have h1224 : segsOk 20000000 4896100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1224 h1225 (by norm_num)
  have h1223 : segsOk 20000000 4892100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1223 h1224 (by norm_num)
  have h1222 : segsOk 20000000 4888100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1222 h1223 (by norm_num)
  have h1221 : segsOk 20000000 4884100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1221 h1222 (by norm_num)
  have h1220 : segsOk 20000000 4880100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1220 h1221 (by norm_num)
  have h1219 : segsOk 20000000 4876100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1219 h1220 (by norm_num)
  have h1218 : segsOk 20000000 4872100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1218 h1219 (by norm_num)
  have h1217 : segsOk 20000000 4868100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1217 h1218 (by norm_num)
  have h1216 : segsOk 20000000 4864100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1216 h1217 (by norm_num)
  have h1215 : segsOk 20000000 4860100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1215 h1216 (by norm_num)
  have h1214 : segsOk 20000000 4856100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1214 h1215 (by norm_num)
  have h1213 : segsOk 20000000 4852100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1213 h1214 (by norm_num)
  have h1212 : segsOk 20000000 4848100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1212 h1213 (by norm_num)
  have h1211 : segsOk 20000000 4844100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1211 h1212 (by norm_num)
  have h1210 : segsOk 20000000 4840100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1210 h1211 (by norm_num)
  have h1209 : segsOk 20000000 4836100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1209 h1210 (by norm_num)
  have h1208 : segsOk 20000000 4832100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1208 h1209 (by norm_num)
  have h1207 : segsOk 20000000 4828100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1207 h1208 (by norm_num)
  have h1206 : segsOk 20000000 4824100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1206 h1207 (by norm_num)
  have h1205 : segsOk 20000000 4820100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1205 h1206 (by norm_num)
  have h1204 : segsOk 20000000 4816100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1204 h1205 (by norm_num)
  have h1203 : segsOk 20000000 4812100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1203 h1204 (by norm_num)
  have h1202 : segsOk 20000000 4808100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1202 h1203 (by norm_num)
  have h1201 : segsOk 20000000 4804100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1201 h1202 (by norm_num)
  have h1200 : segsOk 20000000 4800100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1200 h1201 (by norm_num)
  exact h1200
end Grosswald.Direct
