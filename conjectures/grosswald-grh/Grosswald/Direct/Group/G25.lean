import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1250
import Grosswald.Direct.Run.B1251
import Grosswald.Direct.Run.B1252
import Grosswald.Direct.Run.B1253
import Grosswald.Direct.Run.B1254
import Grosswald.Direct.Run.B1255
import Grosswald.Direct.Run.B1256
import Grosswald.Direct.Run.B1257
import Grosswald.Direct.Run.B1258
import Grosswald.Direct.Run.B1259
import Grosswald.Direct.Run.B1260
import Grosswald.Direct.Run.B1261
import Grosswald.Direct.Run.B1262
import Grosswald.Direct.Run.B1263
import Grosswald.Direct.Run.B1264
import Grosswald.Direct.Run.B1265
import Grosswald.Direct.Run.B1266
import Grosswald.Direct.Run.B1267
import Grosswald.Direct.Run.B1268
import Grosswald.Direct.Run.B1269
import Grosswald.Direct.Run.B1270
import Grosswald.Direct.Run.B1271
import Grosswald.Direct.Run.B1272
import Grosswald.Direct.Run.B1273
import Grosswald.Direct.Run.B1274
import Grosswald.Direct.Run.B1275
import Grosswald.Direct.Run.B1276
import Grosswald.Direct.Run.B1277
import Grosswald.Direct.Run.B1278
import Grosswald.Direct.Run.B1279
import Grosswald.Direct.Run.B1280
import Grosswald.Direct.Run.B1281
import Grosswald.Direct.Run.B1282
import Grosswald.Direct.Run.B1283
import Grosswald.Direct.Run.B1284
import Grosswald.Direct.Run.B1285
import Grosswald.Direct.Run.B1286
import Grosswald.Direct.Run.B1287
import Grosswald.Direct.Run.B1288
import Grosswald.Direct.Run.B1289
import Grosswald.Direct.Run.B1290
import Grosswald.Direct.Run.B1291
import Grosswald.Direct.Run.B1292
import Grosswald.Direct.Run.B1293
import Grosswald.Direct.Run.B1294
import Grosswald.Direct.Run.B1295
import Grosswald.Direct.Run.B1296
import Grosswald.Direct.Run.B1297
import Grosswald.Direct.Run.B1298
import Grosswald.Direct.Run.B1299

namespace Grosswald.Direct
open GrosswaldCompute
theorem g25 : segsOk 20000000 5000100000411 5000 = true := by
  have h1299 : segsOk 20000000 5196100000411 100 = true := Run.b1299
  have h1298 : segsOk 20000000 5192100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1298 h1299 (by norm_num)
  have h1297 : segsOk 20000000 5188100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1297 h1298 (by norm_num)
  have h1296 : segsOk 20000000 5184100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1296 h1297 (by norm_num)
  have h1295 : segsOk 20000000 5180100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1295 h1296 (by norm_num)
  have h1294 : segsOk 20000000 5176100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1294 h1295 (by norm_num)
  have h1293 : segsOk 20000000 5172100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1293 h1294 (by norm_num)
  have h1292 : segsOk 20000000 5168100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1292 h1293 (by norm_num)
  have h1291 : segsOk 20000000 5164100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1291 h1292 (by norm_num)
  have h1290 : segsOk 20000000 5160100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1290 h1291 (by norm_num)
  have h1289 : segsOk 20000000 5156100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1289 h1290 (by norm_num)
  have h1288 : segsOk 20000000 5152100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1288 h1289 (by norm_num)
  have h1287 : segsOk 20000000 5148100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1287 h1288 (by norm_num)
  have h1286 : segsOk 20000000 5144100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1286 h1287 (by norm_num)
  have h1285 : segsOk 20000000 5140100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1285 h1286 (by norm_num)
  have h1284 : segsOk 20000000 5136100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1284 h1285 (by norm_num)
  have h1283 : segsOk 20000000 5132100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1283 h1284 (by norm_num)
  have h1282 : segsOk 20000000 5128100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1282 h1283 (by norm_num)
  have h1281 : segsOk 20000000 5124100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1281 h1282 (by norm_num)
  have h1280 : segsOk 20000000 5120100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1280 h1281 (by norm_num)
  have h1279 : segsOk 20000000 5116100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1279 h1280 (by norm_num)
  have h1278 : segsOk 20000000 5112100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1278 h1279 (by norm_num)
  have h1277 : segsOk 20000000 5108100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1277 h1278 (by norm_num)
  have h1276 : segsOk 20000000 5104100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1276 h1277 (by norm_num)
  have h1275 : segsOk 20000000 5100100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1275 h1276 (by norm_num)
  have h1274 : segsOk 20000000 5096100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1274 h1275 (by norm_num)
  have h1273 : segsOk 20000000 5092100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1273 h1274 (by norm_num)
  have h1272 : segsOk 20000000 5088100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1272 h1273 (by norm_num)
  have h1271 : segsOk 20000000 5084100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1271 h1272 (by norm_num)
  have h1270 : segsOk 20000000 5080100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1270 h1271 (by norm_num)
  have h1269 : segsOk 20000000 5076100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1269 h1270 (by norm_num)
  have h1268 : segsOk 20000000 5072100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1268 h1269 (by norm_num)
  have h1267 : segsOk 20000000 5068100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1267 h1268 (by norm_num)
  have h1266 : segsOk 20000000 5064100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1266 h1267 (by norm_num)
  have h1265 : segsOk 20000000 5060100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1265 h1266 (by norm_num)
  have h1264 : segsOk 20000000 5056100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1264 h1265 (by norm_num)
  have h1263 : segsOk 20000000 5052100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1263 h1264 (by norm_num)
  have h1262 : segsOk 20000000 5048100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1262 h1263 (by norm_num)
  have h1261 : segsOk 20000000 5044100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1261 h1262 (by norm_num)
  have h1260 : segsOk 20000000 5040100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1260 h1261 (by norm_num)
  have h1259 : segsOk 20000000 5036100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1259 h1260 (by norm_num)
  have h1258 : segsOk 20000000 5032100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1258 h1259 (by norm_num)
  have h1257 : segsOk 20000000 5028100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1257 h1258 (by norm_num)
  have h1256 : segsOk 20000000 5024100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1256 h1257 (by norm_num)
  have h1255 : segsOk 20000000 5020100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1255 h1256 (by norm_num)
  have h1254 : segsOk 20000000 5016100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1254 h1255 (by norm_num)
  have h1253 : segsOk 20000000 5012100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1253 h1254 (by norm_num)
  have h1252 : segsOk 20000000 5008100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1252 h1253 (by norm_num)
  have h1251 : segsOk 20000000 5004100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1251 h1252 (by norm_num)
  have h1250 : segsOk 20000000 5000100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1250 h1251 (by norm_num)
  exact h1250
end Grosswald.Direct
