import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0300
import Grosswald.Direct.Run.B0301
import Grosswald.Direct.Run.B0302
import Grosswald.Direct.Run.B0303
import Grosswald.Direct.Run.B0304
import Grosswald.Direct.Run.B0305
import Grosswald.Direct.Run.B0306
import Grosswald.Direct.Run.B0307
import Grosswald.Direct.Run.B0308
import Grosswald.Direct.Run.B0309
import Grosswald.Direct.Run.B0310
import Grosswald.Direct.Run.B0311
import Grosswald.Direct.Run.B0312
import Grosswald.Direct.Run.B0313
import Grosswald.Direct.Run.B0314
import Grosswald.Direct.Run.B0315
import Grosswald.Direct.Run.B0316
import Grosswald.Direct.Run.B0317
import Grosswald.Direct.Run.B0318
import Grosswald.Direct.Run.B0319
import Grosswald.Direct.Run.B0320
import Grosswald.Direct.Run.B0321
import Grosswald.Direct.Run.B0322
import Grosswald.Direct.Run.B0323
import Grosswald.Direct.Run.B0324
import Grosswald.Direct.Run.B0325
import Grosswald.Direct.Run.B0326
import Grosswald.Direct.Run.B0327
import Grosswald.Direct.Run.B0328
import Grosswald.Direct.Run.B0329
import Grosswald.Direct.Run.B0330
import Grosswald.Direct.Run.B0331
import Grosswald.Direct.Run.B0332
import Grosswald.Direct.Run.B0333
import Grosswald.Direct.Run.B0334
import Grosswald.Direct.Run.B0335
import Grosswald.Direct.Run.B0336
import Grosswald.Direct.Run.B0337
import Grosswald.Direct.Run.B0338
import Grosswald.Direct.Run.B0339
import Grosswald.Direct.Run.B0340
import Grosswald.Direct.Run.B0341
import Grosswald.Direct.Run.B0342
import Grosswald.Direct.Run.B0343
import Grosswald.Direct.Run.B0344
import Grosswald.Direct.Run.B0345
import Grosswald.Direct.Run.B0346
import Grosswald.Direct.Run.B0347
import Grosswald.Direct.Run.B0348
import Grosswald.Direct.Run.B0349

namespace Grosswald.Direct
open GrosswaldCompute
theorem g06 : segsOk 20000000 1200100000411 5000 = true := by
  have h0349 : segsOk 20000000 1396100000411 100 = true := Run.b0349
  have h0348 : segsOk 20000000 1392100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0348 h0349 (by norm_num)
  have h0347 : segsOk 20000000 1388100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0347 h0348 (by norm_num)
  have h0346 : segsOk 20000000 1384100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0346 h0347 (by norm_num)
  have h0345 : segsOk 20000000 1380100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0345 h0346 (by norm_num)
  have h0344 : segsOk 20000000 1376100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0344 h0345 (by norm_num)
  have h0343 : segsOk 20000000 1372100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0343 h0344 (by norm_num)
  have h0342 : segsOk 20000000 1368100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0342 h0343 (by norm_num)
  have h0341 : segsOk 20000000 1364100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0341 h0342 (by norm_num)
  have h0340 : segsOk 20000000 1360100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0340 h0341 (by norm_num)
  have h0339 : segsOk 20000000 1356100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0339 h0340 (by norm_num)
  have h0338 : segsOk 20000000 1352100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0338 h0339 (by norm_num)
  have h0337 : segsOk 20000000 1348100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0337 h0338 (by norm_num)
  have h0336 : segsOk 20000000 1344100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0336 h0337 (by norm_num)
  have h0335 : segsOk 20000000 1340100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0335 h0336 (by norm_num)
  have h0334 : segsOk 20000000 1336100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0334 h0335 (by norm_num)
  have h0333 : segsOk 20000000 1332100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0333 h0334 (by norm_num)
  have h0332 : segsOk 20000000 1328100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0332 h0333 (by norm_num)
  have h0331 : segsOk 20000000 1324100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0331 h0332 (by norm_num)
  have h0330 : segsOk 20000000 1320100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0330 h0331 (by norm_num)
  have h0329 : segsOk 20000000 1316100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0329 h0330 (by norm_num)
  have h0328 : segsOk 20000000 1312100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0328 h0329 (by norm_num)
  have h0327 : segsOk 20000000 1308100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0327 h0328 (by norm_num)
  have h0326 : segsOk 20000000 1304100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0326 h0327 (by norm_num)
  have h0325 : segsOk 20000000 1300100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0325 h0326 (by norm_num)
  have h0324 : segsOk 20000000 1296100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0324 h0325 (by norm_num)
  have h0323 : segsOk 20000000 1292100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0323 h0324 (by norm_num)
  have h0322 : segsOk 20000000 1288100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0322 h0323 (by norm_num)
  have h0321 : segsOk 20000000 1284100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0321 h0322 (by norm_num)
  have h0320 : segsOk 20000000 1280100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0320 h0321 (by norm_num)
  have h0319 : segsOk 20000000 1276100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0319 h0320 (by norm_num)
  have h0318 : segsOk 20000000 1272100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0318 h0319 (by norm_num)
  have h0317 : segsOk 20000000 1268100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0317 h0318 (by norm_num)
  have h0316 : segsOk 20000000 1264100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0316 h0317 (by norm_num)
  have h0315 : segsOk 20000000 1260100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0315 h0316 (by norm_num)
  have h0314 : segsOk 20000000 1256100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0314 h0315 (by norm_num)
  have h0313 : segsOk 20000000 1252100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0313 h0314 (by norm_num)
  have h0312 : segsOk 20000000 1248100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0312 h0313 (by norm_num)
  have h0311 : segsOk 20000000 1244100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0311 h0312 (by norm_num)
  have h0310 : segsOk 20000000 1240100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0310 h0311 (by norm_num)
  have h0309 : segsOk 20000000 1236100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0309 h0310 (by norm_num)
  have h0308 : segsOk 20000000 1232100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0308 h0309 (by norm_num)
  have h0307 : segsOk 20000000 1228100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0307 h0308 (by norm_num)
  have h0306 : segsOk 20000000 1224100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0306 h0307 (by norm_num)
  have h0305 : segsOk 20000000 1220100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0305 h0306 (by norm_num)
  have h0304 : segsOk 20000000 1216100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0304 h0305 (by norm_num)
  have h0303 : segsOk 20000000 1212100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0303 h0304 (by norm_num)
  have h0302 : segsOk 20000000 1208100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0302 h0303 (by norm_num)
  have h0301 : segsOk 20000000 1204100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0301 h0302 (by norm_num)
  have h0300 : segsOk 20000000 1200100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0300 h0301 (by norm_num)
  exact h0300
end Grosswald.Direct
