import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1300
import Grosswald.Direct.Run.B1301
import Grosswald.Direct.Run.B1302
import Grosswald.Direct.Run.B1303
import Grosswald.Direct.Run.B1304
import Grosswald.Direct.Run.B1305
import Grosswald.Direct.Run.B1306
import Grosswald.Direct.Run.B1307
import Grosswald.Direct.Run.B1308
import Grosswald.Direct.Run.B1309
import Grosswald.Direct.Run.B1310
import Grosswald.Direct.Run.B1311
import Grosswald.Direct.Run.B1312
import Grosswald.Direct.Run.B1313
import Grosswald.Direct.Run.B1314
import Grosswald.Direct.Run.B1315
import Grosswald.Direct.Run.B1316
import Grosswald.Direct.Run.B1317
import Grosswald.Direct.Run.B1318
import Grosswald.Direct.Run.B1319
import Grosswald.Direct.Run.B1320
import Grosswald.Direct.Run.B1321
import Grosswald.Direct.Run.B1322
import Grosswald.Direct.Run.B1323
import Grosswald.Direct.Run.B1324
import Grosswald.Direct.Run.B1325
import Grosswald.Direct.Run.B1326
import Grosswald.Direct.Run.B1327
import Grosswald.Direct.Run.B1328
import Grosswald.Direct.Run.B1329
import Grosswald.Direct.Run.B1330
import Grosswald.Direct.Run.B1331
import Grosswald.Direct.Run.B1332
import Grosswald.Direct.Run.B1333
import Grosswald.Direct.Run.B1334
import Grosswald.Direct.Run.B1335
import Grosswald.Direct.Run.B1336
import Grosswald.Direct.Run.B1337
import Grosswald.Direct.Run.B1338
import Grosswald.Direct.Run.B1339
import Grosswald.Direct.Run.B1340
import Grosswald.Direct.Run.B1341
import Grosswald.Direct.Run.B1342
import Grosswald.Direct.Run.B1343
import Grosswald.Direct.Run.B1344
import Grosswald.Direct.Run.B1345
import Grosswald.Direct.Run.B1346
import Grosswald.Direct.Run.B1347
import Grosswald.Direct.Run.B1348
import Grosswald.Direct.Run.B1349

namespace Grosswald.Direct
open GrosswaldCompute
theorem g26 : segsOk 20000000 5200100000411 5000 = true := by
  have h1349 : segsOk 20000000 5396100000411 100 = true := Run.b1349
  have h1348 : segsOk 20000000 5392100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1348 h1349 (by norm_num)
  have h1347 : segsOk 20000000 5388100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1347 h1348 (by norm_num)
  have h1346 : segsOk 20000000 5384100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1346 h1347 (by norm_num)
  have h1345 : segsOk 20000000 5380100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1345 h1346 (by norm_num)
  have h1344 : segsOk 20000000 5376100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1344 h1345 (by norm_num)
  have h1343 : segsOk 20000000 5372100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1343 h1344 (by norm_num)
  have h1342 : segsOk 20000000 5368100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1342 h1343 (by norm_num)
  have h1341 : segsOk 20000000 5364100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1341 h1342 (by norm_num)
  have h1340 : segsOk 20000000 5360100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1340 h1341 (by norm_num)
  have h1339 : segsOk 20000000 5356100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1339 h1340 (by norm_num)
  have h1338 : segsOk 20000000 5352100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1338 h1339 (by norm_num)
  have h1337 : segsOk 20000000 5348100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1337 h1338 (by norm_num)
  have h1336 : segsOk 20000000 5344100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1336 h1337 (by norm_num)
  have h1335 : segsOk 20000000 5340100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1335 h1336 (by norm_num)
  have h1334 : segsOk 20000000 5336100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1334 h1335 (by norm_num)
  have h1333 : segsOk 20000000 5332100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1333 h1334 (by norm_num)
  have h1332 : segsOk 20000000 5328100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1332 h1333 (by norm_num)
  have h1331 : segsOk 20000000 5324100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1331 h1332 (by norm_num)
  have h1330 : segsOk 20000000 5320100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1330 h1331 (by norm_num)
  have h1329 : segsOk 20000000 5316100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1329 h1330 (by norm_num)
  have h1328 : segsOk 20000000 5312100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1328 h1329 (by norm_num)
  have h1327 : segsOk 20000000 5308100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1327 h1328 (by norm_num)
  have h1326 : segsOk 20000000 5304100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1326 h1327 (by norm_num)
  have h1325 : segsOk 20000000 5300100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1325 h1326 (by norm_num)
  have h1324 : segsOk 20000000 5296100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1324 h1325 (by norm_num)
  have h1323 : segsOk 20000000 5292100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1323 h1324 (by norm_num)
  have h1322 : segsOk 20000000 5288100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1322 h1323 (by norm_num)
  have h1321 : segsOk 20000000 5284100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1321 h1322 (by norm_num)
  have h1320 : segsOk 20000000 5280100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1320 h1321 (by norm_num)
  have h1319 : segsOk 20000000 5276100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1319 h1320 (by norm_num)
  have h1318 : segsOk 20000000 5272100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1318 h1319 (by norm_num)
  have h1317 : segsOk 20000000 5268100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1317 h1318 (by norm_num)
  have h1316 : segsOk 20000000 5264100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1316 h1317 (by norm_num)
  have h1315 : segsOk 20000000 5260100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1315 h1316 (by norm_num)
  have h1314 : segsOk 20000000 5256100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1314 h1315 (by norm_num)
  have h1313 : segsOk 20000000 5252100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1313 h1314 (by norm_num)
  have h1312 : segsOk 20000000 5248100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1312 h1313 (by norm_num)
  have h1311 : segsOk 20000000 5244100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1311 h1312 (by norm_num)
  have h1310 : segsOk 20000000 5240100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1310 h1311 (by norm_num)
  have h1309 : segsOk 20000000 5236100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1309 h1310 (by norm_num)
  have h1308 : segsOk 20000000 5232100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1308 h1309 (by norm_num)
  have h1307 : segsOk 20000000 5228100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1307 h1308 (by norm_num)
  have h1306 : segsOk 20000000 5224100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1306 h1307 (by norm_num)
  have h1305 : segsOk 20000000 5220100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1305 h1306 (by norm_num)
  have h1304 : segsOk 20000000 5216100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1304 h1305 (by norm_num)
  have h1303 : segsOk 20000000 5212100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1303 h1304 (by norm_num)
  have h1302 : segsOk 20000000 5208100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1302 h1303 (by norm_num)
  have h1301 : segsOk 20000000 5204100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1301 h1302 (by norm_num)
  have h1300 : segsOk 20000000 5200100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1300 h1301 (by norm_num)
  exact h1300
end Grosswald.Direct
