import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1350
import Grosswald.Direct.Run.B1351
import Grosswald.Direct.Run.B1352
import Grosswald.Direct.Run.B1353
import Grosswald.Direct.Run.B1354
import Grosswald.Direct.Run.B1355
import Grosswald.Direct.Run.B1356
import Grosswald.Direct.Run.B1357
import Grosswald.Direct.Run.B1358
import Grosswald.Direct.Run.B1359
import Grosswald.Direct.Run.B1360
import Grosswald.Direct.Run.B1361
import Grosswald.Direct.Run.B1362
import Grosswald.Direct.Run.B1363
import Grosswald.Direct.Run.B1364
import Grosswald.Direct.Run.B1365
import Grosswald.Direct.Run.B1366
import Grosswald.Direct.Run.B1367
import Grosswald.Direct.Run.B1368
import Grosswald.Direct.Run.B1369
import Grosswald.Direct.Run.B1370
import Grosswald.Direct.Run.B1371
import Grosswald.Direct.Run.B1372
import Grosswald.Direct.Run.B1373
import Grosswald.Direct.Run.B1374
import Grosswald.Direct.Run.B1375
import Grosswald.Direct.Run.B1376
import Grosswald.Direct.Run.B1377
import Grosswald.Direct.Run.B1378
import Grosswald.Direct.Run.B1379
import Grosswald.Direct.Run.B1380
import Grosswald.Direct.Run.B1381
import Grosswald.Direct.Run.B1382
import Grosswald.Direct.Run.B1383
import Grosswald.Direct.Run.B1384
import Grosswald.Direct.Run.B1385
import Grosswald.Direct.Run.B1386
import Grosswald.Direct.Run.B1387
import Grosswald.Direct.Run.B1388
import Grosswald.Direct.Run.B1389
import Grosswald.Direct.Run.B1390
import Grosswald.Direct.Run.B1391
import Grosswald.Direct.Run.B1392
import Grosswald.Direct.Run.B1393
import Grosswald.Direct.Run.B1394
import Grosswald.Direct.Run.B1395
import Grosswald.Direct.Run.B1396
import Grosswald.Direct.Run.B1397
import Grosswald.Direct.Run.B1398
import Grosswald.Direct.Run.B1399

namespace Grosswald.Direct
open GrosswaldCompute
theorem g27 : segsOk 20000000 5400100000411 5000 = true := by
  have h1399 : segsOk 20000000 5596100000411 100 = true := Run.b1399
  have h1398 : segsOk 20000000 5592100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1398 h1399 (by norm_num)
  have h1397 : segsOk 20000000 5588100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1397 h1398 (by norm_num)
  have h1396 : segsOk 20000000 5584100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1396 h1397 (by norm_num)
  have h1395 : segsOk 20000000 5580100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1395 h1396 (by norm_num)
  have h1394 : segsOk 20000000 5576100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1394 h1395 (by norm_num)
  have h1393 : segsOk 20000000 5572100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1393 h1394 (by norm_num)
  have h1392 : segsOk 20000000 5568100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1392 h1393 (by norm_num)
  have h1391 : segsOk 20000000 5564100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1391 h1392 (by norm_num)
  have h1390 : segsOk 20000000 5560100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1390 h1391 (by norm_num)
  have h1389 : segsOk 20000000 5556100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1389 h1390 (by norm_num)
  have h1388 : segsOk 20000000 5552100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1388 h1389 (by norm_num)
  have h1387 : segsOk 20000000 5548100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1387 h1388 (by norm_num)
  have h1386 : segsOk 20000000 5544100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1386 h1387 (by norm_num)
  have h1385 : segsOk 20000000 5540100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1385 h1386 (by norm_num)
  have h1384 : segsOk 20000000 5536100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1384 h1385 (by norm_num)
  have h1383 : segsOk 20000000 5532100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1383 h1384 (by norm_num)
  have h1382 : segsOk 20000000 5528100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1382 h1383 (by norm_num)
  have h1381 : segsOk 20000000 5524100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1381 h1382 (by norm_num)
  have h1380 : segsOk 20000000 5520100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1380 h1381 (by norm_num)
  have h1379 : segsOk 20000000 5516100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1379 h1380 (by norm_num)
  have h1378 : segsOk 20000000 5512100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1378 h1379 (by norm_num)
  have h1377 : segsOk 20000000 5508100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1377 h1378 (by norm_num)
  have h1376 : segsOk 20000000 5504100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1376 h1377 (by norm_num)
  have h1375 : segsOk 20000000 5500100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1375 h1376 (by norm_num)
  have h1374 : segsOk 20000000 5496100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1374 h1375 (by norm_num)
  have h1373 : segsOk 20000000 5492100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1373 h1374 (by norm_num)
  have h1372 : segsOk 20000000 5488100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1372 h1373 (by norm_num)
  have h1371 : segsOk 20000000 5484100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1371 h1372 (by norm_num)
  have h1370 : segsOk 20000000 5480100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1370 h1371 (by norm_num)
  have h1369 : segsOk 20000000 5476100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1369 h1370 (by norm_num)
  have h1368 : segsOk 20000000 5472100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1368 h1369 (by norm_num)
  have h1367 : segsOk 20000000 5468100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1367 h1368 (by norm_num)
  have h1366 : segsOk 20000000 5464100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1366 h1367 (by norm_num)
  have h1365 : segsOk 20000000 5460100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1365 h1366 (by norm_num)
  have h1364 : segsOk 20000000 5456100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1364 h1365 (by norm_num)
  have h1363 : segsOk 20000000 5452100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1363 h1364 (by norm_num)
  have h1362 : segsOk 20000000 5448100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1362 h1363 (by norm_num)
  have h1361 : segsOk 20000000 5444100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1361 h1362 (by norm_num)
  have h1360 : segsOk 20000000 5440100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1360 h1361 (by norm_num)
  have h1359 : segsOk 20000000 5436100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1359 h1360 (by norm_num)
  have h1358 : segsOk 20000000 5432100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1358 h1359 (by norm_num)
  have h1357 : segsOk 20000000 5428100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1357 h1358 (by norm_num)
  have h1356 : segsOk 20000000 5424100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1356 h1357 (by norm_num)
  have h1355 : segsOk 20000000 5420100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1355 h1356 (by norm_num)
  have h1354 : segsOk 20000000 5416100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1354 h1355 (by norm_num)
  have h1353 : segsOk 20000000 5412100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1353 h1354 (by norm_num)
  have h1352 : segsOk 20000000 5408100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1352 h1353 (by norm_num)
  have h1351 : segsOk 20000000 5404100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1351 h1352 (by norm_num)
  have h1350 : segsOk 20000000 5400100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1350 h1351 (by norm_num)
  exact h1350
end Grosswald.Direct
