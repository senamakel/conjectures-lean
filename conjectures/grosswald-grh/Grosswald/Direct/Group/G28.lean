import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1400
import Grosswald.Direct.Run.B1401
import Grosswald.Direct.Run.B1402
import Grosswald.Direct.Run.B1403
import Grosswald.Direct.Run.B1404
import Grosswald.Direct.Run.B1405
import Grosswald.Direct.Run.B1406
import Grosswald.Direct.Run.B1407
import Grosswald.Direct.Run.B1408
import Grosswald.Direct.Run.B1409
import Grosswald.Direct.Run.B1410
import Grosswald.Direct.Run.B1411
import Grosswald.Direct.Run.B1412
import Grosswald.Direct.Run.B1413
import Grosswald.Direct.Run.B1414
import Grosswald.Direct.Run.B1415
import Grosswald.Direct.Run.B1416
import Grosswald.Direct.Run.B1417
import Grosswald.Direct.Run.B1418
import Grosswald.Direct.Run.B1419
import Grosswald.Direct.Run.B1420
import Grosswald.Direct.Run.B1421
import Grosswald.Direct.Run.B1422
import Grosswald.Direct.Run.B1423
import Grosswald.Direct.Run.B1424
import Grosswald.Direct.Run.B1425
import Grosswald.Direct.Run.B1426
import Grosswald.Direct.Run.B1427
import Grosswald.Direct.Run.B1428
import Grosswald.Direct.Run.B1429
import Grosswald.Direct.Run.B1430
import Grosswald.Direct.Run.B1431
import Grosswald.Direct.Run.B1432
import Grosswald.Direct.Run.B1433
import Grosswald.Direct.Run.B1434
import Grosswald.Direct.Run.B1435
import Grosswald.Direct.Run.B1436
import Grosswald.Direct.Run.B1437
import Grosswald.Direct.Run.B1438
import Grosswald.Direct.Run.B1439
import Grosswald.Direct.Run.B1440
import Grosswald.Direct.Run.B1441
import Grosswald.Direct.Run.B1442
import Grosswald.Direct.Run.B1443
import Grosswald.Direct.Run.B1444
import Grosswald.Direct.Run.B1445
import Grosswald.Direct.Run.B1446
import Grosswald.Direct.Run.B1447
import Grosswald.Direct.Run.B1448
import Grosswald.Direct.Run.B1449

namespace Grosswald.Direct
open GrosswaldCompute
theorem g28 : segsOk 20000000 5600100000411 5000 = true := by
  have h1449 : segsOk 20000000 5796100000411 100 = true := Run.b1449
  have h1448 : segsOk 20000000 5792100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1448 h1449 (by norm_num)
  have h1447 : segsOk 20000000 5788100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1447 h1448 (by norm_num)
  have h1446 : segsOk 20000000 5784100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1446 h1447 (by norm_num)
  have h1445 : segsOk 20000000 5780100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1445 h1446 (by norm_num)
  have h1444 : segsOk 20000000 5776100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1444 h1445 (by norm_num)
  have h1443 : segsOk 20000000 5772100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1443 h1444 (by norm_num)
  have h1442 : segsOk 20000000 5768100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1442 h1443 (by norm_num)
  have h1441 : segsOk 20000000 5764100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1441 h1442 (by norm_num)
  have h1440 : segsOk 20000000 5760100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1440 h1441 (by norm_num)
  have h1439 : segsOk 20000000 5756100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1439 h1440 (by norm_num)
  have h1438 : segsOk 20000000 5752100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1438 h1439 (by norm_num)
  have h1437 : segsOk 20000000 5748100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1437 h1438 (by norm_num)
  have h1436 : segsOk 20000000 5744100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1436 h1437 (by norm_num)
  have h1435 : segsOk 20000000 5740100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1435 h1436 (by norm_num)
  have h1434 : segsOk 20000000 5736100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1434 h1435 (by norm_num)
  have h1433 : segsOk 20000000 5732100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1433 h1434 (by norm_num)
  have h1432 : segsOk 20000000 5728100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1432 h1433 (by norm_num)
  have h1431 : segsOk 20000000 5724100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1431 h1432 (by norm_num)
  have h1430 : segsOk 20000000 5720100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1430 h1431 (by norm_num)
  have h1429 : segsOk 20000000 5716100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1429 h1430 (by norm_num)
  have h1428 : segsOk 20000000 5712100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1428 h1429 (by norm_num)
  have h1427 : segsOk 20000000 5708100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1427 h1428 (by norm_num)
  have h1426 : segsOk 20000000 5704100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1426 h1427 (by norm_num)
  have h1425 : segsOk 20000000 5700100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1425 h1426 (by norm_num)
  have h1424 : segsOk 20000000 5696100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1424 h1425 (by norm_num)
  have h1423 : segsOk 20000000 5692100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1423 h1424 (by norm_num)
  have h1422 : segsOk 20000000 5688100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1422 h1423 (by norm_num)
  have h1421 : segsOk 20000000 5684100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1421 h1422 (by norm_num)
  have h1420 : segsOk 20000000 5680100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1420 h1421 (by norm_num)
  have h1419 : segsOk 20000000 5676100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1419 h1420 (by norm_num)
  have h1418 : segsOk 20000000 5672100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1418 h1419 (by norm_num)
  have h1417 : segsOk 20000000 5668100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1417 h1418 (by norm_num)
  have h1416 : segsOk 20000000 5664100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1416 h1417 (by norm_num)
  have h1415 : segsOk 20000000 5660100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1415 h1416 (by norm_num)
  have h1414 : segsOk 20000000 5656100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1414 h1415 (by norm_num)
  have h1413 : segsOk 20000000 5652100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1413 h1414 (by norm_num)
  have h1412 : segsOk 20000000 5648100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1412 h1413 (by norm_num)
  have h1411 : segsOk 20000000 5644100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1411 h1412 (by norm_num)
  have h1410 : segsOk 20000000 5640100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1410 h1411 (by norm_num)
  have h1409 : segsOk 20000000 5636100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1409 h1410 (by norm_num)
  have h1408 : segsOk 20000000 5632100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1408 h1409 (by norm_num)
  have h1407 : segsOk 20000000 5628100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1407 h1408 (by norm_num)
  have h1406 : segsOk 20000000 5624100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1406 h1407 (by norm_num)
  have h1405 : segsOk 20000000 5620100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1405 h1406 (by norm_num)
  have h1404 : segsOk 20000000 5616100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1404 h1405 (by norm_num)
  have h1403 : segsOk 20000000 5612100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1403 h1404 (by norm_num)
  have h1402 : segsOk 20000000 5608100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1402 h1403 (by norm_num)
  have h1401 : segsOk 20000000 5604100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1401 h1402 (by norm_num)
  have h1400 : segsOk 20000000 5600100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1400 h1401 (by norm_num)
  exact h1400
end Grosswald.Direct
