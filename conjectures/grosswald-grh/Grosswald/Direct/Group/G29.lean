import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1450
import Grosswald.Direct.Run.B1451
import Grosswald.Direct.Run.B1452
import Grosswald.Direct.Run.B1453
import Grosswald.Direct.Run.B1454
import Grosswald.Direct.Run.B1455
import Grosswald.Direct.Run.B1456
import Grosswald.Direct.Run.B1457
import Grosswald.Direct.Run.B1458
import Grosswald.Direct.Run.B1459
import Grosswald.Direct.Run.B1460
import Grosswald.Direct.Run.B1461
import Grosswald.Direct.Run.B1462
import Grosswald.Direct.Run.B1463
import Grosswald.Direct.Run.B1464
import Grosswald.Direct.Run.B1465
import Grosswald.Direct.Run.B1466
import Grosswald.Direct.Run.B1467
import Grosswald.Direct.Run.B1468
import Grosswald.Direct.Run.B1469
import Grosswald.Direct.Run.B1470
import Grosswald.Direct.Run.B1471
import Grosswald.Direct.Run.B1472
import Grosswald.Direct.Run.B1473
import Grosswald.Direct.Run.B1474
import Grosswald.Direct.Run.B1475
import Grosswald.Direct.Run.B1476
import Grosswald.Direct.Run.B1477
import Grosswald.Direct.Run.B1478
import Grosswald.Direct.Run.B1479
import Grosswald.Direct.Run.B1480
import Grosswald.Direct.Run.B1481
import Grosswald.Direct.Run.B1482
import Grosswald.Direct.Run.B1483
import Grosswald.Direct.Run.B1484
import Grosswald.Direct.Run.B1485
import Grosswald.Direct.Run.B1486
import Grosswald.Direct.Run.B1487
import Grosswald.Direct.Run.B1488
import Grosswald.Direct.Run.B1489
import Grosswald.Direct.Run.B1490
import Grosswald.Direct.Run.B1491
import Grosswald.Direct.Run.B1492
import Grosswald.Direct.Run.B1493
import Grosswald.Direct.Run.B1494
import Grosswald.Direct.Run.B1495
import Grosswald.Direct.Run.B1496
import Grosswald.Direct.Run.B1497
import Grosswald.Direct.Run.B1498
import Grosswald.Direct.Run.B1499

namespace Grosswald.Direct
open GrosswaldCompute
theorem g29 : segsOk 20000000 5800100000411 5000 = true := by
  have h1499 : segsOk 20000000 5996100000411 100 = true := Run.b1499
  have h1498 : segsOk 20000000 5992100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1498 h1499 (by norm_num)
  have h1497 : segsOk 20000000 5988100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1497 h1498 (by norm_num)
  have h1496 : segsOk 20000000 5984100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1496 h1497 (by norm_num)
  have h1495 : segsOk 20000000 5980100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1495 h1496 (by norm_num)
  have h1494 : segsOk 20000000 5976100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1494 h1495 (by norm_num)
  have h1493 : segsOk 20000000 5972100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1493 h1494 (by norm_num)
  have h1492 : segsOk 20000000 5968100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1492 h1493 (by norm_num)
  have h1491 : segsOk 20000000 5964100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1491 h1492 (by norm_num)
  have h1490 : segsOk 20000000 5960100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1490 h1491 (by norm_num)
  have h1489 : segsOk 20000000 5956100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1489 h1490 (by norm_num)
  have h1488 : segsOk 20000000 5952100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1488 h1489 (by norm_num)
  have h1487 : segsOk 20000000 5948100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1487 h1488 (by norm_num)
  have h1486 : segsOk 20000000 5944100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1486 h1487 (by norm_num)
  have h1485 : segsOk 20000000 5940100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1485 h1486 (by norm_num)
  have h1484 : segsOk 20000000 5936100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1484 h1485 (by norm_num)
  have h1483 : segsOk 20000000 5932100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1483 h1484 (by norm_num)
  have h1482 : segsOk 20000000 5928100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1482 h1483 (by norm_num)
  have h1481 : segsOk 20000000 5924100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1481 h1482 (by norm_num)
  have h1480 : segsOk 20000000 5920100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1480 h1481 (by norm_num)
  have h1479 : segsOk 20000000 5916100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1479 h1480 (by norm_num)
  have h1478 : segsOk 20000000 5912100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1478 h1479 (by norm_num)
  have h1477 : segsOk 20000000 5908100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1477 h1478 (by norm_num)
  have h1476 : segsOk 20000000 5904100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1476 h1477 (by norm_num)
  have h1475 : segsOk 20000000 5900100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1475 h1476 (by norm_num)
  have h1474 : segsOk 20000000 5896100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1474 h1475 (by norm_num)
  have h1473 : segsOk 20000000 5892100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1473 h1474 (by norm_num)
  have h1472 : segsOk 20000000 5888100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1472 h1473 (by norm_num)
  have h1471 : segsOk 20000000 5884100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1471 h1472 (by norm_num)
  have h1470 : segsOk 20000000 5880100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1470 h1471 (by norm_num)
  have h1469 : segsOk 20000000 5876100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1469 h1470 (by norm_num)
  have h1468 : segsOk 20000000 5872100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1468 h1469 (by norm_num)
  have h1467 : segsOk 20000000 5868100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1467 h1468 (by norm_num)
  have h1466 : segsOk 20000000 5864100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1466 h1467 (by norm_num)
  have h1465 : segsOk 20000000 5860100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1465 h1466 (by norm_num)
  have h1464 : segsOk 20000000 5856100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1464 h1465 (by norm_num)
  have h1463 : segsOk 20000000 5852100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1463 h1464 (by norm_num)
  have h1462 : segsOk 20000000 5848100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1462 h1463 (by norm_num)
  have h1461 : segsOk 20000000 5844100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1461 h1462 (by norm_num)
  have h1460 : segsOk 20000000 5840100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1460 h1461 (by norm_num)
  have h1459 : segsOk 20000000 5836100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1459 h1460 (by norm_num)
  have h1458 : segsOk 20000000 5832100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1458 h1459 (by norm_num)
  have h1457 : segsOk 20000000 5828100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1457 h1458 (by norm_num)
  have h1456 : segsOk 20000000 5824100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1456 h1457 (by norm_num)
  have h1455 : segsOk 20000000 5820100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1455 h1456 (by norm_num)
  have h1454 : segsOk 20000000 5816100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1454 h1455 (by norm_num)
  have h1453 : segsOk 20000000 5812100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1453 h1454 (by norm_num)
  have h1452 : segsOk 20000000 5808100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1452 h1453 (by norm_num)
  have h1451 : segsOk 20000000 5804100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1451 h1452 (by norm_num)
  have h1450 : segsOk 20000000 5800100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1450 h1451 (by norm_num)
  exact h1450
end Grosswald.Direct
