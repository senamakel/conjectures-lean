import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1500
import Grosswald.Direct.Run.B1501
import Grosswald.Direct.Run.B1502
import Grosswald.Direct.Run.B1503
import Grosswald.Direct.Run.B1504
import Grosswald.Direct.Run.B1505
import Grosswald.Direct.Run.B1506
import Grosswald.Direct.Run.B1507
import Grosswald.Direct.Run.B1508
import Grosswald.Direct.Run.B1509
import Grosswald.Direct.Run.B1510
import Grosswald.Direct.Run.B1511
import Grosswald.Direct.Run.B1512
import Grosswald.Direct.Run.B1513
import Grosswald.Direct.Run.B1514
import Grosswald.Direct.Run.B1515
import Grosswald.Direct.Run.B1516
import Grosswald.Direct.Run.B1517
import Grosswald.Direct.Run.B1518
import Grosswald.Direct.Run.B1519
import Grosswald.Direct.Run.B1520
import Grosswald.Direct.Run.B1521
import Grosswald.Direct.Run.B1522
import Grosswald.Direct.Run.B1523
import Grosswald.Direct.Run.B1524
import Grosswald.Direct.Run.B1525
import Grosswald.Direct.Run.B1526
import Grosswald.Direct.Run.B1527
import Grosswald.Direct.Run.B1528
import Grosswald.Direct.Run.B1529
import Grosswald.Direct.Run.B1530
import Grosswald.Direct.Run.B1531
import Grosswald.Direct.Run.B1532
import Grosswald.Direct.Run.B1533
import Grosswald.Direct.Run.B1534
import Grosswald.Direct.Run.B1535
import Grosswald.Direct.Run.B1536
import Grosswald.Direct.Run.B1537
import Grosswald.Direct.Run.B1538
import Grosswald.Direct.Run.B1539
import Grosswald.Direct.Run.B1540
import Grosswald.Direct.Run.B1541
import Grosswald.Direct.Run.B1542
import Grosswald.Direct.Run.B1543
import Grosswald.Direct.Run.B1544
import Grosswald.Direct.Run.B1545
import Grosswald.Direct.Run.B1546
import Grosswald.Direct.Run.B1547
import Grosswald.Direct.Run.B1548
import Grosswald.Direct.Run.B1549

namespace Grosswald.Direct
open GrosswaldCompute
theorem g30 : segsOk 20000000 6000100000411 5000 = true := by
  have h1549 : segsOk 20000000 6196100000411 100 = true := Run.b1549
  have h1548 : segsOk 20000000 6192100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1548 h1549 (by norm_num)
  have h1547 : segsOk 20000000 6188100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1547 h1548 (by norm_num)
  have h1546 : segsOk 20000000 6184100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1546 h1547 (by norm_num)
  have h1545 : segsOk 20000000 6180100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1545 h1546 (by norm_num)
  have h1544 : segsOk 20000000 6176100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1544 h1545 (by norm_num)
  have h1543 : segsOk 20000000 6172100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1543 h1544 (by norm_num)
  have h1542 : segsOk 20000000 6168100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1542 h1543 (by norm_num)
  have h1541 : segsOk 20000000 6164100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1541 h1542 (by norm_num)
  have h1540 : segsOk 20000000 6160100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1540 h1541 (by norm_num)
  have h1539 : segsOk 20000000 6156100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1539 h1540 (by norm_num)
  have h1538 : segsOk 20000000 6152100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1538 h1539 (by norm_num)
  have h1537 : segsOk 20000000 6148100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1537 h1538 (by norm_num)
  have h1536 : segsOk 20000000 6144100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1536 h1537 (by norm_num)
  have h1535 : segsOk 20000000 6140100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1535 h1536 (by norm_num)
  have h1534 : segsOk 20000000 6136100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1534 h1535 (by norm_num)
  have h1533 : segsOk 20000000 6132100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1533 h1534 (by norm_num)
  have h1532 : segsOk 20000000 6128100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1532 h1533 (by norm_num)
  have h1531 : segsOk 20000000 6124100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1531 h1532 (by norm_num)
  have h1530 : segsOk 20000000 6120100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1530 h1531 (by norm_num)
  have h1529 : segsOk 20000000 6116100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1529 h1530 (by norm_num)
  have h1528 : segsOk 20000000 6112100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1528 h1529 (by norm_num)
  have h1527 : segsOk 20000000 6108100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1527 h1528 (by norm_num)
  have h1526 : segsOk 20000000 6104100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1526 h1527 (by norm_num)
  have h1525 : segsOk 20000000 6100100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1525 h1526 (by norm_num)
  have h1524 : segsOk 20000000 6096100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1524 h1525 (by norm_num)
  have h1523 : segsOk 20000000 6092100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1523 h1524 (by norm_num)
  have h1522 : segsOk 20000000 6088100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1522 h1523 (by norm_num)
  have h1521 : segsOk 20000000 6084100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1521 h1522 (by norm_num)
  have h1520 : segsOk 20000000 6080100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1520 h1521 (by norm_num)
  have h1519 : segsOk 20000000 6076100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1519 h1520 (by norm_num)
  have h1518 : segsOk 20000000 6072100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1518 h1519 (by norm_num)
  have h1517 : segsOk 20000000 6068100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1517 h1518 (by norm_num)
  have h1516 : segsOk 20000000 6064100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1516 h1517 (by norm_num)
  have h1515 : segsOk 20000000 6060100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1515 h1516 (by norm_num)
  have h1514 : segsOk 20000000 6056100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1514 h1515 (by norm_num)
  have h1513 : segsOk 20000000 6052100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1513 h1514 (by norm_num)
  have h1512 : segsOk 20000000 6048100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1512 h1513 (by norm_num)
  have h1511 : segsOk 20000000 6044100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1511 h1512 (by norm_num)
  have h1510 : segsOk 20000000 6040100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1510 h1511 (by norm_num)
  have h1509 : segsOk 20000000 6036100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1509 h1510 (by norm_num)
  have h1508 : segsOk 20000000 6032100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1508 h1509 (by norm_num)
  have h1507 : segsOk 20000000 6028100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1507 h1508 (by norm_num)
  have h1506 : segsOk 20000000 6024100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1506 h1507 (by norm_num)
  have h1505 : segsOk 20000000 6020100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1505 h1506 (by norm_num)
  have h1504 : segsOk 20000000 6016100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1504 h1505 (by norm_num)
  have h1503 : segsOk 20000000 6012100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1503 h1504 (by norm_num)
  have h1502 : segsOk 20000000 6008100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1502 h1503 (by norm_num)
  have h1501 : segsOk 20000000 6004100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1501 h1502 (by norm_num)
  have h1500 : segsOk 20000000 6000100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1500 h1501 (by norm_num)
  exact h1500
end Grosswald.Direct
