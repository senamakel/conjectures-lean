import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1550
import Grosswald.Direct.Run.B1551
import Grosswald.Direct.Run.B1552
import Grosswald.Direct.Run.B1553
import Grosswald.Direct.Run.B1554
import Grosswald.Direct.Run.B1555
import Grosswald.Direct.Run.B1556
import Grosswald.Direct.Run.B1557
import Grosswald.Direct.Run.B1558
import Grosswald.Direct.Run.B1559
import Grosswald.Direct.Run.B1560
import Grosswald.Direct.Run.B1561
import Grosswald.Direct.Run.B1562
import Grosswald.Direct.Run.B1563
import Grosswald.Direct.Run.B1564
import Grosswald.Direct.Run.B1565
import Grosswald.Direct.Run.B1566
import Grosswald.Direct.Run.B1567
import Grosswald.Direct.Run.B1568
import Grosswald.Direct.Run.B1569
import Grosswald.Direct.Run.B1570
import Grosswald.Direct.Run.B1571
import Grosswald.Direct.Run.B1572
import Grosswald.Direct.Run.B1573
import Grosswald.Direct.Run.B1574
import Grosswald.Direct.Run.B1575
import Grosswald.Direct.Run.B1576
import Grosswald.Direct.Run.B1577
import Grosswald.Direct.Run.B1578
import Grosswald.Direct.Run.B1579
import Grosswald.Direct.Run.B1580
import Grosswald.Direct.Run.B1581
import Grosswald.Direct.Run.B1582
import Grosswald.Direct.Run.B1583
import Grosswald.Direct.Run.B1584
import Grosswald.Direct.Run.B1585
import Grosswald.Direct.Run.B1586
import Grosswald.Direct.Run.B1587
import Grosswald.Direct.Run.B1588
import Grosswald.Direct.Run.B1589
import Grosswald.Direct.Run.B1590
import Grosswald.Direct.Run.B1591
import Grosswald.Direct.Run.B1592
import Grosswald.Direct.Run.B1593
import Grosswald.Direct.Run.B1594
import Grosswald.Direct.Run.B1595
import Grosswald.Direct.Run.B1596
import Grosswald.Direct.Run.B1597
import Grosswald.Direct.Run.B1598
import Grosswald.Direct.Run.B1599

namespace Grosswald.Direct
open GrosswaldCompute
theorem g31 : segsOk 20000000 6200100000411 5000 = true := by
  have h1599 : segsOk 20000000 6396100000411 100 = true := Run.b1599
  have h1598 : segsOk 20000000 6392100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1598 h1599 (by norm_num)
  have h1597 : segsOk 20000000 6388100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1597 h1598 (by norm_num)
  have h1596 : segsOk 20000000 6384100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1596 h1597 (by norm_num)
  have h1595 : segsOk 20000000 6380100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1595 h1596 (by norm_num)
  have h1594 : segsOk 20000000 6376100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1594 h1595 (by norm_num)
  have h1593 : segsOk 20000000 6372100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1593 h1594 (by norm_num)
  have h1592 : segsOk 20000000 6368100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1592 h1593 (by norm_num)
  have h1591 : segsOk 20000000 6364100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1591 h1592 (by norm_num)
  have h1590 : segsOk 20000000 6360100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1590 h1591 (by norm_num)
  have h1589 : segsOk 20000000 6356100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1589 h1590 (by norm_num)
  have h1588 : segsOk 20000000 6352100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1588 h1589 (by norm_num)
  have h1587 : segsOk 20000000 6348100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1587 h1588 (by norm_num)
  have h1586 : segsOk 20000000 6344100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1586 h1587 (by norm_num)
  have h1585 : segsOk 20000000 6340100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1585 h1586 (by norm_num)
  have h1584 : segsOk 20000000 6336100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1584 h1585 (by norm_num)
  have h1583 : segsOk 20000000 6332100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1583 h1584 (by norm_num)
  have h1582 : segsOk 20000000 6328100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1582 h1583 (by norm_num)
  have h1581 : segsOk 20000000 6324100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1581 h1582 (by norm_num)
  have h1580 : segsOk 20000000 6320100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1580 h1581 (by norm_num)
  have h1579 : segsOk 20000000 6316100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1579 h1580 (by norm_num)
  have h1578 : segsOk 20000000 6312100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1578 h1579 (by norm_num)
  have h1577 : segsOk 20000000 6308100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1577 h1578 (by norm_num)
  have h1576 : segsOk 20000000 6304100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1576 h1577 (by norm_num)
  have h1575 : segsOk 20000000 6300100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1575 h1576 (by norm_num)
  have h1574 : segsOk 20000000 6296100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1574 h1575 (by norm_num)
  have h1573 : segsOk 20000000 6292100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1573 h1574 (by norm_num)
  have h1572 : segsOk 20000000 6288100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1572 h1573 (by norm_num)
  have h1571 : segsOk 20000000 6284100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1571 h1572 (by norm_num)
  have h1570 : segsOk 20000000 6280100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1570 h1571 (by norm_num)
  have h1569 : segsOk 20000000 6276100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1569 h1570 (by norm_num)
  have h1568 : segsOk 20000000 6272100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1568 h1569 (by norm_num)
  have h1567 : segsOk 20000000 6268100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1567 h1568 (by norm_num)
  have h1566 : segsOk 20000000 6264100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1566 h1567 (by norm_num)
  have h1565 : segsOk 20000000 6260100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1565 h1566 (by norm_num)
  have h1564 : segsOk 20000000 6256100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1564 h1565 (by norm_num)
  have h1563 : segsOk 20000000 6252100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1563 h1564 (by norm_num)
  have h1562 : segsOk 20000000 6248100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1562 h1563 (by norm_num)
  have h1561 : segsOk 20000000 6244100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1561 h1562 (by norm_num)
  have h1560 : segsOk 20000000 6240100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1560 h1561 (by norm_num)
  have h1559 : segsOk 20000000 6236100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1559 h1560 (by norm_num)
  have h1558 : segsOk 20000000 6232100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1558 h1559 (by norm_num)
  have h1557 : segsOk 20000000 6228100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1557 h1558 (by norm_num)
  have h1556 : segsOk 20000000 6224100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1556 h1557 (by norm_num)
  have h1555 : segsOk 20000000 6220100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1555 h1556 (by norm_num)
  have h1554 : segsOk 20000000 6216100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1554 h1555 (by norm_num)
  have h1553 : segsOk 20000000 6212100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1553 h1554 (by norm_num)
  have h1552 : segsOk 20000000 6208100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1552 h1553 (by norm_num)
  have h1551 : segsOk 20000000 6204100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1551 h1552 (by norm_num)
  have h1550 : segsOk 20000000 6200100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1550 h1551 (by norm_num)
  exact h1550
end Grosswald.Direct
