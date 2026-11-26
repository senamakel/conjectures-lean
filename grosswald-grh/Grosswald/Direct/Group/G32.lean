import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1600
import Grosswald.Direct.Run.B1601
import Grosswald.Direct.Run.B1602
import Grosswald.Direct.Run.B1603
import Grosswald.Direct.Run.B1604
import Grosswald.Direct.Run.B1605
import Grosswald.Direct.Run.B1606
import Grosswald.Direct.Run.B1607
import Grosswald.Direct.Run.B1608
import Grosswald.Direct.Run.B1609
import Grosswald.Direct.Run.B1610
import Grosswald.Direct.Run.B1611
import Grosswald.Direct.Run.B1612
import Grosswald.Direct.Run.B1613
import Grosswald.Direct.Run.B1614
import Grosswald.Direct.Run.B1615
import Grosswald.Direct.Run.B1616
import Grosswald.Direct.Run.B1617
import Grosswald.Direct.Run.B1618
import Grosswald.Direct.Run.B1619
import Grosswald.Direct.Run.B1620
import Grosswald.Direct.Run.B1621
import Grosswald.Direct.Run.B1622
import Grosswald.Direct.Run.B1623
import Grosswald.Direct.Run.B1624
import Grosswald.Direct.Run.B1625
import Grosswald.Direct.Run.B1626
import Grosswald.Direct.Run.B1627
import Grosswald.Direct.Run.B1628
import Grosswald.Direct.Run.B1629
import Grosswald.Direct.Run.B1630
import Grosswald.Direct.Run.B1631
import Grosswald.Direct.Run.B1632
import Grosswald.Direct.Run.B1633
import Grosswald.Direct.Run.B1634
import Grosswald.Direct.Run.B1635
import Grosswald.Direct.Run.B1636
import Grosswald.Direct.Run.B1637
import Grosswald.Direct.Run.B1638
import Grosswald.Direct.Run.B1639
import Grosswald.Direct.Run.B1640
import Grosswald.Direct.Run.B1641
import Grosswald.Direct.Run.B1642
import Grosswald.Direct.Run.B1643
import Grosswald.Direct.Run.B1644
import Grosswald.Direct.Run.B1645
import Grosswald.Direct.Run.B1646
import Grosswald.Direct.Run.B1647
import Grosswald.Direct.Run.B1648
import Grosswald.Direct.Run.B1649

namespace Grosswald.Direct
open GrosswaldCompute
theorem g32 : segsOk 20000000 6400100000411 5000 = true := by
  have h1649 : segsOk 20000000 6596100000411 100 = true := Run.b1649
  have h1648 : segsOk 20000000 6592100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1648 h1649 (by norm_num)
  have h1647 : segsOk 20000000 6588100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1647 h1648 (by norm_num)
  have h1646 : segsOk 20000000 6584100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1646 h1647 (by norm_num)
  have h1645 : segsOk 20000000 6580100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1645 h1646 (by norm_num)
  have h1644 : segsOk 20000000 6576100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1644 h1645 (by norm_num)
  have h1643 : segsOk 20000000 6572100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1643 h1644 (by norm_num)
  have h1642 : segsOk 20000000 6568100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1642 h1643 (by norm_num)
  have h1641 : segsOk 20000000 6564100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1641 h1642 (by norm_num)
  have h1640 : segsOk 20000000 6560100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1640 h1641 (by norm_num)
  have h1639 : segsOk 20000000 6556100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1639 h1640 (by norm_num)
  have h1638 : segsOk 20000000 6552100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1638 h1639 (by norm_num)
  have h1637 : segsOk 20000000 6548100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1637 h1638 (by norm_num)
  have h1636 : segsOk 20000000 6544100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1636 h1637 (by norm_num)
  have h1635 : segsOk 20000000 6540100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1635 h1636 (by norm_num)
  have h1634 : segsOk 20000000 6536100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1634 h1635 (by norm_num)
  have h1633 : segsOk 20000000 6532100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1633 h1634 (by norm_num)
  have h1632 : segsOk 20000000 6528100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1632 h1633 (by norm_num)
  have h1631 : segsOk 20000000 6524100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1631 h1632 (by norm_num)
  have h1630 : segsOk 20000000 6520100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1630 h1631 (by norm_num)
  have h1629 : segsOk 20000000 6516100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1629 h1630 (by norm_num)
  have h1628 : segsOk 20000000 6512100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1628 h1629 (by norm_num)
  have h1627 : segsOk 20000000 6508100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1627 h1628 (by norm_num)
  have h1626 : segsOk 20000000 6504100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1626 h1627 (by norm_num)
  have h1625 : segsOk 20000000 6500100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1625 h1626 (by norm_num)
  have h1624 : segsOk 20000000 6496100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1624 h1625 (by norm_num)
  have h1623 : segsOk 20000000 6492100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1623 h1624 (by norm_num)
  have h1622 : segsOk 20000000 6488100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1622 h1623 (by norm_num)
  have h1621 : segsOk 20000000 6484100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1621 h1622 (by norm_num)
  have h1620 : segsOk 20000000 6480100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1620 h1621 (by norm_num)
  have h1619 : segsOk 20000000 6476100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1619 h1620 (by norm_num)
  have h1618 : segsOk 20000000 6472100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1618 h1619 (by norm_num)
  have h1617 : segsOk 20000000 6468100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1617 h1618 (by norm_num)
  have h1616 : segsOk 20000000 6464100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1616 h1617 (by norm_num)
  have h1615 : segsOk 20000000 6460100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1615 h1616 (by norm_num)
  have h1614 : segsOk 20000000 6456100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1614 h1615 (by norm_num)
  have h1613 : segsOk 20000000 6452100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1613 h1614 (by norm_num)
  have h1612 : segsOk 20000000 6448100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1612 h1613 (by norm_num)
  have h1611 : segsOk 20000000 6444100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1611 h1612 (by norm_num)
  have h1610 : segsOk 20000000 6440100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1610 h1611 (by norm_num)
  have h1609 : segsOk 20000000 6436100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1609 h1610 (by norm_num)
  have h1608 : segsOk 20000000 6432100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1608 h1609 (by norm_num)
  have h1607 : segsOk 20000000 6428100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1607 h1608 (by norm_num)
  have h1606 : segsOk 20000000 6424100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1606 h1607 (by norm_num)
  have h1605 : segsOk 20000000 6420100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1605 h1606 (by norm_num)
  have h1604 : segsOk 20000000 6416100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1604 h1605 (by norm_num)
  have h1603 : segsOk 20000000 6412100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1603 h1604 (by norm_num)
  have h1602 : segsOk 20000000 6408100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1602 h1603 (by norm_num)
  have h1601 : segsOk 20000000 6404100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1601 h1602 (by norm_num)
  have h1600 : segsOk 20000000 6400100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1600 h1601 (by norm_num)
  exact h1600
end Grosswald.Direct
