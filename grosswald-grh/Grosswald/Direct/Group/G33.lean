import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1650
import Grosswald.Direct.Run.B1651
import Grosswald.Direct.Run.B1652
import Grosswald.Direct.Run.B1653
import Grosswald.Direct.Run.B1654
import Grosswald.Direct.Run.B1655
import Grosswald.Direct.Run.B1656
import Grosswald.Direct.Run.B1657
import Grosswald.Direct.Run.B1658
import Grosswald.Direct.Run.B1659
import Grosswald.Direct.Run.B1660
import Grosswald.Direct.Run.B1661
import Grosswald.Direct.Run.B1662
import Grosswald.Direct.Run.B1663
import Grosswald.Direct.Run.B1664
import Grosswald.Direct.Run.B1665
import Grosswald.Direct.Run.B1666
import Grosswald.Direct.Run.B1667
import Grosswald.Direct.Run.B1668
import Grosswald.Direct.Run.B1669
import Grosswald.Direct.Run.B1670
import Grosswald.Direct.Run.B1671
import Grosswald.Direct.Run.B1672
import Grosswald.Direct.Run.B1673
import Grosswald.Direct.Run.B1674
import Grosswald.Direct.Run.B1675
import Grosswald.Direct.Run.B1676
import Grosswald.Direct.Run.B1677
import Grosswald.Direct.Run.B1678
import Grosswald.Direct.Run.B1679
import Grosswald.Direct.Run.B1680
import Grosswald.Direct.Run.B1681
import Grosswald.Direct.Run.B1682
import Grosswald.Direct.Run.B1683
import Grosswald.Direct.Run.B1684
import Grosswald.Direct.Run.B1685
import Grosswald.Direct.Run.B1686
import Grosswald.Direct.Run.B1687
import Grosswald.Direct.Run.B1688
import Grosswald.Direct.Run.B1689
import Grosswald.Direct.Run.B1690
import Grosswald.Direct.Run.B1691
import Grosswald.Direct.Run.B1692
import Grosswald.Direct.Run.B1693
import Grosswald.Direct.Run.B1694
import Grosswald.Direct.Run.B1695
import Grosswald.Direct.Run.B1696
import Grosswald.Direct.Run.B1697
import Grosswald.Direct.Run.B1698
import Grosswald.Direct.Run.B1699

namespace Grosswald.Direct
open GrosswaldCompute
theorem g33 : segsOk 20000000 6600100000411 5000 = true := by
  have h1699 : segsOk 20000000 6796100000411 100 = true := Run.b1699
  have h1698 : segsOk 20000000 6792100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1698 h1699 (by norm_num)
  have h1697 : segsOk 20000000 6788100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1697 h1698 (by norm_num)
  have h1696 : segsOk 20000000 6784100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1696 h1697 (by norm_num)
  have h1695 : segsOk 20000000 6780100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1695 h1696 (by norm_num)
  have h1694 : segsOk 20000000 6776100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1694 h1695 (by norm_num)
  have h1693 : segsOk 20000000 6772100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1693 h1694 (by norm_num)
  have h1692 : segsOk 20000000 6768100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1692 h1693 (by norm_num)
  have h1691 : segsOk 20000000 6764100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1691 h1692 (by norm_num)
  have h1690 : segsOk 20000000 6760100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1690 h1691 (by norm_num)
  have h1689 : segsOk 20000000 6756100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1689 h1690 (by norm_num)
  have h1688 : segsOk 20000000 6752100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1688 h1689 (by norm_num)
  have h1687 : segsOk 20000000 6748100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1687 h1688 (by norm_num)
  have h1686 : segsOk 20000000 6744100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1686 h1687 (by norm_num)
  have h1685 : segsOk 20000000 6740100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1685 h1686 (by norm_num)
  have h1684 : segsOk 20000000 6736100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1684 h1685 (by norm_num)
  have h1683 : segsOk 20000000 6732100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1683 h1684 (by norm_num)
  have h1682 : segsOk 20000000 6728100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1682 h1683 (by norm_num)
  have h1681 : segsOk 20000000 6724100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1681 h1682 (by norm_num)
  have h1680 : segsOk 20000000 6720100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1680 h1681 (by norm_num)
  have h1679 : segsOk 20000000 6716100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1679 h1680 (by norm_num)
  have h1678 : segsOk 20000000 6712100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1678 h1679 (by norm_num)
  have h1677 : segsOk 20000000 6708100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1677 h1678 (by norm_num)
  have h1676 : segsOk 20000000 6704100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1676 h1677 (by norm_num)
  have h1675 : segsOk 20000000 6700100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1675 h1676 (by norm_num)
  have h1674 : segsOk 20000000 6696100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1674 h1675 (by norm_num)
  have h1673 : segsOk 20000000 6692100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1673 h1674 (by norm_num)
  have h1672 : segsOk 20000000 6688100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1672 h1673 (by norm_num)
  have h1671 : segsOk 20000000 6684100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1671 h1672 (by norm_num)
  have h1670 : segsOk 20000000 6680100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1670 h1671 (by norm_num)
  have h1669 : segsOk 20000000 6676100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1669 h1670 (by norm_num)
  have h1668 : segsOk 20000000 6672100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1668 h1669 (by norm_num)
  have h1667 : segsOk 20000000 6668100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1667 h1668 (by norm_num)
  have h1666 : segsOk 20000000 6664100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1666 h1667 (by norm_num)
  have h1665 : segsOk 20000000 6660100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1665 h1666 (by norm_num)
  have h1664 : segsOk 20000000 6656100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1664 h1665 (by norm_num)
  have h1663 : segsOk 20000000 6652100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1663 h1664 (by norm_num)
  have h1662 : segsOk 20000000 6648100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1662 h1663 (by norm_num)
  have h1661 : segsOk 20000000 6644100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1661 h1662 (by norm_num)
  have h1660 : segsOk 20000000 6640100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1660 h1661 (by norm_num)
  have h1659 : segsOk 20000000 6636100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1659 h1660 (by norm_num)
  have h1658 : segsOk 20000000 6632100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1658 h1659 (by norm_num)
  have h1657 : segsOk 20000000 6628100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1657 h1658 (by norm_num)
  have h1656 : segsOk 20000000 6624100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1656 h1657 (by norm_num)
  have h1655 : segsOk 20000000 6620100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1655 h1656 (by norm_num)
  have h1654 : segsOk 20000000 6616100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1654 h1655 (by norm_num)
  have h1653 : segsOk 20000000 6612100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1653 h1654 (by norm_num)
  have h1652 : segsOk 20000000 6608100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1652 h1653 (by norm_num)
  have h1651 : segsOk 20000000 6604100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1651 h1652 (by norm_num)
  have h1650 : segsOk 20000000 6600100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1650 h1651 (by norm_num)
  exact h1650
end Grosswald.Direct
