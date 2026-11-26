import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1700
import Grosswald.Direct.Run.B1701
import Grosswald.Direct.Run.B1702
import Grosswald.Direct.Run.B1703
import Grosswald.Direct.Run.B1704
import Grosswald.Direct.Run.B1705
import Grosswald.Direct.Run.B1706
import Grosswald.Direct.Run.B1707
import Grosswald.Direct.Run.B1708
import Grosswald.Direct.Run.B1709
import Grosswald.Direct.Run.B1710
import Grosswald.Direct.Run.B1711
import Grosswald.Direct.Run.B1712
import Grosswald.Direct.Run.B1713
import Grosswald.Direct.Run.B1714
import Grosswald.Direct.Run.B1715
import Grosswald.Direct.Run.B1716
import Grosswald.Direct.Run.B1717
import Grosswald.Direct.Run.B1718
import Grosswald.Direct.Run.B1719
import Grosswald.Direct.Run.B1720
import Grosswald.Direct.Run.B1721
import Grosswald.Direct.Run.B1722
import Grosswald.Direct.Run.B1723
import Grosswald.Direct.Run.B1724
import Grosswald.Direct.Run.B1725
import Grosswald.Direct.Run.B1726
import Grosswald.Direct.Run.B1727
import Grosswald.Direct.Run.B1728
import Grosswald.Direct.Run.B1729
import Grosswald.Direct.Run.B1730
import Grosswald.Direct.Run.B1731
import Grosswald.Direct.Run.B1732
import Grosswald.Direct.Run.B1733
import Grosswald.Direct.Run.B1734
import Grosswald.Direct.Run.B1735
import Grosswald.Direct.Run.B1736
import Grosswald.Direct.Run.B1737
import Grosswald.Direct.Run.B1738
import Grosswald.Direct.Run.B1739
import Grosswald.Direct.Run.B1740
import Grosswald.Direct.Run.B1741
import Grosswald.Direct.Run.B1742
import Grosswald.Direct.Run.B1743
import Grosswald.Direct.Run.B1744
import Grosswald.Direct.Run.B1745
import Grosswald.Direct.Run.B1746
import Grosswald.Direct.Run.B1747
import Grosswald.Direct.Run.B1748
import Grosswald.Direct.Run.B1749

namespace Grosswald.Direct
open GrosswaldCompute
theorem g34 : segsOk 20000000 6800100000411 5000 = true := by
  have h1749 : segsOk 20000000 6996100000411 100 = true := Run.b1749
  have h1748 : segsOk 20000000 6992100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1748 h1749 (by norm_num)
  have h1747 : segsOk 20000000 6988100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1747 h1748 (by norm_num)
  have h1746 : segsOk 20000000 6984100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1746 h1747 (by norm_num)
  have h1745 : segsOk 20000000 6980100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1745 h1746 (by norm_num)
  have h1744 : segsOk 20000000 6976100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1744 h1745 (by norm_num)
  have h1743 : segsOk 20000000 6972100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1743 h1744 (by norm_num)
  have h1742 : segsOk 20000000 6968100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1742 h1743 (by norm_num)
  have h1741 : segsOk 20000000 6964100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1741 h1742 (by norm_num)
  have h1740 : segsOk 20000000 6960100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1740 h1741 (by norm_num)
  have h1739 : segsOk 20000000 6956100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1739 h1740 (by norm_num)
  have h1738 : segsOk 20000000 6952100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1738 h1739 (by norm_num)
  have h1737 : segsOk 20000000 6948100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1737 h1738 (by norm_num)
  have h1736 : segsOk 20000000 6944100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1736 h1737 (by norm_num)
  have h1735 : segsOk 20000000 6940100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1735 h1736 (by norm_num)
  have h1734 : segsOk 20000000 6936100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1734 h1735 (by norm_num)
  have h1733 : segsOk 20000000 6932100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1733 h1734 (by norm_num)
  have h1732 : segsOk 20000000 6928100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1732 h1733 (by norm_num)
  have h1731 : segsOk 20000000 6924100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1731 h1732 (by norm_num)
  have h1730 : segsOk 20000000 6920100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1730 h1731 (by norm_num)
  have h1729 : segsOk 20000000 6916100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1729 h1730 (by norm_num)
  have h1728 : segsOk 20000000 6912100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1728 h1729 (by norm_num)
  have h1727 : segsOk 20000000 6908100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1727 h1728 (by norm_num)
  have h1726 : segsOk 20000000 6904100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1726 h1727 (by norm_num)
  have h1725 : segsOk 20000000 6900100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1725 h1726 (by norm_num)
  have h1724 : segsOk 20000000 6896100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1724 h1725 (by norm_num)
  have h1723 : segsOk 20000000 6892100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1723 h1724 (by norm_num)
  have h1722 : segsOk 20000000 6888100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1722 h1723 (by norm_num)
  have h1721 : segsOk 20000000 6884100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1721 h1722 (by norm_num)
  have h1720 : segsOk 20000000 6880100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1720 h1721 (by norm_num)
  have h1719 : segsOk 20000000 6876100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1719 h1720 (by norm_num)
  have h1718 : segsOk 20000000 6872100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1718 h1719 (by norm_num)
  have h1717 : segsOk 20000000 6868100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1717 h1718 (by norm_num)
  have h1716 : segsOk 20000000 6864100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1716 h1717 (by norm_num)
  have h1715 : segsOk 20000000 6860100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1715 h1716 (by norm_num)
  have h1714 : segsOk 20000000 6856100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1714 h1715 (by norm_num)
  have h1713 : segsOk 20000000 6852100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1713 h1714 (by norm_num)
  have h1712 : segsOk 20000000 6848100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1712 h1713 (by norm_num)
  have h1711 : segsOk 20000000 6844100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1711 h1712 (by norm_num)
  have h1710 : segsOk 20000000 6840100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1710 h1711 (by norm_num)
  have h1709 : segsOk 20000000 6836100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1709 h1710 (by norm_num)
  have h1708 : segsOk 20000000 6832100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1708 h1709 (by norm_num)
  have h1707 : segsOk 20000000 6828100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1707 h1708 (by norm_num)
  have h1706 : segsOk 20000000 6824100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1706 h1707 (by norm_num)
  have h1705 : segsOk 20000000 6820100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1705 h1706 (by norm_num)
  have h1704 : segsOk 20000000 6816100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1704 h1705 (by norm_num)
  have h1703 : segsOk 20000000 6812100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1703 h1704 (by norm_num)
  have h1702 : segsOk 20000000 6808100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1702 h1703 (by norm_num)
  have h1701 : segsOk 20000000 6804100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1701 h1702 (by norm_num)
  have h1700 : segsOk 20000000 6800100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1700 h1701 (by norm_num)
  exact h1700
end Grosswald.Direct
