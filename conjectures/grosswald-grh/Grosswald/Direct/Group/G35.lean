import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1750
import Grosswald.Direct.Run.B1751
import Grosswald.Direct.Run.B1752
import Grosswald.Direct.Run.B1753
import Grosswald.Direct.Run.B1754
import Grosswald.Direct.Run.B1755
import Grosswald.Direct.Run.B1756
import Grosswald.Direct.Run.B1757
import Grosswald.Direct.Run.B1758
import Grosswald.Direct.Run.B1759
import Grosswald.Direct.Run.B1760
import Grosswald.Direct.Run.B1761
import Grosswald.Direct.Run.B1762
import Grosswald.Direct.Run.B1763
import Grosswald.Direct.Run.B1764
import Grosswald.Direct.Run.B1765
import Grosswald.Direct.Run.B1766
import Grosswald.Direct.Run.B1767
import Grosswald.Direct.Run.B1768
import Grosswald.Direct.Run.B1769
import Grosswald.Direct.Run.B1770
import Grosswald.Direct.Run.B1771
import Grosswald.Direct.Run.B1772
import Grosswald.Direct.Run.B1773
import Grosswald.Direct.Run.B1774
import Grosswald.Direct.Run.B1775
import Grosswald.Direct.Run.B1776
import Grosswald.Direct.Run.B1777
import Grosswald.Direct.Run.B1778
import Grosswald.Direct.Run.B1779
import Grosswald.Direct.Run.B1780
import Grosswald.Direct.Run.B1781
import Grosswald.Direct.Run.B1782
import Grosswald.Direct.Run.B1783
import Grosswald.Direct.Run.B1784
import Grosswald.Direct.Run.B1785
import Grosswald.Direct.Run.B1786
import Grosswald.Direct.Run.B1787
import Grosswald.Direct.Run.B1788
import Grosswald.Direct.Run.B1789
import Grosswald.Direct.Run.B1790
import Grosswald.Direct.Run.B1791
import Grosswald.Direct.Run.B1792
import Grosswald.Direct.Run.B1793
import Grosswald.Direct.Run.B1794
import Grosswald.Direct.Run.B1795
import Grosswald.Direct.Run.B1796
import Grosswald.Direct.Run.B1797
import Grosswald.Direct.Run.B1798
import Grosswald.Direct.Run.B1799

namespace Grosswald.Direct
open GrosswaldCompute
theorem g35 : segsOk 20000000 7000100000411 5000 = true := by
  have h1799 : segsOk 20000000 7196100000411 100 = true := Run.b1799
  have h1798 : segsOk 20000000 7192100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1798 h1799 (by norm_num)
  have h1797 : segsOk 20000000 7188100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1797 h1798 (by norm_num)
  have h1796 : segsOk 20000000 7184100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1796 h1797 (by norm_num)
  have h1795 : segsOk 20000000 7180100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1795 h1796 (by norm_num)
  have h1794 : segsOk 20000000 7176100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1794 h1795 (by norm_num)
  have h1793 : segsOk 20000000 7172100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1793 h1794 (by norm_num)
  have h1792 : segsOk 20000000 7168100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1792 h1793 (by norm_num)
  have h1791 : segsOk 20000000 7164100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1791 h1792 (by norm_num)
  have h1790 : segsOk 20000000 7160100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1790 h1791 (by norm_num)
  have h1789 : segsOk 20000000 7156100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1789 h1790 (by norm_num)
  have h1788 : segsOk 20000000 7152100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1788 h1789 (by norm_num)
  have h1787 : segsOk 20000000 7148100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1787 h1788 (by norm_num)
  have h1786 : segsOk 20000000 7144100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1786 h1787 (by norm_num)
  have h1785 : segsOk 20000000 7140100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1785 h1786 (by norm_num)
  have h1784 : segsOk 20000000 7136100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1784 h1785 (by norm_num)
  have h1783 : segsOk 20000000 7132100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1783 h1784 (by norm_num)
  have h1782 : segsOk 20000000 7128100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1782 h1783 (by norm_num)
  have h1781 : segsOk 20000000 7124100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1781 h1782 (by norm_num)
  have h1780 : segsOk 20000000 7120100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1780 h1781 (by norm_num)
  have h1779 : segsOk 20000000 7116100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1779 h1780 (by norm_num)
  have h1778 : segsOk 20000000 7112100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1778 h1779 (by norm_num)
  have h1777 : segsOk 20000000 7108100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1777 h1778 (by norm_num)
  have h1776 : segsOk 20000000 7104100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1776 h1777 (by norm_num)
  have h1775 : segsOk 20000000 7100100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1775 h1776 (by norm_num)
  have h1774 : segsOk 20000000 7096100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1774 h1775 (by norm_num)
  have h1773 : segsOk 20000000 7092100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1773 h1774 (by norm_num)
  have h1772 : segsOk 20000000 7088100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1772 h1773 (by norm_num)
  have h1771 : segsOk 20000000 7084100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1771 h1772 (by norm_num)
  have h1770 : segsOk 20000000 7080100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1770 h1771 (by norm_num)
  have h1769 : segsOk 20000000 7076100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1769 h1770 (by norm_num)
  have h1768 : segsOk 20000000 7072100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1768 h1769 (by norm_num)
  have h1767 : segsOk 20000000 7068100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1767 h1768 (by norm_num)
  have h1766 : segsOk 20000000 7064100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1766 h1767 (by norm_num)
  have h1765 : segsOk 20000000 7060100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1765 h1766 (by norm_num)
  have h1764 : segsOk 20000000 7056100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1764 h1765 (by norm_num)
  have h1763 : segsOk 20000000 7052100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1763 h1764 (by norm_num)
  have h1762 : segsOk 20000000 7048100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1762 h1763 (by norm_num)
  have h1761 : segsOk 20000000 7044100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1761 h1762 (by norm_num)
  have h1760 : segsOk 20000000 7040100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1760 h1761 (by norm_num)
  have h1759 : segsOk 20000000 7036100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1759 h1760 (by norm_num)
  have h1758 : segsOk 20000000 7032100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1758 h1759 (by norm_num)
  have h1757 : segsOk 20000000 7028100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1757 h1758 (by norm_num)
  have h1756 : segsOk 20000000 7024100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1756 h1757 (by norm_num)
  have h1755 : segsOk 20000000 7020100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1755 h1756 (by norm_num)
  have h1754 : segsOk 20000000 7016100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1754 h1755 (by norm_num)
  have h1753 : segsOk 20000000 7012100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1753 h1754 (by norm_num)
  have h1752 : segsOk 20000000 7008100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1752 h1753 (by norm_num)
  have h1751 : segsOk 20000000 7004100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1751 h1752 (by norm_num)
  have h1750 : segsOk 20000000 7000100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1750 h1751 (by norm_num)
  exact h1750
end Grosswald.Direct
