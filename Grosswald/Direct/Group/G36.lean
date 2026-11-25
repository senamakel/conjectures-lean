import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1800
import Grosswald.Direct.Run.B1801
import Grosswald.Direct.Run.B1802
import Grosswald.Direct.Run.B1803
import Grosswald.Direct.Run.B1804
import Grosswald.Direct.Run.B1805
import Grosswald.Direct.Run.B1806
import Grosswald.Direct.Run.B1807
import Grosswald.Direct.Run.B1808
import Grosswald.Direct.Run.B1809
import Grosswald.Direct.Run.B1810
import Grosswald.Direct.Run.B1811
import Grosswald.Direct.Run.B1812
import Grosswald.Direct.Run.B1813
import Grosswald.Direct.Run.B1814
import Grosswald.Direct.Run.B1815
import Grosswald.Direct.Run.B1816
import Grosswald.Direct.Run.B1817
import Grosswald.Direct.Run.B1818
import Grosswald.Direct.Run.B1819
import Grosswald.Direct.Run.B1820
import Grosswald.Direct.Run.B1821
import Grosswald.Direct.Run.B1822
import Grosswald.Direct.Run.B1823
import Grosswald.Direct.Run.B1824
import Grosswald.Direct.Run.B1825
import Grosswald.Direct.Run.B1826
import Grosswald.Direct.Run.B1827
import Grosswald.Direct.Run.B1828
import Grosswald.Direct.Run.B1829
import Grosswald.Direct.Run.B1830
import Grosswald.Direct.Run.B1831
import Grosswald.Direct.Run.B1832
import Grosswald.Direct.Run.B1833
import Grosswald.Direct.Run.B1834
import Grosswald.Direct.Run.B1835
import Grosswald.Direct.Run.B1836
import Grosswald.Direct.Run.B1837
import Grosswald.Direct.Run.B1838
import Grosswald.Direct.Run.B1839
import Grosswald.Direct.Run.B1840
import Grosswald.Direct.Run.B1841
import Grosswald.Direct.Run.B1842
import Grosswald.Direct.Run.B1843
import Grosswald.Direct.Run.B1844
import Grosswald.Direct.Run.B1845
import Grosswald.Direct.Run.B1846
import Grosswald.Direct.Run.B1847
import Grosswald.Direct.Run.B1848
import Grosswald.Direct.Run.B1849

namespace Grosswald.Direct
open GrosswaldCompute
theorem g36 : segsOk 20000000 7200100000411 5000 = true := by
  have h1849 : segsOk 20000000 7396100000411 100 = true := Run.b1849
  have h1848 : segsOk 20000000 7392100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1848 h1849 (by norm_num)
  have h1847 : segsOk 20000000 7388100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1847 h1848 (by norm_num)
  have h1846 : segsOk 20000000 7384100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1846 h1847 (by norm_num)
  have h1845 : segsOk 20000000 7380100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1845 h1846 (by norm_num)
  have h1844 : segsOk 20000000 7376100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1844 h1845 (by norm_num)
  have h1843 : segsOk 20000000 7372100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1843 h1844 (by norm_num)
  have h1842 : segsOk 20000000 7368100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1842 h1843 (by norm_num)
  have h1841 : segsOk 20000000 7364100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1841 h1842 (by norm_num)
  have h1840 : segsOk 20000000 7360100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1840 h1841 (by norm_num)
  have h1839 : segsOk 20000000 7356100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1839 h1840 (by norm_num)
  have h1838 : segsOk 20000000 7352100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1838 h1839 (by norm_num)
  have h1837 : segsOk 20000000 7348100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1837 h1838 (by norm_num)
  have h1836 : segsOk 20000000 7344100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1836 h1837 (by norm_num)
  have h1835 : segsOk 20000000 7340100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1835 h1836 (by norm_num)
  have h1834 : segsOk 20000000 7336100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1834 h1835 (by norm_num)
  have h1833 : segsOk 20000000 7332100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1833 h1834 (by norm_num)
  have h1832 : segsOk 20000000 7328100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1832 h1833 (by norm_num)
  have h1831 : segsOk 20000000 7324100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1831 h1832 (by norm_num)
  have h1830 : segsOk 20000000 7320100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1830 h1831 (by norm_num)
  have h1829 : segsOk 20000000 7316100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1829 h1830 (by norm_num)
  have h1828 : segsOk 20000000 7312100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1828 h1829 (by norm_num)
  have h1827 : segsOk 20000000 7308100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1827 h1828 (by norm_num)
  have h1826 : segsOk 20000000 7304100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1826 h1827 (by norm_num)
  have h1825 : segsOk 20000000 7300100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1825 h1826 (by norm_num)
  have h1824 : segsOk 20000000 7296100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1824 h1825 (by norm_num)
  have h1823 : segsOk 20000000 7292100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1823 h1824 (by norm_num)
  have h1822 : segsOk 20000000 7288100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1822 h1823 (by norm_num)
  have h1821 : segsOk 20000000 7284100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1821 h1822 (by norm_num)
  have h1820 : segsOk 20000000 7280100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1820 h1821 (by norm_num)
  have h1819 : segsOk 20000000 7276100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1819 h1820 (by norm_num)
  have h1818 : segsOk 20000000 7272100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1818 h1819 (by norm_num)
  have h1817 : segsOk 20000000 7268100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1817 h1818 (by norm_num)
  have h1816 : segsOk 20000000 7264100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1816 h1817 (by norm_num)
  have h1815 : segsOk 20000000 7260100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1815 h1816 (by norm_num)
  have h1814 : segsOk 20000000 7256100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1814 h1815 (by norm_num)
  have h1813 : segsOk 20000000 7252100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1813 h1814 (by norm_num)
  have h1812 : segsOk 20000000 7248100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1812 h1813 (by norm_num)
  have h1811 : segsOk 20000000 7244100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1811 h1812 (by norm_num)
  have h1810 : segsOk 20000000 7240100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1810 h1811 (by norm_num)
  have h1809 : segsOk 20000000 7236100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1809 h1810 (by norm_num)
  have h1808 : segsOk 20000000 7232100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1808 h1809 (by norm_num)
  have h1807 : segsOk 20000000 7228100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1807 h1808 (by norm_num)
  have h1806 : segsOk 20000000 7224100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1806 h1807 (by norm_num)
  have h1805 : segsOk 20000000 7220100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1805 h1806 (by norm_num)
  have h1804 : segsOk 20000000 7216100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1804 h1805 (by norm_num)
  have h1803 : segsOk 20000000 7212100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1803 h1804 (by norm_num)
  have h1802 : segsOk 20000000 7208100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1802 h1803 (by norm_num)
  have h1801 : segsOk 20000000 7204100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1801 h1802 (by norm_num)
  have h1800 : segsOk 20000000 7200100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1800 h1801 (by norm_num)
  exact h1800
end Grosswald.Direct
