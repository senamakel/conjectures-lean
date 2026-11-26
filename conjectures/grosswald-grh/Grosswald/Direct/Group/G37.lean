import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1850
import Grosswald.Direct.Run.B1851
import Grosswald.Direct.Run.B1852
import Grosswald.Direct.Run.B1853
import Grosswald.Direct.Run.B1854
import Grosswald.Direct.Run.B1855
import Grosswald.Direct.Run.B1856
import Grosswald.Direct.Run.B1857
import Grosswald.Direct.Run.B1858
import Grosswald.Direct.Run.B1859
import Grosswald.Direct.Run.B1860
import Grosswald.Direct.Run.B1861
import Grosswald.Direct.Run.B1862
import Grosswald.Direct.Run.B1863
import Grosswald.Direct.Run.B1864
import Grosswald.Direct.Run.B1865
import Grosswald.Direct.Run.B1866
import Grosswald.Direct.Run.B1867
import Grosswald.Direct.Run.B1868
import Grosswald.Direct.Run.B1869
import Grosswald.Direct.Run.B1870
import Grosswald.Direct.Run.B1871
import Grosswald.Direct.Run.B1872
import Grosswald.Direct.Run.B1873
import Grosswald.Direct.Run.B1874
import Grosswald.Direct.Run.B1875
import Grosswald.Direct.Run.B1876
import Grosswald.Direct.Run.B1877
import Grosswald.Direct.Run.B1878
import Grosswald.Direct.Run.B1879
import Grosswald.Direct.Run.B1880
import Grosswald.Direct.Run.B1881
import Grosswald.Direct.Run.B1882
import Grosswald.Direct.Run.B1883
import Grosswald.Direct.Run.B1884
import Grosswald.Direct.Run.B1885
import Grosswald.Direct.Run.B1886
import Grosswald.Direct.Run.B1887
import Grosswald.Direct.Run.B1888
import Grosswald.Direct.Run.B1889
import Grosswald.Direct.Run.B1890
import Grosswald.Direct.Run.B1891
import Grosswald.Direct.Run.B1892
import Grosswald.Direct.Run.B1893
import Grosswald.Direct.Run.B1894
import Grosswald.Direct.Run.B1895
import Grosswald.Direct.Run.B1896
import Grosswald.Direct.Run.B1897
import Grosswald.Direct.Run.B1898
import Grosswald.Direct.Run.B1899

namespace Grosswald.Direct
open GrosswaldCompute
theorem g37 : segsOk 20000000 7400100000411 5000 = true := by
  have h1899 : segsOk 20000000 7596100000411 100 = true := Run.b1899
  have h1898 : segsOk 20000000 7592100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1898 h1899 (by norm_num)
  have h1897 : segsOk 20000000 7588100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1897 h1898 (by norm_num)
  have h1896 : segsOk 20000000 7584100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1896 h1897 (by norm_num)
  have h1895 : segsOk 20000000 7580100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1895 h1896 (by norm_num)
  have h1894 : segsOk 20000000 7576100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1894 h1895 (by norm_num)
  have h1893 : segsOk 20000000 7572100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1893 h1894 (by norm_num)
  have h1892 : segsOk 20000000 7568100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1892 h1893 (by norm_num)
  have h1891 : segsOk 20000000 7564100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1891 h1892 (by norm_num)
  have h1890 : segsOk 20000000 7560100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1890 h1891 (by norm_num)
  have h1889 : segsOk 20000000 7556100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1889 h1890 (by norm_num)
  have h1888 : segsOk 20000000 7552100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1888 h1889 (by norm_num)
  have h1887 : segsOk 20000000 7548100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1887 h1888 (by norm_num)
  have h1886 : segsOk 20000000 7544100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1886 h1887 (by norm_num)
  have h1885 : segsOk 20000000 7540100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1885 h1886 (by norm_num)
  have h1884 : segsOk 20000000 7536100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1884 h1885 (by norm_num)
  have h1883 : segsOk 20000000 7532100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1883 h1884 (by norm_num)
  have h1882 : segsOk 20000000 7528100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1882 h1883 (by norm_num)
  have h1881 : segsOk 20000000 7524100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1881 h1882 (by norm_num)
  have h1880 : segsOk 20000000 7520100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1880 h1881 (by norm_num)
  have h1879 : segsOk 20000000 7516100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1879 h1880 (by norm_num)
  have h1878 : segsOk 20000000 7512100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1878 h1879 (by norm_num)
  have h1877 : segsOk 20000000 7508100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1877 h1878 (by norm_num)
  have h1876 : segsOk 20000000 7504100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1876 h1877 (by norm_num)
  have h1875 : segsOk 20000000 7500100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1875 h1876 (by norm_num)
  have h1874 : segsOk 20000000 7496100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1874 h1875 (by norm_num)
  have h1873 : segsOk 20000000 7492100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1873 h1874 (by norm_num)
  have h1872 : segsOk 20000000 7488100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1872 h1873 (by norm_num)
  have h1871 : segsOk 20000000 7484100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1871 h1872 (by norm_num)
  have h1870 : segsOk 20000000 7480100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1870 h1871 (by norm_num)
  have h1869 : segsOk 20000000 7476100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1869 h1870 (by norm_num)
  have h1868 : segsOk 20000000 7472100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1868 h1869 (by norm_num)
  have h1867 : segsOk 20000000 7468100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1867 h1868 (by norm_num)
  have h1866 : segsOk 20000000 7464100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1866 h1867 (by norm_num)
  have h1865 : segsOk 20000000 7460100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1865 h1866 (by norm_num)
  have h1864 : segsOk 20000000 7456100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1864 h1865 (by norm_num)
  have h1863 : segsOk 20000000 7452100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1863 h1864 (by norm_num)
  have h1862 : segsOk 20000000 7448100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1862 h1863 (by norm_num)
  have h1861 : segsOk 20000000 7444100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1861 h1862 (by norm_num)
  have h1860 : segsOk 20000000 7440100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1860 h1861 (by norm_num)
  have h1859 : segsOk 20000000 7436100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1859 h1860 (by norm_num)
  have h1858 : segsOk 20000000 7432100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1858 h1859 (by norm_num)
  have h1857 : segsOk 20000000 7428100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1857 h1858 (by norm_num)
  have h1856 : segsOk 20000000 7424100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1856 h1857 (by norm_num)
  have h1855 : segsOk 20000000 7420100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1855 h1856 (by norm_num)
  have h1854 : segsOk 20000000 7416100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1854 h1855 (by norm_num)
  have h1853 : segsOk 20000000 7412100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1853 h1854 (by norm_num)
  have h1852 : segsOk 20000000 7408100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1852 h1853 (by norm_num)
  have h1851 : segsOk 20000000 7404100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1851 h1852 (by norm_num)
  have h1850 : segsOk 20000000 7400100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1850 h1851 (by norm_num)
  exact h1850
end Grosswald.Direct
