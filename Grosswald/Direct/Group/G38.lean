import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1900
import Grosswald.Direct.Run.B1901
import Grosswald.Direct.Run.B1902
import Grosswald.Direct.Run.B1903
import Grosswald.Direct.Run.B1904
import Grosswald.Direct.Run.B1905
import Grosswald.Direct.Run.B1906
import Grosswald.Direct.Run.B1907
import Grosswald.Direct.Run.B1908
import Grosswald.Direct.Run.B1909
import Grosswald.Direct.Run.B1910
import Grosswald.Direct.Run.B1911
import Grosswald.Direct.Run.B1912
import Grosswald.Direct.Run.B1913
import Grosswald.Direct.Run.B1914
import Grosswald.Direct.Run.B1915
import Grosswald.Direct.Run.B1916
import Grosswald.Direct.Run.B1917
import Grosswald.Direct.Run.B1918
import Grosswald.Direct.Run.B1919
import Grosswald.Direct.Run.B1920
import Grosswald.Direct.Run.B1921
import Grosswald.Direct.Run.B1922
import Grosswald.Direct.Run.B1923
import Grosswald.Direct.Run.B1924
import Grosswald.Direct.Run.B1925
import Grosswald.Direct.Run.B1926
import Grosswald.Direct.Run.B1927
import Grosswald.Direct.Run.B1928
import Grosswald.Direct.Run.B1929
import Grosswald.Direct.Run.B1930
import Grosswald.Direct.Run.B1931
import Grosswald.Direct.Run.B1932
import Grosswald.Direct.Run.B1933
import Grosswald.Direct.Run.B1934
import Grosswald.Direct.Run.B1935
import Grosswald.Direct.Run.B1936
import Grosswald.Direct.Run.B1937
import Grosswald.Direct.Run.B1938
import Grosswald.Direct.Run.B1939
import Grosswald.Direct.Run.B1940
import Grosswald.Direct.Run.B1941
import Grosswald.Direct.Run.B1942
import Grosswald.Direct.Run.B1943
import Grosswald.Direct.Run.B1944
import Grosswald.Direct.Run.B1945
import Grosswald.Direct.Run.B1946
import Grosswald.Direct.Run.B1947
import Grosswald.Direct.Run.B1948
import Grosswald.Direct.Run.B1949

namespace Grosswald.Direct
open GrosswaldCompute
theorem g38 : segsOk 20000000 7600100000411 5000 = true := by
  have h1949 : segsOk 20000000 7796100000411 100 = true := Run.b1949
  have h1948 : segsOk 20000000 7792100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1948 h1949 (by norm_num)
  have h1947 : segsOk 20000000 7788100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1947 h1948 (by norm_num)
  have h1946 : segsOk 20000000 7784100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1946 h1947 (by norm_num)
  have h1945 : segsOk 20000000 7780100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1945 h1946 (by norm_num)
  have h1944 : segsOk 20000000 7776100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1944 h1945 (by norm_num)
  have h1943 : segsOk 20000000 7772100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1943 h1944 (by norm_num)
  have h1942 : segsOk 20000000 7768100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1942 h1943 (by norm_num)
  have h1941 : segsOk 20000000 7764100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1941 h1942 (by norm_num)
  have h1940 : segsOk 20000000 7760100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1940 h1941 (by norm_num)
  have h1939 : segsOk 20000000 7756100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1939 h1940 (by norm_num)
  have h1938 : segsOk 20000000 7752100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1938 h1939 (by norm_num)
  have h1937 : segsOk 20000000 7748100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1937 h1938 (by norm_num)
  have h1936 : segsOk 20000000 7744100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1936 h1937 (by norm_num)
  have h1935 : segsOk 20000000 7740100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1935 h1936 (by norm_num)
  have h1934 : segsOk 20000000 7736100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1934 h1935 (by norm_num)
  have h1933 : segsOk 20000000 7732100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1933 h1934 (by norm_num)
  have h1932 : segsOk 20000000 7728100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1932 h1933 (by norm_num)
  have h1931 : segsOk 20000000 7724100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1931 h1932 (by norm_num)
  have h1930 : segsOk 20000000 7720100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1930 h1931 (by norm_num)
  have h1929 : segsOk 20000000 7716100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1929 h1930 (by norm_num)
  have h1928 : segsOk 20000000 7712100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1928 h1929 (by norm_num)
  have h1927 : segsOk 20000000 7708100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1927 h1928 (by norm_num)
  have h1926 : segsOk 20000000 7704100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1926 h1927 (by norm_num)
  have h1925 : segsOk 20000000 7700100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1925 h1926 (by norm_num)
  have h1924 : segsOk 20000000 7696100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1924 h1925 (by norm_num)
  have h1923 : segsOk 20000000 7692100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1923 h1924 (by norm_num)
  have h1922 : segsOk 20000000 7688100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1922 h1923 (by norm_num)
  have h1921 : segsOk 20000000 7684100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1921 h1922 (by norm_num)
  have h1920 : segsOk 20000000 7680100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1920 h1921 (by norm_num)
  have h1919 : segsOk 20000000 7676100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1919 h1920 (by norm_num)
  have h1918 : segsOk 20000000 7672100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1918 h1919 (by norm_num)
  have h1917 : segsOk 20000000 7668100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1917 h1918 (by norm_num)
  have h1916 : segsOk 20000000 7664100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1916 h1917 (by norm_num)
  have h1915 : segsOk 20000000 7660100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1915 h1916 (by norm_num)
  have h1914 : segsOk 20000000 7656100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1914 h1915 (by norm_num)
  have h1913 : segsOk 20000000 7652100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1913 h1914 (by norm_num)
  have h1912 : segsOk 20000000 7648100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1912 h1913 (by norm_num)
  have h1911 : segsOk 20000000 7644100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1911 h1912 (by norm_num)
  have h1910 : segsOk 20000000 7640100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1910 h1911 (by norm_num)
  have h1909 : segsOk 20000000 7636100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1909 h1910 (by norm_num)
  have h1908 : segsOk 20000000 7632100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1908 h1909 (by norm_num)
  have h1907 : segsOk 20000000 7628100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1907 h1908 (by norm_num)
  have h1906 : segsOk 20000000 7624100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1906 h1907 (by norm_num)
  have h1905 : segsOk 20000000 7620100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1905 h1906 (by norm_num)
  have h1904 : segsOk 20000000 7616100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1904 h1905 (by norm_num)
  have h1903 : segsOk 20000000 7612100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1903 h1904 (by norm_num)
  have h1902 : segsOk 20000000 7608100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1902 h1903 (by norm_num)
  have h1901 : segsOk 20000000 7604100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1901 h1902 (by norm_num)
  have h1900 : segsOk 20000000 7600100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1900 h1901 (by norm_num)
  exact h1900
end Grosswald.Direct
