import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B1950
import Grosswald.Direct.Run.B1951
import Grosswald.Direct.Run.B1952
import Grosswald.Direct.Run.B1953
import Grosswald.Direct.Run.B1954
import Grosswald.Direct.Run.B1955
import Grosswald.Direct.Run.B1956
import Grosswald.Direct.Run.B1957
import Grosswald.Direct.Run.B1958
import Grosswald.Direct.Run.B1959
import Grosswald.Direct.Run.B1960
import Grosswald.Direct.Run.B1961
import Grosswald.Direct.Run.B1962
import Grosswald.Direct.Run.B1963
import Grosswald.Direct.Run.B1964
import Grosswald.Direct.Run.B1965
import Grosswald.Direct.Run.B1966
import Grosswald.Direct.Run.B1967
import Grosswald.Direct.Run.B1968
import Grosswald.Direct.Run.B1969
import Grosswald.Direct.Run.B1970
import Grosswald.Direct.Run.B1971
import Grosswald.Direct.Run.B1972
import Grosswald.Direct.Run.B1973
import Grosswald.Direct.Run.B1974
import Grosswald.Direct.Run.B1975
import Grosswald.Direct.Run.B1976
import Grosswald.Direct.Run.B1977
import Grosswald.Direct.Run.B1978
import Grosswald.Direct.Run.B1979
import Grosswald.Direct.Run.B1980
import Grosswald.Direct.Run.B1981
import Grosswald.Direct.Run.B1982
import Grosswald.Direct.Run.B1983
import Grosswald.Direct.Run.B1984
import Grosswald.Direct.Run.B1985
import Grosswald.Direct.Run.B1986
import Grosswald.Direct.Run.B1987
import Grosswald.Direct.Run.B1988
import Grosswald.Direct.Run.B1989
import Grosswald.Direct.Run.B1990
import Grosswald.Direct.Run.B1991
import Grosswald.Direct.Run.B1992
import Grosswald.Direct.Run.B1993
import Grosswald.Direct.Run.B1994
import Grosswald.Direct.Run.B1995
import Grosswald.Direct.Run.B1996
import Grosswald.Direct.Run.B1997
import Grosswald.Direct.Run.B1998
import Grosswald.Direct.Run.B1999

namespace Grosswald.Direct
open GrosswaldCompute
theorem g39 : segsOk 20000000 7800100000411 5000 = true := by
  have h1999 : segsOk 20000000 7996100000411 100 = true := Run.b1999
  have h1998 : segsOk 20000000 7992100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b1998 h1999 (by norm_num)
  have h1997 : segsOk 20000000 7988100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b1997 h1998 (by norm_num)
  have h1996 : segsOk 20000000 7984100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b1996 h1997 (by norm_num)
  have h1995 : segsOk 20000000 7980100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b1995 h1996 (by norm_num)
  have h1994 : segsOk 20000000 7976100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b1994 h1995 (by norm_num)
  have h1993 : segsOk 20000000 7972100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b1993 h1994 (by norm_num)
  have h1992 : segsOk 20000000 7968100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b1992 h1993 (by norm_num)
  have h1991 : segsOk 20000000 7964100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b1991 h1992 (by norm_num)
  have h1990 : segsOk 20000000 7960100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b1990 h1991 (by norm_num)
  have h1989 : segsOk 20000000 7956100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b1989 h1990 (by norm_num)
  have h1988 : segsOk 20000000 7952100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b1988 h1989 (by norm_num)
  have h1987 : segsOk 20000000 7948100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b1987 h1988 (by norm_num)
  have h1986 : segsOk 20000000 7944100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b1986 h1987 (by norm_num)
  have h1985 : segsOk 20000000 7940100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b1985 h1986 (by norm_num)
  have h1984 : segsOk 20000000 7936100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b1984 h1985 (by norm_num)
  have h1983 : segsOk 20000000 7932100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b1983 h1984 (by norm_num)
  have h1982 : segsOk 20000000 7928100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b1982 h1983 (by norm_num)
  have h1981 : segsOk 20000000 7924100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b1981 h1982 (by norm_num)
  have h1980 : segsOk 20000000 7920100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b1980 h1981 (by norm_num)
  have h1979 : segsOk 20000000 7916100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b1979 h1980 (by norm_num)
  have h1978 : segsOk 20000000 7912100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b1978 h1979 (by norm_num)
  have h1977 : segsOk 20000000 7908100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b1977 h1978 (by norm_num)
  have h1976 : segsOk 20000000 7904100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b1976 h1977 (by norm_num)
  have h1975 : segsOk 20000000 7900100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b1975 h1976 (by norm_num)
  have h1974 : segsOk 20000000 7896100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b1974 h1975 (by norm_num)
  have h1973 : segsOk 20000000 7892100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b1973 h1974 (by norm_num)
  have h1972 : segsOk 20000000 7888100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b1972 h1973 (by norm_num)
  have h1971 : segsOk 20000000 7884100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b1971 h1972 (by norm_num)
  have h1970 : segsOk 20000000 7880100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b1970 h1971 (by norm_num)
  have h1969 : segsOk 20000000 7876100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b1969 h1970 (by norm_num)
  have h1968 : segsOk 20000000 7872100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b1968 h1969 (by norm_num)
  have h1967 : segsOk 20000000 7868100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b1967 h1968 (by norm_num)
  have h1966 : segsOk 20000000 7864100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b1966 h1967 (by norm_num)
  have h1965 : segsOk 20000000 7860100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b1965 h1966 (by norm_num)
  have h1964 : segsOk 20000000 7856100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b1964 h1965 (by norm_num)
  have h1963 : segsOk 20000000 7852100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b1963 h1964 (by norm_num)
  have h1962 : segsOk 20000000 7848100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b1962 h1963 (by norm_num)
  have h1961 : segsOk 20000000 7844100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b1961 h1962 (by norm_num)
  have h1960 : segsOk 20000000 7840100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b1960 h1961 (by norm_num)
  have h1959 : segsOk 20000000 7836100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b1959 h1960 (by norm_num)
  have h1958 : segsOk 20000000 7832100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b1958 h1959 (by norm_num)
  have h1957 : segsOk 20000000 7828100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b1957 h1958 (by norm_num)
  have h1956 : segsOk 20000000 7824100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b1956 h1957 (by norm_num)
  have h1955 : segsOk 20000000 7820100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b1955 h1956 (by norm_num)
  have h1954 : segsOk 20000000 7816100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b1954 h1955 (by norm_num)
  have h1953 : segsOk 20000000 7812100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b1953 h1954 (by norm_num)
  have h1952 : segsOk 20000000 7808100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b1952 h1953 (by norm_num)
  have h1951 : segsOk 20000000 7804100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b1951 h1952 (by norm_num)
  have h1950 : segsOk 20000000 7800100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b1950 h1951 (by norm_num)
  exact h1950
end Grosswald.Direct
