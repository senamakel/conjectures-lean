import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B2050
import Grosswald.Direct.Run.B2051
import Grosswald.Direct.Run.B2052
import Grosswald.Direct.Run.B2053
import Grosswald.Direct.Run.B2054
import Grosswald.Direct.Run.B2055
import Grosswald.Direct.Run.B2056
import Grosswald.Direct.Run.B2057
import Grosswald.Direct.Run.B2058
import Grosswald.Direct.Run.B2059
import Grosswald.Direct.Run.B2060
import Grosswald.Direct.Run.B2061
import Grosswald.Direct.Run.B2062
import Grosswald.Direct.Run.B2063
import Grosswald.Direct.Run.B2064
import Grosswald.Direct.Run.B2065
import Grosswald.Direct.Run.B2066
import Grosswald.Direct.Run.B2067
import Grosswald.Direct.Run.B2068
import Grosswald.Direct.Run.B2069
import Grosswald.Direct.Run.B2070
import Grosswald.Direct.Run.B2071
import Grosswald.Direct.Run.B2072
import Grosswald.Direct.Run.B2073
import Grosswald.Direct.Run.B2074
import Grosswald.Direct.Run.B2075
import Grosswald.Direct.Run.B2076
import Grosswald.Direct.Run.B2077
import Grosswald.Direct.Run.B2078
import Grosswald.Direct.Run.B2079
import Grosswald.Direct.Run.B2080
import Grosswald.Direct.Run.B2081
import Grosswald.Direct.Run.B2082
import Grosswald.Direct.Run.B2083
import Grosswald.Direct.Run.B2084
import Grosswald.Direct.Run.B2085
import Grosswald.Direct.Run.B2086
import Grosswald.Direct.Run.B2087
import Grosswald.Direct.Run.B2088
import Grosswald.Direct.Run.B2089
import Grosswald.Direct.Run.B2090
import Grosswald.Direct.Run.B2091
import Grosswald.Direct.Run.B2092
import Grosswald.Direct.Run.B2093
import Grosswald.Direct.Run.B2094
import Grosswald.Direct.Run.B2095
import Grosswald.Direct.Run.B2096
import Grosswald.Direct.Run.B2097
import Grosswald.Direct.Run.B2098
import Grosswald.Direct.Run.B2099

namespace Grosswald.Direct
open GrosswaldCompute
theorem g41 : segsOk 20000000 8200100000411 5000 = true := by
  have h2099 : segsOk 20000000 8396100000411 100 = true := Run.b2099
  have h2098 : segsOk 20000000 8392100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b2098 h2099 (by norm_num)
  have h2097 : segsOk 20000000 8388100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b2097 h2098 (by norm_num)
  have h2096 : segsOk 20000000 8384100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b2096 h2097 (by norm_num)
  have h2095 : segsOk 20000000 8380100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b2095 h2096 (by norm_num)
  have h2094 : segsOk 20000000 8376100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b2094 h2095 (by norm_num)
  have h2093 : segsOk 20000000 8372100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b2093 h2094 (by norm_num)
  have h2092 : segsOk 20000000 8368100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b2092 h2093 (by norm_num)
  have h2091 : segsOk 20000000 8364100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b2091 h2092 (by norm_num)
  have h2090 : segsOk 20000000 8360100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b2090 h2091 (by norm_num)
  have h2089 : segsOk 20000000 8356100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b2089 h2090 (by norm_num)
  have h2088 : segsOk 20000000 8352100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b2088 h2089 (by norm_num)
  have h2087 : segsOk 20000000 8348100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b2087 h2088 (by norm_num)
  have h2086 : segsOk 20000000 8344100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b2086 h2087 (by norm_num)
  have h2085 : segsOk 20000000 8340100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b2085 h2086 (by norm_num)
  have h2084 : segsOk 20000000 8336100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b2084 h2085 (by norm_num)
  have h2083 : segsOk 20000000 8332100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b2083 h2084 (by norm_num)
  have h2082 : segsOk 20000000 8328100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b2082 h2083 (by norm_num)
  have h2081 : segsOk 20000000 8324100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b2081 h2082 (by norm_num)
  have h2080 : segsOk 20000000 8320100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b2080 h2081 (by norm_num)
  have h2079 : segsOk 20000000 8316100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b2079 h2080 (by norm_num)
  have h2078 : segsOk 20000000 8312100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b2078 h2079 (by norm_num)
  have h2077 : segsOk 20000000 8308100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b2077 h2078 (by norm_num)
  have h2076 : segsOk 20000000 8304100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b2076 h2077 (by norm_num)
  have h2075 : segsOk 20000000 8300100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b2075 h2076 (by norm_num)
  have h2074 : segsOk 20000000 8296100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b2074 h2075 (by norm_num)
  have h2073 : segsOk 20000000 8292100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b2073 h2074 (by norm_num)
  have h2072 : segsOk 20000000 8288100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b2072 h2073 (by norm_num)
  have h2071 : segsOk 20000000 8284100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b2071 h2072 (by norm_num)
  have h2070 : segsOk 20000000 8280100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b2070 h2071 (by norm_num)
  have h2069 : segsOk 20000000 8276100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b2069 h2070 (by norm_num)
  have h2068 : segsOk 20000000 8272100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b2068 h2069 (by norm_num)
  have h2067 : segsOk 20000000 8268100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b2067 h2068 (by norm_num)
  have h2066 : segsOk 20000000 8264100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b2066 h2067 (by norm_num)
  have h2065 : segsOk 20000000 8260100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b2065 h2066 (by norm_num)
  have h2064 : segsOk 20000000 8256100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b2064 h2065 (by norm_num)
  have h2063 : segsOk 20000000 8252100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b2063 h2064 (by norm_num)
  have h2062 : segsOk 20000000 8248100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b2062 h2063 (by norm_num)
  have h2061 : segsOk 20000000 8244100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b2061 h2062 (by norm_num)
  have h2060 : segsOk 20000000 8240100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b2060 h2061 (by norm_num)
  have h2059 : segsOk 20000000 8236100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b2059 h2060 (by norm_num)
  have h2058 : segsOk 20000000 8232100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b2058 h2059 (by norm_num)
  have h2057 : segsOk 20000000 8228100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b2057 h2058 (by norm_num)
  have h2056 : segsOk 20000000 8224100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b2056 h2057 (by norm_num)
  have h2055 : segsOk 20000000 8220100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b2055 h2056 (by norm_num)
  have h2054 : segsOk 20000000 8216100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b2054 h2055 (by norm_num)
  have h2053 : segsOk 20000000 8212100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b2053 h2054 (by norm_num)
  have h2052 : segsOk 20000000 8208100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b2052 h2053 (by norm_num)
  have h2051 : segsOk 20000000 8204100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b2051 h2052 (by norm_num)
  have h2050 : segsOk 20000000 8200100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b2050 h2051 (by norm_num)
  exact h2050
end Grosswald.Direct
