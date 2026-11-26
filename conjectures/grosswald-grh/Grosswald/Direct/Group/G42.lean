import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B2100
import Grosswald.Direct.Run.B2101
import Grosswald.Direct.Run.B2102
import Grosswald.Direct.Run.B2103
import Grosswald.Direct.Run.B2104
import Grosswald.Direct.Run.B2105
import Grosswald.Direct.Run.B2106
import Grosswald.Direct.Run.B2107
import Grosswald.Direct.Run.B2108
import Grosswald.Direct.Run.B2109
import Grosswald.Direct.Run.B2110
import Grosswald.Direct.Run.B2111
import Grosswald.Direct.Run.B2112
import Grosswald.Direct.Run.B2113
import Grosswald.Direct.Run.B2114
import Grosswald.Direct.Run.B2115
import Grosswald.Direct.Run.B2116
import Grosswald.Direct.Run.B2117
import Grosswald.Direct.Run.B2118
import Grosswald.Direct.Run.B2119
import Grosswald.Direct.Run.B2120
import Grosswald.Direct.Run.B2121
import Grosswald.Direct.Run.B2122
import Grosswald.Direct.Run.B2123
import Grosswald.Direct.Run.B2124
import Grosswald.Direct.Run.B2125
import Grosswald.Direct.Run.B2126
import Grosswald.Direct.Run.B2127
import Grosswald.Direct.Run.B2128
import Grosswald.Direct.Run.B2129
import Grosswald.Direct.Run.B2130
import Grosswald.Direct.Run.B2131
import Grosswald.Direct.Run.B2132
import Grosswald.Direct.Run.B2133
import Grosswald.Direct.Run.B2134
import Grosswald.Direct.Run.B2135
import Grosswald.Direct.Run.B2136
import Grosswald.Direct.Run.B2137
import Grosswald.Direct.Run.B2138
import Grosswald.Direct.Run.B2139
import Grosswald.Direct.Run.B2140
import Grosswald.Direct.Run.B2141
import Grosswald.Direct.Run.B2142
import Grosswald.Direct.Run.B2143
import Grosswald.Direct.Run.B2144
import Grosswald.Direct.Run.B2145
import Grosswald.Direct.Run.B2146
import Grosswald.Direct.Run.B2147
import Grosswald.Direct.Run.B2148
import Grosswald.Direct.Run.B2149

namespace Grosswald.Direct
open GrosswaldCompute
theorem g42 : segsOk 20000000 8400100000411 5000 = true := by
  have h2149 : segsOk 20000000 8596100000411 100 = true := Run.b2149
  have h2148 : segsOk 20000000 8592100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b2148 h2149 (by norm_num)
  have h2147 : segsOk 20000000 8588100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b2147 h2148 (by norm_num)
  have h2146 : segsOk 20000000 8584100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b2146 h2147 (by norm_num)
  have h2145 : segsOk 20000000 8580100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b2145 h2146 (by norm_num)
  have h2144 : segsOk 20000000 8576100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b2144 h2145 (by norm_num)
  have h2143 : segsOk 20000000 8572100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b2143 h2144 (by norm_num)
  have h2142 : segsOk 20000000 8568100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b2142 h2143 (by norm_num)
  have h2141 : segsOk 20000000 8564100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b2141 h2142 (by norm_num)
  have h2140 : segsOk 20000000 8560100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b2140 h2141 (by norm_num)
  have h2139 : segsOk 20000000 8556100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b2139 h2140 (by norm_num)
  have h2138 : segsOk 20000000 8552100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b2138 h2139 (by norm_num)
  have h2137 : segsOk 20000000 8548100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b2137 h2138 (by norm_num)
  have h2136 : segsOk 20000000 8544100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b2136 h2137 (by norm_num)
  have h2135 : segsOk 20000000 8540100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b2135 h2136 (by norm_num)
  have h2134 : segsOk 20000000 8536100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b2134 h2135 (by norm_num)
  have h2133 : segsOk 20000000 8532100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b2133 h2134 (by norm_num)
  have h2132 : segsOk 20000000 8528100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b2132 h2133 (by norm_num)
  have h2131 : segsOk 20000000 8524100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b2131 h2132 (by norm_num)
  have h2130 : segsOk 20000000 8520100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b2130 h2131 (by norm_num)
  have h2129 : segsOk 20000000 8516100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b2129 h2130 (by norm_num)
  have h2128 : segsOk 20000000 8512100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b2128 h2129 (by norm_num)
  have h2127 : segsOk 20000000 8508100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b2127 h2128 (by norm_num)
  have h2126 : segsOk 20000000 8504100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b2126 h2127 (by norm_num)
  have h2125 : segsOk 20000000 8500100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b2125 h2126 (by norm_num)
  have h2124 : segsOk 20000000 8496100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b2124 h2125 (by norm_num)
  have h2123 : segsOk 20000000 8492100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b2123 h2124 (by norm_num)
  have h2122 : segsOk 20000000 8488100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b2122 h2123 (by norm_num)
  have h2121 : segsOk 20000000 8484100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b2121 h2122 (by norm_num)
  have h2120 : segsOk 20000000 8480100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b2120 h2121 (by norm_num)
  have h2119 : segsOk 20000000 8476100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b2119 h2120 (by norm_num)
  have h2118 : segsOk 20000000 8472100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b2118 h2119 (by norm_num)
  have h2117 : segsOk 20000000 8468100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b2117 h2118 (by norm_num)
  have h2116 : segsOk 20000000 8464100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b2116 h2117 (by norm_num)
  have h2115 : segsOk 20000000 8460100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b2115 h2116 (by norm_num)
  have h2114 : segsOk 20000000 8456100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b2114 h2115 (by norm_num)
  have h2113 : segsOk 20000000 8452100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b2113 h2114 (by norm_num)
  have h2112 : segsOk 20000000 8448100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b2112 h2113 (by norm_num)
  have h2111 : segsOk 20000000 8444100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b2111 h2112 (by norm_num)
  have h2110 : segsOk 20000000 8440100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b2110 h2111 (by norm_num)
  have h2109 : segsOk 20000000 8436100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b2109 h2110 (by norm_num)
  have h2108 : segsOk 20000000 8432100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b2108 h2109 (by norm_num)
  have h2107 : segsOk 20000000 8428100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b2107 h2108 (by norm_num)
  have h2106 : segsOk 20000000 8424100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b2106 h2107 (by norm_num)
  have h2105 : segsOk 20000000 8420100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b2105 h2106 (by norm_num)
  have h2104 : segsOk 20000000 8416100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b2104 h2105 (by norm_num)
  have h2103 : segsOk 20000000 8412100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b2103 h2104 (by norm_num)
  have h2102 : segsOk 20000000 8408100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b2102 h2103 (by norm_num)
  have h2101 : segsOk 20000000 8404100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b2101 h2102 (by norm_num)
  have h2100 : segsOk 20000000 8400100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b2100 h2101 (by norm_num)
  exact h2100
end Grosswald.Direct
