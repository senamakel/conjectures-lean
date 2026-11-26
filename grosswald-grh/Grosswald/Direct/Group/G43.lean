import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B2150
import Grosswald.Direct.Run.B2151
import Grosswald.Direct.Run.B2152
import Grosswald.Direct.Run.B2153
import Grosswald.Direct.Run.B2154
import Grosswald.Direct.Run.B2155
import Grosswald.Direct.Run.B2156
import Grosswald.Direct.Run.B2157
import Grosswald.Direct.Run.B2158
import Grosswald.Direct.Run.B2159
import Grosswald.Direct.Run.B2160
import Grosswald.Direct.Run.B2161
import Grosswald.Direct.Run.B2162
import Grosswald.Direct.Run.B2163
import Grosswald.Direct.Run.B2164
import Grosswald.Direct.Run.B2165
import Grosswald.Direct.Run.B2166
import Grosswald.Direct.Run.B2167
import Grosswald.Direct.Run.B2168
import Grosswald.Direct.Run.B2169
import Grosswald.Direct.Run.B2170
import Grosswald.Direct.Run.B2171
import Grosswald.Direct.Run.B2172
import Grosswald.Direct.Run.B2173
import Grosswald.Direct.Run.B2174
import Grosswald.Direct.Run.B2175
import Grosswald.Direct.Run.B2176
import Grosswald.Direct.Run.B2177
import Grosswald.Direct.Run.B2178
import Grosswald.Direct.Run.B2179
import Grosswald.Direct.Run.B2180
import Grosswald.Direct.Run.B2181
import Grosswald.Direct.Run.B2182
import Grosswald.Direct.Run.B2183
import Grosswald.Direct.Run.B2184
import Grosswald.Direct.Run.B2185
import Grosswald.Direct.Run.B2186
import Grosswald.Direct.Run.B2187
import Grosswald.Direct.Run.B2188
import Grosswald.Direct.Run.B2189
import Grosswald.Direct.Run.B2190
import Grosswald.Direct.Run.B2191
import Grosswald.Direct.Run.B2192
import Grosswald.Direct.Run.B2193
import Grosswald.Direct.Run.B2194
import Grosswald.Direct.Run.B2195
import Grosswald.Direct.Run.B2196
import Grosswald.Direct.Run.B2197
import Grosswald.Direct.Run.B2198
import Grosswald.Direct.Run.B2199

namespace Grosswald.Direct
open GrosswaldCompute
theorem g43 : segsOk 20000000 8600100000411 5000 = true := by
  have h2199 : segsOk 20000000 8796100000411 100 = true := Run.b2199
  have h2198 : segsOk 20000000 8792100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b2198 h2199 (by norm_num)
  have h2197 : segsOk 20000000 8788100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b2197 h2198 (by norm_num)
  have h2196 : segsOk 20000000 8784100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b2196 h2197 (by norm_num)
  have h2195 : segsOk 20000000 8780100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b2195 h2196 (by norm_num)
  have h2194 : segsOk 20000000 8776100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b2194 h2195 (by norm_num)
  have h2193 : segsOk 20000000 8772100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b2193 h2194 (by norm_num)
  have h2192 : segsOk 20000000 8768100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b2192 h2193 (by norm_num)
  have h2191 : segsOk 20000000 8764100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b2191 h2192 (by norm_num)
  have h2190 : segsOk 20000000 8760100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b2190 h2191 (by norm_num)
  have h2189 : segsOk 20000000 8756100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b2189 h2190 (by norm_num)
  have h2188 : segsOk 20000000 8752100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b2188 h2189 (by norm_num)
  have h2187 : segsOk 20000000 8748100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b2187 h2188 (by norm_num)
  have h2186 : segsOk 20000000 8744100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b2186 h2187 (by norm_num)
  have h2185 : segsOk 20000000 8740100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b2185 h2186 (by norm_num)
  have h2184 : segsOk 20000000 8736100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b2184 h2185 (by norm_num)
  have h2183 : segsOk 20000000 8732100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b2183 h2184 (by norm_num)
  have h2182 : segsOk 20000000 8728100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b2182 h2183 (by norm_num)
  have h2181 : segsOk 20000000 8724100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b2181 h2182 (by norm_num)
  have h2180 : segsOk 20000000 8720100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b2180 h2181 (by norm_num)
  have h2179 : segsOk 20000000 8716100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b2179 h2180 (by norm_num)
  have h2178 : segsOk 20000000 8712100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b2178 h2179 (by norm_num)
  have h2177 : segsOk 20000000 8708100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b2177 h2178 (by norm_num)
  have h2176 : segsOk 20000000 8704100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b2176 h2177 (by norm_num)
  have h2175 : segsOk 20000000 8700100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b2175 h2176 (by norm_num)
  have h2174 : segsOk 20000000 8696100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b2174 h2175 (by norm_num)
  have h2173 : segsOk 20000000 8692100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b2173 h2174 (by norm_num)
  have h2172 : segsOk 20000000 8688100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b2172 h2173 (by norm_num)
  have h2171 : segsOk 20000000 8684100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b2171 h2172 (by norm_num)
  have h2170 : segsOk 20000000 8680100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b2170 h2171 (by norm_num)
  have h2169 : segsOk 20000000 8676100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b2169 h2170 (by norm_num)
  have h2168 : segsOk 20000000 8672100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b2168 h2169 (by norm_num)
  have h2167 : segsOk 20000000 8668100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b2167 h2168 (by norm_num)
  have h2166 : segsOk 20000000 8664100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b2166 h2167 (by norm_num)
  have h2165 : segsOk 20000000 8660100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b2165 h2166 (by norm_num)
  have h2164 : segsOk 20000000 8656100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b2164 h2165 (by norm_num)
  have h2163 : segsOk 20000000 8652100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b2163 h2164 (by norm_num)
  have h2162 : segsOk 20000000 8648100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b2162 h2163 (by norm_num)
  have h2161 : segsOk 20000000 8644100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b2161 h2162 (by norm_num)
  have h2160 : segsOk 20000000 8640100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b2160 h2161 (by norm_num)
  have h2159 : segsOk 20000000 8636100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b2159 h2160 (by norm_num)
  have h2158 : segsOk 20000000 8632100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b2158 h2159 (by norm_num)
  have h2157 : segsOk 20000000 8628100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b2157 h2158 (by norm_num)
  have h2156 : segsOk 20000000 8624100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b2156 h2157 (by norm_num)
  have h2155 : segsOk 20000000 8620100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b2155 h2156 (by norm_num)
  have h2154 : segsOk 20000000 8616100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b2154 h2155 (by norm_num)
  have h2153 : segsOk 20000000 8612100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b2153 h2154 (by norm_num)
  have h2152 : segsOk 20000000 8608100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b2152 h2153 (by norm_num)
  have h2151 : segsOk 20000000 8604100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b2151 h2152 (by norm_num)
  have h2150 : segsOk 20000000 8600100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b2150 h2151 (by norm_num)
  exact h2150
end Grosswald.Direct
