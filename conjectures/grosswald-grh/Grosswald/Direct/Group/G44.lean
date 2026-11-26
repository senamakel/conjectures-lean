import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B2200
import Grosswald.Direct.Run.B2201
import Grosswald.Direct.Run.B2202
import Grosswald.Direct.Run.B2203
import Grosswald.Direct.Run.B2204
import Grosswald.Direct.Run.B2205
import Grosswald.Direct.Run.B2206
import Grosswald.Direct.Run.B2207
import Grosswald.Direct.Run.B2208
import Grosswald.Direct.Run.B2209
import Grosswald.Direct.Run.B2210
import Grosswald.Direct.Run.B2211
import Grosswald.Direct.Run.B2212
import Grosswald.Direct.Run.B2213
import Grosswald.Direct.Run.B2214
import Grosswald.Direct.Run.B2215
import Grosswald.Direct.Run.B2216
import Grosswald.Direct.Run.B2217
import Grosswald.Direct.Run.B2218
import Grosswald.Direct.Run.B2219
import Grosswald.Direct.Run.B2220
import Grosswald.Direct.Run.B2221
import Grosswald.Direct.Run.B2222
import Grosswald.Direct.Run.B2223
import Grosswald.Direct.Run.B2224
import Grosswald.Direct.Run.B2225
import Grosswald.Direct.Run.B2226
import Grosswald.Direct.Run.B2227
import Grosswald.Direct.Run.B2228
import Grosswald.Direct.Run.B2229
import Grosswald.Direct.Run.B2230
import Grosswald.Direct.Run.B2231
import Grosswald.Direct.Run.B2232
import Grosswald.Direct.Run.B2233
import Grosswald.Direct.Run.B2234
import Grosswald.Direct.Run.B2235
import Grosswald.Direct.Run.B2236
import Grosswald.Direct.Run.B2237
import Grosswald.Direct.Run.B2238
import Grosswald.Direct.Run.B2239
import Grosswald.Direct.Run.B2240
import Grosswald.Direct.Run.B2241
import Grosswald.Direct.Run.B2242
import Grosswald.Direct.Run.B2243
import Grosswald.Direct.Run.B2244
import Grosswald.Direct.Run.B2245
import Grosswald.Direct.Run.B2246
import Grosswald.Direct.Run.B2247
import Grosswald.Direct.Run.B2248
import Grosswald.Direct.Run.B2249

namespace Grosswald.Direct
open GrosswaldCompute
theorem g44 : segsOk 20000000 8800100000411 5000 = true := by
  have h2249 : segsOk 20000000 8996100000411 100 = true := Run.b2249
  have h2248 : segsOk 20000000 8992100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b2248 h2249 (by norm_num)
  have h2247 : segsOk 20000000 8988100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b2247 h2248 (by norm_num)
  have h2246 : segsOk 20000000 8984100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b2246 h2247 (by norm_num)
  have h2245 : segsOk 20000000 8980100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b2245 h2246 (by norm_num)
  have h2244 : segsOk 20000000 8976100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b2244 h2245 (by norm_num)
  have h2243 : segsOk 20000000 8972100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b2243 h2244 (by norm_num)
  have h2242 : segsOk 20000000 8968100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b2242 h2243 (by norm_num)
  have h2241 : segsOk 20000000 8964100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b2241 h2242 (by norm_num)
  have h2240 : segsOk 20000000 8960100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b2240 h2241 (by norm_num)
  have h2239 : segsOk 20000000 8956100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b2239 h2240 (by norm_num)
  have h2238 : segsOk 20000000 8952100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b2238 h2239 (by norm_num)
  have h2237 : segsOk 20000000 8948100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b2237 h2238 (by norm_num)
  have h2236 : segsOk 20000000 8944100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b2236 h2237 (by norm_num)
  have h2235 : segsOk 20000000 8940100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b2235 h2236 (by norm_num)
  have h2234 : segsOk 20000000 8936100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b2234 h2235 (by norm_num)
  have h2233 : segsOk 20000000 8932100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b2233 h2234 (by norm_num)
  have h2232 : segsOk 20000000 8928100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b2232 h2233 (by norm_num)
  have h2231 : segsOk 20000000 8924100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b2231 h2232 (by norm_num)
  have h2230 : segsOk 20000000 8920100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b2230 h2231 (by norm_num)
  have h2229 : segsOk 20000000 8916100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b2229 h2230 (by norm_num)
  have h2228 : segsOk 20000000 8912100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b2228 h2229 (by norm_num)
  have h2227 : segsOk 20000000 8908100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b2227 h2228 (by norm_num)
  have h2226 : segsOk 20000000 8904100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b2226 h2227 (by norm_num)
  have h2225 : segsOk 20000000 8900100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b2225 h2226 (by norm_num)
  have h2224 : segsOk 20000000 8896100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b2224 h2225 (by norm_num)
  have h2223 : segsOk 20000000 8892100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b2223 h2224 (by norm_num)
  have h2222 : segsOk 20000000 8888100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b2222 h2223 (by norm_num)
  have h2221 : segsOk 20000000 8884100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b2221 h2222 (by norm_num)
  have h2220 : segsOk 20000000 8880100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b2220 h2221 (by norm_num)
  have h2219 : segsOk 20000000 8876100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b2219 h2220 (by norm_num)
  have h2218 : segsOk 20000000 8872100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b2218 h2219 (by norm_num)
  have h2217 : segsOk 20000000 8868100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b2217 h2218 (by norm_num)
  have h2216 : segsOk 20000000 8864100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b2216 h2217 (by norm_num)
  have h2215 : segsOk 20000000 8860100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b2215 h2216 (by norm_num)
  have h2214 : segsOk 20000000 8856100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b2214 h2215 (by norm_num)
  have h2213 : segsOk 20000000 8852100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b2213 h2214 (by norm_num)
  have h2212 : segsOk 20000000 8848100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b2212 h2213 (by norm_num)
  have h2211 : segsOk 20000000 8844100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b2211 h2212 (by norm_num)
  have h2210 : segsOk 20000000 8840100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b2210 h2211 (by norm_num)
  have h2209 : segsOk 20000000 8836100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b2209 h2210 (by norm_num)
  have h2208 : segsOk 20000000 8832100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b2208 h2209 (by norm_num)
  have h2207 : segsOk 20000000 8828100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b2207 h2208 (by norm_num)
  have h2206 : segsOk 20000000 8824100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b2206 h2207 (by norm_num)
  have h2205 : segsOk 20000000 8820100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b2205 h2206 (by norm_num)
  have h2204 : segsOk 20000000 8816100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b2204 h2205 (by norm_num)
  have h2203 : segsOk 20000000 8812100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b2203 h2204 (by norm_num)
  have h2202 : segsOk 20000000 8808100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b2202 h2203 (by norm_num)
  have h2201 : segsOk 20000000 8804100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b2201 h2202 (by norm_num)
  have h2200 : segsOk 20000000 8800100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b2200 h2201 (by norm_num)
  exact h2200
end Grosswald.Direct
