import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B2250
import Grosswald.Direct.Run.B2251
import Grosswald.Direct.Run.B2252
import Grosswald.Direct.Run.B2253
import Grosswald.Direct.Run.B2254
import Grosswald.Direct.Run.B2255
import Grosswald.Direct.Run.B2256
import Grosswald.Direct.Run.B2257
import Grosswald.Direct.Run.B2258
import Grosswald.Direct.Run.B2259
import Grosswald.Direct.Run.B2260
import Grosswald.Direct.Run.B2261
import Grosswald.Direct.Run.B2262
import Grosswald.Direct.Run.B2263
import Grosswald.Direct.Run.B2264
import Grosswald.Direct.Run.B2265
import Grosswald.Direct.Run.B2266
import Grosswald.Direct.Run.B2267
import Grosswald.Direct.Run.B2268
import Grosswald.Direct.Run.B2269
import Grosswald.Direct.Run.B2270
import Grosswald.Direct.Run.B2271
import Grosswald.Direct.Run.B2272
import Grosswald.Direct.Run.B2273
import Grosswald.Direct.Run.B2274
import Grosswald.Direct.Run.B2275
import Grosswald.Direct.Run.B2276
import Grosswald.Direct.Run.B2277
import Grosswald.Direct.Run.B2278
import Grosswald.Direct.Run.B2279
import Grosswald.Direct.Run.B2280
import Grosswald.Direct.Run.B2281
import Grosswald.Direct.Run.B2282
import Grosswald.Direct.Run.B2283
import Grosswald.Direct.Run.B2284
import Grosswald.Direct.Run.B2285
import Grosswald.Direct.Run.B2286
import Grosswald.Direct.Run.B2287
import Grosswald.Direct.Run.B2288
import Grosswald.Direct.Run.B2289
import Grosswald.Direct.Run.B2290
import Grosswald.Direct.Run.B2291
import Grosswald.Direct.Run.B2292
import Grosswald.Direct.Run.B2293
import Grosswald.Direct.Run.B2294
import Grosswald.Direct.Run.B2295
import Grosswald.Direct.Run.B2296
import Grosswald.Direct.Run.B2297
import Grosswald.Direct.Run.B2298
import Grosswald.Direct.Run.B2299

namespace Grosswald.Direct
open GrosswaldCompute
theorem g45 : segsOk 20000000 9000100000411 5000 = true := by
  have h2299 : segsOk 20000000 9196100000411 100 = true := Run.b2299
  have h2298 : segsOk 20000000 9192100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b2298 h2299 (by norm_num)
  have h2297 : segsOk 20000000 9188100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b2297 h2298 (by norm_num)
  have h2296 : segsOk 20000000 9184100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b2296 h2297 (by norm_num)
  have h2295 : segsOk 20000000 9180100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b2295 h2296 (by norm_num)
  have h2294 : segsOk 20000000 9176100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b2294 h2295 (by norm_num)
  have h2293 : segsOk 20000000 9172100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b2293 h2294 (by norm_num)
  have h2292 : segsOk 20000000 9168100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b2292 h2293 (by norm_num)
  have h2291 : segsOk 20000000 9164100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b2291 h2292 (by norm_num)
  have h2290 : segsOk 20000000 9160100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b2290 h2291 (by norm_num)
  have h2289 : segsOk 20000000 9156100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b2289 h2290 (by norm_num)
  have h2288 : segsOk 20000000 9152100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b2288 h2289 (by norm_num)
  have h2287 : segsOk 20000000 9148100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b2287 h2288 (by norm_num)
  have h2286 : segsOk 20000000 9144100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b2286 h2287 (by norm_num)
  have h2285 : segsOk 20000000 9140100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b2285 h2286 (by norm_num)
  have h2284 : segsOk 20000000 9136100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b2284 h2285 (by norm_num)
  have h2283 : segsOk 20000000 9132100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b2283 h2284 (by norm_num)
  have h2282 : segsOk 20000000 9128100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b2282 h2283 (by norm_num)
  have h2281 : segsOk 20000000 9124100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b2281 h2282 (by norm_num)
  have h2280 : segsOk 20000000 9120100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b2280 h2281 (by norm_num)
  have h2279 : segsOk 20000000 9116100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b2279 h2280 (by norm_num)
  have h2278 : segsOk 20000000 9112100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b2278 h2279 (by norm_num)
  have h2277 : segsOk 20000000 9108100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b2277 h2278 (by norm_num)
  have h2276 : segsOk 20000000 9104100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b2276 h2277 (by norm_num)
  have h2275 : segsOk 20000000 9100100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b2275 h2276 (by norm_num)
  have h2274 : segsOk 20000000 9096100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b2274 h2275 (by norm_num)
  have h2273 : segsOk 20000000 9092100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b2273 h2274 (by norm_num)
  have h2272 : segsOk 20000000 9088100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b2272 h2273 (by norm_num)
  have h2271 : segsOk 20000000 9084100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b2271 h2272 (by norm_num)
  have h2270 : segsOk 20000000 9080100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b2270 h2271 (by norm_num)
  have h2269 : segsOk 20000000 9076100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b2269 h2270 (by norm_num)
  have h2268 : segsOk 20000000 9072100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b2268 h2269 (by norm_num)
  have h2267 : segsOk 20000000 9068100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b2267 h2268 (by norm_num)
  have h2266 : segsOk 20000000 9064100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b2266 h2267 (by norm_num)
  have h2265 : segsOk 20000000 9060100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b2265 h2266 (by norm_num)
  have h2264 : segsOk 20000000 9056100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b2264 h2265 (by norm_num)
  have h2263 : segsOk 20000000 9052100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b2263 h2264 (by norm_num)
  have h2262 : segsOk 20000000 9048100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b2262 h2263 (by norm_num)
  have h2261 : segsOk 20000000 9044100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b2261 h2262 (by norm_num)
  have h2260 : segsOk 20000000 9040100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b2260 h2261 (by norm_num)
  have h2259 : segsOk 20000000 9036100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b2259 h2260 (by norm_num)
  have h2258 : segsOk 20000000 9032100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b2258 h2259 (by norm_num)
  have h2257 : segsOk 20000000 9028100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b2257 h2258 (by norm_num)
  have h2256 : segsOk 20000000 9024100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b2256 h2257 (by norm_num)
  have h2255 : segsOk 20000000 9020100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b2255 h2256 (by norm_num)
  have h2254 : segsOk 20000000 9016100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b2254 h2255 (by norm_num)
  have h2253 : segsOk 20000000 9012100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b2253 h2254 (by norm_num)
  have h2252 : segsOk 20000000 9008100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b2252 h2253 (by norm_num)
  have h2251 : segsOk 20000000 9004100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b2251 h2252 (by norm_num)
  have h2250 : segsOk 20000000 9000100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b2250 h2251 (by norm_num)
  exact h2250
end Grosswald.Direct
