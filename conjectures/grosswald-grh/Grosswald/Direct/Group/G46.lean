import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B2300
import Grosswald.Direct.Run.B2301
import Grosswald.Direct.Run.B2302
import Grosswald.Direct.Run.B2303
import Grosswald.Direct.Run.B2304
import Grosswald.Direct.Run.B2305
import Grosswald.Direct.Run.B2306
import Grosswald.Direct.Run.B2307
import Grosswald.Direct.Run.B2308
import Grosswald.Direct.Run.B2309
import Grosswald.Direct.Run.B2310
import Grosswald.Direct.Run.B2311
import Grosswald.Direct.Run.B2312
import Grosswald.Direct.Run.B2313
import Grosswald.Direct.Run.B2314
import Grosswald.Direct.Run.B2315
import Grosswald.Direct.Run.B2316
import Grosswald.Direct.Run.B2317
import Grosswald.Direct.Run.B2318
import Grosswald.Direct.Run.B2319
import Grosswald.Direct.Run.B2320
import Grosswald.Direct.Run.B2321
import Grosswald.Direct.Run.B2322
import Grosswald.Direct.Run.B2323
import Grosswald.Direct.Run.B2324
import Grosswald.Direct.Run.B2325
import Grosswald.Direct.Run.B2326
import Grosswald.Direct.Run.B2327
import Grosswald.Direct.Run.B2328
import Grosswald.Direct.Run.B2329
import Grosswald.Direct.Run.B2330
import Grosswald.Direct.Run.B2331
import Grosswald.Direct.Run.B2332
import Grosswald.Direct.Run.B2333
import Grosswald.Direct.Run.B2334
import Grosswald.Direct.Run.B2335
import Grosswald.Direct.Run.B2336
import Grosswald.Direct.Run.B2337
import Grosswald.Direct.Run.B2338
import Grosswald.Direct.Run.B2339
import Grosswald.Direct.Run.B2340
import Grosswald.Direct.Run.B2341
import Grosswald.Direct.Run.B2342
import Grosswald.Direct.Run.B2343
import Grosswald.Direct.Run.B2344
import Grosswald.Direct.Run.B2345
import Grosswald.Direct.Run.B2346
import Grosswald.Direct.Run.B2347
import Grosswald.Direct.Run.B2348
import Grosswald.Direct.Run.B2349

namespace Grosswald.Direct
open GrosswaldCompute
theorem g46 : segsOk 20000000 9200100000411 5000 = true := by
  have h2349 : segsOk 20000000 9396100000411 100 = true := Run.b2349
  have h2348 : segsOk 20000000 9392100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b2348 h2349 (by norm_num)
  have h2347 : segsOk 20000000 9388100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b2347 h2348 (by norm_num)
  have h2346 : segsOk 20000000 9384100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b2346 h2347 (by norm_num)
  have h2345 : segsOk 20000000 9380100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b2345 h2346 (by norm_num)
  have h2344 : segsOk 20000000 9376100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b2344 h2345 (by norm_num)
  have h2343 : segsOk 20000000 9372100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b2343 h2344 (by norm_num)
  have h2342 : segsOk 20000000 9368100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b2342 h2343 (by norm_num)
  have h2341 : segsOk 20000000 9364100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b2341 h2342 (by norm_num)
  have h2340 : segsOk 20000000 9360100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b2340 h2341 (by norm_num)
  have h2339 : segsOk 20000000 9356100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b2339 h2340 (by norm_num)
  have h2338 : segsOk 20000000 9352100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b2338 h2339 (by norm_num)
  have h2337 : segsOk 20000000 9348100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b2337 h2338 (by norm_num)
  have h2336 : segsOk 20000000 9344100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b2336 h2337 (by norm_num)
  have h2335 : segsOk 20000000 9340100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b2335 h2336 (by norm_num)
  have h2334 : segsOk 20000000 9336100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b2334 h2335 (by norm_num)
  have h2333 : segsOk 20000000 9332100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b2333 h2334 (by norm_num)
  have h2332 : segsOk 20000000 9328100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b2332 h2333 (by norm_num)
  have h2331 : segsOk 20000000 9324100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b2331 h2332 (by norm_num)
  have h2330 : segsOk 20000000 9320100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b2330 h2331 (by norm_num)
  have h2329 : segsOk 20000000 9316100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b2329 h2330 (by norm_num)
  have h2328 : segsOk 20000000 9312100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b2328 h2329 (by norm_num)
  have h2327 : segsOk 20000000 9308100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b2327 h2328 (by norm_num)
  have h2326 : segsOk 20000000 9304100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b2326 h2327 (by norm_num)
  have h2325 : segsOk 20000000 9300100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b2325 h2326 (by norm_num)
  have h2324 : segsOk 20000000 9296100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b2324 h2325 (by norm_num)
  have h2323 : segsOk 20000000 9292100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b2323 h2324 (by norm_num)
  have h2322 : segsOk 20000000 9288100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b2322 h2323 (by norm_num)
  have h2321 : segsOk 20000000 9284100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b2321 h2322 (by norm_num)
  have h2320 : segsOk 20000000 9280100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b2320 h2321 (by norm_num)
  have h2319 : segsOk 20000000 9276100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b2319 h2320 (by norm_num)
  have h2318 : segsOk 20000000 9272100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b2318 h2319 (by norm_num)
  have h2317 : segsOk 20000000 9268100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b2317 h2318 (by norm_num)
  have h2316 : segsOk 20000000 9264100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b2316 h2317 (by norm_num)
  have h2315 : segsOk 20000000 9260100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b2315 h2316 (by norm_num)
  have h2314 : segsOk 20000000 9256100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b2314 h2315 (by norm_num)
  have h2313 : segsOk 20000000 9252100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b2313 h2314 (by norm_num)
  have h2312 : segsOk 20000000 9248100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b2312 h2313 (by norm_num)
  have h2311 : segsOk 20000000 9244100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b2311 h2312 (by norm_num)
  have h2310 : segsOk 20000000 9240100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b2310 h2311 (by norm_num)
  have h2309 : segsOk 20000000 9236100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b2309 h2310 (by norm_num)
  have h2308 : segsOk 20000000 9232100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b2308 h2309 (by norm_num)
  have h2307 : segsOk 20000000 9228100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b2307 h2308 (by norm_num)
  have h2306 : segsOk 20000000 9224100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b2306 h2307 (by norm_num)
  have h2305 : segsOk 20000000 9220100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b2305 h2306 (by norm_num)
  have h2304 : segsOk 20000000 9216100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b2304 h2305 (by norm_num)
  have h2303 : segsOk 20000000 9212100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b2303 h2304 (by norm_num)
  have h2302 : segsOk 20000000 9208100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b2302 h2303 (by norm_num)
  have h2301 : segsOk 20000000 9204100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b2301 h2302 (by norm_num)
  have h2300 : segsOk 20000000 9200100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b2300 h2301 (by norm_num)
  exact h2300
end Grosswald.Direct
