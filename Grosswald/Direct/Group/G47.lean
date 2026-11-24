import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B2350
import Grosswald.Direct.Run.B2351
import Grosswald.Direct.Run.B2352
import Grosswald.Direct.Run.B2353
import Grosswald.Direct.Run.B2354
import Grosswald.Direct.Run.B2355
import Grosswald.Direct.Run.B2356
import Grosswald.Direct.Run.B2357
import Grosswald.Direct.Run.B2358
import Grosswald.Direct.Run.B2359
import Grosswald.Direct.Run.B2360
import Grosswald.Direct.Run.B2361
import Grosswald.Direct.Run.B2362
import Grosswald.Direct.Run.B2363
import Grosswald.Direct.Run.B2364
import Grosswald.Direct.Run.B2365
import Grosswald.Direct.Run.B2366
import Grosswald.Direct.Run.B2367
import Grosswald.Direct.Run.B2368
import Grosswald.Direct.Run.B2369
import Grosswald.Direct.Run.B2370
import Grosswald.Direct.Run.B2371
import Grosswald.Direct.Run.B2372
import Grosswald.Direct.Run.B2373
import Grosswald.Direct.Run.B2374
import Grosswald.Direct.Run.B2375
import Grosswald.Direct.Run.B2376
import Grosswald.Direct.Run.B2377
import Grosswald.Direct.Run.B2378
import Grosswald.Direct.Run.B2379
import Grosswald.Direct.Run.B2380
import Grosswald.Direct.Run.B2381
import Grosswald.Direct.Run.B2382
import Grosswald.Direct.Run.B2383
import Grosswald.Direct.Run.B2384
import Grosswald.Direct.Run.B2385
import Grosswald.Direct.Run.B2386
import Grosswald.Direct.Run.B2387
import Grosswald.Direct.Run.B2388
import Grosswald.Direct.Run.B2389
import Grosswald.Direct.Run.B2390
import Grosswald.Direct.Run.B2391
import Grosswald.Direct.Run.B2392
import Grosswald.Direct.Run.B2393
import Grosswald.Direct.Run.B2394
import Grosswald.Direct.Run.B2395
import Grosswald.Direct.Run.B2396
import Grosswald.Direct.Run.B2397
import Grosswald.Direct.Run.B2398
import Grosswald.Direct.Run.B2399

namespace Grosswald.Direct
open GrosswaldCompute
theorem g47 : segsOk 20000000 9400100000411 5000 = true := by
  have h2399 : segsOk 20000000 9596100000411 100 = true := Run.b2399
  have h2398 : segsOk 20000000 9592100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b2398 h2399 (by norm_num)
  have h2397 : segsOk 20000000 9588100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b2397 h2398 (by norm_num)
  have h2396 : segsOk 20000000 9584100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b2396 h2397 (by norm_num)
  have h2395 : segsOk 20000000 9580100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b2395 h2396 (by norm_num)
  have h2394 : segsOk 20000000 9576100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b2394 h2395 (by norm_num)
  have h2393 : segsOk 20000000 9572100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b2393 h2394 (by norm_num)
  have h2392 : segsOk 20000000 9568100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b2392 h2393 (by norm_num)
  have h2391 : segsOk 20000000 9564100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b2391 h2392 (by norm_num)
  have h2390 : segsOk 20000000 9560100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b2390 h2391 (by norm_num)
  have h2389 : segsOk 20000000 9556100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b2389 h2390 (by norm_num)
  have h2388 : segsOk 20000000 9552100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b2388 h2389 (by norm_num)
  have h2387 : segsOk 20000000 9548100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b2387 h2388 (by norm_num)
  have h2386 : segsOk 20000000 9544100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b2386 h2387 (by norm_num)
  have h2385 : segsOk 20000000 9540100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b2385 h2386 (by norm_num)
  have h2384 : segsOk 20000000 9536100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b2384 h2385 (by norm_num)
  have h2383 : segsOk 20000000 9532100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b2383 h2384 (by norm_num)
  have h2382 : segsOk 20000000 9528100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b2382 h2383 (by norm_num)
  have h2381 : segsOk 20000000 9524100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b2381 h2382 (by norm_num)
  have h2380 : segsOk 20000000 9520100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b2380 h2381 (by norm_num)
  have h2379 : segsOk 20000000 9516100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b2379 h2380 (by norm_num)
  have h2378 : segsOk 20000000 9512100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b2378 h2379 (by norm_num)
  have h2377 : segsOk 20000000 9508100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b2377 h2378 (by norm_num)
  have h2376 : segsOk 20000000 9504100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b2376 h2377 (by norm_num)
  have h2375 : segsOk 20000000 9500100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b2375 h2376 (by norm_num)
  have h2374 : segsOk 20000000 9496100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b2374 h2375 (by norm_num)
  have h2373 : segsOk 20000000 9492100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b2373 h2374 (by norm_num)
  have h2372 : segsOk 20000000 9488100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b2372 h2373 (by norm_num)
  have h2371 : segsOk 20000000 9484100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b2371 h2372 (by norm_num)
  have h2370 : segsOk 20000000 9480100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b2370 h2371 (by norm_num)
  have h2369 : segsOk 20000000 9476100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b2369 h2370 (by norm_num)
  have h2368 : segsOk 20000000 9472100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b2368 h2369 (by norm_num)
  have h2367 : segsOk 20000000 9468100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b2367 h2368 (by norm_num)
  have h2366 : segsOk 20000000 9464100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b2366 h2367 (by norm_num)
  have h2365 : segsOk 20000000 9460100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b2365 h2366 (by norm_num)
  have h2364 : segsOk 20000000 9456100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b2364 h2365 (by norm_num)
  have h2363 : segsOk 20000000 9452100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b2363 h2364 (by norm_num)
  have h2362 : segsOk 20000000 9448100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b2362 h2363 (by norm_num)
  have h2361 : segsOk 20000000 9444100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b2361 h2362 (by norm_num)
  have h2360 : segsOk 20000000 9440100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b2360 h2361 (by norm_num)
  have h2359 : segsOk 20000000 9436100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b2359 h2360 (by norm_num)
  have h2358 : segsOk 20000000 9432100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b2358 h2359 (by norm_num)
  have h2357 : segsOk 20000000 9428100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b2357 h2358 (by norm_num)
  have h2356 : segsOk 20000000 9424100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b2356 h2357 (by norm_num)
  have h2355 : segsOk 20000000 9420100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b2355 h2356 (by norm_num)
  have h2354 : segsOk 20000000 9416100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b2354 h2355 (by norm_num)
  have h2353 : segsOk 20000000 9412100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b2353 h2354 (by norm_num)
  have h2352 : segsOk 20000000 9408100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b2352 h2353 (by norm_num)
  have h2351 : segsOk 20000000 9404100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b2351 h2352 (by norm_num)
  have h2350 : segsOk 20000000 9400100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b2350 h2351 (by norm_num)
  exact h2350
end Grosswald.Direct
