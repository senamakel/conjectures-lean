import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B2400
import Grosswald.Direct.Run.B2401
import Grosswald.Direct.Run.B2402
import Grosswald.Direct.Run.B2403
import Grosswald.Direct.Run.B2404
import Grosswald.Direct.Run.B2405
import Grosswald.Direct.Run.B2406
import Grosswald.Direct.Run.B2407
import Grosswald.Direct.Run.B2408
import Grosswald.Direct.Run.B2409
import Grosswald.Direct.Run.B2410
import Grosswald.Direct.Run.B2411
import Grosswald.Direct.Run.B2412
import Grosswald.Direct.Run.B2413
import Grosswald.Direct.Run.B2414
import Grosswald.Direct.Run.B2415
import Grosswald.Direct.Run.B2416
import Grosswald.Direct.Run.B2417
import Grosswald.Direct.Run.B2418
import Grosswald.Direct.Run.B2419
import Grosswald.Direct.Run.B2420
import Grosswald.Direct.Run.B2421
import Grosswald.Direct.Run.B2422
import Grosswald.Direct.Run.B2423
import Grosswald.Direct.Run.B2424
import Grosswald.Direct.Run.B2425
import Grosswald.Direct.Run.B2426
import Grosswald.Direct.Run.B2427
import Grosswald.Direct.Run.B2428
import Grosswald.Direct.Run.B2429
import Grosswald.Direct.Run.B2430
import Grosswald.Direct.Run.B2431
import Grosswald.Direct.Run.B2432
import Grosswald.Direct.Run.B2433
import Grosswald.Direct.Run.B2434
import Grosswald.Direct.Run.B2435
import Grosswald.Direct.Run.B2436
import Grosswald.Direct.Run.B2437
import Grosswald.Direct.Run.B2438
import Grosswald.Direct.Run.B2439
import Grosswald.Direct.Run.B2440
import Grosswald.Direct.Run.B2441
import Grosswald.Direct.Run.B2442
import Grosswald.Direct.Run.B2443
import Grosswald.Direct.Run.B2444
import Grosswald.Direct.Run.B2445
import Grosswald.Direct.Run.B2446
import Grosswald.Direct.Run.B2447
import Grosswald.Direct.Run.B2448
import Grosswald.Direct.Run.B2449

namespace Grosswald.Direct
open GrosswaldCompute
theorem g48 : segsOk 20000000 9600100000411 5000 = true := by
  have h2449 : segsOk 20000000 9796100000411 100 = true := Run.b2449
  have h2448 : segsOk 20000000 9792100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b2448 h2449 (by norm_num)
  have h2447 : segsOk 20000000 9788100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b2447 h2448 (by norm_num)
  have h2446 : segsOk 20000000 9784100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b2446 h2447 (by norm_num)
  have h2445 : segsOk 20000000 9780100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b2445 h2446 (by norm_num)
  have h2444 : segsOk 20000000 9776100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b2444 h2445 (by norm_num)
  have h2443 : segsOk 20000000 9772100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b2443 h2444 (by norm_num)
  have h2442 : segsOk 20000000 9768100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b2442 h2443 (by norm_num)
  have h2441 : segsOk 20000000 9764100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b2441 h2442 (by norm_num)
  have h2440 : segsOk 20000000 9760100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b2440 h2441 (by norm_num)
  have h2439 : segsOk 20000000 9756100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b2439 h2440 (by norm_num)
  have h2438 : segsOk 20000000 9752100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b2438 h2439 (by norm_num)
  have h2437 : segsOk 20000000 9748100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b2437 h2438 (by norm_num)
  have h2436 : segsOk 20000000 9744100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b2436 h2437 (by norm_num)
  have h2435 : segsOk 20000000 9740100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b2435 h2436 (by norm_num)
  have h2434 : segsOk 20000000 9736100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b2434 h2435 (by norm_num)
  have h2433 : segsOk 20000000 9732100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b2433 h2434 (by norm_num)
  have h2432 : segsOk 20000000 9728100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b2432 h2433 (by norm_num)
  have h2431 : segsOk 20000000 9724100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b2431 h2432 (by norm_num)
  have h2430 : segsOk 20000000 9720100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b2430 h2431 (by norm_num)
  have h2429 : segsOk 20000000 9716100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b2429 h2430 (by norm_num)
  have h2428 : segsOk 20000000 9712100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b2428 h2429 (by norm_num)
  have h2427 : segsOk 20000000 9708100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b2427 h2428 (by norm_num)
  have h2426 : segsOk 20000000 9704100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b2426 h2427 (by norm_num)
  have h2425 : segsOk 20000000 9700100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b2425 h2426 (by norm_num)
  have h2424 : segsOk 20000000 9696100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b2424 h2425 (by norm_num)
  have h2423 : segsOk 20000000 9692100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b2423 h2424 (by norm_num)
  have h2422 : segsOk 20000000 9688100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b2422 h2423 (by norm_num)
  have h2421 : segsOk 20000000 9684100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b2421 h2422 (by norm_num)
  have h2420 : segsOk 20000000 9680100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b2420 h2421 (by norm_num)
  have h2419 : segsOk 20000000 9676100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b2419 h2420 (by norm_num)
  have h2418 : segsOk 20000000 9672100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b2418 h2419 (by norm_num)
  have h2417 : segsOk 20000000 9668100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b2417 h2418 (by norm_num)
  have h2416 : segsOk 20000000 9664100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b2416 h2417 (by norm_num)
  have h2415 : segsOk 20000000 9660100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b2415 h2416 (by norm_num)
  have h2414 : segsOk 20000000 9656100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b2414 h2415 (by norm_num)
  have h2413 : segsOk 20000000 9652100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b2413 h2414 (by norm_num)
  have h2412 : segsOk 20000000 9648100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b2412 h2413 (by norm_num)
  have h2411 : segsOk 20000000 9644100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b2411 h2412 (by norm_num)
  have h2410 : segsOk 20000000 9640100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b2410 h2411 (by norm_num)
  have h2409 : segsOk 20000000 9636100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b2409 h2410 (by norm_num)
  have h2408 : segsOk 20000000 9632100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b2408 h2409 (by norm_num)
  have h2407 : segsOk 20000000 9628100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b2407 h2408 (by norm_num)
  have h2406 : segsOk 20000000 9624100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b2406 h2407 (by norm_num)
  have h2405 : segsOk 20000000 9620100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b2405 h2406 (by norm_num)
  have h2404 : segsOk 20000000 9616100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b2404 h2405 (by norm_num)
  have h2403 : segsOk 20000000 9612100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b2403 h2404 (by norm_num)
  have h2402 : segsOk 20000000 9608100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b2402 h2403 (by norm_num)
  have h2401 : segsOk 20000000 9604100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b2401 h2402 (by norm_num)
  have h2400 : segsOk 20000000 9600100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b2400 h2401 (by norm_num)
  exact h2400
end Grosswald.Direct
