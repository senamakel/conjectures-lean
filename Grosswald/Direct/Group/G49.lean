import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B2450
import Grosswald.Direct.Run.B2451
import Grosswald.Direct.Run.B2452
import Grosswald.Direct.Run.B2453
import Grosswald.Direct.Run.B2454
import Grosswald.Direct.Run.B2455
import Grosswald.Direct.Run.B2456
import Grosswald.Direct.Run.B2457
import Grosswald.Direct.Run.B2458
import Grosswald.Direct.Run.B2459
import Grosswald.Direct.Run.B2460
import Grosswald.Direct.Run.B2461
import Grosswald.Direct.Run.B2462
import Grosswald.Direct.Run.B2463
import Grosswald.Direct.Run.B2464
import Grosswald.Direct.Run.B2465
import Grosswald.Direct.Run.B2466
import Grosswald.Direct.Run.B2467
import Grosswald.Direct.Run.B2468
import Grosswald.Direct.Run.B2469
import Grosswald.Direct.Run.B2470
import Grosswald.Direct.Run.B2471
import Grosswald.Direct.Run.B2472
import Grosswald.Direct.Run.B2473
import Grosswald.Direct.Run.B2474
import Grosswald.Direct.Run.B2475
import Grosswald.Direct.Run.B2476
import Grosswald.Direct.Run.B2477
import Grosswald.Direct.Run.B2478
import Grosswald.Direct.Run.B2479
import Grosswald.Direct.Run.B2480
import Grosswald.Direct.Run.B2481
import Grosswald.Direct.Run.B2482
import Grosswald.Direct.Run.B2483
import Grosswald.Direct.Run.B2484
import Grosswald.Direct.Run.B2485
import Grosswald.Direct.Run.B2486
import Grosswald.Direct.Run.B2487
import Grosswald.Direct.Run.B2488
import Grosswald.Direct.Run.B2489
import Grosswald.Direct.Run.B2490
import Grosswald.Direct.Run.B2491
import Grosswald.Direct.Run.B2492
import Grosswald.Direct.Run.B2493
import Grosswald.Direct.Run.B2494
import Grosswald.Direct.Run.B2495
import Grosswald.Direct.Run.B2496
import Grosswald.Direct.Run.B2497
import Grosswald.Direct.Run.B2498
import Grosswald.Direct.Run.B2499

namespace Grosswald.Direct
open GrosswaldCompute
theorem g49 : segsOk 20000000 9800100000411 5000 = true := by
  have h2499 : segsOk 20000000 9996100000411 100 = true := Run.b2499
  have h2498 : segsOk 20000000 9992100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b2498 h2499 (by norm_num)
  have h2497 : segsOk 20000000 9988100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b2497 h2498 (by norm_num)
  have h2496 : segsOk 20000000 9984100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b2496 h2497 (by norm_num)
  have h2495 : segsOk 20000000 9980100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b2495 h2496 (by norm_num)
  have h2494 : segsOk 20000000 9976100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b2494 h2495 (by norm_num)
  have h2493 : segsOk 20000000 9972100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b2493 h2494 (by norm_num)
  have h2492 : segsOk 20000000 9968100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b2492 h2493 (by norm_num)
  have h2491 : segsOk 20000000 9964100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b2491 h2492 (by norm_num)
  have h2490 : segsOk 20000000 9960100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b2490 h2491 (by norm_num)
  have h2489 : segsOk 20000000 9956100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b2489 h2490 (by norm_num)
  have h2488 : segsOk 20000000 9952100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b2488 h2489 (by norm_num)
  have h2487 : segsOk 20000000 9948100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b2487 h2488 (by norm_num)
  have h2486 : segsOk 20000000 9944100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b2486 h2487 (by norm_num)
  have h2485 : segsOk 20000000 9940100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b2485 h2486 (by norm_num)
  have h2484 : segsOk 20000000 9936100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b2484 h2485 (by norm_num)
  have h2483 : segsOk 20000000 9932100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b2483 h2484 (by norm_num)
  have h2482 : segsOk 20000000 9928100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b2482 h2483 (by norm_num)
  have h2481 : segsOk 20000000 9924100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b2481 h2482 (by norm_num)
  have h2480 : segsOk 20000000 9920100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b2480 h2481 (by norm_num)
  have h2479 : segsOk 20000000 9916100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b2479 h2480 (by norm_num)
  have h2478 : segsOk 20000000 9912100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b2478 h2479 (by norm_num)
  have h2477 : segsOk 20000000 9908100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b2477 h2478 (by norm_num)
  have h2476 : segsOk 20000000 9904100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b2476 h2477 (by norm_num)
  have h2475 : segsOk 20000000 9900100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b2475 h2476 (by norm_num)
  have h2474 : segsOk 20000000 9896100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b2474 h2475 (by norm_num)
  have h2473 : segsOk 20000000 9892100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b2473 h2474 (by norm_num)
  have h2472 : segsOk 20000000 9888100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b2472 h2473 (by norm_num)
  have h2471 : segsOk 20000000 9884100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b2471 h2472 (by norm_num)
  have h2470 : segsOk 20000000 9880100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b2470 h2471 (by norm_num)
  have h2469 : segsOk 20000000 9876100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b2469 h2470 (by norm_num)
  have h2468 : segsOk 20000000 9872100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b2468 h2469 (by norm_num)
  have h2467 : segsOk 20000000 9868100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b2467 h2468 (by norm_num)
  have h2466 : segsOk 20000000 9864100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b2466 h2467 (by norm_num)
  have h2465 : segsOk 20000000 9860100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b2465 h2466 (by norm_num)
  have h2464 : segsOk 20000000 9856100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b2464 h2465 (by norm_num)
  have h2463 : segsOk 20000000 9852100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b2463 h2464 (by norm_num)
  have h2462 : segsOk 20000000 9848100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b2462 h2463 (by norm_num)
  have h2461 : segsOk 20000000 9844100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b2461 h2462 (by norm_num)
  have h2460 : segsOk 20000000 9840100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b2460 h2461 (by norm_num)
  have h2459 : segsOk 20000000 9836100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b2459 h2460 (by norm_num)
  have h2458 : segsOk 20000000 9832100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b2458 h2459 (by norm_num)
  have h2457 : segsOk 20000000 9828100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b2457 h2458 (by norm_num)
  have h2456 : segsOk 20000000 9824100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b2456 h2457 (by norm_num)
  have h2455 : segsOk 20000000 9820100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b2455 h2456 (by norm_num)
  have h2454 : segsOk 20000000 9816100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b2454 h2455 (by norm_num)
  have h2453 : segsOk 20000000 9812100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b2453 h2454 (by norm_num)
  have h2452 : segsOk 20000000 9808100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b2452 h2453 (by norm_num)
  have h2451 : segsOk 20000000 9804100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b2451 h2452 (by norm_num)
  have h2450 : segsOk 20000000 9800100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b2450 h2451 (by norm_num)
  exact h2450
end Grosswald.Direct
