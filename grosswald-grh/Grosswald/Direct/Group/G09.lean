import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0450
import Grosswald.Direct.Run.B0451
import Grosswald.Direct.Run.B0452
import Grosswald.Direct.Run.B0453
import Grosswald.Direct.Run.B0454
import Grosswald.Direct.Run.B0455
import Grosswald.Direct.Run.B0456
import Grosswald.Direct.Run.B0457
import Grosswald.Direct.Run.B0458
import Grosswald.Direct.Run.B0459
import Grosswald.Direct.Run.B0460
import Grosswald.Direct.Run.B0461
import Grosswald.Direct.Run.B0462
import Grosswald.Direct.Run.B0463
import Grosswald.Direct.Run.B0464
import Grosswald.Direct.Run.B0465
import Grosswald.Direct.Run.B0466
import Grosswald.Direct.Run.B0467
import Grosswald.Direct.Run.B0468
import Grosswald.Direct.Run.B0469
import Grosswald.Direct.Run.B0470
import Grosswald.Direct.Run.B0471
import Grosswald.Direct.Run.B0472
import Grosswald.Direct.Run.B0473
import Grosswald.Direct.Run.B0474
import Grosswald.Direct.Run.B0475
import Grosswald.Direct.Run.B0476
import Grosswald.Direct.Run.B0477
import Grosswald.Direct.Run.B0478
import Grosswald.Direct.Run.B0479
import Grosswald.Direct.Run.B0480
import Grosswald.Direct.Run.B0481
import Grosswald.Direct.Run.B0482
import Grosswald.Direct.Run.B0483
import Grosswald.Direct.Run.B0484
import Grosswald.Direct.Run.B0485
import Grosswald.Direct.Run.B0486
import Grosswald.Direct.Run.B0487
import Grosswald.Direct.Run.B0488
import Grosswald.Direct.Run.B0489
import Grosswald.Direct.Run.B0490
import Grosswald.Direct.Run.B0491
import Grosswald.Direct.Run.B0492
import Grosswald.Direct.Run.B0493
import Grosswald.Direct.Run.B0494
import Grosswald.Direct.Run.B0495
import Grosswald.Direct.Run.B0496
import Grosswald.Direct.Run.B0497
import Grosswald.Direct.Run.B0498
import Grosswald.Direct.Run.B0499

namespace Grosswald.Direct
open GrosswaldCompute
theorem g09 : segsOk 20000000 1800100000411 5000 = true := by
  have h0499 : segsOk 20000000 1996100000411 100 = true := Run.b0499
  have h0498 : segsOk 20000000 1992100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0498 h0499 (by norm_num)
  have h0497 : segsOk 20000000 1988100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0497 h0498 (by norm_num)
  have h0496 : segsOk 20000000 1984100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0496 h0497 (by norm_num)
  have h0495 : segsOk 20000000 1980100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0495 h0496 (by norm_num)
  have h0494 : segsOk 20000000 1976100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0494 h0495 (by norm_num)
  have h0493 : segsOk 20000000 1972100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0493 h0494 (by norm_num)
  have h0492 : segsOk 20000000 1968100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0492 h0493 (by norm_num)
  have h0491 : segsOk 20000000 1964100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0491 h0492 (by norm_num)
  have h0490 : segsOk 20000000 1960100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0490 h0491 (by norm_num)
  have h0489 : segsOk 20000000 1956100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0489 h0490 (by norm_num)
  have h0488 : segsOk 20000000 1952100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0488 h0489 (by norm_num)
  have h0487 : segsOk 20000000 1948100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0487 h0488 (by norm_num)
  have h0486 : segsOk 20000000 1944100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0486 h0487 (by norm_num)
  have h0485 : segsOk 20000000 1940100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0485 h0486 (by norm_num)
  have h0484 : segsOk 20000000 1936100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0484 h0485 (by norm_num)
  have h0483 : segsOk 20000000 1932100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0483 h0484 (by norm_num)
  have h0482 : segsOk 20000000 1928100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0482 h0483 (by norm_num)
  have h0481 : segsOk 20000000 1924100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0481 h0482 (by norm_num)
  have h0480 : segsOk 20000000 1920100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0480 h0481 (by norm_num)
  have h0479 : segsOk 20000000 1916100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0479 h0480 (by norm_num)
  have h0478 : segsOk 20000000 1912100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0478 h0479 (by norm_num)
  have h0477 : segsOk 20000000 1908100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0477 h0478 (by norm_num)
  have h0476 : segsOk 20000000 1904100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0476 h0477 (by norm_num)
  have h0475 : segsOk 20000000 1900100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0475 h0476 (by norm_num)
  have h0474 : segsOk 20000000 1896100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0474 h0475 (by norm_num)
  have h0473 : segsOk 20000000 1892100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0473 h0474 (by norm_num)
  have h0472 : segsOk 20000000 1888100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0472 h0473 (by norm_num)
  have h0471 : segsOk 20000000 1884100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0471 h0472 (by norm_num)
  have h0470 : segsOk 20000000 1880100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0470 h0471 (by norm_num)
  have h0469 : segsOk 20000000 1876100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0469 h0470 (by norm_num)
  have h0468 : segsOk 20000000 1872100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0468 h0469 (by norm_num)
  have h0467 : segsOk 20000000 1868100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0467 h0468 (by norm_num)
  have h0466 : segsOk 20000000 1864100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0466 h0467 (by norm_num)
  have h0465 : segsOk 20000000 1860100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0465 h0466 (by norm_num)
  have h0464 : segsOk 20000000 1856100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0464 h0465 (by norm_num)
  have h0463 : segsOk 20000000 1852100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0463 h0464 (by norm_num)
  have h0462 : segsOk 20000000 1848100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0462 h0463 (by norm_num)
  have h0461 : segsOk 20000000 1844100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0461 h0462 (by norm_num)
  have h0460 : segsOk 20000000 1840100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0460 h0461 (by norm_num)
  have h0459 : segsOk 20000000 1836100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0459 h0460 (by norm_num)
  have h0458 : segsOk 20000000 1832100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0458 h0459 (by norm_num)
  have h0457 : segsOk 20000000 1828100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0457 h0458 (by norm_num)
  have h0456 : segsOk 20000000 1824100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0456 h0457 (by norm_num)
  have h0455 : segsOk 20000000 1820100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0455 h0456 (by norm_num)
  have h0454 : segsOk 20000000 1816100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0454 h0455 (by norm_num)
  have h0453 : segsOk 20000000 1812100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0453 h0454 (by norm_num)
  have h0452 : segsOk 20000000 1808100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0452 h0453 (by norm_num)
  have h0451 : segsOk 20000000 1804100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0451 h0452 (by norm_num)
  have h0450 : segsOk 20000000 1800100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0450 h0451 (by norm_num)
  exact h0450
end Grosswald.Direct
