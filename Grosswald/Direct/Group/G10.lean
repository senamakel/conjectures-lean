import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0500
import Grosswald.Direct.Run.B0501
import Grosswald.Direct.Run.B0502
import Grosswald.Direct.Run.B0503
import Grosswald.Direct.Run.B0504
import Grosswald.Direct.Run.B0505
import Grosswald.Direct.Run.B0506
import Grosswald.Direct.Run.B0507
import Grosswald.Direct.Run.B0508
import Grosswald.Direct.Run.B0509
import Grosswald.Direct.Run.B0510
import Grosswald.Direct.Run.B0511
import Grosswald.Direct.Run.B0512
import Grosswald.Direct.Run.B0513
import Grosswald.Direct.Run.B0514
import Grosswald.Direct.Run.B0515
import Grosswald.Direct.Run.B0516
import Grosswald.Direct.Run.B0517
import Grosswald.Direct.Run.B0518
import Grosswald.Direct.Run.B0519
import Grosswald.Direct.Run.B0520
import Grosswald.Direct.Run.B0521
import Grosswald.Direct.Run.B0522
import Grosswald.Direct.Run.B0523
import Grosswald.Direct.Run.B0524
import Grosswald.Direct.Run.B0525
import Grosswald.Direct.Run.B0526
import Grosswald.Direct.Run.B0527
import Grosswald.Direct.Run.B0528
import Grosswald.Direct.Run.B0529
import Grosswald.Direct.Run.B0530
import Grosswald.Direct.Run.B0531
import Grosswald.Direct.Run.B0532
import Grosswald.Direct.Run.B0533
import Grosswald.Direct.Run.B0534
import Grosswald.Direct.Run.B0535
import Grosswald.Direct.Run.B0536
import Grosswald.Direct.Run.B0537
import Grosswald.Direct.Run.B0538
import Grosswald.Direct.Run.B0539
import Grosswald.Direct.Run.B0540
import Grosswald.Direct.Run.B0541
import Grosswald.Direct.Run.B0542
import Grosswald.Direct.Run.B0543
import Grosswald.Direct.Run.B0544
import Grosswald.Direct.Run.B0545
import Grosswald.Direct.Run.B0546
import Grosswald.Direct.Run.B0547
import Grosswald.Direct.Run.B0548
import Grosswald.Direct.Run.B0549

namespace Grosswald.Direct
open GrosswaldCompute
theorem g10 : segsOk 20000000 2000100000411 5000 = true := by
  have h0549 : segsOk 20000000 2196100000411 100 = true := Run.b0549
  have h0548 : segsOk 20000000 2192100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0548 h0549 (by norm_num)
  have h0547 : segsOk 20000000 2188100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0547 h0548 (by norm_num)
  have h0546 : segsOk 20000000 2184100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0546 h0547 (by norm_num)
  have h0545 : segsOk 20000000 2180100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0545 h0546 (by norm_num)
  have h0544 : segsOk 20000000 2176100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0544 h0545 (by norm_num)
  have h0543 : segsOk 20000000 2172100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0543 h0544 (by norm_num)
  have h0542 : segsOk 20000000 2168100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0542 h0543 (by norm_num)
  have h0541 : segsOk 20000000 2164100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0541 h0542 (by norm_num)
  have h0540 : segsOk 20000000 2160100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0540 h0541 (by norm_num)
  have h0539 : segsOk 20000000 2156100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0539 h0540 (by norm_num)
  have h0538 : segsOk 20000000 2152100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0538 h0539 (by norm_num)
  have h0537 : segsOk 20000000 2148100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0537 h0538 (by norm_num)
  have h0536 : segsOk 20000000 2144100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0536 h0537 (by norm_num)
  have h0535 : segsOk 20000000 2140100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0535 h0536 (by norm_num)
  have h0534 : segsOk 20000000 2136100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0534 h0535 (by norm_num)
  have h0533 : segsOk 20000000 2132100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0533 h0534 (by norm_num)
  have h0532 : segsOk 20000000 2128100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0532 h0533 (by norm_num)
  have h0531 : segsOk 20000000 2124100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0531 h0532 (by norm_num)
  have h0530 : segsOk 20000000 2120100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0530 h0531 (by norm_num)
  have h0529 : segsOk 20000000 2116100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0529 h0530 (by norm_num)
  have h0528 : segsOk 20000000 2112100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0528 h0529 (by norm_num)
  have h0527 : segsOk 20000000 2108100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0527 h0528 (by norm_num)
  have h0526 : segsOk 20000000 2104100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0526 h0527 (by norm_num)
  have h0525 : segsOk 20000000 2100100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0525 h0526 (by norm_num)
  have h0524 : segsOk 20000000 2096100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0524 h0525 (by norm_num)
  have h0523 : segsOk 20000000 2092100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0523 h0524 (by norm_num)
  have h0522 : segsOk 20000000 2088100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0522 h0523 (by norm_num)
  have h0521 : segsOk 20000000 2084100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0521 h0522 (by norm_num)
  have h0520 : segsOk 20000000 2080100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0520 h0521 (by norm_num)
  have h0519 : segsOk 20000000 2076100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0519 h0520 (by norm_num)
  have h0518 : segsOk 20000000 2072100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0518 h0519 (by norm_num)
  have h0517 : segsOk 20000000 2068100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0517 h0518 (by norm_num)
  have h0516 : segsOk 20000000 2064100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0516 h0517 (by norm_num)
  have h0515 : segsOk 20000000 2060100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0515 h0516 (by norm_num)
  have h0514 : segsOk 20000000 2056100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0514 h0515 (by norm_num)
  have h0513 : segsOk 20000000 2052100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0513 h0514 (by norm_num)
  have h0512 : segsOk 20000000 2048100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0512 h0513 (by norm_num)
  have h0511 : segsOk 20000000 2044100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0511 h0512 (by norm_num)
  have h0510 : segsOk 20000000 2040100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0510 h0511 (by norm_num)
  have h0509 : segsOk 20000000 2036100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0509 h0510 (by norm_num)
  have h0508 : segsOk 20000000 2032100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0508 h0509 (by norm_num)
  have h0507 : segsOk 20000000 2028100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0507 h0508 (by norm_num)
  have h0506 : segsOk 20000000 2024100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0506 h0507 (by norm_num)
  have h0505 : segsOk 20000000 2020100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0505 h0506 (by norm_num)
  have h0504 : segsOk 20000000 2016100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0504 h0505 (by norm_num)
  have h0503 : segsOk 20000000 2012100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0503 h0504 (by norm_num)
  have h0502 : segsOk 20000000 2008100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0502 h0503 (by norm_num)
  have h0501 : segsOk 20000000 2004100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0501 h0502 (by norm_num)
  have h0500 : segsOk 20000000 2000100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0500 h0501 (by norm_num)
  exact h0500
end Grosswald.Direct
