import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0400
import Grosswald.Direct.Run.B0401
import Grosswald.Direct.Run.B0402
import Grosswald.Direct.Run.B0403
import Grosswald.Direct.Run.B0404
import Grosswald.Direct.Run.B0405
import Grosswald.Direct.Run.B0406
import Grosswald.Direct.Run.B0407
import Grosswald.Direct.Run.B0408
import Grosswald.Direct.Run.B0409
import Grosswald.Direct.Run.B0410
import Grosswald.Direct.Run.B0411
import Grosswald.Direct.Run.B0412
import Grosswald.Direct.Run.B0413
import Grosswald.Direct.Run.B0414
import Grosswald.Direct.Run.B0415
import Grosswald.Direct.Run.B0416
import Grosswald.Direct.Run.B0417
import Grosswald.Direct.Run.B0418
import Grosswald.Direct.Run.B0419
import Grosswald.Direct.Run.B0420
import Grosswald.Direct.Run.B0421
import Grosswald.Direct.Run.B0422
import Grosswald.Direct.Run.B0423
import Grosswald.Direct.Run.B0424
import Grosswald.Direct.Run.B0425
import Grosswald.Direct.Run.B0426
import Grosswald.Direct.Run.B0427
import Grosswald.Direct.Run.B0428
import Grosswald.Direct.Run.B0429
import Grosswald.Direct.Run.B0430
import Grosswald.Direct.Run.B0431
import Grosswald.Direct.Run.B0432
import Grosswald.Direct.Run.B0433
import Grosswald.Direct.Run.B0434
import Grosswald.Direct.Run.B0435
import Grosswald.Direct.Run.B0436
import Grosswald.Direct.Run.B0437
import Grosswald.Direct.Run.B0438
import Grosswald.Direct.Run.B0439
import Grosswald.Direct.Run.B0440
import Grosswald.Direct.Run.B0441
import Grosswald.Direct.Run.B0442
import Grosswald.Direct.Run.B0443
import Grosswald.Direct.Run.B0444
import Grosswald.Direct.Run.B0445
import Grosswald.Direct.Run.B0446
import Grosswald.Direct.Run.B0447
import Grosswald.Direct.Run.B0448
import Grosswald.Direct.Run.B0449

namespace Grosswald.Direct
open GrosswaldCompute
theorem g08 : segsOk 20000000 1600100000411 5000 = true := by
  have h0449 : segsOk 20000000 1796100000411 100 = true := Run.b0449
  have h0448 : segsOk 20000000 1792100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0448 h0449 (by norm_num)
  have h0447 : segsOk 20000000 1788100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0447 h0448 (by norm_num)
  have h0446 : segsOk 20000000 1784100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0446 h0447 (by norm_num)
  have h0445 : segsOk 20000000 1780100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0445 h0446 (by norm_num)
  have h0444 : segsOk 20000000 1776100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0444 h0445 (by norm_num)
  have h0443 : segsOk 20000000 1772100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0443 h0444 (by norm_num)
  have h0442 : segsOk 20000000 1768100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0442 h0443 (by norm_num)
  have h0441 : segsOk 20000000 1764100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0441 h0442 (by norm_num)
  have h0440 : segsOk 20000000 1760100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0440 h0441 (by norm_num)
  have h0439 : segsOk 20000000 1756100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0439 h0440 (by norm_num)
  have h0438 : segsOk 20000000 1752100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0438 h0439 (by norm_num)
  have h0437 : segsOk 20000000 1748100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0437 h0438 (by norm_num)
  have h0436 : segsOk 20000000 1744100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0436 h0437 (by norm_num)
  have h0435 : segsOk 20000000 1740100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0435 h0436 (by norm_num)
  have h0434 : segsOk 20000000 1736100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0434 h0435 (by norm_num)
  have h0433 : segsOk 20000000 1732100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0433 h0434 (by norm_num)
  have h0432 : segsOk 20000000 1728100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0432 h0433 (by norm_num)
  have h0431 : segsOk 20000000 1724100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0431 h0432 (by norm_num)
  have h0430 : segsOk 20000000 1720100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0430 h0431 (by norm_num)
  have h0429 : segsOk 20000000 1716100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0429 h0430 (by norm_num)
  have h0428 : segsOk 20000000 1712100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0428 h0429 (by norm_num)
  have h0427 : segsOk 20000000 1708100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0427 h0428 (by norm_num)
  have h0426 : segsOk 20000000 1704100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0426 h0427 (by norm_num)
  have h0425 : segsOk 20000000 1700100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0425 h0426 (by norm_num)
  have h0424 : segsOk 20000000 1696100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0424 h0425 (by norm_num)
  have h0423 : segsOk 20000000 1692100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0423 h0424 (by norm_num)
  have h0422 : segsOk 20000000 1688100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0422 h0423 (by norm_num)
  have h0421 : segsOk 20000000 1684100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0421 h0422 (by norm_num)
  have h0420 : segsOk 20000000 1680100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0420 h0421 (by norm_num)
  have h0419 : segsOk 20000000 1676100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0419 h0420 (by norm_num)
  have h0418 : segsOk 20000000 1672100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0418 h0419 (by norm_num)
  have h0417 : segsOk 20000000 1668100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0417 h0418 (by norm_num)
  have h0416 : segsOk 20000000 1664100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0416 h0417 (by norm_num)
  have h0415 : segsOk 20000000 1660100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0415 h0416 (by norm_num)
  have h0414 : segsOk 20000000 1656100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0414 h0415 (by norm_num)
  have h0413 : segsOk 20000000 1652100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0413 h0414 (by norm_num)
  have h0412 : segsOk 20000000 1648100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0412 h0413 (by norm_num)
  have h0411 : segsOk 20000000 1644100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0411 h0412 (by norm_num)
  have h0410 : segsOk 20000000 1640100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0410 h0411 (by norm_num)
  have h0409 : segsOk 20000000 1636100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0409 h0410 (by norm_num)
  have h0408 : segsOk 20000000 1632100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0408 h0409 (by norm_num)
  have h0407 : segsOk 20000000 1628100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0407 h0408 (by norm_num)
  have h0406 : segsOk 20000000 1624100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0406 h0407 (by norm_num)
  have h0405 : segsOk 20000000 1620100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0405 h0406 (by norm_num)
  have h0404 : segsOk 20000000 1616100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0404 h0405 (by norm_num)
  have h0403 : segsOk 20000000 1612100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0403 h0404 (by norm_num)
  have h0402 : segsOk 20000000 1608100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0402 h0403 (by norm_num)
  have h0401 : segsOk 20000000 1604100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0401 h0402 (by norm_num)
  have h0400 : segsOk 20000000 1600100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0400 h0401 (by norm_num)
  exact h0400
end Grosswald.Direct
