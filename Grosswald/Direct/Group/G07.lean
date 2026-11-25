import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0350
import Grosswald.Direct.Run.B0351
import Grosswald.Direct.Run.B0352
import Grosswald.Direct.Run.B0353
import Grosswald.Direct.Run.B0354
import Grosswald.Direct.Run.B0355
import Grosswald.Direct.Run.B0356
import Grosswald.Direct.Run.B0357
import Grosswald.Direct.Run.B0358
import Grosswald.Direct.Run.B0359
import Grosswald.Direct.Run.B0360
import Grosswald.Direct.Run.B0361
import Grosswald.Direct.Run.B0362
import Grosswald.Direct.Run.B0363
import Grosswald.Direct.Run.B0364
import Grosswald.Direct.Run.B0365
import Grosswald.Direct.Run.B0366
import Grosswald.Direct.Run.B0367
import Grosswald.Direct.Run.B0368
import Grosswald.Direct.Run.B0369
import Grosswald.Direct.Run.B0370
import Grosswald.Direct.Run.B0371
import Grosswald.Direct.Run.B0372
import Grosswald.Direct.Run.B0373
import Grosswald.Direct.Run.B0374
import Grosswald.Direct.Run.B0375
import Grosswald.Direct.Run.B0376
import Grosswald.Direct.Run.B0377
import Grosswald.Direct.Run.B0378
import Grosswald.Direct.Run.B0379
import Grosswald.Direct.Run.B0380
import Grosswald.Direct.Run.B0381
import Grosswald.Direct.Run.B0382
import Grosswald.Direct.Run.B0383
import Grosswald.Direct.Run.B0384
import Grosswald.Direct.Run.B0385
import Grosswald.Direct.Run.B0386
import Grosswald.Direct.Run.B0387
import Grosswald.Direct.Run.B0388
import Grosswald.Direct.Run.B0389
import Grosswald.Direct.Run.B0390
import Grosswald.Direct.Run.B0391
import Grosswald.Direct.Run.B0392
import Grosswald.Direct.Run.B0393
import Grosswald.Direct.Run.B0394
import Grosswald.Direct.Run.B0395
import Grosswald.Direct.Run.B0396
import Grosswald.Direct.Run.B0397
import Grosswald.Direct.Run.B0398
import Grosswald.Direct.Run.B0399

namespace Grosswald.Direct
open GrosswaldCompute
theorem g07 : segsOk 20000000 1400100000411 5000 = true := by
  have h0399 : segsOk 20000000 1596100000411 100 = true := Run.b0399
  have h0398 : segsOk 20000000 1592100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0398 h0399 (by norm_num)
  have h0397 : segsOk 20000000 1588100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0397 h0398 (by norm_num)
  have h0396 : segsOk 20000000 1584100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0396 h0397 (by norm_num)
  have h0395 : segsOk 20000000 1580100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0395 h0396 (by norm_num)
  have h0394 : segsOk 20000000 1576100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0394 h0395 (by norm_num)
  have h0393 : segsOk 20000000 1572100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0393 h0394 (by norm_num)
  have h0392 : segsOk 20000000 1568100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0392 h0393 (by norm_num)
  have h0391 : segsOk 20000000 1564100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0391 h0392 (by norm_num)
  have h0390 : segsOk 20000000 1560100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0390 h0391 (by norm_num)
  have h0389 : segsOk 20000000 1556100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0389 h0390 (by norm_num)
  have h0388 : segsOk 20000000 1552100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0388 h0389 (by norm_num)
  have h0387 : segsOk 20000000 1548100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0387 h0388 (by norm_num)
  have h0386 : segsOk 20000000 1544100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0386 h0387 (by norm_num)
  have h0385 : segsOk 20000000 1540100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0385 h0386 (by norm_num)
  have h0384 : segsOk 20000000 1536100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0384 h0385 (by norm_num)
  have h0383 : segsOk 20000000 1532100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0383 h0384 (by norm_num)
  have h0382 : segsOk 20000000 1528100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0382 h0383 (by norm_num)
  have h0381 : segsOk 20000000 1524100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0381 h0382 (by norm_num)
  have h0380 : segsOk 20000000 1520100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0380 h0381 (by norm_num)
  have h0379 : segsOk 20000000 1516100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0379 h0380 (by norm_num)
  have h0378 : segsOk 20000000 1512100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0378 h0379 (by norm_num)
  have h0377 : segsOk 20000000 1508100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0377 h0378 (by norm_num)
  have h0376 : segsOk 20000000 1504100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0376 h0377 (by norm_num)
  have h0375 : segsOk 20000000 1500100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0375 h0376 (by norm_num)
  have h0374 : segsOk 20000000 1496100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0374 h0375 (by norm_num)
  have h0373 : segsOk 20000000 1492100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0373 h0374 (by norm_num)
  have h0372 : segsOk 20000000 1488100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0372 h0373 (by norm_num)
  have h0371 : segsOk 20000000 1484100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0371 h0372 (by norm_num)
  have h0370 : segsOk 20000000 1480100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0370 h0371 (by norm_num)
  have h0369 : segsOk 20000000 1476100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0369 h0370 (by norm_num)
  have h0368 : segsOk 20000000 1472100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0368 h0369 (by norm_num)
  have h0367 : segsOk 20000000 1468100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0367 h0368 (by norm_num)
  have h0366 : segsOk 20000000 1464100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0366 h0367 (by norm_num)
  have h0365 : segsOk 20000000 1460100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0365 h0366 (by norm_num)
  have h0364 : segsOk 20000000 1456100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0364 h0365 (by norm_num)
  have h0363 : segsOk 20000000 1452100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0363 h0364 (by norm_num)
  have h0362 : segsOk 20000000 1448100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0362 h0363 (by norm_num)
  have h0361 : segsOk 20000000 1444100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0361 h0362 (by norm_num)
  have h0360 : segsOk 20000000 1440100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0360 h0361 (by norm_num)
  have h0359 : segsOk 20000000 1436100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0359 h0360 (by norm_num)
  have h0358 : segsOk 20000000 1432100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0358 h0359 (by norm_num)
  have h0357 : segsOk 20000000 1428100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0357 h0358 (by norm_num)
  have h0356 : segsOk 20000000 1424100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0356 h0357 (by norm_num)
  have h0355 : segsOk 20000000 1420100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0355 h0356 (by norm_num)
  have h0354 : segsOk 20000000 1416100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0354 h0355 (by norm_num)
  have h0353 : segsOk 20000000 1412100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0353 h0354 (by norm_num)
  have h0352 : segsOk 20000000 1408100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0352 h0353 (by norm_num)
  have h0351 : segsOk 20000000 1404100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0351 h0352 (by norm_num)
  have h0350 : segsOk 20000000 1400100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0350 h0351 (by norm_num)
  exact h0350
end Grosswald.Direct
