import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0250
import Grosswald.Direct.Run.B0251
import Grosswald.Direct.Run.B0252
import Grosswald.Direct.Run.B0253
import Grosswald.Direct.Run.B0254
import Grosswald.Direct.Run.B0255
import Grosswald.Direct.Run.B0256
import Grosswald.Direct.Run.B0257
import Grosswald.Direct.Run.B0258
import Grosswald.Direct.Run.B0259
import Grosswald.Direct.Run.B0260
import Grosswald.Direct.Run.B0261
import Grosswald.Direct.Run.B0262
import Grosswald.Direct.Run.B0263
import Grosswald.Direct.Run.B0264
import Grosswald.Direct.Run.B0265
import Grosswald.Direct.Run.B0266
import Grosswald.Direct.Run.B0267
import Grosswald.Direct.Run.B0268
import Grosswald.Direct.Run.B0269
import Grosswald.Direct.Run.B0270
import Grosswald.Direct.Run.B0271
import Grosswald.Direct.Run.B0272
import Grosswald.Direct.Run.B0273
import Grosswald.Direct.Run.B0274
import Grosswald.Direct.Run.B0275
import Grosswald.Direct.Run.B0276
import Grosswald.Direct.Run.B0277
import Grosswald.Direct.Run.B0278
import Grosswald.Direct.Run.B0279
import Grosswald.Direct.Run.B0280
import Grosswald.Direct.Run.B0281
import Grosswald.Direct.Run.B0282
import Grosswald.Direct.Run.B0283
import Grosswald.Direct.Run.B0284
import Grosswald.Direct.Run.B0285
import Grosswald.Direct.Run.B0286
import Grosswald.Direct.Run.B0287
import Grosswald.Direct.Run.B0288
import Grosswald.Direct.Run.B0289
import Grosswald.Direct.Run.B0290
import Grosswald.Direct.Run.B0291
import Grosswald.Direct.Run.B0292
import Grosswald.Direct.Run.B0293
import Grosswald.Direct.Run.B0294
import Grosswald.Direct.Run.B0295
import Grosswald.Direct.Run.B0296
import Grosswald.Direct.Run.B0297
import Grosswald.Direct.Run.B0298
import Grosswald.Direct.Run.B0299

namespace Grosswald.Direct
open GrosswaldCompute
theorem g05 : segsOk 20000000 1000100000411 5000 = true := by
  have h0299 : segsOk 20000000 1196100000411 100 = true := Run.b0299
  have h0298 : segsOk 20000000 1192100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0298 h0299 (by norm_num)
  have h0297 : segsOk 20000000 1188100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0297 h0298 (by norm_num)
  have h0296 : segsOk 20000000 1184100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0296 h0297 (by norm_num)
  have h0295 : segsOk 20000000 1180100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0295 h0296 (by norm_num)
  have h0294 : segsOk 20000000 1176100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0294 h0295 (by norm_num)
  have h0293 : segsOk 20000000 1172100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0293 h0294 (by norm_num)
  have h0292 : segsOk 20000000 1168100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0292 h0293 (by norm_num)
  have h0291 : segsOk 20000000 1164100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0291 h0292 (by norm_num)
  have h0290 : segsOk 20000000 1160100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0290 h0291 (by norm_num)
  have h0289 : segsOk 20000000 1156100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0289 h0290 (by norm_num)
  have h0288 : segsOk 20000000 1152100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0288 h0289 (by norm_num)
  have h0287 : segsOk 20000000 1148100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0287 h0288 (by norm_num)
  have h0286 : segsOk 20000000 1144100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0286 h0287 (by norm_num)
  have h0285 : segsOk 20000000 1140100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0285 h0286 (by norm_num)
  have h0284 : segsOk 20000000 1136100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0284 h0285 (by norm_num)
  have h0283 : segsOk 20000000 1132100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0283 h0284 (by norm_num)
  have h0282 : segsOk 20000000 1128100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0282 h0283 (by norm_num)
  have h0281 : segsOk 20000000 1124100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0281 h0282 (by norm_num)
  have h0280 : segsOk 20000000 1120100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0280 h0281 (by norm_num)
  have h0279 : segsOk 20000000 1116100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0279 h0280 (by norm_num)
  have h0278 : segsOk 20000000 1112100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0278 h0279 (by norm_num)
  have h0277 : segsOk 20000000 1108100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0277 h0278 (by norm_num)
  have h0276 : segsOk 20000000 1104100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0276 h0277 (by norm_num)
  have h0275 : segsOk 20000000 1100100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0275 h0276 (by norm_num)
  have h0274 : segsOk 20000000 1096100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0274 h0275 (by norm_num)
  have h0273 : segsOk 20000000 1092100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0273 h0274 (by norm_num)
  have h0272 : segsOk 20000000 1088100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0272 h0273 (by norm_num)
  have h0271 : segsOk 20000000 1084100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0271 h0272 (by norm_num)
  have h0270 : segsOk 20000000 1080100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0270 h0271 (by norm_num)
  have h0269 : segsOk 20000000 1076100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0269 h0270 (by norm_num)
  have h0268 : segsOk 20000000 1072100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0268 h0269 (by norm_num)
  have h0267 : segsOk 20000000 1068100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0267 h0268 (by norm_num)
  have h0266 : segsOk 20000000 1064100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0266 h0267 (by norm_num)
  have h0265 : segsOk 20000000 1060100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0265 h0266 (by norm_num)
  have h0264 : segsOk 20000000 1056100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0264 h0265 (by norm_num)
  have h0263 : segsOk 20000000 1052100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0263 h0264 (by norm_num)
  have h0262 : segsOk 20000000 1048100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0262 h0263 (by norm_num)
  have h0261 : segsOk 20000000 1044100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0261 h0262 (by norm_num)
  have h0260 : segsOk 20000000 1040100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0260 h0261 (by norm_num)
  have h0259 : segsOk 20000000 1036100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0259 h0260 (by norm_num)
  have h0258 : segsOk 20000000 1032100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0258 h0259 (by norm_num)
  have h0257 : segsOk 20000000 1028100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0257 h0258 (by norm_num)
  have h0256 : segsOk 20000000 1024100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0256 h0257 (by norm_num)
  have h0255 : segsOk 20000000 1020100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0255 h0256 (by norm_num)
  have h0254 : segsOk 20000000 1016100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0254 h0255 (by norm_num)
  have h0253 : segsOk 20000000 1012100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0253 h0254 (by norm_num)
  have h0252 : segsOk 20000000 1008100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0252 h0253 (by norm_num)
  have h0251 : segsOk 20000000 1004100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0251 h0252 (by norm_num)
  have h0250 : segsOk 20000000 1000100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0250 h0251 (by norm_num)
  exact h0250
end Grosswald.Direct
