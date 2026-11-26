import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0200
import Grosswald.Direct.Run.B0201
import Grosswald.Direct.Run.B0202
import Grosswald.Direct.Run.B0203
import Grosswald.Direct.Run.B0204
import Grosswald.Direct.Run.B0205
import Grosswald.Direct.Run.B0206
import Grosswald.Direct.Run.B0207
import Grosswald.Direct.Run.B0208
import Grosswald.Direct.Run.B0209
import Grosswald.Direct.Run.B0210
import Grosswald.Direct.Run.B0211
import Grosswald.Direct.Run.B0212
import Grosswald.Direct.Run.B0213
import Grosswald.Direct.Run.B0214
import Grosswald.Direct.Run.B0215
import Grosswald.Direct.Run.B0216
import Grosswald.Direct.Run.B0217
import Grosswald.Direct.Run.B0218
import Grosswald.Direct.Run.B0219
import Grosswald.Direct.Run.B0220
import Grosswald.Direct.Run.B0221
import Grosswald.Direct.Run.B0222
import Grosswald.Direct.Run.B0223
import Grosswald.Direct.Run.B0224
import Grosswald.Direct.Run.B0225
import Grosswald.Direct.Run.B0226
import Grosswald.Direct.Run.B0227
import Grosswald.Direct.Run.B0228
import Grosswald.Direct.Run.B0229
import Grosswald.Direct.Run.B0230
import Grosswald.Direct.Run.B0231
import Grosswald.Direct.Run.B0232
import Grosswald.Direct.Run.B0233
import Grosswald.Direct.Run.B0234
import Grosswald.Direct.Run.B0235
import Grosswald.Direct.Run.B0236
import Grosswald.Direct.Run.B0237
import Grosswald.Direct.Run.B0238
import Grosswald.Direct.Run.B0239
import Grosswald.Direct.Run.B0240
import Grosswald.Direct.Run.B0241
import Grosswald.Direct.Run.B0242
import Grosswald.Direct.Run.B0243
import Grosswald.Direct.Run.B0244
import Grosswald.Direct.Run.B0245
import Grosswald.Direct.Run.B0246
import Grosswald.Direct.Run.B0247
import Grosswald.Direct.Run.B0248
import Grosswald.Direct.Run.B0249

namespace Grosswald.Direct
open GrosswaldCompute
theorem g04 : segsOk 20000000 800100000411 5000 = true := by
  have h0249 : segsOk 20000000 996100000411 100 = true := Run.b0249
  have h0248 : segsOk 20000000 992100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0248 h0249 (by norm_num)
  have h0247 : segsOk 20000000 988100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0247 h0248 (by norm_num)
  have h0246 : segsOk 20000000 984100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0246 h0247 (by norm_num)
  have h0245 : segsOk 20000000 980100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0245 h0246 (by norm_num)
  have h0244 : segsOk 20000000 976100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0244 h0245 (by norm_num)
  have h0243 : segsOk 20000000 972100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0243 h0244 (by norm_num)
  have h0242 : segsOk 20000000 968100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0242 h0243 (by norm_num)
  have h0241 : segsOk 20000000 964100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0241 h0242 (by norm_num)
  have h0240 : segsOk 20000000 960100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0240 h0241 (by norm_num)
  have h0239 : segsOk 20000000 956100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0239 h0240 (by norm_num)
  have h0238 : segsOk 20000000 952100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0238 h0239 (by norm_num)
  have h0237 : segsOk 20000000 948100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0237 h0238 (by norm_num)
  have h0236 : segsOk 20000000 944100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0236 h0237 (by norm_num)
  have h0235 : segsOk 20000000 940100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0235 h0236 (by norm_num)
  have h0234 : segsOk 20000000 936100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0234 h0235 (by norm_num)
  have h0233 : segsOk 20000000 932100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0233 h0234 (by norm_num)
  have h0232 : segsOk 20000000 928100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0232 h0233 (by norm_num)
  have h0231 : segsOk 20000000 924100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0231 h0232 (by norm_num)
  have h0230 : segsOk 20000000 920100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0230 h0231 (by norm_num)
  have h0229 : segsOk 20000000 916100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0229 h0230 (by norm_num)
  have h0228 : segsOk 20000000 912100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0228 h0229 (by norm_num)
  have h0227 : segsOk 20000000 908100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0227 h0228 (by norm_num)
  have h0226 : segsOk 20000000 904100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0226 h0227 (by norm_num)
  have h0225 : segsOk 20000000 900100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0225 h0226 (by norm_num)
  have h0224 : segsOk 20000000 896100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0224 h0225 (by norm_num)
  have h0223 : segsOk 20000000 892100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0223 h0224 (by norm_num)
  have h0222 : segsOk 20000000 888100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0222 h0223 (by norm_num)
  have h0221 : segsOk 20000000 884100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0221 h0222 (by norm_num)
  have h0220 : segsOk 20000000 880100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0220 h0221 (by norm_num)
  have h0219 : segsOk 20000000 876100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0219 h0220 (by norm_num)
  have h0218 : segsOk 20000000 872100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0218 h0219 (by norm_num)
  have h0217 : segsOk 20000000 868100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0217 h0218 (by norm_num)
  have h0216 : segsOk 20000000 864100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0216 h0217 (by norm_num)
  have h0215 : segsOk 20000000 860100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0215 h0216 (by norm_num)
  have h0214 : segsOk 20000000 856100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0214 h0215 (by norm_num)
  have h0213 : segsOk 20000000 852100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0213 h0214 (by norm_num)
  have h0212 : segsOk 20000000 848100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0212 h0213 (by norm_num)
  have h0211 : segsOk 20000000 844100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0211 h0212 (by norm_num)
  have h0210 : segsOk 20000000 840100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0210 h0211 (by norm_num)
  have h0209 : segsOk 20000000 836100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0209 h0210 (by norm_num)
  have h0208 : segsOk 20000000 832100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0208 h0209 (by norm_num)
  have h0207 : segsOk 20000000 828100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0207 h0208 (by norm_num)
  have h0206 : segsOk 20000000 824100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0206 h0207 (by norm_num)
  have h0205 : segsOk 20000000 820100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0205 h0206 (by norm_num)
  have h0204 : segsOk 20000000 816100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0204 h0205 (by norm_num)
  have h0203 : segsOk 20000000 812100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0203 h0204 (by norm_num)
  have h0202 : segsOk 20000000 808100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0202 h0203 (by norm_num)
  have h0201 : segsOk 20000000 804100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0201 h0202 (by norm_num)
  have h0200 : segsOk 20000000 800100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0200 h0201 (by norm_num)
  exact h0200
end Grosswald.Direct
