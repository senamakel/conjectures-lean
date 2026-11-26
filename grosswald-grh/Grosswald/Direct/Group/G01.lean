import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0050
import Grosswald.Direct.Run.B0051
import Grosswald.Direct.Run.B0052
import Grosswald.Direct.Run.B0053
import Grosswald.Direct.Run.B0054
import Grosswald.Direct.Run.B0055
import Grosswald.Direct.Run.B0056
import Grosswald.Direct.Run.B0057
import Grosswald.Direct.Run.B0058
import Grosswald.Direct.Run.B0059
import Grosswald.Direct.Run.B0060
import Grosswald.Direct.Run.B0061
import Grosswald.Direct.Run.B0062
import Grosswald.Direct.Run.B0063
import Grosswald.Direct.Run.B0064
import Grosswald.Direct.Run.B0065
import Grosswald.Direct.Run.B0066
import Grosswald.Direct.Run.B0067
import Grosswald.Direct.Run.B0068
import Grosswald.Direct.Run.B0069
import Grosswald.Direct.Run.B0070
import Grosswald.Direct.Run.B0071
import Grosswald.Direct.Run.B0072
import Grosswald.Direct.Run.B0073
import Grosswald.Direct.Run.B0074
import Grosswald.Direct.Run.B0075
import Grosswald.Direct.Run.B0076
import Grosswald.Direct.Run.B0077
import Grosswald.Direct.Run.B0078
import Grosswald.Direct.Run.B0079
import Grosswald.Direct.Run.B0080
import Grosswald.Direct.Run.B0081
import Grosswald.Direct.Run.B0082
import Grosswald.Direct.Run.B0083
import Grosswald.Direct.Run.B0084
import Grosswald.Direct.Run.B0085
import Grosswald.Direct.Run.B0086
import Grosswald.Direct.Run.B0087
import Grosswald.Direct.Run.B0088
import Grosswald.Direct.Run.B0089
import Grosswald.Direct.Run.B0090
import Grosswald.Direct.Run.B0091
import Grosswald.Direct.Run.B0092
import Grosswald.Direct.Run.B0093
import Grosswald.Direct.Run.B0094
import Grosswald.Direct.Run.B0095
import Grosswald.Direct.Run.B0096
import Grosswald.Direct.Run.B0097
import Grosswald.Direct.Run.B0098
import Grosswald.Direct.Run.B0099

namespace Grosswald.Direct
open GrosswaldCompute
theorem g01 : segsOk 20000000 200100000411 5000 = true := by
  have h0099 : segsOk 20000000 396100000411 100 = true := Run.b0099
  have h0098 : segsOk 20000000 392100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0098 h0099 (by norm_num)
  have h0097 : segsOk 20000000 388100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0097 h0098 (by norm_num)
  have h0096 : segsOk 20000000 384100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0096 h0097 (by norm_num)
  have h0095 : segsOk 20000000 380100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0095 h0096 (by norm_num)
  have h0094 : segsOk 20000000 376100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0094 h0095 (by norm_num)
  have h0093 : segsOk 20000000 372100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0093 h0094 (by norm_num)
  have h0092 : segsOk 20000000 368100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0092 h0093 (by norm_num)
  have h0091 : segsOk 20000000 364100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0091 h0092 (by norm_num)
  have h0090 : segsOk 20000000 360100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0090 h0091 (by norm_num)
  have h0089 : segsOk 20000000 356100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0089 h0090 (by norm_num)
  have h0088 : segsOk 20000000 352100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0088 h0089 (by norm_num)
  have h0087 : segsOk 20000000 348100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0087 h0088 (by norm_num)
  have h0086 : segsOk 20000000 344100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0086 h0087 (by norm_num)
  have h0085 : segsOk 20000000 340100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0085 h0086 (by norm_num)
  have h0084 : segsOk 20000000 336100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0084 h0085 (by norm_num)
  have h0083 : segsOk 20000000 332100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0083 h0084 (by norm_num)
  have h0082 : segsOk 20000000 328100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0082 h0083 (by norm_num)
  have h0081 : segsOk 20000000 324100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0081 h0082 (by norm_num)
  have h0080 : segsOk 20000000 320100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0080 h0081 (by norm_num)
  have h0079 : segsOk 20000000 316100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0079 h0080 (by norm_num)
  have h0078 : segsOk 20000000 312100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0078 h0079 (by norm_num)
  have h0077 : segsOk 20000000 308100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0077 h0078 (by norm_num)
  have h0076 : segsOk 20000000 304100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0076 h0077 (by norm_num)
  have h0075 : segsOk 20000000 300100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0075 h0076 (by norm_num)
  have h0074 : segsOk 20000000 296100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0074 h0075 (by norm_num)
  have h0073 : segsOk 20000000 292100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0073 h0074 (by norm_num)
  have h0072 : segsOk 20000000 288100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0072 h0073 (by norm_num)
  have h0071 : segsOk 20000000 284100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0071 h0072 (by norm_num)
  have h0070 : segsOk 20000000 280100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0070 h0071 (by norm_num)
  have h0069 : segsOk 20000000 276100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0069 h0070 (by norm_num)
  have h0068 : segsOk 20000000 272100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0068 h0069 (by norm_num)
  have h0067 : segsOk 20000000 268100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0067 h0068 (by norm_num)
  have h0066 : segsOk 20000000 264100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0066 h0067 (by norm_num)
  have h0065 : segsOk 20000000 260100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0065 h0066 (by norm_num)
  have h0064 : segsOk 20000000 256100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0064 h0065 (by norm_num)
  have h0063 : segsOk 20000000 252100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0063 h0064 (by norm_num)
  have h0062 : segsOk 20000000 248100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0062 h0063 (by norm_num)
  have h0061 : segsOk 20000000 244100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0061 h0062 (by norm_num)
  have h0060 : segsOk 20000000 240100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0060 h0061 (by norm_num)
  have h0059 : segsOk 20000000 236100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0059 h0060 (by norm_num)
  have h0058 : segsOk 20000000 232100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0058 h0059 (by norm_num)
  have h0057 : segsOk 20000000 228100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0057 h0058 (by norm_num)
  have h0056 : segsOk 20000000 224100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0056 h0057 (by norm_num)
  have h0055 : segsOk 20000000 220100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0055 h0056 (by norm_num)
  have h0054 : segsOk 20000000 216100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0054 h0055 (by norm_num)
  have h0053 : segsOk 20000000 212100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0053 h0054 (by norm_num)
  have h0052 : segsOk 20000000 208100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0052 h0053 (by norm_num)
  have h0051 : segsOk 20000000 204100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0051 h0052 (by norm_num)
  have h0050 : segsOk 20000000 200100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0050 h0051 (by norm_num)
  exact h0050
end Grosswald.Direct
