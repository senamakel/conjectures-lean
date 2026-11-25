import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0100
import Grosswald.Direct.Run.B0101
import Grosswald.Direct.Run.B0102
import Grosswald.Direct.Run.B0103
import Grosswald.Direct.Run.B0104
import Grosswald.Direct.Run.B0105
import Grosswald.Direct.Run.B0106
import Grosswald.Direct.Run.B0107
import Grosswald.Direct.Run.B0108
import Grosswald.Direct.Run.B0109
import Grosswald.Direct.Run.B0110
import Grosswald.Direct.Run.B0111
import Grosswald.Direct.Run.B0112
import Grosswald.Direct.Run.B0113
import Grosswald.Direct.Run.B0114
import Grosswald.Direct.Run.B0115
import Grosswald.Direct.Run.B0116
import Grosswald.Direct.Run.B0117
import Grosswald.Direct.Run.B0118
import Grosswald.Direct.Run.B0119
import Grosswald.Direct.Run.B0120
import Grosswald.Direct.Run.B0121
import Grosswald.Direct.Run.B0122
import Grosswald.Direct.Run.B0123
import Grosswald.Direct.Run.B0124
import Grosswald.Direct.Run.B0125
import Grosswald.Direct.Run.B0126
import Grosswald.Direct.Run.B0127
import Grosswald.Direct.Run.B0128
import Grosswald.Direct.Run.B0129
import Grosswald.Direct.Run.B0130
import Grosswald.Direct.Run.B0131
import Grosswald.Direct.Run.B0132
import Grosswald.Direct.Run.B0133
import Grosswald.Direct.Run.B0134
import Grosswald.Direct.Run.B0135
import Grosswald.Direct.Run.B0136
import Grosswald.Direct.Run.B0137
import Grosswald.Direct.Run.B0138
import Grosswald.Direct.Run.B0139
import Grosswald.Direct.Run.B0140
import Grosswald.Direct.Run.B0141
import Grosswald.Direct.Run.B0142
import Grosswald.Direct.Run.B0143
import Grosswald.Direct.Run.B0144
import Grosswald.Direct.Run.B0145
import Grosswald.Direct.Run.B0146
import Grosswald.Direct.Run.B0147
import Grosswald.Direct.Run.B0148
import Grosswald.Direct.Run.B0149

namespace Grosswald.Direct
open GrosswaldCompute
theorem g02 : segsOk 20000000 400100000411 5000 = true := by
  have h0149 : segsOk 20000000 596100000411 100 = true := Run.b0149
  have h0148 : segsOk 20000000 592100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0148 h0149 (by norm_num)
  have h0147 : segsOk 20000000 588100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0147 h0148 (by norm_num)
  have h0146 : segsOk 20000000 584100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0146 h0147 (by norm_num)
  have h0145 : segsOk 20000000 580100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0145 h0146 (by norm_num)
  have h0144 : segsOk 20000000 576100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0144 h0145 (by norm_num)
  have h0143 : segsOk 20000000 572100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0143 h0144 (by norm_num)
  have h0142 : segsOk 20000000 568100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0142 h0143 (by norm_num)
  have h0141 : segsOk 20000000 564100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0141 h0142 (by norm_num)
  have h0140 : segsOk 20000000 560100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0140 h0141 (by norm_num)
  have h0139 : segsOk 20000000 556100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0139 h0140 (by norm_num)
  have h0138 : segsOk 20000000 552100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0138 h0139 (by norm_num)
  have h0137 : segsOk 20000000 548100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0137 h0138 (by norm_num)
  have h0136 : segsOk 20000000 544100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0136 h0137 (by norm_num)
  have h0135 : segsOk 20000000 540100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0135 h0136 (by norm_num)
  have h0134 : segsOk 20000000 536100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0134 h0135 (by norm_num)
  have h0133 : segsOk 20000000 532100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0133 h0134 (by norm_num)
  have h0132 : segsOk 20000000 528100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0132 h0133 (by norm_num)
  have h0131 : segsOk 20000000 524100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0131 h0132 (by norm_num)
  have h0130 : segsOk 20000000 520100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0130 h0131 (by norm_num)
  have h0129 : segsOk 20000000 516100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0129 h0130 (by norm_num)
  have h0128 : segsOk 20000000 512100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0128 h0129 (by norm_num)
  have h0127 : segsOk 20000000 508100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0127 h0128 (by norm_num)
  have h0126 : segsOk 20000000 504100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0126 h0127 (by norm_num)
  have h0125 : segsOk 20000000 500100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0125 h0126 (by norm_num)
  have h0124 : segsOk 20000000 496100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0124 h0125 (by norm_num)
  have h0123 : segsOk 20000000 492100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0123 h0124 (by norm_num)
  have h0122 : segsOk 20000000 488100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0122 h0123 (by norm_num)
  have h0121 : segsOk 20000000 484100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0121 h0122 (by norm_num)
  have h0120 : segsOk 20000000 480100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0120 h0121 (by norm_num)
  have h0119 : segsOk 20000000 476100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0119 h0120 (by norm_num)
  have h0118 : segsOk 20000000 472100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0118 h0119 (by norm_num)
  have h0117 : segsOk 20000000 468100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0117 h0118 (by norm_num)
  have h0116 : segsOk 20000000 464100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0116 h0117 (by norm_num)
  have h0115 : segsOk 20000000 460100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0115 h0116 (by norm_num)
  have h0114 : segsOk 20000000 456100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0114 h0115 (by norm_num)
  have h0113 : segsOk 20000000 452100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0113 h0114 (by norm_num)
  have h0112 : segsOk 20000000 448100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0112 h0113 (by norm_num)
  have h0111 : segsOk 20000000 444100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0111 h0112 (by norm_num)
  have h0110 : segsOk 20000000 440100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0110 h0111 (by norm_num)
  have h0109 : segsOk 20000000 436100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0109 h0110 (by norm_num)
  have h0108 : segsOk 20000000 432100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0108 h0109 (by norm_num)
  have h0107 : segsOk 20000000 428100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0107 h0108 (by norm_num)
  have h0106 : segsOk 20000000 424100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0106 h0107 (by norm_num)
  have h0105 : segsOk 20000000 420100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0105 h0106 (by norm_num)
  have h0104 : segsOk 20000000 416100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0104 h0105 (by norm_num)
  have h0103 : segsOk 20000000 412100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0103 h0104 (by norm_num)
  have h0102 : segsOk 20000000 408100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0102 h0103 (by norm_num)
  have h0101 : segsOk 20000000 404100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0101 h0102 (by norm_num)
  have h0100 : segsOk 20000000 400100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0100 h0101 (by norm_num)
  exact h0100
end Grosswald.Direct
