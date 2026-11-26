import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0150
import Grosswald.Direct.Run.B0151
import Grosswald.Direct.Run.B0152
import Grosswald.Direct.Run.B0153
import Grosswald.Direct.Run.B0154
import Grosswald.Direct.Run.B0155
import Grosswald.Direct.Run.B0156
import Grosswald.Direct.Run.B0157
import Grosswald.Direct.Run.B0158
import Grosswald.Direct.Run.B0159
import Grosswald.Direct.Run.B0160
import Grosswald.Direct.Run.B0161
import Grosswald.Direct.Run.B0162
import Grosswald.Direct.Run.B0163
import Grosswald.Direct.Run.B0164
import Grosswald.Direct.Run.B0165
import Grosswald.Direct.Run.B0166
import Grosswald.Direct.Run.B0167
import Grosswald.Direct.Run.B0168
import Grosswald.Direct.Run.B0169
import Grosswald.Direct.Run.B0170
import Grosswald.Direct.Run.B0171
import Grosswald.Direct.Run.B0172
import Grosswald.Direct.Run.B0173
import Grosswald.Direct.Run.B0174
import Grosswald.Direct.Run.B0175
import Grosswald.Direct.Run.B0176
import Grosswald.Direct.Run.B0177
import Grosswald.Direct.Run.B0178
import Grosswald.Direct.Run.B0179
import Grosswald.Direct.Run.B0180
import Grosswald.Direct.Run.B0181
import Grosswald.Direct.Run.B0182
import Grosswald.Direct.Run.B0183
import Grosswald.Direct.Run.B0184
import Grosswald.Direct.Run.B0185
import Grosswald.Direct.Run.B0186
import Grosswald.Direct.Run.B0187
import Grosswald.Direct.Run.B0188
import Grosswald.Direct.Run.B0189
import Grosswald.Direct.Run.B0190
import Grosswald.Direct.Run.B0191
import Grosswald.Direct.Run.B0192
import Grosswald.Direct.Run.B0193
import Grosswald.Direct.Run.B0194
import Grosswald.Direct.Run.B0195
import Grosswald.Direct.Run.B0196
import Grosswald.Direct.Run.B0197
import Grosswald.Direct.Run.B0198
import Grosswald.Direct.Run.B0199

namespace Grosswald.Direct
open GrosswaldCompute
theorem g03 : segsOk 20000000 600100000411 5000 = true := by
  have h0199 : segsOk 20000000 796100000411 100 = true := Run.b0199
  have h0198 : segsOk 20000000 792100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0198 h0199 (by norm_num)
  have h0197 : segsOk 20000000 788100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0197 h0198 (by norm_num)
  have h0196 : segsOk 20000000 784100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0196 h0197 (by norm_num)
  have h0195 : segsOk 20000000 780100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0195 h0196 (by norm_num)
  have h0194 : segsOk 20000000 776100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0194 h0195 (by norm_num)
  have h0193 : segsOk 20000000 772100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0193 h0194 (by norm_num)
  have h0192 : segsOk 20000000 768100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0192 h0193 (by norm_num)
  have h0191 : segsOk 20000000 764100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0191 h0192 (by norm_num)
  have h0190 : segsOk 20000000 760100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0190 h0191 (by norm_num)
  have h0189 : segsOk 20000000 756100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0189 h0190 (by norm_num)
  have h0188 : segsOk 20000000 752100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0188 h0189 (by norm_num)
  have h0187 : segsOk 20000000 748100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0187 h0188 (by norm_num)
  have h0186 : segsOk 20000000 744100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0186 h0187 (by norm_num)
  have h0185 : segsOk 20000000 740100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0185 h0186 (by norm_num)
  have h0184 : segsOk 20000000 736100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0184 h0185 (by norm_num)
  have h0183 : segsOk 20000000 732100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0183 h0184 (by norm_num)
  have h0182 : segsOk 20000000 728100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0182 h0183 (by norm_num)
  have h0181 : segsOk 20000000 724100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0181 h0182 (by norm_num)
  have h0180 : segsOk 20000000 720100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0180 h0181 (by norm_num)
  have h0179 : segsOk 20000000 716100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0179 h0180 (by norm_num)
  have h0178 : segsOk 20000000 712100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0178 h0179 (by norm_num)
  have h0177 : segsOk 20000000 708100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0177 h0178 (by norm_num)
  have h0176 : segsOk 20000000 704100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0176 h0177 (by norm_num)
  have h0175 : segsOk 20000000 700100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0175 h0176 (by norm_num)
  have h0174 : segsOk 20000000 696100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0174 h0175 (by norm_num)
  have h0173 : segsOk 20000000 692100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0173 h0174 (by norm_num)
  have h0172 : segsOk 20000000 688100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0172 h0173 (by norm_num)
  have h0171 : segsOk 20000000 684100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0171 h0172 (by norm_num)
  have h0170 : segsOk 20000000 680100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0170 h0171 (by norm_num)
  have h0169 : segsOk 20000000 676100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0169 h0170 (by norm_num)
  have h0168 : segsOk 20000000 672100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0168 h0169 (by norm_num)
  have h0167 : segsOk 20000000 668100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0167 h0168 (by norm_num)
  have h0166 : segsOk 20000000 664100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0166 h0167 (by norm_num)
  have h0165 : segsOk 20000000 660100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0165 h0166 (by norm_num)
  have h0164 : segsOk 20000000 656100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0164 h0165 (by norm_num)
  have h0163 : segsOk 20000000 652100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0163 h0164 (by norm_num)
  have h0162 : segsOk 20000000 648100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0162 h0163 (by norm_num)
  have h0161 : segsOk 20000000 644100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0161 h0162 (by norm_num)
  have h0160 : segsOk 20000000 640100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0160 h0161 (by norm_num)
  have h0159 : segsOk 20000000 636100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0159 h0160 (by norm_num)
  have h0158 : segsOk 20000000 632100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0158 h0159 (by norm_num)
  have h0157 : segsOk 20000000 628100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0157 h0158 (by norm_num)
  have h0156 : segsOk 20000000 624100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0156 h0157 (by norm_num)
  have h0155 : segsOk 20000000 620100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0155 h0156 (by norm_num)
  have h0154 : segsOk 20000000 616100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0154 h0155 (by norm_num)
  have h0153 : segsOk 20000000 612100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0153 h0154 (by norm_num)
  have h0152 : segsOk 20000000 608100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0152 h0153 (by norm_num)
  have h0151 : segsOk 20000000 604100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0151 h0152 (by norm_num)
  have h0150 : segsOk 20000000 600100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0150 h0151 (by norm_num)
  exact h0150
end Grosswald.Direct
