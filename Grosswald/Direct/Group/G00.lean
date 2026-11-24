import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B0000
import Grosswald.Direct.Run.B0001
import Grosswald.Direct.Run.B0002
import Grosswald.Direct.Run.B0003
import Grosswald.Direct.Run.B0004
import Grosswald.Direct.Run.B0005
import Grosswald.Direct.Run.B0006
import Grosswald.Direct.Run.B0007
import Grosswald.Direct.Run.B0008
import Grosswald.Direct.Run.B0009
import Grosswald.Direct.Run.B0010
import Grosswald.Direct.Run.B0011
import Grosswald.Direct.Run.B0012
import Grosswald.Direct.Run.B0013
import Grosswald.Direct.Run.B0014
import Grosswald.Direct.Run.B0015
import Grosswald.Direct.Run.B0016
import Grosswald.Direct.Run.B0017
import Grosswald.Direct.Run.B0018
import Grosswald.Direct.Run.B0019
import Grosswald.Direct.Run.B0020
import Grosswald.Direct.Run.B0021
import Grosswald.Direct.Run.B0022
import Grosswald.Direct.Run.B0023
import Grosswald.Direct.Run.B0024
import Grosswald.Direct.Run.B0025
import Grosswald.Direct.Run.B0026
import Grosswald.Direct.Run.B0027
import Grosswald.Direct.Run.B0028
import Grosswald.Direct.Run.B0029
import Grosswald.Direct.Run.B0030
import Grosswald.Direct.Run.B0031
import Grosswald.Direct.Run.B0032
import Grosswald.Direct.Run.B0033
import Grosswald.Direct.Run.B0034
import Grosswald.Direct.Run.B0035
import Grosswald.Direct.Run.B0036
import Grosswald.Direct.Run.B0037
import Grosswald.Direct.Run.B0038
import Grosswald.Direct.Run.B0039
import Grosswald.Direct.Run.B0040
import Grosswald.Direct.Run.B0041
import Grosswald.Direct.Run.B0042
import Grosswald.Direct.Run.B0043
import Grosswald.Direct.Run.B0044
import Grosswald.Direct.Run.B0045
import Grosswald.Direct.Run.B0046
import Grosswald.Direct.Run.B0047
import Grosswald.Direct.Run.B0048
import Grosswald.Direct.Run.B0049

namespace Grosswald.Direct
open GrosswaldCompute
theorem g00 : segsOk 20000000 100000411 5000 = true := by
  have h0049 : segsOk 20000000 196100000411 100 = true := Run.b0049
  have h0048 : segsOk 20000000 192100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b0048 h0049 (by norm_num)
  have h0047 : segsOk 20000000 188100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b0047 h0048 (by norm_num)
  have h0046 : segsOk 20000000 184100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b0046 h0047 (by norm_num)
  have h0045 : segsOk 20000000 180100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b0045 h0046 (by norm_num)
  have h0044 : segsOk 20000000 176100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b0044 h0045 (by norm_num)
  have h0043 : segsOk 20000000 172100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b0043 h0044 (by norm_num)
  have h0042 : segsOk 20000000 168100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b0042 h0043 (by norm_num)
  have h0041 : segsOk 20000000 164100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b0041 h0042 (by norm_num)
  have h0040 : segsOk 20000000 160100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b0040 h0041 (by norm_num)
  have h0039 : segsOk 20000000 156100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b0039 h0040 (by norm_num)
  have h0038 : segsOk 20000000 152100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b0038 h0039 (by norm_num)
  have h0037 : segsOk 20000000 148100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b0037 h0038 (by norm_num)
  have h0036 : segsOk 20000000 144100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b0036 h0037 (by norm_num)
  have h0035 : segsOk 20000000 140100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b0035 h0036 (by norm_num)
  have h0034 : segsOk 20000000 136100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b0034 h0035 (by norm_num)
  have h0033 : segsOk 20000000 132100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b0033 h0034 (by norm_num)
  have h0032 : segsOk 20000000 128100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b0032 h0033 (by norm_num)
  have h0031 : segsOk 20000000 124100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b0031 h0032 (by norm_num)
  have h0030 : segsOk 20000000 120100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b0030 h0031 (by norm_num)
  have h0029 : segsOk 20000000 116100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b0029 h0030 (by norm_num)
  have h0028 : segsOk 20000000 112100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b0028 h0029 (by norm_num)
  have h0027 : segsOk 20000000 108100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b0027 h0028 (by norm_num)
  have h0026 : segsOk 20000000 104100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b0026 h0027 (by norm_num)
  have h0025 : segsOk 20000000 100100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b0025 h0026 (by norm_num)
  have h0024 : segsOk 20000000 96100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b0024 h0025 (by norm_num)
  have h0023 : segsOk 20000000 92100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b0023 h0024 (by norm_num)
  have h0022 : segsOk 20000000 88100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b0022 h0023 (by norm_num)
  have h0021 : segsOk 20000000 84100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b0021 h0022 (by norm_num)
  have h0020 : segsOk 20000000 80100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b0020 h0021 (by norm_num)
  have h0019 : segsOk 20000000 76100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b0019 h0020 (by norm_num)
  have h0018 : segsOk 20000000 72100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b0018 h0019 (by norm_num)
  have h0017 : segsOk 20000000 68100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b0017 h0018 (by norm_num)
  have h0016 : segsOk 20000000 64100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b0016 h0017 (by norm_num)
  have h0015 : segsOk 20000000 60100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b0015 h0016 (by norm_num)
  have h0014 : segsOk 20000000 56100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b0014 h0015 (by norm_num)
  have h0013 : segsOk 20000000 52100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b0013 h0014 (by norm_num)
  have h0012 : segsOk 20000000 48100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b0012 h0013 (by norm_num)
  have h0011 : segsOk 20000000 44100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b0011 h0012 (by norm_num)
  have h0010 : segsOk 20000000 40100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b0010 h0011 (by norm_num)
  have h0009 : segsOk 20000000 36100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b0009 h0010 (by norm_num)
  have h0008 : segsOk 20000000 32100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b0008 h0009 (by norm_num)
  have h0007 : segsOk 20000000 28100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b0007 h0008 (by norm_num)
  have h0006 : segsOk 20000000 24100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b0006 h0007 (by norm_num)
  have h0005 : segsOk 20000000 20100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b0005 h0006 (by norm_num)
  have h0004 : segsOk 20000000 16100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b0004 h0005 (by norm_num)
  have h0003 : segsOk 20000000 12100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b0003 h0004 (by norm_num)
  have h0002 : segsOk 20000000 8100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b0002 h0003 (by norm_num)
  have h0001 : segsOk 20000000 4100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b0001 h0002 (by norm_num)
  have h0000 : segsOk 20000000 100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b0000 h0001 (by norm_num)
  exact h0000
end Grosswald.Direct
