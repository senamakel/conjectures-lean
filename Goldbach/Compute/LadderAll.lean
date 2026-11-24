import Goldbach.Compute.Ladder
import Goldbach.Compute.LadderChunks.L000
import Goldbach.Compute.LadderChunks.L001
import Goldbach.Compute.LadderChunks.L002
import Goldbach.Compute.LadderChunks.L003
import Goldbach.Compute.LadderChunks.L004
import Goldbach.Compute.LadderChunks.L005
import Goldbach.Compute.LadderChunks.L006
import Goldbach.Compute.LadderChunks.L007
import Goldbach.Compute.LadderChunks.L008
import Goldbach.Compute.LadderChunks.L009
import Goldbach.Compute.LadderChunks.L010
import Goldbach.Compute.LadderChunks.L011
import Goldbach.Compute.LadderChunks.L012
import Goldbach.Compute.LadderChunks.L013
import Goldbach.Compute.LadderChunks.L014
import Goldbach.Compute.LadderChunks.L015
import Goldbach.Compute.LadderChunks.L016
import Goldbach.Compute.LadderChunks.L017
import Goldbach.Compute.LadderChunks.L018
import Goldbach.Compute.LadderChunks.L019
import Goldbach.Compute.LadderChunks.L020
import Goldbach.Compute.LadderChunks.L021
import Goldbach.Compute.LadderChunks.L022
import Goldbach.Compute.LadderChunks.L023
import Goldbach.Compute.LadderChunks.L024
import Goldbach.Compute.LadderChunks.L025
import Goldbach.Compute.LadderChunks.L026
import Goldbach.Compute.LadderChunks.L027
import Goldbach.Compute.LadderChunks.L028
import Goldbach.Compute.LadderChunks.L029
import Goldbach.Compute.LadderChunks.L030
import Goldbach.Compute.LadderChunks.L031
import Goldbach.Compute.LadderChunks.L032
import Goldbach.Compute.LadderChunks.L033
import Goldbach.Compute.LadderChunks.L034
import Goldbach.Compute.LadderChunks.L035
import Goldbach.Compute.LadderChunks.L036
import Goldbach.Compute.LadderChunks.L037
import Goldbach.Compute.LadderChunks.L038
import Goldbach.Compute.LadderChunks.L039
import Goldbach.Compute.LadderChunks.L040
import Goldbach.Compute.LadderChunks.L041
import Goldbach.Compute.LadderChunks.L042
import Goldbach.Compute.LadderChunks.L043
import Goldbach.Compute.LadderChunks.L044
import Goldbach.Compute.LadderChunks.L045
import Goldbach.Compute.LadderChunks.L046
import Goldbach.Compute.LadderChunks.L047
import Goldbach.Compute.LadderChunks.L048
import Goldbach.Compute.LadderChunks.L049
import Goldbach.Compute.LadderChunks.L050
import Goldbach.Compute.LadderChunks.L051
import Goldbach.Compute.LadderChunks.L052
import Goldbach.Compute.LadderChunks.L053
import Goldbach.Compute.LadderChunks.L054
import Goldbach.Compute.LadderChunks.L055
import Goldbach.Compute.LadderChunks.L056
import Goldbach.Compute.LadderChunks.L057
import Goldbach.Compute.LadderChunks.L058
import Goldbach.Compute.LadderChunks.L059
import Goldbach.Compute.LadderChunks.L060
import Goldbach.Compute.LadderChunks.L061
import Goldbach.Compute.LadderChunks.L062
import Goldbach.Compute.LadderChunks.L063
import Goldbach.Compute.LadderChunks.L064
import Goldbach.Compute.LadderChunks.L065
import Goldbach.Compute.LadderChunks.L066
import Goldbach.Compute.LadderChunks.L067
import Goldbach.Compute.LadderChunks.L068
import Goldbach.Compute.LadderChunks.L069
import Goldbach.Compute.LadderChunks.L070
import Goldbach.Compute.LadderChunks.L071
import Goldbach.Compute.LadderChunks.L072
import Goldbach.Compute.LadderChunks.L073
import Goldbach.Compute.LadderChunks.L074
import Goldbach.Compute.LadderChunks.L075
import Goldbach.Compute.LadderChunks.L076
import Goldbach.Compute.LadderChunks.L077
import Goldbach.Compute.LadderChunks.L078
import Goldbach.Compute.LadderChunks.L079
import Goldbach.Compute.LadderChunks.L080
import Goldbach.Compute.LadderChunks.L081
import Goldbach.Compute.LadderChunks.L082
import Goldbach.Compute.LadderChunks.L083
import Goldbach.Compute.LadderChunks.L084
import Goldbach.Compute.LadderChunks.L085
import Goldbach.Compute.LadderChunks.L086
import Goldbach.Compute.LadderChunks.L087
import Goldbach.Compute.LadderChunks.L088
import Goldbach.Compute.LadderChunks.L089
import Goldbach.Compute.LadderChunks.L090
import Goldbach.Compute.LadderChunks.L091
import Goldbach.Compute.LadderChunks.L092
import Goldbach.Compute.LadderChunks.L093
import Goldbach.Compute.LadderChunks.L094
import Goldbach.Compute.LadderChunks.L095
import Goldbach.Compute.LadderChunks.L096
import Goldbach.Compute.LadderChunks.L097
import Goldbach.Compute.LadderChunks.L098
import Goldbach.Compute.LadderChunks.L099

/-!
# A prime ladder with gaps `≤ 1999999999996` from `2·10¹²` to `10²⁰` (verified computation)

The 100 chunks `ladder_chunk_j` (files `LadderChunks/L*.lean`) each check
`ladderCover 1999999999996 lo_j hi_j = true` by `native_decide`, with `lo_0 = 2000000000000`,
`lo_j = j * 1000000000000000000` for `j ≥ 1` and `hi_j = (j + 1) * 1000000000000000000`.
-/

namespace Goldbach.Check

theorem ladder_chunks_ok : ∀ j < 100,
    ladderCover 1999999999996 (if j = 0 then 2000000000000 else j * 1000000000000000000) ((j + 1) * 1000000000000000000) = true := by
  intro j hj
  interval_cases j
  · exact ladder_chunk_0
  · exact ladder_chunk_1
  · exact ladder_chunk_2
  · exact ladder_chunk_3
  · exact ladder_chunk_4
  · exact ladder_chunk_5
  · exact ladder_chunk_6
  · exact ladder_chunk_7
  · exact ladder_chunk_8
  · exact ladder_chunk_9
  · exact ladder_chunk_10
  · exact ladder_chunk_11
  · exact ladder_chunk_12
  · exact ladder_chunk_13
  · exact ladder_chunk_14
  · exact ladder_chunk_15
  · exact ladder_chunk_16
  · exact ladder_chunk_17
  · exact ladder_chunk_18
  · exact ladder_chunk_19
  · exact ladder_chunk_20
  · exact ladder_chunk_21
  · exact ladder_chunk_22
  · exact ladder_chunk_23
  · exact ladder_chunk_24
  · exact ladder_chunk_25
  · exact ladder_chunk_26
  · exact ladder_chunk_27
  · exact ladder_chunk_28
  · exact ladder_chunk_29
  · exact ladder_chunk_30
  · exact ladder_chunk_31
  · exact ladder_chunk_32
  · exact ladder_chunk_33
  · exact ladder_chunk_34
  · exact ladder_chunk_35
  · exact ladder_chunk_36
  · exact ladder_chunk_37
  · exact ladder_chunk_38
  · exact ladder_chunk_39
  · exact ladder_chunk_40
  · exact ladder_chunk_41
  · exact ladder_chunk_42
  · exact ladder_chunk_43
  · exact ladder_chunk_44
  · exact ladder_chunk_45
  · exact ladder_chunk_46
  · exact ladder_chunk_47
  · exact ladder_chunk_48
  · exact ladder_chunk_49
  · exact ladder_chunk_50
  · exact ladder_chunk_51
  · exact ladder_chunk_52
  · exact ladder_chunk_53
  · exact ladder_chunk_54
  · exact ladder_chunk_55
  · exact ladder_chunk_56
  · exact ladder_chunk_57
  · exact ladder_chunk_58
  · exact ladder_chunk_59
  · exact ladder_chunk_60
  · exact ladder_chunk_61
  · exact ladder_chunk_62
  · exact ladder_chunk_63
  · exact ladder_chunk_64
  · exact ladder_chunk_65
  · exact ladder_chunk_66
  · exact ladder_chunk_67
  · exact ladder_chunk_68
  · exact ladder_chunk_69
  · exact ladder_chunk_70
  · exact ladder_chunk_71
  · exact ladder_chunk_72
  · exact ladder_chunk_73
  · exact ladder_chunk_74
  · exact ladder_chunk_75
  · exact ladder_chunk_76
  · exact ladder_chunk_77
  · exact ladder_chunk_78
  · exact ladder_chunk_79
  · exact ladder_chunk_80
  · exact ladder_chunk_81
  · exact ladder_chunk_82
  · exact ladder_chunk_83
  · exact ladder_chunk_84
  · exact ladder_chunk_85
  · exact ladder_chunk_86
  · exact ladder_chunk_87
  · exact ladder_chunk_88
  · exact ladder_chunk_89
  · exact ladder_chunk_90
  · exact ladder_chunk_91
  · exact ladder_chunk_92
  · exact ladder_chunk_93
  · exact ladder_chunk_94
  · exact ladder_chunk_95
  · exact ladder_chunk_96
  · exact ladder_chunk_97
  · exact ladder_chunk_98
  · exact ladder_chunk_99

end Goldbach.Check
