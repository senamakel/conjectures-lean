import Grosswald.Direct.Sound
import Grosswald.Direct.Run.B2000
import Grosswald.Direct.Run.B2001
import Grosswald.Direct.Run.B2002
import Grosswald.Direct.Run.B2003
import Grosswald.Direct.Run.B2004
import Grosswald.Direct.Run.B2005
import Grosswald.Direct.Run.B2006
import Grosswald.Direct.Run.B2007
import Grosswald.Direct.Run.B2008
import Grosswald.Direct.Run.B2009
import Grosswald.Direct.Run.B2010
import Grosswald.Direct.Run.B2011
import Grosswald.Direct.Run.B2012
import Grosswald.Direct.Run.B2013
import Grosswald.Direct.Run.B2014
import Grosswald.Direct.Run.B2015
import Grosswald.Direct.Run.B2016
import Grosswald.Direct.Run.B2017
import Grosswald.Direct.Run.B2018
import Grosswald.Direct.Run.B2019
import Grosswald.Direct.Run.B2020
import Grosswald.Direct.Run.B2021
import Grosswald.Direct.Run.B2022
import Grosswald.Direct.Run.B2023
import Grosswald.Direct.Run.B2024
import Grosswald.Direct.Run.B2025
import Grosswald.Direct.Run.B2026
import Grosswald.Direct.Run.B2027
import Grosswald.Direct.Run.B2028
import Grosswald.Direct.Run.B2029
import Grosswald.Direct.Run.B2030
import Grosswald.Direct.Run.B2031
import Grosswald.Direct.Run.B2032
import Grosswald.Direct.Run.B2033
import Grosswald.Direct.Run.B2034
import Grosswald.Direct.Run.B2035
import Grosswald.Direct.Run.B2036
import Grosswald.Direct.Run.B2037
import Grosswald.Direct.Run.B2038
import Grosswald.Direct.Run.B2039
import Grosswald.Direct.Run.B2040
import Grosswald.Direct.Run.B2041
import Grosswald.Direct.Run.B2042
import Grosswald.Direct.Run.B2043
import Grosswald.Direct.Run.B2044
import Grosswald.Direct.Run.B2045
import Grosswald.Direct.Run.B2046
import Grosswald.Direct.Run.B2047
import Grosswald.Direct.Run.B2048
import Grosswald.Direct.Run.B2049

namespace Grosswald.Direct
open GrosswaldCompute
theorem g40 : segsOk 20000000 8000100000411 5000 = true := by
  have h2049 : segsOk 20000000 8196100000411 100 = true := Run.b2049
  have h2048 : segsOk 20000000 8192100000411 200 = true :=
    segsOk_append 100 _ _ _ Run.b2048 h2049 (by norm_num)
  have h2047 : segsOk 20000000 8188100000411 300 = true :=
    segsOk_append 100 _ _ _ Run.b2047 h2048 (by norm_num)
  have h2046 : segsOk 20000000 8184100000411 400 = true :=
    segsOk_append 100 _ _ _ Run.b2046 h2047 (by norm_num)
  have h2045 : segsOk 20000000 8180100000411 500 = true :=
    segsOk_append 100 _ _ _ Run.b2045 h2046 (by norm_num)
  have h2044 : segsOk 20000000 8176100000411 600 = true :=
    segsOk_append 100 _ _ _ Run.b2044 h2045 (by norm_num)
  have h2043 : segsOk 20000000 8172100000411 700 = true :=
    segsOk_append 100 _ _ _ Run.b2043 h2044 (by norm_num)
  have h2042 : segsOk 20000000 8168100000411 800 = true :=
    segsOk_append 100 _ _ _ Run.b2042 h2043 (by norm_num)
  have h2041 : segsOk 20000000 8164100000411 900 = true :=
    segsOk_append 100 _ _ _ Run.b2041 h2042 (by norm_num)
  have h2040 : segsOk 20000000 8160100000411 1000 = true :=
    segsOk_append 100 _ _ _ Run.b2040 h2041 (by norm_num)
  have h2039 : segsOk 20000000 8156100000411 1100 = true :=
    segsOk_append 100 _ _ _ Run.b2039 h2040 (by norm_num)
  have h2038 : segsOk 20000000 8152100000411 1200 = true :=
    segsOk_append 100 _ _ _ Run.b2038 h2039 (by norm_num)
  have h2037 : segsOk 20000000 8148100000411 1300 = true :=
    segsOk_append 100 _ _ _ Run.b2037 h2038 (by norm_num)
  have h2036 : segsOk 20000000 8144100000411 1400 = true :=
    segsOk_append 100 _ _ _ Run.b2036 h2037 (by norm_num)
  have h2035 : segsOk 20000000 8140100000411 1500 = true :=
    segsOk_append 100 _ _ _ Run.b2035 h2036 (by norm_num)
  have h2034 : segsOk 20000000 8136100000411 1600 = true :=
    segsOk_append 100 _ _ _ Run.b2034 h2035 (by norm_num)
  have h2033 : segsOk 20000000 8132100000411 1700 = true :=
    segsOk_append 100 _ _ _ Run.b2033 h2034 (by norm_num)
  have h2032 : segsOk 20000000 8128100000411 1800 = true :=
    segsOk_append 100 _ _ _ Run.b2032 h2033 (by norm_num)
  have h2031 : segsOk 20000000 8124100000411 1900 = true :=
    segsOk_append 100 _ _ _ Run.b2031 h2032 (by norm_num)
  have h2030 : segsOk 20000000 8120100000411 2000 = true :=
    segsOk_append 100 _ _ _ Run.b2030 h2031 (by norm_num)
  have h2029 : segsOk 20000000 8116100000411 2100 = true :=
    segsOk_append 100 _ _ _ Run.b2029 h2030 (by norm_num)
  have h2028 : segsOk 20000000 8112100000411 2200 = true :=
    segsOk_append 100 _ _ _ Run.b2028 h2029 (by norm_num)
  have h2027 : segsOk 20000000 8108100000411 2300 = true :=
    segsOk_append 100 _ _ _ Run.b2027 h2028 (by norm_num)
  have h2026 : segsOk 20000000 8104100000411 2400 = true :=
    segsOk_append 100 _ _ _ Run.b2026 h2027 (by norm_num)
  have h2025 : segsOk 20000000 8100100000411 2500 = true :=
    segsOk_append 100 _ _ _ Run.b2025 h2026 (by norm_num)
  have h2024 : segsOk 20000000 8096100000411 2600 = true :=
    segsOk_append 100 _ _ _ Run.b2024 h2025 (by norm_num)
  have h2023 : segsOk 20000000 8092100000411 2700 = true :=
    segsOk_append 100 _ _ _ Run.b2023 h2024 (by norm_num)
  have h2022 : segsOk 20000000 8088100000411 2800 = true :=
    segsOk_append 100 _ _ _ Run.b2022 h2023 (by norm_num)
  have h2021 : segsOk 20000000 8084100000411 2900 = true :=
    segsOk_append 100 _ _ _ Run.b2021 h2022 (by norm_num)
  have h2020 : segsOk 20000000 8080100000411 3000 = true :=
    segsOk_append 100 _ _ _ Run.b2020 h2021 (by norm_num)
  have h2019 : segsOk 20000000 8076100000411 3100 = true :=
    segsOk_append 100 _ _ _ Run.b2019 h2020 (by norm_num)
  have h2018 : segsOk 20000000 8072100000411 3200 = true :=
    segsOk_append 100 _ _ _ Run.b2018 h2019 (by norm_num)
  have h2017 : segsOk 20000000 8068100000411 3300 = true :=
    segsOk_append 100 _ _ _ Run.b2017 h2018 (by norm_num)
  have h2016 : segsOk 20000000 8064100000411 3400 = true :=
    segsOk_append 100 _ _ _ Run.b2016 h2017 (by norm_num)
  have h2015 : segsOk 20000000 8060100000411 3500 = true :=
    segsOk_append 100 _ _ _ Run.b2015 h2016 (by norm_num)
  have h2014 : segsOk 20000000 8056100000411 3600 = true :=
    segsOk_append 100 _ _ _ Run.b2014 h2015 (by norm_num)
  have h2013 : segsOk 20000000 8052100000411 3700 = true :=
    segsOk_append 100 _ _ _ Run.b2013 h2014 (by norm_num)
  have h2012 : segsOk 20000000 8048100000411 3800 = true :=
    segsOk_append 100 _ _ _ Run.b2012 h2013 (by norm_num)
  have h2011 : segsOk 20000000 8044100000411 3900 = true :=
    segsOk_append 100 _ _ _ Run.b2011 h2012 (by norm_num)
  have h2010 : segsOk 20000000 8040100000411 4000 = true :=
    segsOk_append 100 _ _ _ Run.b2010 h2011 (by norm_num)
  have h2009 : segsOk 20000000 8036100000411 4100 = true :=
    segsOk_append 100 _ _ _ Run.b2009 h2010 (by norm_num)
  have h2008 : segsOk 20000000 8032100000411 4200 = true :=
    segsOk_append 100 _ _ _ Run.b2008 h2009 (by norm_num)
  have h2007 : segsOk 20000000 8028100000411 4300 = true :=
    segsOk_append 100 _ _ _ Run.b2007 h2008 (by norm_num)
  have h2006 : segsOk 20000000 8024100000411 4400 = true :=
    segsOk_append 100 _ _ _ Run.b2006 h2007 (by norm_num)
  have h2005 : segsOk 20000000 8020100000411 4500 = true :=
    segsOk_append 100 _ _ _ Run.b2005 h2006 (by norm_num)
  have h2004 : segsOk 20000000 8016100000411 4600 = true :=
    segsOk_append 100 _ _ _ Run.b2004 h2005 (by norm_num)
  have h2003 : segsOk 20000000 8012100000411 4700 = true :=
    segsOk_append 100 _ _ _ Run.b2003 h2004 (by norm_num)
  have h2002 : segsOk 20000000 8008100000411 4800 = true :=
    segsOk_append 100 _ _ _ Run.b2002 h2003 (by norm_num)
  have h2001 : segsOk 20000000 8004100000411 4900 = true :=
    segsOk_append 100 _ _ _ Run.b2001 h2002 (by norm_num)
  have h2000 : segsOk 20000000 8000100000411 5000 = true :=
    segsOk_append 100 _ _ _ Run.b2000 h2001 (by norm_num)
  exact h2000
end Grosswald.Direct
