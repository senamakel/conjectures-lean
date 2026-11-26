import RobinCompute.Data

namespace RobinCompute

/-- The direct check for `5040 < n ≤ 10000` and the initial coverage bound (`native_decide`). -/
theorem small_ok : ((List.range' 5041 4960).all directOK &&
    decide (x0 * D ≤ XS * logLoNat 10001)) = true := by native_decide

end RobinCompute
