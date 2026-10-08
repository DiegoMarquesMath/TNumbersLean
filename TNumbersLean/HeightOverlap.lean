import Mathlib

namespace TNumbersLean

/-- Logical core of the last-admissible-stage argument:
if H is after the current left endpoint, before the next left endpoint,
and the next left endpoint is below the current right endpoint,
then H belongs to the current height range. -/
theorem height_in_current_range
    {L H Lnext R : ℝ}
    (hLH : L ≤ H)
    (hHnext : H < Lnext)
    (hoverlap : Lnext ≤ R) :
    L ≤ H ∧ H ≤ R := by
  constructor
  · exact hLH
  · linarith

end TNumbersLean
