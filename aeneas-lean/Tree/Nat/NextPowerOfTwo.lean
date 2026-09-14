module

import all Init.Data.Nat.Power2.Basic
public import Init.Data.Nat.Power2.Basic
import Init.Data.Nat.Lemmas
import Init.Omega

public section

namespace Nat

private theorem nextPowerOfTwo_go_power (target power : Nat) (hbound : power ≤ target) :
    Nat.nextPowerOfTwo.go (2 ^ target) (2 ^ power) (Nat.two_pow_pos power) =
      2 ^ target := by
  rw [Nat.nextPowerOfTwo.go]
  by_cases heq : power = target
  · subst power
    simp
  · have hlt : power < target := by omega
    rw [if_pos (Nat.pow_lt_pow_right (by omega) hlt)]
    simpa only [← Nat.pow_succ] using
      nextPowerOfTwo_go_power target (power + 1) (by omega)
termination_by target - power
decreasing_by omega

/-- Rounding an exact power of two up to the next power leaves it unchanged. -/
theorem nextPowerOfTwo_two_pow (depth : Nat) :
    Nat.nextPowerOfTwo (2 ^ depth) = 2 ^ depth := by
  simpa only [Nat.nextPowerOfTwo, Nat.pow_zero] using
    nextPowerOfTwo_go_power depth 0 (Nat.zero_le _)

end Nat
