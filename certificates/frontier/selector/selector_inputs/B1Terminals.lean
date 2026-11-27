import Collatz.SevenStepCertificate.B1Primitives

/-! Generated exact terminal paths for all ten elementary B1 guards.
Every theorem quantifies over its whole affine parameter domain. -/

namespace Collatz.SevenStepCertificate

theorem b1_terminal_large_1_1 (t : Nat) :
    run (.p2, 9*(2^1*(4*t+1))) 3 = (.p5, 81*t+21) := by
  have h0 : next (.p2, 9*(2^1*(4*t+1))) = (.p3, 108*t+27) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 108*t+27) = (.p4, 162*t+41) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 162*t+41) = (.p5, 81*t+21) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem b1_terminal_small_1_1 (t : Nat) :
    run (.p2, 3*(2^1*(4*t+1))) 3 = (.p5, 81*t+21) := by
  have h0 : next (.p2, 3*(2^1*(4*t+1))) = (.p3, 36*t+9) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 36*t+9) = (.p4, 54*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 54*t+14) = (.p5, 81*t+21) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem b1_terminal_1_1 (t : Nat) :
    run (.p2,9*(2^1*(4*t+1))) (1+2) =
      run (.p2,3*(2^1*(4*t+1))) (1+2) := by
  rw [b1_terminal_large_1_1,b1_terminal_small_1_1]

theorem b1_terminal_large_2_3 (t : Nat) :
    run (.p2, 9*(2^2*(4*t+3))) 4 = (.p6, 27*t+21) := by
  have h0 : next (.p2, 9*(2^2*(4*t+3))) = (.p3, 216*t+162) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 216*t+162) = (.p4, 108*t+81) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 108*t+81) = (.p5, 54*t+41) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 54*t+41) = (.p6, 27*t+21) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3]

theorem b1_terminal_small_2_3 (t : Nat) :
    run (.p2, 3*(2^2*(4*t+3))) 4 = (.p6, 27*t+21) := by
  have h0 : next (.p2, 3*(2^2*(4*t+3))) = (.p3, 72*t+54) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 72*t+54) = (.p4, 36*t+27) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 36*t+27) = (.p5, 18*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 18*t+14) = (.p6, 27*t+21) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3]

theorem b1_terminal_2_3 (t : Nat) :
    run (.p2,9*(2^2*(4*t+3))) (2+2) =
      run (.p2,3*(2^2*(4*t+3))) (2+2) := by
  rw [b1_terminal_large_2_3,b1_terminal_small_2_3]

theorem b1_terminal_large_4_1 (t : Nat) :
    run (.p2, 9*(2^4*(4*t+1))) 6 = (.p1, 729*t+183) := by
  have h0 : next (.p2, 9*(2^4*(4*t+1))) = (.p3, 864*t+216) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 864*t+216) = (.p4, 432*t+108) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 432*t+108) = (.p5, 648*t+162) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 648*t+162) = (.p6, 972*t+243) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 972*t+243) = (.p0, 1458*t+365) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 1458*t+365) = (.p1, 729*t+183) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem b1_terminal_small_4_1 (t : Nat) :
    run (.p2, 3*(2^4*(4*t+1))) 6 = (.p1, 729*t+183) := by
  have h0 : next (.p2, 3*(2^4*(4*t+1))) = (.p3, 288*t+72) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 288*t+72) = (.p4, 144*t+36) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 144*t+36) = (.p5, 216*t+54) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 216*t+54) = (.p6, 324*t+81) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 324*t+81) = (.p0, 486*t+122) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 486*t+122) = (.p1, 729*t+183) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem b1_terminal_4_1 (t : Nat) :
    run (.p2,9*(2^4*(4*t+1))) (4+2) =
      run (.p2,3*(2^4*(4*t+1))) (4+2) := by
  rw [b1_terminal_large_4_1,b1_terminal_small_4_1]

theorem b1_terminal_large_5_3 (t : Nat) :
    run (.p2, 9*(2^5*(4*t+3))) 7 = (.p2, 243*t+183) := by
  have h0 : next (.p2, 9*(2^5*(4*t+3))) = (.p3, 1728*t+1296) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 1728*t+1296) = (.p4, 864*t+648) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 864*t+648) = (.p5, 1296*t+972) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 1296*t+972) = (.p6, 1944*t+1458) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 1944*t+1458) = (.p0, 972*t+729) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 972*t+729) = (.p1, 486*t+365) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 486*t+365) = (.p2, 243*t+183) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_terminal_small_5_3 (t : Nat) :
    run (.p2, 3*(2^5*(4*t+3))) 7 = (.p2, 243*t+183) := by
  have h0 : next (.p2, 3*(2^5*(4*t+3))) = (.p3, 576*t+432) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 576*t+432) = (.p4, 288*t+216) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 288*t+216) = (.p5, 432*t+324) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 432*t+324) = (.p6, 648*t+486) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 648*t+486) = (.p0, 324*t+243) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 324*t+243) = (.p1, 162*t+122) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 162*t+122) = (.p2, 243*t+183) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_terminal_5_3 (t : Nat) :
    run (.p2,9*(2^5*(4*t+3))) (5+2) =
      run (.p2,3*(2^5*(4*t+3))) (5+2) := by
  rw [b1_terminal_large_5_3,b1_terminal_small_5_3]

theorem b1_terminal_large_6_1 (t : Nat) :
    run (.p2, 9*(2^6*(4*t+1))) 8 = (.p3, 729*t+183) := by
  have h0 : next (.p2, 9*(2^6*(4*t+1))) = (.p3, 3456*t+864) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 3456*t+864) = (.p4, 1728*t+432) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 1728*t+432) = (.p5, 2592*t+648) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 2592*t+648) = (.p6, 3888*t+972) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 3888*t+972) = (.p0, 1944*t+486) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 1944*t+486) = (.p1, 2916*t+729) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 2916*t+729) = (.p2, 1458*t+365) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 1458*t+365) = (.p3, 729*t+183) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7]

theorem b1_terminal_small_6_1 (t : Nat) :
    run (.p2, 3*(2^6*(4*t+1))) 8 = (.p3, 729*t+183) := by
  have h0 : next (.p2, 3*(2^6*(4*t+1))) = (.p3, 1152*t+288) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 1152*t+288) = (.p4, 576*t+144) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 576*t+144) = (.p5, 864*t+216) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 864*t+216) = (.p6, 1296*t+324) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 1296*t+324) = (.p0, 648*t+162) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 648*t+162) = (.p1, 972*t+243) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 972*t+243) = (.p2, 486*t+122) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 486*t+122) = (.p3, 729*t+183) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7]

theorem b1_terminal_6_1 (t : Nat) :
    run (.p2,9*(2^6*(4*t+1))) (6+2) =
      run (.p2,3*(2^6*(4*t+1))) (6+2) := by
  rw [b1_terminal_large_6_1,b1_terminal_small_6_1]

theorem b1_terminal_large_8_3 (t : Nat) :
    run (.p2, 9*(2^8*(4*t+3))) 10 = (.p5, 19683*t+14763) := by
  have h0 : next (.p2, 9*(2^8*(4*t+3))) = (.p3, 13824*t+10368) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 13824*t+10368) = (.p4, 6912*t+5184) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 6912*t+5184) = (.p5, 10368*t+7776) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 10368*t+7776) = (.p6, 15552*t+11664) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 15552*t+11664) = (.p0, 7776*t+5832) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 7776*t+5832) = (.p1, 11664*t+8748) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 11664*t+8748) = (.p2, 17496*t+13122) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 17496*t+13122) = (.p3, 26244*t+19683) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p3, 26244*t+19683) = (.p4, 39366*t+29525) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h9 : next (.p4, 39366*t+29525) = (.p5, 19683*t+14763) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem b1_terminal_small_8_3 (t : Nat) :
    run (.p2, 3*(2^8*(4*t+3))) 10 = (.p5, 19683*t+14763) := by
  have h0 : next (.p2, 3*(2^8*(4*t+3))) = (.p3, 4608*t+3456) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 4608*t+3456) = (.p4, 2304*t+1728) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 2304*t+1728) = (.p5, 3456*t+2592) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 3456*t+2592) = (.p6, 5184*t+3888) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 5184*t+3888) = (.p0, 2592*t+1944) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 2592*t+1944) = (.p1, 3888*t+2916) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 3888*t+2916) = (.p2, 5832*t+4374) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 5832*t+4374) = (.p3, 8748*t+6561) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p3, 8748*t+6561) = (.p4, 13122*t+9842) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h9 : next (.p4, 13122*t+9842) = (.p5, 19683*t+14763) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem b1_terminal_8_3 (t : Nat) :
    run (.p2,9*(2^8*(4*t+3))) (8+2) =
      run (.p2,3*(2^8*(4*t+3))) (8+2) := by
  rw [b1_terminal_large_8_3,b1_terminal_small_8_3]

theorem b1_terminal_large_9_1 (t : Nat) :
    run (.p2, 9*(2^9*(4*t+1))) 11 = (.p6, 6561*t+1641) := by
  have h0 : next (.p2, 9*(2^9*(4*t+1))) = (.p3, 27648*t+6912) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 27648*t+6912) = (.p4, 13824*t+3456) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 13824*t+3456) = (.p5, 20736*t+5184) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 20736*t+5184) = (.p6, 31104*t+7776) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 31104*t+7776) = (.p0, 15552*t+3888) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 15552*t+3888) = (.p1, 23328*t+5832) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 23328*t+5832) = (.p2, 34992*t+8748) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 34992*t+8748) = (.p3, 52488*t+13122) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p3, 52488*t+13122) = (.p4, 26244*t+6561) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h9 : next (.p4, 26244*t+6561) = (.p5, 13122*t+3281) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h10 : next (.p5, 13122*t+3281) = (.p6, 6561*t+1641) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem b1_terminal_small_9_1 (t : Nat) :
    run (.p2, 3*(2^9*(4*t+1))) 11 = (.p6, 6561*t+1641) := by
  have h0 : next (.p2, 3*(2^9*(4*t+1))) = (.p3, 9216*t+2304) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 9216*t+2304) = (.p4, 4608*t+1152) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 4608*t+1152) = (.p5, 6912*t+1728) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 6912*t+1728) = (.p6, 10368*t+2592) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 10368*t+2592) = (.p0, 5184*t+1296) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 5184*t+1296) = (.p1, 7776*t+1944) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 7776*t+1944) = (.p2, 11664*t+2916) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 11664*t+2916) = (.p3, 17496*t+4374) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p3, 17496*t+4374) = (.p4, 8748*t+2187) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h9 : next (.p4, 8748*t+2187) = (.p5, 4374*t+1094) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h10 : next (.p5, 4374*t+1094) = (.p6, 6561*t+1641) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem b1_terminal_9_1 (t : Nat) :
    run (.p2,9*(2^9*(4*t+1))) (9+2) =
      run (.p2,3*(2^9*(4*t+1))) (9+2) := by
  rw [b1_terminal_large_9_1,b1_terminal_small_9_1]

theorem b1_terminal_large_11_3 (t : Nat) :
    run (.p2, 9*(2^11*(4*t+3))) 13 = (.p1, 177147*t+132861) := by
  have h0 : next (.p2, 9*(2^11*(4*t+3))) = (.p3, 110592*t+82944) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 110592*t+82944) = (.p4, 55296*t+41472) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 55296*t+41472) = (.p5, 82944*t+62208) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 82944*t+62208) = (.p6, 124416*t+93312) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 124416*t+93312) = (.p0, 62208*t+46656) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 62208*t+46656) = (.p1, 93312*t+69984) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 93312*t+69984) = (.p2, 139968*t+104976) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 139968*t+104976) = (.p3, 209952*t+157464) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p3, 209952*t+157464) = (.p4, 104976*t+78732) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h9 : next (.p4, 104976*t+78732) = (.p5, 157464*t+118098) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h10 : next (.p5, 157464*t+118098) = (.p6, 236196*t+177147) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p6, 236196*t+177147) = (.p0, 354294*t+265721) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h12 : next (.p0, 354294*t+265721) = (.p1, 177147*t+132861) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

theorem b1_terminal_small_11_3 (t : Nat) :
    run (.p2, 3*(2^11*(4*t+3))) 13 = (.p1, 177147*t+132861) := by
  have h0 : next (.p2, 3*(2^11*(4*t+3))) = (.p3, 36864*t+27648) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 36864*t+27648) = (.p4, 18432*t+13824) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 18432*t+13824) = (.p5, 27648*t+20736) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 27648*t+20736) = (.p6, 41472*t+31104) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 41472*t+31104) = (.p0, 20736*t+15552) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 20736*t+15552) = (.p1, 31104*t+23328) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 31104*t+23328) = (.p2, 46656*t+34992) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 46656*t+34992) = (.p3, 69984*t+52488) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p3, 69984*t+52488) = (.p4, 34992*t+26244) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h9 : next (.p4, 34992*t+26244) = (.p5, 52488*t+39366) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h10 : next (.p5, 52488*t+39366) = (.p6, 78732*t+59049) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p6, 78732*t+59049) = (.p0, 118098*t+88574) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h12 : next (.p0, 118098*t+88574) = (.p1, 177147*t+132861) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

theorem b1_terminal_11_3 (t : Nat) :
    run (.p2,9*(2^11*(4*t+3))) (11+2) =
      run (.p2,3*(2^11*(4*t+3))) (11+2) := by
  rw [b1_terminal_large_11_3,b1_terminal_small_11_3]

theorem b1_terminal_large_12_1 (t : Nat) :
    run (.p2, 9*(2^12*(4*t+1))) 14 = (.p2, 59049*t+14763) := by
  have h0 : next (.p2, 9*(2^12*(4*t+1))) = (.p3, 221184*t+55296) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 221184*t+55296) = (.p4, 110592*t+27648) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 110592*t+27648) = (.p5, 165888*t+41472) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 165888*t+41472) = (.p6, 248832*t+62208) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 248832*t+62208) = (.p0, 124416*t+31104) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 124416*t+31104) = (.p1, 186624*t+46656) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 186624*t+46656) = (.p2, 279936*t+69984) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 279936*t+69984) = (.p3, 419904*t+104976) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p3, 419904*t+104976) = (.p4, 209952*t+52488) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h9 : next (.p4, 209952*t+52488) = (.p5, 314928*t+78732) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h10 : next (.p5, 314928*t+78732) = (.p6, 472392*t+118098) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p6, 472392*t+118098) = (.p0, 236196*t+59049) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h12 : next (.p0, 236196*t+59049) = (.p1, 118098*t+29525) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h13 : next (.p1, 118098*t+29525) = (.p2, 59049*t+14763) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem b1_terminal_small_12_1 (t : Nat) :
    run (.p2, 3*(2^12*(4*t+1))) 14 = (.p2, 59049*t+14763) := by
  have h0 : next (.p2, 3*(2^12*(4*t+1))) = (.p3, 73728*t+18432) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 73728*t+18432) = (.p4, 36864*t+9216) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 36864*t+9216) = (.p5, 55296*t+13824) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 55296*t+13824) = (.p6, 82944*t+20736) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 82944*t+20736) = (.p0, 41472*t+10368) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 41472*t+10368) = (.p1, 62208*t+15552) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 62208*t+15552) = (.p2, 93312*t+23328) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 93312*t+23328) = (.p3, 139968*t+34992) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p3, 139968*t+34992) = (.p4, 69984*t+17496) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h9 : next (.p4, 69984*t+17496) = (.p5, 104976*t+26244) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h10 : next (.p5, 104976*t+26244) = (.p6, 157464*t+39366) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p6, 157464*t+39366) = (.p0, 78732*t+19683) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h12 : next (.p0, 78732*t+19683) = (.p1, 39366*t+9842) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h13 : next (.p1, 39366*t+9842) = (.p2, 59049*t+14763) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem b1_terminal_12_1 (t : Nat) :
    run (.p2,9*(2^12*(4*t+1))) (12+2) =
      run (.p2,3*(2^12*(4*t+1))) (12+2) := by
  rw [b1_terminal_large_12_1,b1_terminal_small_12_1]

theorem b1_terminal_large_13_3 (t : Nat) :
    run (.p2, 9*(2^13*(4*t+3))) 15 = (.p3, 177147*t+132861) := by
  have h0 : next (.p2, 9*(2^13*(4*t+3))) = (.p3, 442368*t+331776) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 442368*t+331776) = (.p4, 221184*t+165888) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 221184*t+165888) = (.p5, 331776*t+248832) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 331776*t+248832) = (.p6, 497664*t+373248) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 497664*t+373248) = (.p0, 248832*t+186624) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 248832*t+186624) = (.p1, 373248*t+279936) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 373248*t+279936) = (.p2, 559872*t+419904) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 559872*t+419904) = (.p3, 839808*t+629856) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p3, 839808*t+629856) = (.p4, 419904*t+314928) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h9 : next (.p4, 419904*t+314928) = (.p5, 629856*t+472392) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h10 : next (.p5, 629856*t+472392) = (.p6, 944784*t+708588) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p6, 944784*t+708588) = (.p0, 472392*t+354294) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h12 : next (.p0, 472392*t+354294) = (.p1, 708588*t+531441) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h13 : next (.p1, 708588*t+531441) = (.p2, 354294*t+265721) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h14 : next (.p2, 354294*t+265721) = (.p3, 177147*t+132861) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]

theorem b1_terminal_small_13_3 (t : Nat) :
    run (.p2, 3*(2^13*(4*t+3))) 15 = (.p3, 177147*t+132861) := by
  have h0 : next (.p2, 3*(2^13*(4*t+3))) = (.p3, 147456*t+110592) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 147456*t+110592) = (.p4, 73728*t+55296) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 73728*t+55296) = (.p5, 110592*t+82944) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 110592*t+82944) = (.p6, 165888*t+124416) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 165888*t+124416) = (.p0, 82944*t+62208) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 82944*t+62208) = (.p1, 124416*t+93312) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 124416*t+93312) = (.p2, 186624*t+139968) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p2, 186624*t+139968) = (.p3, 279936*t+209952) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p3, 279936*t+209952) = (.p4, 139968*t+104976) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h9 : next (.p4, 139968*t+104976) = (.p5, 209952*t+157464) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h10 : next (.p5, 209952*t+157464) = (.p6, 314928*t+236196) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p6, 314928*t+236196) = (.p0, 157464*t+118098) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h12 : next (.p0, 157464*t+118098) = (.p1, 236196*t+177147) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h13 : next (.p1, 236196*t+177147) = (.p2, 118098*t+88574) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h14 : next (.p2, 118098*t+88574) = (.p3, 177147*t+132861) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]

theorem b1_terminal_13_3 (t : Nat) :
    run (.p2,9*(2^13*(4*t+3))) (13+2) =
      run (.p2,3*(2^13*(4*t+3))) (13+2) := by
  rw [b1_terminal_large_13_3,b1_terminal_small_13_3]

end Collatz.SevenStepCertificate
