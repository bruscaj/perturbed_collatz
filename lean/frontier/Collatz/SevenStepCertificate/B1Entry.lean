import Collatz.SevenStepCertificate

/-! Explicit finite inverse rays and a complete B1-only conditional theorem.
No analytical density statement or unproved A3/N03 premise is used.
Regenerate with research/final_proof_push/formal/generate_b1_entry.py. -/

namespace Collatz.SevenStepCertificate

theorem b1_inverse_ray_01 (t : Nat) :
    run (.p1, 6*(8192*t+59)) 14 = (.p1, 27*t+1) := by
  have h0 : next (.p1, 6*(8192*t+59)) = (.p2, 73728*t+531) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 73728*t+531) = (.p3, 36864*t+266) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 36864*t+266) = (.p4, 18432*t+133) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 18432*t+133) = (.p5, 9216*t+67) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 9216*t+67) = (.p6, 4608*t+34) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 4608*t+34) = (.p0, 2304*t+17) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 2304*t+17) = (.p1, 1152*t+9) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 1152*t+9) = (.p2, 576*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 576*t+5) = (.p3, 288*t+3) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 288*t+3) = (.p4, 432*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 432*t+5) = (.p5, 216*t+3) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 216*t+3) = (.p6, 108*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 108*t+2) = (.p0, 54*t+1) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 54*t+1) = (.p1, 27*t+1) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem b1_inverse_ray_02 (t : Nat) :
    run (.p1, 6*(64*t+3)) 7 = (.p1, 27*t+2) := by
  have h0 : next (.p1, 6*(64*t+3)) = (.p2, 576*t+27) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 576*t+27) = (.p3, 288*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 288*t+14) = (.p4, 144*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 144*t+7) = (.p5, 72*t+4) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 72*t+4) = (.p6, 108*t+6) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 108*t+6) = (.p0, 54*t+3) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 54*t+3) = (.p1, 27*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_inverse_ray_03 (t : Nat) :
    run (.p1, 6*(3145728*t+266043)) 21 = (.p1, 27*t+3) := by
  have h0 : next (.p1, 6*(3145728*t+266043)) = (.p2, 28311552*t+2394387) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 28311552*t+2394387) = (.p3, 14155776*t+1197194) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 14155776*t+1197194) = (.p4, 7077888*t+598597) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 7077888*t+598597) = (.p5, 3538944*t+299299) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 3538944*t+299299) = (.p6, 1769472*t+149650) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 1769472*t+149650) = (.p0, 884736*t+74825) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 884736*t+74825) = (.p1, 442368*t+37413) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 442368*t+37413) = (.p2, 221184*t+18707) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 221184*t+18707) = (.p3, 110592*t+9354) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 110592*t+9354) = (.p4, 55296*t+4677) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 55296*t+4677) = (.p5, 27648*t+2339) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 27648*t+2339) = (.p6, 13824*t+1170) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 13824*t+1170) = (.p0, 6912*t+585) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 6912*t+585) = (.p1, 3456*t+293) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h14 : next (.p1, 3456*t+293) = (.p2, 1728*t+147) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h15 : next (.p2, 1728*t+147) = (.p3, 864*t+74) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h16 : next (.p3, 864*t+74) = (.p4, 432*t+37) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h17 : next (.p4, 432*t+37) = (.p5, 216*t+19) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h18 : next (.p5, 216*t+19) = (.p6, 108*t+10) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h19 : next (.p6, 108*t+10) = (.p0, 54*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h20 : next (.p0, 54*t+5) = (.p1, 27*t+3) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

theorem b1_inverse_ray_04 (t : Nat) :
    run (.p1, 6*(1048576*t+127517)) 21 = (.p1, 27*t+4) := by
  have h0 : next (.p1, 6*(1048576*t+127517)) = (.p2, 9437184*t+1147653) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 9437184*t+1147653) = (.p3, 4718592*t+573827) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 4718592*t+573827) = (.p4, 7077888*t+860741) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 7077888*t+860741) = (.p5, 3538944*t+430371) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 3538944*t+430371) = (.p6, 1769472*t+215186) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 1769472*t+215186) = (.p0, 884736*t+107593) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 884736*t+107593) = (.p1, 442368*t+53797) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 442368*t+53797) = (.p2, 221184*t+26899) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 221184*t+26899) = (.p3, 110592*t+13450) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 110592*t+13450) = (.p4, 55296*t+6725) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 55296*t+6725) = (.p5, 27648*t+3363) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 27648*t+3363) = (.p6, 13824*t+1682) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 13824*t+1682) = (.p0, 6912*t+841) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 6912*t+841) = (.p1, 3456*t+421) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h14 : next (.p1, 3456*t+421) = (.p2, 1728*t+211) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h15 : next (.p2, 1728*t+211) = (.p3, 864*t+106) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h16 : next (.p3, 864*t+106) = (.p4, 432*t+53) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h17 : next (.p4, 432*t+53) = (.p5, 216*t+27) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h18 : next (.p5, 216*t+27) = (.p6, 108*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h19 : next (.p6, 108*t+14) = (.p0, 54*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h20 : next (.p0, 54*t+7) = (.p1, 27*t+4) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

theorem b1_inverse_ray_05 (t : Nat) :
    run (.p1, 6*(24576*t+3899)) 14 = (.p1, 27*t+5) := by
  have h0 : next (.p1, 6*(24576*t+3899)) = (.p2, 221184*t+35091) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 221184*t+35091) = (.p3, 110592*t+17546) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 110592*t+17546) = (.p4, 55296*t+8773) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 55296*t+8773) = (.p5, 27648*t+4387) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 27648*t+4387) = (.p6, 13824*t+2194) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 13824*t+2194) = (.p0, 6912*t+1097) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 6912*t+1097) = (.p1, 3456*t+549) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 3456*t+549) = (.p2, 1728*t+275) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 1728*t+275) = (.p3, 864*t+138) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 864*t+138) = (.p4, 432*t+69) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 432*t+69) = (.p5, 216*t+35) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 216*t+35) = (.p6, 108*t+18) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 108*t+18) = (.p0, 54*t+9) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 54*t+9) = (.p1, 27*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem b1_inverse_ray_06 (t : Nat) :
    run (.p1, 6*(64*t+11)) 7 = (.p1, 27*t+6) := by
  have h0 : next (.p1, 6*(64*t+11)) = (.p2, 576*t+99) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 576*t+99) = (.p3, 288*t+50) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 288*t+50) = (.p4, 144*t+25) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 144*t+25) = (.p5, 72*t+13) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 72*t+13) = (.p6, 36*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 36*t+7) = (.p0, 54*t+11) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 54*t+11) = (.p1, 27*t+6) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_inverse_ray_07 (t : Nat) :
    run (.p1, 6*(64*t+15)) 7 = (.p1, 27*t+7) := by
  have h0 : next (.p1, 6*(64*t+15)) = (.p2, 576*t+135) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 576*t+135) = (.p3, 288*t+68) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 288*t+68) = (.p4, 144*t+34) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 144*t+34) = (.p5, 216*t+51) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 216*t+51) = (.p6, 108*t+26) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 108*t+26) = (.p0, 54*t+13) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 54*t+13) = (.p1, 27*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_inverse_ray_08 (t : Nat) :
    run (.p1, 6*(1048576*t+282427)) 21 = (.p1, 27*t+8) := by
  have h0 : next (.p1, 6*(1048576*t+282427)) = (.p2, 9437184*t+2541843) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 9437184*t+2541843) = (.p3, 4718592*t+1270922) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 4718592*t+1270922) = (.p4, 2359296*t+635461) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 2359296*t+635461) = (.p5, 1179648*t+317731) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 1179648*t+317731) = (.p6, 589824*t+158866) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 589824*t+158866) = (.p0, 294912*t+79433) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 294912*t+79433) = (.p1, 147456*t+39717) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 147456*t+39717) = (.p2, 73728*t+19859) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 73728*t+19859) = (.p3, 36864*t+9930) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 36864*t+9930) = (.p4, 18432*t+4965) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 18432*t+4965) = (.p5, 9216*t+2483) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 9216*t+2483) = (.p6, 4608*t+1242) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 4608*t+1242) = (.p0, 2304*t+621) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 2304*t+621) = (.p1, 1152*t+311) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h14 : next (.p1, 1152*t+311) = (.p2, 576*t+156) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h15 : next (.p2, 576*t+156) = (.p3, 864*t+234) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h16 : next (.p3, 864*t+234) = (.p4, 432*t+117) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h17 : next (.p4, 432*t+117) = (.p5, 216*t+59) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h18 : next (.p5, 216*t+59) = (.p6, 108*t+30) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h19 : next (.p6, 108*t+30) = (.p0, 54*t+15) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h20 : next (.p0, 54*t+15) = (.p1, 27*t+8) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

theorem b1_inverse_ray_09 (t : Nat) :
    run (.p1, 6*(192*t+59)) 7 = (.p1, 27*t+9) := by
  have h0 : next (.p1, 6*(192*t+59)) = (.p2, 1728*t+531) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1728*t+531) = (.p3, 864*t+266) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 864*t+266) = (.p4, 432*t+133) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 432*t+133) = (.p5, 216*t+67) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 216*t+67) = (.p6, 108*t+34) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 108*t+34) = (.p0, 54*t+17) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 54*t+17) = (.p1, 27*t+9) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_inverse_ray_10 (t : Nat) :
    run (.p1, 6*(1048576*t+360507)) 21 = (.p1, 27*t+10) := by
  have h0 : next (.p1, 6*(1048576*t+360507)) = (.p2, 9437184*t+3244563) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 9437184*t+3244563) = (.p3, 4718592*t+1622282) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 4718592*t+1622282) = (.p4, 2359296*t+811141) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 2359296*t+811141) = (.p5, 1179648*t+405571) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 1179648*t+405571) = (.p6, 589824*t+202786) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 589824*t+202786) = (.p0, 294912*t+101393) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 294912*t+101393) = (.p1, 147456*t+50697) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 147456*t+50697) = (.p2, 73728*t+25349) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 73728*t+25349) = (.p3, 36864*t+12675) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 36864*t+12675) = (.p4, 55296*t+19013) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 55296*t+19013) = (.p5, 27648*t+9507) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 27648*t+9507) = (.p6, 13824*t+4754) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 13824*t+4754) = (.p0, 6912*t+2377) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 6912*t+2377) = (.p1, 3456*t+1189) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h14 : next (.p1, 3456*t+1189) = (.p2, 1728*t+595) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h15 : next (.p2, 1728*t+595) = (.p3, 864*t+298) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h16 : next (.p3, 864*t+298) = (.p4, 432*t+149) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h17 : next (.p4, 432*t+149) = (.p5, 216*t+75) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h18 : next (.p5, 216*t+75) = (.p6, 108*t+38) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h19 : next (.p6, 108*t+38) = (.p0, 54*t+19) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h20 : next (.p0, 54*t+19) = (.p1, 27*t+10) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

theorem b1_inverse_ray_11 (t : Nat) :
    run (.p1, 6*(1048576*t+399163)) 21 = (.p1, 27*t+11) := by
  have h0 : next (.p1, 6*(1048576*t+399163)) = (.p2, 9437184*t+3592467) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 9437184*t+3592467) = (.p3, 4718592*t+1796234) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 4718592*t+1796234) = (.p4, 2359296*t+898117) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 2359296*t+898117) = (.p5, 1179648*t+449059) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 1179648*t+449059) = (.p6, 589824*t+224530) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 589824*t+224530) = (.p0, 294912*t+112265) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 294912*t+112265) = (.p1, 147456*t+56133) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 147456*t+56133) = (.p2, 73728*t+28067) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 73728*t+28067) = (.p3, 36864*t+14034) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 36864*t+14034) = (.p4, 18432*t+7017) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 18432*t+7017) = (.p5, 9216*t+3509) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 9216*t+3509) = (.p6, 4608*t+1755) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 4608*t+1755) = (.p0, 6912*t+2633) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 6912*t+2633) = (.p1, 3456*t+1317) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h14 : next (.p1, 3456*t+1317) = (.p2, 1728*t+659) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h15 : next (.p2, 1728*t+659) = (.p3, 864*t+330) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h16 : next (.p3, 864*t+330) = (.p4, 432*t+165) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h17 : next (.p4, 432*t+165) = (.p5, 216*t+83) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h18 : next (.p5, 216*t+83) = (.p6, 108*t+42) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h19 : next (.p6, 108*t+42) = (.p0, 54*t+21) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h20 : next (.p0, 54*t+21) = (.p1, 27*t+11) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

theorem b1_inverse_ray_12 (t : Nat) :
    run (.p1, 6*(64*t+27)) 7 = (.p1, 27*t+12) := by
  have h0 : next (.p1, 6*(64*t+27)) = (.p2, 576*t+243) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 576*t+243) = (.p3, 288*t+122) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 288*t+122) = (.p4, 144*t+61) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 144*t+61) = (.p5, 72*t+31) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 72*t+31) = (.p6, 36*t+16) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 36*t+16) = (.p0, 18*t+8) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 18*t+8) = (.p1, 27*t+12) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_inverse_ray_13 (t : Nat) :
    run (.p1, 6*(64*t+29)) 7 = (.p1, 27*t+13) := by
  have h0 : next (.p1, 6*(64*t+29)) = (.p2, 576*t+261) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 576*t+261) = (.p3, 288*t+131) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 288*t+131) = (.p4, 432*t+197) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 432*t+197) = (.p5, 216*t+99) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 216*t+99) = (.p6, 108*t+50) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 108*t+50) = (.p0, 54*t+25) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 54*t+25) = (.p1, 27*t+13) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_inverse_ray_14 (t : Nat) :
    run (.p1, 6*(24576*t+12091)) 14 = (.p1, 27*t+14) := by
  have h0 : next (.p1, 6*(24576*t+12091)) = (.p2, 221184*t+108819) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 221184*t+108819) = (.p3, 110592*t+54410) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 110592*t+54410) = (.p4, 55296*t+27205) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 55296*t+27205) = (.p5, 27648*t+13603) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 27648*t+13603) = (.p6, 13824*t+6802) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 13824*t+6802) = (.p0, 6912*t+3401) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 6912*t+3401) = (.p1, 3456*t+1701) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 3456*t+1701) = (.p2, 1728*t+851) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 1728*t+851) = (.p3, 864*t+426) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 864*t+426) = (.p4, 432*t+213) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 432*t+213) = (.p5, 216*t+107) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 216*t+107) = (.p6, 108*t+54) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 108*t+54) = (.p0, 54*t+27) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 54*t+27) = (.p1, 27*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem b1_inverse_ray_15 (t : Nat) :
    run (.p1, 6*(1048576*t+554715)) 21 = (.p1, 27*t+15) := by
  have h0 : next (.p1, 6*(1048576*t+554715)) = (.p2, 9437184*t+4992435) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 9437184*t+4992435) = (.p3, 4718592*t+2496218) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 4718592*t+2496218) = (.p4, 2359296*t+1248109) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 2359296*t+1248109) = (.p5, 1179648*t+624055) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 1179648*t+624055) = (.p6, 589824*t+312028) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 589824*t+312028) = (.p0, 294912*t+156014) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 294912*t+156014) = (.p1, 442368*t+234021) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 442368*t+234021) = (.p2, 221184*t+117011) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 221184*t+117011) = (.p3, 110592*t+58506) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 110592*t+58506) = (.p4, 55296*t+29253) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 55296*t+29253) = (.p5, 27648*t+14627) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 27648*t+14627) = (.p6, 13824*t+7314) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 13824*t+7314) = (.p0, 6912*t+3657) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 6912*t+3657) = (.p1, 3456*t+1829) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h14 : next (.p1, 3456*t+1829) = (.p2, 1728*t+915) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h15 : next (.p2, 1728*t+915) = (.p3, 864*t+458) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h16 : next (.p3, 864*t+458) = (.p4, 432*t+229) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h17 : next (.p4, 432*t+229) = (.p5, 216*t+115) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h18 : next (.p5, 216*t+115) = (.p6, 108*t+58) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h19 : next (.p6, 108*t+58) = (.p0, 54*t+29) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h20 : next (.p0, 54*t+29) = (.p1, 27*t+15) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

theorem b1_inverse_ray_16 (t : Nat) :
    run (.p1, 6*(8192*t+4637)) 14 = (.p1, 27*t+16) := by
  have h0 : next (.p1, 6*(8192*t+4637)) = (.p2, 73728*t+41733) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 73728*t+41733) = (.p3, 36864*t+20867) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 36864*t+20867) = (.p4, 55296*t+31301) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 55296*t+31301) = (.p5, 27648*t+15651) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 27648*t+15651) = (.p6, 13824*t+7826) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 13824*t+7826) = (.p0, 6912*t+3913) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 6912*t+3913) = (.p1, 3456*t+1957) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 3456*t+1957) = (.p2, 1728*t+979) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 1728*t+979) = (.p3, 864*t+490) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 864*t+490) = (.p4, 432*t+245) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 432*t+245) = (.p5, 216*t+123) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 216*t+123) = (.p6, 108*t+62) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 108*t+62) = (.p0, 54*t+31) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 54*t+31) = (.p1, 27*t+16) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem b1_inverse_ray_17 (t : Nat) :
    run (.p1, 6*(8192*t+4939)) 14 = (.p1, 27*t+17) := by
  have h0 : next (.p1, 6*(8192*t+4939)) = (.p2, 73728*t+44451) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 73728*t+44451) = (.p3, 36864*t+22226) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 36864*t+22226) = (.p4, 18432*t+11113) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 18432*t+11113) = (.p5, 9216*t+5557) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 9216*t+5557) = (.p6, 4608*t+2779) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 4608*t+2779) = (.p0, 6912*t+4169) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 6912*t+4169) = (.p1, 3456*t+2085) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 3456*t+2085) = (.p2, 1728*t+1043) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 1728*t+1043) = (.p3, 864*t+522) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 864*t+522) = (.p4, 432*t+261) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 432*t+261) = (.p5, 216*t+131) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 216*t+131) = (.p6, 108*t+66) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 108*t+66) = (.p0, 54*t+33) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 54*t+33) = (.p1, 27*t+17) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem b1_inverse_ray_18 (t : Nat) :
    run (.p1, 6*(192*t+123)) 7 = (.p1, 27*t+18) := by
  have h0 : next (.p1, 6*(192*t+123)) = (.p2, 1728*t+1107) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1728*t+1107) = (.p3, 864*t+554) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 864*t+554) = (.p4, 432*t+277) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 432*t+277) = (.p5, 216*t+139) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 216*t+139) = (.p6, 108*t+70) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 108*t+70) = (.p0, 54*t+35) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 54*t+35) = (.p1, 27*t+18) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_inverse_ray_19 (t : Nat) :
    run (.p1, 6*(134217728*t+90443579)) 28 = (.p1, 27*t+19) := by
  have h0 : next (.p1, 6*(134217728*t+90443579)) = (.p2, 1207959552*t+813992211) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1207959552*t+813992211) = (.p3, 603979776*t+406996106) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 603979776*t+406996106) = (.p4, 301989888*t+203498053) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 301989888*t+203498053) = (.p5, 150994944*t+101749027) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 150994944*t+101749027) = (.p6, 75497472*t+50874514) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 75497472*t+50874514) = (.p0, 37748736*t+25437257) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 37748736*t+25437257) = (.p1, 18874368*t+12718629) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 18874368*t+12718629) = (.p2, 9437184*t+6359315) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 9437184*t+6359315) = (.p3, 4718592*t+3179658) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 4718592*t+3179658) = (.p4, 2359296*t+1589829) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 2359296*t+1589829) = (.p5, 1179648*t+794915) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 1179648*t+794915) = (.p6, 589824*t+397458) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 589824*t+397458) = (.p0, 294912*t+198729) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 294912*t+198729) = (.p1, 147456*t+99365) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h14 : next (.p1, 147456*t+99365) = (.p2, 73728*t+49683) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h15 : next (.p2, 73728*t+49683) = (.p3, 36864*t+24842) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h16 : next (.p3, 36864*t+24842) = (.p4, 18432*t+12421) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h17 : next (.p4, 18432*t+12421) = (.p5, 9216*t+6211) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h18 : next (.p5, 9216*t+6211) = (.p6, 4608*t+3106) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h19 : next (.p6, 4608*t+3106) = (.p0, 2304*t+1553) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h20 : next (.p0, 2304*t+1553) = (.p1, 1152*t+777) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h21 : next (.p1, 1152*t+777) = (.p2, 576*t+389) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h22 : next (.p2, 576*t+389) = (.p3, 288*t+195) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h23 : next (.p3, 288*t+195) = (.p4, 432*t+293) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h24 : next (.p4, 432*t+293) = (.p5, 216*t+147) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h25 : next (.p5, 216*t+147) = (.p6, 108*t+74) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h26 : next (.p6, 108*t+74) = (.p0, 54*t+37) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h27 : next (.p0, 54*t+37) = (.p1, 27*t+19) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]

theorem b1_inverse_ray_20 (t : Nat) :
    run (.p1, 6*(8192*t+5851)) 14 = (.p1, 27*t+20) := by
  have h0 : next (.p1, 6*(8192*t+5851)) = (.p2, 73728*t+52659) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 73728*t+52659) = (.p3, 36864*t+26330) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 36864*t+26330) = (.p4, 18432*t+13165) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 18432*t+13165) = (.p5, 9216*t+6583) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 9216*t+6583) = (.p6, 4608*t+3292) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 4608*t+3292) = (.p0, 2304*t+1646) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 2304*t+1646) = (.p1, 3456*t+2469) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 3456*t+2469) = (.p2, 1728*t+1235) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 1728*t+1235) = (.p3, 864*t+618) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 864*t+618) = (.p4, 432*t+309) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 432*t+309) = (.p5, 216*t+155) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 216*t+155) = (.p6, 108*t+78) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 108*t+78) = (.p0, 54*t+39) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 54*t+39) = (.p1, 27*t+20) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem b1_inverse_ray_21 (t : Nat) :
    run (.p1, 6*(8192*t+5947)) 14 = (.p1, 27*t+21) := by
  have h0 : next (.p1, 6*(8192*t+5947)) = (.p2, 73728*t+53523) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 73728*t+53523) = (.p3, 36864*t+26762) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 36864*t+26762) = (.p4, 18432*t+13381) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 18432*t+13381) = (.p5, 9216*t+6691) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 9216*t+6691) = (.p6, 4608*t+3346) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 4608*t+3346) = (.p0, 2304*t+1673) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 2304*t+1673) = (.p1, 1152*t+837) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 1152*t+837) = (.p2, 576*t+419) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 576*t+419) = (.p3, 288*t+210) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 288*t+210) = (.p4, 144*t+105) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 144*t+105) = (.p5, 72*t+53) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 72*t+53) = (.p6, 36*t+27) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 36*t+27) = (.p0, 54*t+41) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 54*t+41) = (.p1, 27*t+21) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem b1_inverse_ray_22 (t : Nat) :
    run (.p1, 6*(8192*t+6459)) 14 = (.p1, 27*t+22) := by
  have h0 : next (.p1, 6*(8192*t+6459)) = (.p2, 73728*t+58131) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 73728*t+58131) = (.p3, 36864*t+29066) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 36864*t+29066) = (.p4, 18432*t+14533) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 18432*t+14533) = (.p5, 9216*t+7267) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 9216*t+7267) = (.p6, 4608*t+3634) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 4608*t+3634) = (.p0, 2304*t+1817) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 2304*t+1817) = (.p1, 1152*t+909) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 1152*t+909) = (.p2, 576*t+455) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 576*t+455) = (.p3, 288*t+228) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 288*t+228) = (.p4, 144*t+114) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 144*t+114) = (.p5, 216*t+171) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 216*t+171) = (.p6, 108*t+86) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 108*t+86) = (.p0, 54*t+43) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 54*t+43) = (.p1, 27*t+22) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem b1_inverse_ray_23 (t : Nat) :
    run (.p1, 6*(24576*t+20283)) 14 = (.p1, 27*t+23) := by
  have h0 : next (.p1, 6*(24576*t+20283)) = (.p2, 221184*t+182547) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 221184*t+182547) = (.p3, 110592*t+91274) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 110592*t+91274) = (.p4, 55296*t+45637) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 55296*t+45637) = (.p5, 27648*t+22819) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 27648*t+22819) = (.p6, 13824*t+11410) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 13824*t+11410) = (.p0, 6912*t+5705) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 6912*t+5705) = (.p1, 3456*t+2853) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 3456*t+2853) = (.p2, 1728*t+1427) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 1728*t+1427) = (.p3, 864*t+714) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 864*t+714) = (.p4, 432*t+357) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 432*t+357) = (.p5, 216*t+179) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 216*t+179) = (.p6, 108*t+90) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 108*t+90) = (.p0, 54*t+45) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 54*t+45) = (.p1, 27*t+23) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

theorem b1_inverse_ray_24 (t : Nat) :
    run (.p1, 6*(134217728*t+115742523)) 28 = (.p1, 27*t+24) := by
  have h0 : next (.p1, 6*(134217728*t+115742523)) = (.p2, 1207959552*t+1041682707) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1207959552*t+1041682707) = (.p3, 603979776*t+520841354) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 603979776*t+520841354) = (.p4, 301989888*t+260420677) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 301989888*t+260420677) = (.p5, 150994944*t+130210339) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 150994944*t+130210339) = (.p6, 75497472*t+65105170) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 75497472*t+65105170) = (.p0, 37748736*t+32552585) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 37748736*t+32552585) = (.p1, 18874368*t+16276293) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 18874368*t+16276293) = (.p2, 9437184*t+8138147) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 9437184*t+8138147) = (.p3, 4718592*t+4069074) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 4718592*t+4069074) = (.p4, 2359296*t+2034537) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 2359296*t+2034537) = (.p5, 1179648*t+1017269) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 1179648*t+1017269) = (.p6, 589824*t+508635) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 589824*t+508635) = (.p0, 884736*t+762953) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 884736*t+762953) = (.p1, 442368*t+381477) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h14 : next (.p1, 442368*t+381477) = (.p2, 221184*t+190739) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h15 : next (.p2, 221184*t+190739) = (.p3, 110592*t+95370) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h16 : next (.p3, 110592*t+95370) = (.p4, 55296*t+47685) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h17 : next (.p4, 55296*t+47685) = (.p5, 27648*t+23843) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h18 : next (.p5, 27648*t+23843) = (.p6, 13824*t+11922) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h19 : next (.p6, 13824*t+11922) = (.p0, 6912*t+5961) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h20 : next (.p0, 6912*t+5961) = (.p1, 3456*t+2981) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h21 : next (.p1, 3456*t+2981) = (.p2, 1728*t+1491) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h22 : next (.p2, 1728*t+1491) = (.p3, 864*t+746) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h23 : next (.p3, 864*t+746) = (.p4, 432*t+373) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h24 : next (.p4, 432*t+373) = (.p5, 216*t+187) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h25 : next (.p5, 216*t+187) = (.p6, 108*t+94) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h26 : next (.p6, 108*t+94) = (.p0, 54*t+47) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h27 : next (.p0, 54*t+47) = (.p1, 27*t+24) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]

theorem b1_inverse_ray_25 (t : Nat) :
    run (.p1, 6*(134217728*t+120713757)) 28 = (.p1, 27*t+25) := by
  have h0 : next (.p1, 6*(134217728*t+120713757)) = (.p2, 1207959552*t+1086423813) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1207959552*t+1086423813) = (.p3, 603979776*t+543211907) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 603979776*t+543211907) = (.p4, 905969664*t+814817861) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 905969664*t+814817861) = (.p5, 452984832*t+407408931) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 452984832*t+407408931) = (.p6, 226492416*t+203704466) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 226492416*t+203704466) = (.p0, 113246208*t+101852233) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 113246208*t+101852233) = (.p1, 56623104*t+50926117) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h7 : next (.p1, 56623104*t+50926117) = (.p2, 28311552*t+25463059) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h8 : next (.p2, 28311552*t+25463059) = (.p3, 14155776*t+12731530) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h9 : next (.p3, 14155776*t+12731530) = (.p4, 7077888*t+6365765) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h10 : next (.p4, 7077888*t+6365765) = (.p5, 3538944*t+3182883) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h11 : next (.p5, 3538944*t+3182883) = (.p6, 1769472*t+1591442) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h12 : next (.p6, 1769472*t+1591442) = (.p0, 884736*t+795721) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h13 : next (.p0, 884736*t+795721) = (.p1, 442368*t+397861) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h14 : next (.p1, 442368*t+397861) = (.p2, 221184*t+198931) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h15 : next (.p2, 221184*t+198931) = (.p3, 110592*t+99466) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h16 : next (.p3, 110592*t+99466) = (.p4, 55296*t+49733) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h17 : next (.p4, 55296*t+49733) = (.p5, 27648*t+24867) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h18 : next (.p5, 27648*t+24867) = (.p6, 13824*t+12434) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h19 : next (.p6, 13824*t+12434) = (.p0, 6912*t+6217) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h20 : next (.p0, 6912*t+6217) = (.p1, 3456*t+3109) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h21 : next (.p1, 3456*t+3109) = (.p2, 1728*t+1555) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h22 : next (.p2, 1728*t+1555) = (.p3, 864*t+778) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h23 : next (.p3, 864*t+778) = (.p4, 432*t+389) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h24 : next (.p4, 432*t+389) = (.p5, 216*t+195) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h25 : next (.p5, 216*t+195) = (.p6, 108*t+98) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h26 : next (.p6, 108*t+98) = (.p0, 54*t+49) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h27 : next (.p0, 54*t+49) = (.p1, 27*t+25) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]

theorem b1_inverse_ray_26 (t : Nat) :
    run (.p1, 6*(64*t+60)) 7 = (.p1, 27*t+26) := by
  have h0 : next (.p1, 6*(64*t+60)) = (.p2, 576*t+540) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 576*t+540) = (.p3, 864*t+810) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 864*t+810) = (.p4, 432*t+405) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 432*t+405) = (.p5, 216*t+203) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 216*t+203) = (.p6, 108*t+102) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 108*t+102) = (.p0, 54*t+51) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 54*t+51) = (.p1, 27*t+26) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_inverse_ray_27 (t : Nat) :
    run (.p1, 6*(192*t+187)) 7 = (.p1, 27*t+27) := by
  have h0 : next (.p1, 6*(192*t+187)) = (.p2, 1728*t+1683) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1728*t+1683) = (.p3, 864*t+842) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 864*t+842) = (.p4, 432*t+421) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 432*t+421) = (.p5, 216*t+211) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 216*t+211) = (.p6, 108*t+106) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 108*t+106) = (.p0, 54*t+53) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 54*t+53) = (.p1, 27*t+27) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_ancestor_phase_one (z : Nat) (hz : 0 < z) :
    ∃ t k, 0 < t ∧ k ≤ 28 ∧ run (.p1,6*t) k = (.p1,z) := by
  have hbound : (z-1) % 27 < 27 := Nat.mod_lt _ (by decide)

  by_cases hpart : (z-1) % 27 < 13
  ·

    by_cases hpart : (z-1) % 27 < 6
    ·

      by_cases hpart : (z-1) % 27 < 3
      ·

        by_cases hpart : (z-1) % 27 < 1
        ·

          have hr : (z-1) % 27 = 0 := by omega
          have heq : z = 27*((z-1)/27)+1 := by omega
          refine ⟨8192*((z-1)/27)+59,14,?_,by decide,?_⟩
          · omega
          · have path := b1_inverse_ray_01 ((z-1)/27)
            rw [← heq] at path
            exact path

        ·

          by_cases hpart : (z-1) % 27 < 2
          ·

            have hr : (z-1) % 27 = 1 := by omega
            have heq : z = 27*((z-1)/27)+2 := by omega
            refine ⟨64*((z-1)/27)+3,7,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_02 ((z-1)/27)
              rw [← heq] at path
              exact path

          ·

            have hr : (z-1) % 27 = 2 := by omega
            have heq : z = 27*((z-1)/27)+3 := by omega
            refine ⟨3145728*((z-1)/27)+266043,21,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_03 ((z-1)/27)
              rw [← heq] at path
              exact path

      ·

        by_cases hpart : (z-1) % 27 < 4
        ·

          have hr : (z-1) % 27 = 3 := by omega
          have heq : z = 27*((z-1)/27)+4 := by omega
          refine ⟨1048576*((z-1)/27)+127517,21,?_,by decide,?_⟩
          · omega
          · have path := b1_inverse_ray_04 ((z-1)/27)
            rw [← heq] at path
            exact path

        ·

          by_cases hpart : (z-1) % 27 < 5
          ·

            have hr : (z-1) % 27 = 4 := by omega
            have heq : z = 27*((z-1)/27)+5 := by omega
            refine ⟨24576*((z-1)/27)+3899,14,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_05 ((z-1)/27)
              rw [← heq] at path
              exact path

          ·

            have hr : (z-1) % 27 = 5 := by omega
            have heq : z = 27*((z-1)/27)+6 := by omega
            refine ⟨64*((z-1)/27)+11,7,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_06 ((z-1)/27)
              rw [← heq] at path
              exact path

    ·

      by_cases hpart : (z-1) % 27 < 9
      ·

        by_cases hpart : (z-1) % 27 < 7
        ·

          have hr : (z-1) % 27 = 6 := by omega
          have heq : z = 27*((z-1)/27)+7 := by omega
          refine ⟨64*((z-1)/27)+15,7,?_,by decide,?_⟩
          · omega
          · have path := b1_inverse_ray_07 ((z-1)/27)
            rw [← heq] at path
            exact path

        ·

          by_cases hpart : (z-1) % 27 < 8
          ·

            have hr : (z-1) % 27 = 7 := by omega
            have heq : z = 27*((z-1)/27)+8 := by omega
            refine ⟨1048576*((z-1)/27)+282427,21,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_08 ((z-1)/27)
              rw [← heq] at path
              exact path

          ·

            have hr : (z-1) % 27 = 8 := by omega
            have heq : z = 27*((z-1)/27)+9 := by omega
            refine ⟨192*((z-1)/27)+59,7,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_09 ((z-1)/27)
              rw [← heq] at path
              exact path

      ·

        by_cases hpart : (z-1) % 27 < 11
        ·

          by_cases hpart : (z-1) % 27 < 10
          ·

            have hr : (z-1) % 27 = 9 := by omega
            have heq : z = 27*((z-1)/27)+10 := by omega
            refine ⟨1048576*((z-1)/27)+360507,21,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_10 ((z-1)/27)
              rw [← heq] at path
              exact path

          ·

            have hr : (z-1) % 27 = 10 := by omega
            have heq : z = 27*((z-1)/27)+11 := by omega
            refine ⟨1048576*((z-1)/27)+399163,21,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_11 ((z-1)/27)
              rw [← heq] at path
              exact path

        ·

          by_cases hpart : (z-1) % 27 < 12
          ·

            have hr : (z-1) % 27 = 11 := by omega
            have heq : z = 27*((z-1)/27)+12 := by omega
            refine ⟨64*((z-1)/27)+27,7,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_12 ((z-1)/27)
              rw [← heq] at path
              exact path

          ·

            have hr : (z-1) % 27 = 12 := by omega
            have heq : z = 27*((z-1)/27)+13 := by omega
            refine ⟨64*((z-1)/27)+29,7,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_13 ((z-1)/27)
              rw [← heq] at path
              exact path

  ·

    by_cases hpart : (z-1) % 27 < 20
    ·

      by_cases hpart : (z-1) % 27 < 16
      ·

        by_cases hpart : (z-1) % 27 < 14
        ·

          have hr : (z-1) % 27 = 13 := by omega
          have heq : z = 27*((z-1)/27)+14 := by omega
          refine ⟨24576*((z-1)/27)+12091,14,?_,by decide,?_⟩
          · omega
          · have path := b1_inverse_ray_14 ((z-1)/27)
            rw [← heq] at path
            exact path

        ·

          by_cases hpart : (z-1) % 27 < 15
          ·

            have hr : (z-1) % 27 = 14 := by omega
            have heq : z = 27*((z-1)/27)+15 := by omega
            refine ⟨1048576*((z-1)/27)+554715,21,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_15 ((z-1)/27)
              rw [← heq] at path
              exact path

          ·

            have hr : (z-1) % 27 = 15 := by omega
            have heq : z = 27*((z-1)/27)+16 := by omega
            refine ⟨8192*((z-1)/27)+4637,14,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_16 ((z-1)/27)
              rw [← heq] at path
              exact path

      ·

        by_cases hpart : (z-1) % 27 < 18
        ·

          by_cases hpart : (z-1) % 27 < 17
          ·

            have hr : (z-1) % 27 = 16 := by omega
            have heq : z = 27*((z-1)/27)+17 := by omega
            refine ⟨8192*((z-1)/27)+4939,14,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_17 ((z-1)/27)
              rw [← heq] at path
              exact path

          ·

            have hr : (z-1) % 27 = 17 := by omega
            have heq : z = 27*((z-1)/27)+18 := by omega
            refine ⟨192*((z-1)/27)+123,7,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_18 ((z-1)/27)
              rw [← heq] at path
              exact path

        ·

          by_cases hpart : (z-1) % 27 < 19
          ·

            have hr : (z-1) % 27 = 18 := by omega
            have heq : z = 27*((z-1)/27)+19 := by omega
            refine ⟨134217728*((z-1)/27)+90443579,28,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_19 ((z-1)/27)
              rw [← heq] at path
              exact path

          ·

            have hr : (z-1) % 27 = 19 := by omega
            have heq : z = 27*((z-1)/27)+20 := by omega
            refine ⟨8192*((z-1)/27)+5851,14,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_20 ((z-1)/27)
              rw [← heq] at path
              exact path

    ·

      by_cases hpart : (z-1) % 27 < 23
      ·

        by_cases hpart : (z-1) % 27 < 21
        ·

          have hr : (z-1) % 27 = 20 := by omega
          have heq : z = 27*((z-1)/27)+21 := by omega
          refine ⟨8192*((z-1)/27)+5947,14,?_,by decide,?_⟩
          · omega
          · have path := b1_inverse_ray_21 ((z-1)/27)
            rw [← heq] at path
            exact path

        ·

          by_cases hpart : (z-1) % 27 < 22
          ·

            have hr : (z-1) % 27 = 21 := by omega
            have heq : z = 27*((z-1)/27)+22 := by omega
            refine ⟨8192*((z-1)/27)+6459,14,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_22 ((z-1)/27)
              rw [← heq] at path
              exact path

          ·

            have hr : (z-1) % 27 = 22 := by omega
            have heq : z = 27*((z-1)/27)+23 := by omega
            refine ⟨24576*((z-1)/27)+20283,14,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_23 ((z-1)/27)
              rw [← heq] at path
              exact path

      ·

        by_cases hpart : (z-1) % 27 < 25
        ·

          by_cases hpart : (z-1) % 27 < 24
          ·

            have hr : (z-1) % 27 = 23 := by omega
            have heq : z = 27*((z-1)/27)+24 := by omega
            refine ⟨134217728*((z-1)/27)+115742523,28,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_24 ((z-1)/27)
              rw [← heq] at path
              exact path

          ·

            have hr : (z-1) % 27 = 24 := by omega
            have heq : z = 27*((z-1)/27)+25 := by omega
            refine ⟨134217728*((z-1)/27)+120713757,28,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_25 ((z-1)/27)
              rw [← heq] at path
              exact path

        ·

          by_cases hpart : (z-1) % 27 < 26
          ·

            have hr : (z-1) % 27 = 25 := by omega
            have heq : z = 27*((z-1)/27)+26 := by omega
            refine ⟨64*((z-1)/27)+60,7,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_26 ((z-1)/27)
              rw [← heq] at path
              exact path

          ·

            have hr : (z-1) % 27 = 26 := by omega
            have heq : z = 27*((z-1)/27)+27 := by omega
            refine ⟨192*((z-1)/27)+187,7,?_,by decide,?_⟩
            · omega
            · have path := b1_inverse_ray_27 ((z-1)/27)
              rw [← heq] at path
              exact path


theorem phase_one_capture_of_b1_alone (hB1 : B1Obligation) (z : Nat) (hz : 0 < z) :
    Captured (.p1,z) := by
  obtain ⟨t,k,ht,_,meet⟩ := b1_ancestor_phase_one z hz
  have source : 3*(2*t) = 6*t := by omega
  have captured : Captured (.p1,6*t) := by simpa only [source] using hB1 t ht
  have future := captured_run (.p1,6*t) captured k
  rw [meet] at future
  exact future

def alignmentOne : Phase → Nat
  | .p0 => 1 | .p1 => 0 | .p2 => 6 | .p3 => 5
  | .p4 => 4 | .p5 => 3 | .p6 => 2

theorem alignmentOne_bound (p : Phase) : alignmentOne p ≤ 6 := by
  cases p <;> decide

theorem alignmentOne_phase (p : Phase) (z : Nat) :
    (run (p,z) (alignmentOne p)).1 = .p1 := by
  cases p <;> rfl

/-- A complete universal capture theorem with B1 as its sole unresolved premise. -/
theorem global_capture_of_b1_alone (hB1 : B1Obligation)
    (p : Phase) (z : Nat) (hz : 0 < z) : Captured (p,z) := by
  have positive := run_pos (p,z) hz (alignmentOne p)
  have aligned : run (p,z) (alignmentOne p) = (.p1,(run (p,z) (alignmentOne p)).2) := by
    apply Prod.ext
    · exact alignmentOne_phase p z
    · rfl
  apply captured_of_run (p,z) (alignmentOne p)
  rw [aligned]
  exact phase_one_capture_of_b1_alone hB1 _ positive

theorem global_capture_iff_b1_alone :
    (∀ p z, 0 < z → Captured (p,z)) ↔ B1Obligation := by
  constructor
  · intro h t ht
    exact h .p1 (3*(2*t)) (by omega)
  · exact global_capture_of_b1_alone

theorem global_safe_physical_capture_of_b1_alone (hB1 : B1Obligation)
    (p : Phase) (n : Nat) (hs : PhysicalSafe p n) :
    ∃ k q, physicalRun (p,(n : Int)) k = (q,physical q (cycleValue q)) := by
  have obligations := global_capture_iff_three.mp (global_capture_of_b1_alone hB1)
  exact global_safe_physical_capture_of_three obligations.1 obligations.2.1 obligations.2.2 p n hs

end Collatz.SevenStepCertificate
