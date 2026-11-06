(* Rtt102TopProbe.v: prints the generalized signatures of the A' stretch theorems and of the one named condition, so the
   A' composition can pass every argument by position. No lemma. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Rtt102XA Rtt102CKA Rtt102O2A Rtt102FA Rtt102EA
  Rtt102CmpA Rtt102TA.
Set Printing Width 4000.
About Rtt102XA.rtt_seg_x_A.
About Rtt102CKA.rtt_seg_ck_A.
About Rtt102O2A.rtt_seg_o2_A.
About Rtt102FA.rtt_seg_f_A.
About Rtt102EA.rtt_seg_e_A.
About Rtt102CmpA.rtt_seg_cmp_A.
About Rtt102TA.rtt_seg_t_A_cond.
About Rtt102TA.RTT_T_TRACE_AT.
Check Rtt102XA.rtt_seg_x_A.
Check Rtt102CKA.rtt_seg_ck_A.
Check Rtt102O2A.rtt_seg_o2_A.
Check Rtt102FA.rtt_seg_f_A.
Check Rtt102EA.rtt_seg_e_A.
Check Rtt102CmpA.rtt_seg_cmp_A.
Check Rtt102TA.rtt_seg_t_A_cond.
