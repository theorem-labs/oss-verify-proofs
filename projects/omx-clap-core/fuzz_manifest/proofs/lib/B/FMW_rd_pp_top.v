(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pp_top.v (a working branch e2e59892bef). *)
(* lv2_locate_manifest_readings on fm.asan-ubsan, segment PP (FMW_rd_top.v SEG_P): rd_P_holds from its pieces -- P's own
   stretch and the space body (FMW_rd_pp.v pp_p_body), the three inner loops (FMW_rd_pp_w1/_w2/_w3.v), the store of
   the name's length at the ':' and the strchr stretch at the '<' (FMW_rd_pp_st.v pp_l3e_holds, pp_st_holds), chained
   through the cut statements of FMW_rd_pp_cuts.v: ST -> W3 -> L3E -> W2 -> W1 -> P. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YG0f YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_cuts FMW_rd_pp_cuts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_pp FMW_rd_pp_w1 FMW_rd_pp_w2 FMW_rd_pp_w3 FMW_rd_pp_st.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRCHR : astrchr_realizes tfibsegs B PC_strchr.

(* FMW_rd_top.v SEG_P *)
Theorem rd_P_holds : forall f, rd_seg_L B CTX f -> rd_seg_C8 B CTX (S f) -> rd_seg_P B CTX (S f).
Proof.
intros f HL HC8.
assert (HST : pp_seg_ST B CTX f) by (eapply pp_st_holds; eassumption).
assert (HW3 : pp_seg_W3 B CTX f) by (eapply pp_w3_holds; eassumption).
assert (HL3E : pp_seg_L3E B CTX f) by (eapply pp_l3e_holds; eassumption).
assert (HW2 : pp_seg_W2 B CTX f) by (eapply pp_w2_holds; eassumption).
assert (HW1 : pp_seg_W1 B CTX f) by (eapply pp_w1_holds; eassumption).
eapply pp_p_body; eassumption.
Qed.
End c.
