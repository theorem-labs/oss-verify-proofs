(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pre.v (a working branch e2e59892bef), re-walked on
   B's code (B-readings.lst lines 1-69). *)
(* lv2_locate_manifest_readings, entry segment PRE (0x81e94 .. RD_L 0x81fa8 / RD_R 0x82374):
   rd_E_holds (FMW_rd_top.v SEG_E) from the pieces FMW_rd_pre_e (0x81e94 .. RD_C2), FMW_rd_pre_c2 (.. snprintf ..
   RD_C3), FMW_rd_pre_c3 (.. strstr .. RD_C4), FMW_rd_pre_c4 (.. fuzz_free .. RD_C5), FMW_rd_pre_c5 (.. RD_R / RD_L),
   whose cuts FMW_rd_pre_cuts.v states. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_cuts FMW_rd_ret.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_pre_k FMW_rd_pre_cuts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_pre_e FMW_rd_pre_c2 FMW_rd_pre_c3 FMW_rd_pre_c4 FMW_rd_pre_c5.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
Hypothesis CELLS : g3_cells B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.
Hypothesis SNPRINTF : asnprintf_realizes tfibsegs B PC_snprintf.
Hypothesis STRSTR : astrstr_realizes tfibsegs B PC_strstr.
Hypothesis MALLOC : fuzz_malloc_spec tfibsegs B CTX_fuzz_malloc.
Hypothesis FREE : fuzz_free_spec tfibsegs B CTX_fuzz_free.

(* FMW_rd_top.v SEG_E: the entry segment, from its pieces (FMW_rd_pre_cuts.v) *)
Theorem rd_E_holds : (forall f, rd_seg_L B CTX f) -> rd_seg_E B CTX.
Proof.
intros SEGL.
assert (C5 : rdp_seg_C5 B CTX) by (eapply rdp_C5_holds; eassumption).
assert (C4 : rdp_seg_C4 B CTX) by (eapply rdp_C4_holds; eassumption).
assert (C3 : rdp_seg_C3 B CTX) by (eapply rdp_C3_holds; eassumption).
assert (C2 : rdp_seg_C2 B CTX) by (eapply rdp_C2_holds; eassumption).
eapply rdp_E_holds; eassumption.
Qed.
End c.
