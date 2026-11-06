(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v; 57 of its 96 lines of code are new or changed and 270 lines of the source are left out. *)
(* check_verdict on image A (fuzz_link.asan 0x885f4, listing offset AF_check_verdict = 0x6428; listing
   (internal path) (internal record, sha256 ac819c2b6a96)): the walk of its contract
   lib/A/Prog/check_verdict_c.v `check_verdict_acontract` (link_amem.v `aleaf`, K = 16, EV 0, SIDE [], write set []).

   +0x00..+0x04 push the 16-byte frame and save ra; +0x08 `bne a0, a1` to +0x18 (the abort path: before_abort, abort);
   +0x0c..+0x14 restore ra, pop, ret. The Pre (a0 = a1) makes the branch fall through; the abort path is refuted at
   the branch. The run writes only the frame (LinkWalkNoWrite.v), so the Post (True) closes with lf_finish0.

   Section hypotheses: LAWS, LV (LinkVals) are the image instance's facts (LAWS is YG0q.AR_laws_ok at the image's
   segments: check_verdict_aproof_img).

   Proves check_verdict (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite check_verdict_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.

Theorem check_verdict_aproof : forall rlo rhi, check_verdict_acontract SK SEGS rlo rhi B.
Proof.
intros rlo rhi. unfold check_verdict_acontract, aleaf, check_verdict_apost, check_verdict_awr.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HPre.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & _).
unfold check_verdict_apre in HPre. unfold CHECK_VERDICT_AK, CHECK_VERDICT_AFRAME in *.
unfold YK0s.ret_ok in Hret.
pose proof HJ as HJ0.
assert (HS : st_ok_pi SEGS VAL (lf_E regs) (lf_ss AF_check_verdict 16)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_verdict)) memc (seg_rom SEGS))))
  by (eapply lf_entry; [vm_compute; reflexivity | lia | exact HJ | exact H16 | exact Hwlo | exact Hwhi]).
replace (cfg_at SEGS CHECK_VERDICT_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_check_verdict)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, CHECK_VERDICT_A, AF_check_verdict; rewrite (lv_text LV); reflexivity).
remember (lf_E regs) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) memc)) by constructor.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 16 (spZ regs) a ->
          aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (HGc : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
(* +0x00 .. +0x08: the frame, `bne a0, a1` *)
paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
lf_kept HFr W 16 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 16 (spZ regs).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a0 <> a1: the abort path, refuted by the Pre *)
  exfalso. rewrite branch_ne_U, !lf_U_reg, E10, E11, HPre, Z.eqb_refl in Hc. discriminate.
- (* +0x0c .. +0x14: restore ra, pop, ret *)
  paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
  lf_kept HFr W 16 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 16 (spZ regs).
  lf_ret PI LAWS W regs [Z_to_bv 64 SB] HS HAE E1 Hret HJ0 HJ Hwlo Hwhi UN HGc.
Qed.
End w.

(* LAWS discharged on the image's segments (lib/Reusable/YG0q.v AR_laws_ok) *)
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem check_verdict_aproof_img : forall B, LinkVals -> pa_segs = AB1v.tfibsegs ->
  forall rlo rhi, check_verdict_acontract SK pa_segs rlo rhi B.
Proof.
intros B LV Hsegs.
assert (LAWS : AR_laws pa_segs B) by (rewrite Hsegs; exact (YG0q.AR_laws_ok AB1v.tfibsegs B)).
exact (check_verdict_aproof SK B LAWS LV).
Qed.
End img.

Print Assumptions check_verdict_aproof.
Print Assumptions check_verdict_aproof_img.
