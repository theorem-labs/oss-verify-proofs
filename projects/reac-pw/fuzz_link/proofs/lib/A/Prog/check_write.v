(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v; 89 of its 137 lines of code are new or changed and 261 lines of the source are left out. *)
(* check_write and check_mark on image A (fuzz_link.asan 0x88398 and 0x88450, listing offsets AF_check_write = 0x61cc and
   AF_check_mark = 0x6284; listings (internal path) (internal record, sha256 aa7920dd2ebb)
   and (internal path) (internal record, sha256 02dda35ead16)): the walk of their one contract
   lib/A/Prog/check_write_c.v `check_rc_acontract pc` (link_amem.v `aleaf`, K = 16, EV 0, SIDE [], write set []) at both entries.

   The two listings have the same instruction words at every offset but the two jal of the abort path (which reach
   the same targets), so `check_rc_aproof` runs one script at both listing offsets (the run computes on concrete
   offsets: `AF = AF_check_write \/ AF = AF_check_mark`, destructed). +0x00..+0x04 push the frame and save ra;
   +0x08..+0x0c a2 := 1000000 = RC_FAILS; +0x10 `beq a1, a2`; then a0 := (a0 = 0) (+0x20, a1 = RC_FAILS) or
   a0 := (a0 xor a1) <> 0 (+0x14..+0x18); +0x24 `bnez a0` to the abort path; +0x28..+0x30 restore ra, pop, ret.
   The Pre (same_rc_aregs) refutes the abort path on both arms: cr_seqz (a1 = RC_FAILS, so a0 <> 0) and cr_xor
   (a1 <> RC_FAILS, so a0 = a1). check_mark_aproof is in check_mark.v.

   Section hypotheses: LAWS, LV (LinkVals) are the image instance's facts (LAWS is YG0q.AR_laws_ok at the image's
   segments: check_write_aproof_img).

   Proves check_write (kind: function proof). *)
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
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite check_write_c.
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

(* the two branch conditions of the code, read off the run *)
Lemma cr_eq_rc : forall E (r : word), ew E 11 = r ->
  branch_taken BC_EQ (sv_denot E (SOff 11 0)) (sv_denot E (SLit 1000000)) = true -> r = w64 RC_FAILS.
Proof.
intros E r Er Hc. rewrite branch_eq_U, lf_U_reg, U_SLit, Er in Hc. apply Z.eqb_eq in Hc.
change (zcanon 1000000) with 1000000 in Hc. apply bv_eq. unfold w64, RC_FAILS. rewrite Hc.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma cr_ne_rc : forall E (r : word), ew E 11 = r ->
  branch_taken BC_EQ (sv_denot E (SOff 11 0)) (sv_denot E (SLit 1000000)) = false -> r <> w64 RC_FAILS.
Proof.
intros E r Er Hc Hr. rewrite branch_eq_U, lf_U_reg, U_SLit, Er, Hr in Hc. unfold w64, RC_FAILS in Hc.
rewrite unsigned_lit_small in Hc by lia. change (zcanon 1000000) with 1000000 in Hc.
rewrite Z.eqb_refl in Hc. discriminate.
Qed.

(* +0x20 seqz, +0x24 bnez: the abort arm needs a0 = 0 *)
Lemma cr_seqz : forall E (r : word), ew E 10 = r -> r <> w64 0 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_SLTU (SOff 10 0) (SLit 1))) (sv_denot E (SLit 0)) = true -> False.
Proof.
intros E r Er Hr Hc. rewrite branch_ne_U, U_SAlu, lf_U_reg, !U_SLit, Er in Hc.
change (zcanon 1) with 1 in Hc. cbn [zalu_raw] in Hc.
revert Hc. destruct (bv_unsigned r <? 1) eqn:El; intros Hc.
- apply Z.ltb_lt in El. apply Hr. apply bv_eq. pose proof (bv_unsigned_in_range 64 r) as H.
  change (bv_modulus 64) with (2 ^ 64) in H. unfold w64. rewrite unsigned_lit_small by lia. lia.
- vm_compute in Hc. discriminate.
Qed.

(* +0x14 xor, +0x18 snez, +0x24 bnez: the abort arm needs a0 <> a1 *)
Lemma cr_xor : forall E (r : word), ew E 10 = r -> ew E 11 = r ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff 10 0) (SOff 11 0))))
    (sv_denot E (SLit 0)) = true -> False.
Proof.
intros E r E10 E11 Hc. rewrite branch_ne_U, !U_SAlu, !lf_U_reg, !U_SLit, E10, E11 in Hc.
cbn [zalu_raw] in Hc. rewrite Z.lxor_nilpotent in Hc. vm_compute in Hc. discriminate.
Qed.

Theorem check_rc_aproof : forall AF, AF = AF_check_write \/ AF = AF_check_mark ->
  forall rlo rhi, check_rc_acontract SK SEGS rlo rhi B (BASE + AF).
Proof.
intros AF HAF rlo rhi. unfold check_rc_acontract, aleaf, check_rc_apost, check_rc_awr.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HPre.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & _).
unfold check_rc_apre, same_rc_aregs in HPre. destruct HPre as (HPf & HPn).
unfold CHECK_RC_AK, CHECK_RC_AFRAME in *. unfold YK0s.ret_ok in Hret.
pose proof HJ as HJ0.
assert (HS : st_ok_pi SEGS VAL (lf_E regs) (lf_ss AF 16)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF)) memc (seg_rom SEGS))))
  by (eapply lf_entry; [vm_compute; reflexivity | lia | exact HJ | exact H16 | exact Hwlo | exact Hwhi]).
unfold cfg_at, w64.
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
destruct HAF as [-> | ->].
all: paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
all: lf_kept HFr W 16 (spZ regs) UNk; clear HF HFr; lf_fold UN HGc UNk HG W memc 16 (spZ regs).
all: psrr_branch_tok RUN BR HS SHOK Bspan.
(* +0x10 `beq a1, a2`, then the arm, then +0x24 `bnez a0` *)
all: paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
all: lf_kept HFr W 16 (spZ regs) UNk; clear HF HFr; lf_fold UN HGc UNk HG W memc 16 (spZ regs).
all: psrr_branch_tok RUN BR HS SHOK Bspan.
(* the abort path is refuted on both arms; the other two paths restore ra, pop and return *)
all: first
  [ exfalso; exact (cr_seqz E (getr regs 10) E10 (HPf (cr_eq_rc E _ E11 Hc)) Hc0)
  | exfalso; refine (cr_xor E (getr regs 11) _ E11 Hc0); rewrite E10; exact (HPn (cr_ne_rc E _ E11 Hc))
  | paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |];
    lf_kept HFr W 16 (spZ regs) UNk; clear HF HFr; lf_fold UN HGc UNk HG W memc 16 (spZ regs);
    lf_ret PI LAWS W regs [Z_to_bv 64 SB] HS HAE E1 Hret HJ0 HJ Hwlo Hwhi UN HGc ].
Qed.

Theorem check_write_aproof : forall rlo rhi, check_write_acontract SK SEGS rlo rhi B.
Proof.
intros rlo rhi. unfold check_write_acontract.
replace CHECK_WRITE_A with (BASE + AF_check_write) by (rewrite (lv_text LV); reflexivity).
exact (check_rc_aproof AF_check_write (or_introl eq_refl) rlo rhi).
Qed.
End w.

(* LAWS discharged on the image's segments (lib/Reusable/YG0q.v AR_laws_ok) *)
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem check_write_aproof_img : forall B, LinkVals -> pa_segs = AB1v.tfibsegs ->
  forall rlo rhi, check_write_acontract SK pa_segs rlo rhi B.
Proof.
intros B LV Hsegs.
assert (LAWS : AR_laws pa_segs B) by (rewrite Hsegs; exact (YG0q.AR_laws_ok AB1v.tfibsegs B)).
exact (check_write_aproof SK B LAWS LV).
Qed.
End img.

Print Assumptions check_rc_aproof.
Print Assumptions check_write_aproof.
Print Assumptions check_write_aproof_img.
