(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v; 229 of its 269 lines of code are new or changed and 269 lines of the source are left out. *)
(* check_read on image A (fuzz_link.asan 0x86930, listing offset AF_check_read = 0x4764; listing
   (internal path) (internal record, sha256 68ad23d44113)): the walk of its contract
   lib/A/Prog/check_read_c.v `check_read_acontract` (link_amem.v `aleaf_rd`, K = 32 + 2 * ESTACK = 8224, EV 0,
   SIDE [], write set []).

   +0x00..+0x0c push the 32-byte frame (ra, s0, s1); +0x10..+0x14 s0 := a5, s1 := a4; +0x18..+0x34 the rc test of
   check_write (same_rc on a0, a1; the abort arms refuted by check_write.v's cr_seqz / cr_xor); +0x38 `bnez a0` to
   the return (rc <> 0: nothing compared; when a1 = RC_FAILS the Pre makes a0 <> 0, rd_a0_zero refutes the other
   way); else +0x3c..+0x44 wrapper_strcmp(a2, a3) and +0x4c..+0x54 wrapper_strcmp(a4, a5) (0x4304c, LinkWalk.v
   aj_gx_strcmp_at; each string's premises from the Pre by LinkWalkStrArg.v astr_call), each followed by `bnez a0` to
   the abort path, refuted since the Pre makes the two strings of each call equal (rd_ne_zero);
   +0x5c..+0x6c restore, pop, ret. The run and both calls write only [sp - 8224, sp) (LinkWalkNoWrite.v), so the
   Post (True) closes with lf_finish0.

   Section hypotheses: LAWS, LV (LinkVals) are the image instance's facts; STRCMP (lib/A/Rt/RtString.v
   astrcmp_realizes at the wrapper) is discharged on the image by lib/A/Rt/RtStrcmpClosed.v `link_strcmp_closed`
   from the image's asyms record (check_read_aproof_img).

   Proves check_read (kind: function proof). *)
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
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite LinkWalkStrArg index_of_c check_write_c check_write check_read_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString RtStrcmpClosed.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Lemma rd_a0_zero : forall E (r : word), ew E 10 = r ->
  branch_taken BC_NE (sv_denot E (SOff 10 0)) (sv_denot E (SLit 0)) = false -> r = w64 0.
Proof.
intros E r Er Hc. rewrite branch_ne_U, lf_U_reg, U_SLit, Er in Hc. change (zcanon 0) with 0 in Hc.
apply negb_false_iff, Z.eqb_eq in Hc. apply bv_eq. unfold w64. rewrite Hc. reflexivity.
Qed.

Lemma rd_ne_zero : forall E n (r : word), ew E n = r -> r = w64 0 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> False.
Proof. intros E n r Er Hr Hc. rewrite branch_ne_U, lf_U_reg, U_SLit, Er, Hr in Hc. vm_compute in Hc. discriminate. Qed.

Lemma rd_grows_of_present : forall H m m',
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Eh; [exact Hx|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)).
{ unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Eh | exists b; exact Em]. }
destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

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
Hypothesis STRCMP : RtString.astrcmp_realizes SEGS B (pa_sigma LS___interceptor_trampoline_strcmp).

Theorem check_read_aproof : forall rlo rhi, check_read_acontract SK SEGS rlo rhi B.
Proof.
intros rlo rhi. unfold check_read_acontract, aleaf_rd, check_read_apost, check_read_awr.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HRd HPre.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & _).
destruct HPre as (HPf & HPn & HP3).
unfold CHECK_READ_AK, CHECK_READ_AFRAME in *. change ESTACK with 4096 in *.
unfold YK0s.ret_ok in Hret.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as HJ0.
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HS : st_ok_pi SEGS VAL (lf_E regs) (lf_ss AF_check_read 32)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_read)) memc (seg_rom SEGS))))
  by (eapply lf_entry; [vm_compute; reflexivity | lia | exact HJ | exact H16 | lia | exact Hwhi]).
replace (cfg_at SEGS CHECK_READ_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_check_read)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, CHECK_READ_A, AF_check_read; rewrite (lv_text LV); reflexivity).
remember (lf_E regs) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E12 : ew E 12 = getr regs 12) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 12 12%bv eq_refl)).
assert (E13 : ew E 13 = getr regs 13) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 13 13%bv eq_refl)).
assert (E14 : ew E 14 = getr regs 14) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 14 14%bv eq_refl)).
assert (E15 : ew E 15 = getr regs 15) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 15 15%bv eq_refl)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
(* the read-only bytes of the image, at any memory that agrees with the entry's outside the window *)
assert (HROM : forall mT, (forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 8224 (spZ regs) a ->
            aview SEGS (w_H W) mT a = aview SEGS (w_H W) memc a) -> rt_rom_view SEGS B W mT).
{ intros mT U a H1 H2 H3. assert (Hi : in_img SEGS a) by (destruct H1 as (sg & Hin & _ & Hb); exists sg; split; [exact Hin | exact Hb]).
  pose proof (pa_segs_low a Hi) as Hlow.
  rewrite U by (unfold lf_Zs, kLowMemEnd in *; lia). exact (HROD a (or_introl H1) H2 H3). }
(* the window's bytes are present at any later memory that grew from the entry's *)
assert (HWINg : forall mT, mem_grows (rdW W memc) (rdW W mT) ->
          forall a, spZ regs - 8224 <= a < spZ regs -> aview SEGS (w_H W) mT a <> None).
{ intros mT Hg a Ha. apply aview_some_of_apresent. eapply apresent_grows; [exact Hg | apply Hpres; lia]. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) memc)) by constructor.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 8224 (spZ regs) a ->
          aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (HGc : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
(* +0x00 .. +0x20: the frame, s0, s1, RC_FAILS, `beq a1, a4` *)
paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
lf_kept HFr W 8224 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 8224 (spZ regs).
psrr_branch_tok RUN BR HS SHOK Bspan.
(* the arm, then +0x34 `bnez a1` *)
all: paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
all: lf_kept HFr W 8224 (spZ regs) UNk; clear HF HFr; lf_fold UN HGc UNk HG W memc 8224 (spZ regs).
all: psrr_branch_tok RUN BR HS SHOK Bspan.
all: try (exfalso; first
  [ exact (cr_seqz E (getr regs 10) E10 (HPf (cr_eq_rc E _ E11 Hc)) Hc0)
  | refine (cr_xor E (getr regs 11) _ E11 Hc0); rewrite E10; exact (HPn (cr_ne_rc E _ E11 Hc)) ]).
(* +0x38 `bnez a0` (the run stops at once: the branch) *)
all: paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
all: lf_kept HFr W 8224 (spZ regs) UNk; clear HF HFr; lf_fold UN HGc UNk HG W memc 8224 (spZ regs).
all: psrr_branch_tok RUN BR HS SHOK Bspan.
(* a1 = RC_FAILS and a0 = 0 contradict the Pre *)
all: try (exfalso; exact (HPf (cr_eq_rc E _ E11 Hc) (rd_a0_zero E _ E10 Hc1))).
(* a0 <> 0: +0x5c .. +0x6c restore, pop, ret *)
all: try (paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |];
  lf_kept HFr W 8224 (spZ regs) UNk; clear HF HFr; lf_fold UN HGc UNk HG W memc 8224 (spZ regs);
  lf_ret PI LAWS W regs [Z_to_bv 64 SB] HS HAE E1 Hret HJ0 HJ Hwlo Hwhi UN HGc; fail).
(* a0 = 0 (and a1 <> RC_FAILS): the two compares *)
pose proof (rd_a0_zero E _ E10 Hc1) as Hz.
destruct (HP3 Hz) as (k1 & k1' & s1 & s1' & Hk & Hk' & Hs & Hs' & Ak & Ak' & As & As' & <- & <-).
clear Hc Hc0 Hc1.
(* +0x3c .. +0x44: wrapper_strcmp(a2, a3) *)
paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
lf_kept HFr W 8224 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 8224 (spZ regs).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into msA end.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
rewrite Usp in R2.
assert (Usp1 : spZ (ms_regs msA) = spZ regs - 32) by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
eapply SRr_bind.
{ eapply (aj_gx_strcmp_at SK SEGS B LAWS pa_segs_low _ STRCMP G XO OUT W (ms_regs msA) (ms_mem msA) STK sp0 FP ly S
      W0 mem0 md0 own lyc Sc _ k (aarg regs 2) (aarg regs 3) k1 k1 _ HGX HJ).
  - rewrite Usp1; lia.
  - rewrite Usp1; change ESTACK with 4096; lia.
  - rewrite Usp1; lia.
  - rewrite R3, E3; exact Hgp.
  - rewrite R4, E4; exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; lia.
  - rewrite R10, E12; unfold w64; symmetry; apply Z_to_bv_bv_unsigned.
  - rewrite R11, E13; unfold w64; symmetry; apply Z_to_bv_bv_unsigned.
  - exact (proj1 Ak).
  - exact (proj1 Ak').
  - exact (proj1 (astr_call SEGS W regs (ms_regs msA) memc (ms_mem msA) 8224 32 (aarg regs 2) k1 ltac:(lia) ltac:(change ESTACK with 4096; lia) Usp1 ltac:(lia) ltac:(lia) UN (HWINg _ HGc) Hk Ak)).
  - exact (proj1 (astr_call SEGS W regs (ms_regs msA) memc (ms_mem msA) 8224 32 (aarg regs 3) k1 ltac:(lia) ltac:(change ESTACK with 4096; lia) Usp1 ltac:(lia) ltac:(lia) UN (HWINg _ HGc) Hk' Ak')).
  - exact (proj1 (proj2 (astr_call SEGS W regs (ms_regs msA) memc (ms_mem msA) 8224 32 (aarg regs 2) k1 ltac:(lia) ltac:(change ESTACK with 4096; lia) Usp1 ltac:(lia) ltac:(lia) UN (HWINg _ HGc) Hk Ak))).
  - exact (proj1 (proj2 (astr_call SEGS W regs (ms_regs msA) memc (ms_mem msA) 8224 32 (aarg regs 3) k1 ltac:(lia) ltac:(change ESTACK with 4096; lia) Usp1 ltac:(lia) ltac:(lia) UN (HWINg _ HGc) Hk' Ak'))).
  - exact (proj2 (proj2 (astr_call SEGS W regs (ms_regs msA) memc (ms_mem msA) 8224 32 (aarg regs 2) k1 ltac:(lia) ltac:(change ESTACK with 4096; lia) Usp1 ltac:(lia) ltac:(lia) UN (HWINg _ HGc) Hk Ak))).
  - exact (proj2 (proj2 (astr_call SEGS W regs (ms_regs msA) memc (ms_mem msA) 8224 32 (aarg regs 3) k1 ltac:(lia) ltac:(change ESTACK with 4096; lia) Usp1 ltac:(lia) ltac:(lia) UN (HWINg _ HGc) Hk' Ak'))).
  - exact (HROM _ UN). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hiff & Hkeep & Hpres2 & Hsm).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  unfold region_kept. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]. rewrite Usp. split.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hkeep; [lia|]. rewrite Usp1. change ESTACK with 4096. lia.
  - intros a Ha Hw. apply (writable_kept (segs := SEGS) (w_H W) (ms_mem msA) mem2); [intros Hp; exact (Hpres2 _ Hp) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 40)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE' : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (E1' : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
assert (E3' : ew E' 3 = getr regs 3) by (rewrite OLD by lia; exact E3).
assert (E4' : ew E' 4 = getr regs 4) by (rewrite OLD by lia; exact E4).
assert (E14' : ew E' 14 = getr regs 14) by (rewrite OLD by lia; exact E14).
assert (E15' : ew E' 15 = getr regs 15) by (rewrite OLD by lia; exact E15).
assert (E44 : ew E' 44 = getr regs2 10) by (rewrite HE'; reflexivity).
clear HE' OLD.
assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 8224 (spZ regs) a ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hz'. rewrite Hkeep; [apply UN; assumption | exact Ha | rewrite Usp1; change ESTACK with 4096; unfold lf_Zs in Hz'; lia]. }
assert (HGc2 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2))
  by (eapply mem_grows_trans; [exact HGc | apply rd_grows_of_present; exact Hpres2]).
clear UN HGc. rename UN2 into UN. rename HGc2 into HGc.
clear SHOK. assert (SHOK : sh_ok SEGS (SOff 32 0) [] E' (mrestrict (w_H W) mem2)) by constructor.
(* +0x48 `bnez a0`: the two strings are equal, so a0 = 0 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- exfalso. exact (rd_ne_zero E' 44 _ E44 (proj2 Hiff eq_refl) Hc).
- (* +0x4c .. +0x54: wrapper_strcmp(s1, s0) = (a4, a5) *)
  paj_run_tok RUN HS HJ2 SHOK Bspan; [lf_awr |].
  lf_kept HFr W 8224 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 8224 (spZ regs).
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into msB end.
  clear R1 R2 R3 R4 R10 R11. pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
  rewrite Usp' in R2.
  assert (Usp0 : spZ (ms_regs msB) = spZ regs - 32) by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
  eapply SRr_bind.
  { eapply (aj_gx_strcmp_at SK SEGS B LAWS pa_segs_low _ STRCMP G XO OUT W (ms_regs msB) (ms_mem msB) STK sp0 FP ly S
        W0 mem0 md0 own lyc Sc _ k (aarg regs 4) (aarg regs 5) s1 s1 _ HGX HJ2).
    - rewrite Usp0; lia.
    - rewrite Usp0; change ESTACK with 4096; lia.
    - rewrite Usp0; lia.
    - rewrite R3, E3'; exact Hgp.
    - rewrite R4, E4'; exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; lia.
    - rewrite R10, E14'; unfold w64; symmetry; apply Z_to_bv_bv_unsigned.
    - rewrite R11, E15'; unfold w64; symmetry; apply Z_to_bv_bv_unsigned.
    - exact (proj1 As).
    - exact (proj1 As').
    - exact (proj1 (astr_call SEGS W regs (ms_regs msB) memc (ms_mem msB) 8224 32 (aarg regs 4) s1 ltac:(lia) ltac:(change ESTACK with 4096; lia) Usp0 ltac:(lia) ltac:(lia) UN (HWINg _ HGc) Hs As)).
    - exact (proj1 (astr_call SEGS W regs (ms_regs msB) memc (ms_mem msB) 8224 32 (aarg regs 5) s1 ltac:(lia) ltac:(change ESTACK with 4096; lia) Usp0 ltac:(lia) ltac:(lia) UN (HWINg _ HGc) Hs' As')).
    - exact (proj1 (proj2 (astr_call SEGS W regs (ms_regs msB) memc (ms_mem msB) 8224 32 (aarg regs 4) s1 ltac:(lia) ltac:(change ESTACK with 4096; lia) Usp0 ltac:(lia) ltac:(lia) UN (HWINg _ HGc) Hs As))).
    - exact (proj1 (proj2 (astr_call SEGS W regs (ms_regs msB) memc (ms_mem msB) 8224 32 (aarg regs 5) s1 ltac:(lia) ltac:(change ESTACK with 4096; lia) Usp0 ltac:(lia) ltac:(lia) UN (HWINg _ HGc) Hs' As'))).
    - exact (proj2 (proj2 (astr_call SEGS W regs (ms_regs msB) memc (ms_mem msB) 8224 32 (aarg regs 4) s1 ltac:(lia) ltac:(change ESTACK with 4096; lia) Usp0 ltac:(lia) ltac:(lia) UN (HWINg _ HGc) Hs As))).
    - exact (proj2 (proj2 (astr_call SEGS W regs (ms_regs msB) memc (ms_mem msB) 8224 32 (aarg regs 5) s1 ltac:(lia) ltac:(change ESTACK with 4096; lia) Usp0 ltac:(lia) ltac:(lia) UN (HWINg _ HGc) Hs' As'))).
    - exact (HROM _ UN). }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3' & Hiff3 & Hkeep3 & Hpres3 & Hsm3).
  jafter_call_keep_pi HS 80%nat regs3 (mrestrict (w_H W) mem3) HP3' [0]%nat HS3.
  match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    unfold region_kept. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]. rewrite Usp'. split.
    - intros a Ha. apply (mbyte_of_aview SEGS). apply Hkeep3; [lia|]. rewrite Usp0. change ESTACK with 4096. lia.
    - intros a Ha Hw. apply (writable_kept (segs := SEGS) (w_H W) (ms_mem msB) mem3); [intros Hp; exact (Hpres3 _ Hp) | exact Hw]. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc E' 80 (map (getr regs3) CLOB)) as E'' eqn:HE'' in HS.
  assert (HEI'' : img_env VAL A_LIM E'') by (rewrite HE''; apply img_env_havoc; [exact HEI' | cbv; lia]).
  assert (OLD : forall n, (n < 80)%nat -> ew E'' n = ew E' n) by (intros n Hn; rewrite HE''; apply YN3v.ew_havoc_old; exact Hn).
  assert (HAE'' : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) E'') by (rewrite HE''; apply env_agree_havoc_ge; [lia | exact HAE']).
  assert (E1'' : ew E'' 1 = getr regs 1) by (rewrite OLD by lia; exact E1').
  assert (Usp'' : bv_unsigned (ew E'' 2) = spZ regs) by (rewrite OLD by lia; exact Usp').
  assert (E84 : ew E'' 84 = getr regs3 10) by (rewrite HE''; reflexivity).
  clear HE'' OLD.
  assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 8224 (spZ regs) a ->
            aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a).
  { intros a Ha Hz'. rewrite Hkeep3; [apply UN; assumption | exact Ha | rewrite Usp0; change ESTACK with 4096; unfold lf_Zs in Hz'; lia]. }
  assert (HGc3 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem3))
    by (eapply mem_grows_trans; [exact HGc | apply rd_grows_of_present; exact Hpres3]).
  clear UN HGc. rename UN3 into UN. rename HGc3 into HGc.
  clear SHOK. assert (SHOK : sh_ok SEGS (SOff 32 0) [] E'' (mrestrict (w_H W) mem3)) by constructor.
  (* +0x58 `bnez a0` *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + exfalso. match goal with H : branch_taken BC_NE (sv_denot E'' (SOff 84 0)) _ = true |- _ =>
      exact (rd_ne_zero E'' 84 _ E84 (proj2 Hiff3 eq_refl) H) end.
  + (* +0x5c .. +0x6c: restore, pop, ret *)
    paj_run_tok RUN HS HJ3 SHOK Bspan; [lf_awr |].
    lf_kept HFr W 8224 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 8224 (spZ regs).
    lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ =>
      assert (HAEf : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) Ef)
        by (split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE'' nn Hnn) | exact (proj2 HAE'')])
    end.
    lf_ret PI LAWS W regs [Z_to_bv 64 SB] HS HAEf E1'' Hret HJ0 HJ3 Hwlo Hwhi UN HGc.
Qed.
End w.

(* LAWS and STRCMP discharged on the image's segments: lib/Reusable/YG0q.v AR_laws_ok and lib/A/Rt/RtStrcmpClosed.v
   link_strcmp_closed, from the image's asyms record (lib/A/AF0m.v PcapSyms; on the image lib/A/AD2l.v PcapB_syms) *)
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem check_read_aproof_img : forall B, LinkVals -> AF0m.PcapSyms B -> pa_segs = AB1v.tfibsegs ->
  forall rlo rhi, check_read_acontract SK pa_segs rlo rhi B.
Proof.
intros B LV TS Hsegs.
assert (LAWS : AR_laws pa_segs B) by (rewrite Hsegs; exact (YG0q.AR_laws_ok AB1v.tfibsegs B)).
apply (check_read_aproof SK B LAWS LV).
rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs. exact (RtStrcmpClosed.link_strcmp_closed B TS).
Qed.
End img.

Print Assumptions check_read_aproof.
Print Assumptions check_read_aproof_img.
