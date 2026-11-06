(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v, with its module names changed; 405 of its 449 lines of code are new or changed and 265 lines of the source are left out. *)
(* text_buf on image A (fuzz_link.asan 0x863d0, listing offset AF_text_buf = 0x4204; listing
   (internal path) (internal record, sha256 e2ba9446e8c9)): the walk of its contract
   lib/A/Prog/text_buf_c.v `text_buf_acontract` (link_amem.v `aleaf_alloc`, K = 32 + ASTACK, EV 1, LIVE 40,
   MO = mo_malloc MT 40, write set []).

   +0x00..+0x0c push the 32-byte frame (ra, s0, s1); +0x10 `beqz a0`:
   - cap = 0: +0x38..+0x50 a0 := 0, restore, pop, ret (LinkWalk.v apost_leaf);
   - cap <> 0: +0x14..+0x1c s1 := cap + 1, wrapper_malloc(cap + 1) (LinkWalkAlloc.v aj_gx_malloc_d over
     LinkMallocDepot.v amalloc04_rule_d; the frame chain from aleaf_alloc's achain, its trace from text_buf_traces);
     +0x20 `beqz a0` refuted (4096 <= the block); +0x24..+0x30 checked_memset(block, 0x5a, cap + 1) (link_ajkit.v
     aj_gx_intrin_at; the block's bytes are a block of the journal's current state that the call's state did not
     have: in_tmp_block, or bytes of the journal's footprint when the pair was a block at the journal's start);
     +0x34..+0x50 a0 := block, restore, pop, ret. The apost: the kept clause composes the entry run, malloc's
     acall_kept and the run after it (akept_trans, akept_trans_ly) with the fresh block excepted, then drops it
     (LinkWalkAlloc.v akept_drop_block); the shadow clause by ashadow_kept_AR; the meter by mo_le_mono over
     mo_malloc_mono; the depot by alc_depot_fixed (the trace is fixed: text_buf_traces).

   Section hypotheses: LAWS, TL (PALib), LV (LinkVals), MTL (the meter's laws) are the image instance's facts;
   MALLOC (amalloc04_rule_d) is discharged on the image by lib/A/Rt/LinkMallocDepotA.v PcapB_AMALLOC4_D; MEMSET
   (aintrin_realizes OSet at checked_memset) by lib/A/AE2r.v asan_memset_realizes.

   Proves text_buf (kind: function proof). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YG0p YG08 YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite LinkWalkSide LinkWalkAlloc text_buf_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepot.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Lemma tb_unwind_spine : forall (pc0 sp ra s0 : Z) (ch : list (Z * Z * Z)),
  unwind_of_chain pc0 ((sp, ra, s0) :: ch) =
  firstn kUnwindMax (pc0 :: flat_map (fun r => if r =? pc0 then [] else [r]) (ra :: spine ch)).
Proof.
  intros pc0 sp ra s0 ch. unfold unwind_of_chain, spine. f_equal. f_equal.
  cbn [flat_map map]. f_equal. induction ch as [|((x, y), z) ch IH]; [reflexivity|].
  cbn [flat_map map fst snd]. rewrite IH. reflexivity.
Qed.

Lemma tb_mbyte2 : forall segs (H H' : word -> bool) (m m' : word -> option byte) a,
  aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
  intros segs H H' m m' a E. unfold aview in E.
  destruct (mbyte segs (mrestrict H' m') a) as [b'|], (mbyte segs (mrestrict H m) a) as [b|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma tb_grows_of_present : forall H m m',
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Eh; [exact Hx|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)).
{ unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Eh | exists b; exact Em]. }
destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

Lemma tb_grow : forall (H : word -> bool) (m m' : word -> option byte),
  mem_grows (mrestrict H m) (mrestrict H m') -> forall a, apresent H m a -> apresent H m' a.
Proof.
  intros H m m' HG a (Hh & b & Hb). split; [exact Hh|].
  specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh, Hb in HG.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply HG; [discriminate | reflexivity].
Qed.

Lemma tb_nth_rep : forall (x : byte) c i, (i < S c)%nat -> nth_error (repeat x c ++ [x]) i = Some x.
Proof.
  intros x c i Hi. destruct (Nat.lt_ge_cases i c) as [H|H].
  - rewrite nth_error_app1 by (rewrite repeat_length; lia). apply nth_error_repeat. lia.
  - rewrite nth_error_app2 by (rewrite repeat_length; lia).
    replace (i - length (repeat x c))%nat with 0%nat by (rewrite repeat_length; lia). reflexivity.
Qed.

Lemma tb_mbyte_some : forall segs H m a v, aview segs H m a = Some v ->
  mbyte segs (mrestrict H m) a = Some (Z_to_bv 8 v).
Proof.
  intros segs H m a v E. unfold aview in E. destruct (mbyte segs (mrestrict H m) a) as [b|]; [|discriminate].
  cbn in E. injection E as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma tb_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof.
  intros [x1 x2] [y1 y2]. destruct (Z.eq_dec x1 y1), (Z.eq_dec x2 y2);
    [left; congruence | right; congruence | right; congruence | right; congruence].
Qed.

(* the bytes a run left as they were: every byte outside [sp - K, sp) *)
Ltac tb_kept HFr W K sp UN := lf_kept HFr W K sp UN.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis MTL : ameter_laws MT.
Hypothesis MALLOC : amalloc04_rule_d (SK := SK) SEGS B MT.
Hypothesis MEMSET : aintrin_realizes SEGS B OSet (pa_sigma LS___asan_memset).

Definition tb_Q (regs : bvmap 5 word) (W : world SEGS) memc lyc Sc :=
  fun ly2 S2 (W2 : world SEGS) regs2 mem2 (md2 : Model) =>
    mo_le MT Sc S2 (mo_malloc MT TEXT_BUF_LIVE) /\ text_buf_ledpost B Sc S2 /\
    text_buf_apostA SEGS regs (rdW W memc) regs2 (rdW W2 mem2) (ablocks B lyc Sc) (ablocks B ly2 S2).

Theorem text_buf_aproof : forall rlo rhi, text_buf_acontract SK SEGS rlo rhi B MT CTX.
Proof.
intros rlo rhi. unfold text_buf_acontract, aleaf_alloc, text_buf_awr.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch HA Hlive Hmo Hch HCTX _ HPre.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & _).
destruct HPre as (Hcap & HTR).
unfold TEXT_BUF_AK, TEXT_BUF_AFRAME in *. change ASTACK with 16384 in *.
unfold YK0s.ret_ok in Hret.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as HJ0.
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
assert (Etop : ly_top lyc = ly_top ly) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
pose proof (bv_unsigned_in_range 64 (getr regs 10)) as R10r. change (bv_modulus 64) with (2 ^ 64) in R10r.
assert (A0 : aarg regs 0 = bv_unsigned (getr regs 10)) by reflexivity.
set (cap := aarg regs 0) in *.
assert (HS : st_ok_pi SEGS VAL (lf_E regs) (lf_ss AF_text_buf 32)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_text_buf)) memc (seg_rom SEGS))))
  by (eapply lf_entry; [vm_compute; reflexivity | lia | exact HJ | exact H16 | lia | exact Hwhi]).
replace (cfg_at SEGS TEXT_BUF_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_text_buf)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, TEXT_BUF_A, AF_text_buf; rewrite (lv_text LV); reflexivity).
change (SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_text_buf)) memc (seg_rom SEGS)) mdc)
  (apost SK SEGS B (32 + 16384) 1 (fun a => inFP [] a) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
     regs (tb_Q regs W memc lyc Sc))).
remember (lf_E regs) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) memc)) by constructor.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 16416 (spZ regs) a ->
          aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (HGc : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
(* +0x00 .. +0x10: the frame, `beqz a0` *)
paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
lf_kept HFr W 16416 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 16416 (spZ regs).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* cap = 0: +0x38 .. +0x50 *)
  assert (Hc0 : cap = 0).
  { rewrite branch_eq_U, lf_U_reg, U_SLit in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite E10 in Hc.
    change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. exact Hc. }
  paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
  lf_kept HFr W 16416 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 16416 (spZ regs).
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ (restrict _ ?msF) =>
    assert (HAEf : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) Ef)
      by (split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE nn Hnn) | exact (proj2 HAE)]);
    pose proof (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs [Z_to_bv 64 SB] HS HAEf ltac:(vm_compute; reflexivity)) as HPr;
    rename msF into msF0
  end.
  prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
  eapply (paj_ret_at (PL := PL_link) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  rewrite R1; rewrite ?ew_ewset_other by lia; rewrite E1, Hret.
  apply (apost_leaf SK SEGS B LAWS pa_segs_low (32 + 16384) 1 (fun a => inFP [] a)
    G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ _ HJ0).
  + first [ exact HJ | (repeat rewrite wvb_collapse in HJ); exact HJ
          | apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low);
            first [exact HJ | (repeat rewrite wvb_collapse in HJ); exact HJ] ].
  + lia.
  + lia.
  + lia.
  + repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity.
  + repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity.
  + exact HPr.
  + intros a Ha Hw _. exact (UN a Ha Hw).
  + intros a Ha. exact (tb_grow _ _ _ HGc a Ha).
  + intros a Ha. pose proof HJ as (_ & HXO2 & (memS2 & HJ2i & _) & _).
    pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    apply Hpres2. lia.
  + intros x ((lo, hi) & [] & _).
  + unfold tb_Q. split.
    { apply (mo_le_mono MT MTL Sc Sc 0); [apply (mo_le_refl MT MTL) | apply (mo_malloc_nonneg MT MTL); unfold TEXT_BUF_LIVE; lia]. }
    split; [unfold text_buf_ledpost; lia|].
    unfold text_buf_apostA. split.
    * intros _. split; [| apply Permutation_refl].
      rewrite R10. rewrite ?ew_ewset_other by lia. reflexivity.
    * intros Hne. exfalso. exact (Hne Hc0).
- (* cap <> 0: +0x14 .. +0x1c, wrapper_malloc(cap + 1) *)
  assert (Hcnz : cap <> 0).
  { intros H0. rewrite branch_eq_U, lf_U_reg, U_SLit in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite E10 in Hc.
    change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc. exact (Hc H0). }
  assert (VB : BASE = 0x821cc) by exact (lv_text LV).
  assert (HcapB : 0 <= cap < 40) by (unfold cap, aarg, argZ in *; lia).
  paj_run_tok RUN HS HJ SHOK Bspan; [lf_awr |].
  lf_kept HFr W 16416 (spZ regs) UNk. clear HF HFr. lf_fold UN HGc UNk HG W memc 16416 (spZ regs).
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into msA end.
  pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10.
  rewrite ?ew_ewset_other in R2, R3, R4, R8, R10 by lia.
  rewrite Usp in R2. rewrite E3 in R3. rewrite E4 in R4. rewrite E8 in R8. rewrite ?E10 in R10.
  assert (Hspa : spZ (ms_regs msA) = spZ regs - 32)
    by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
  assert (HJA : ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msA) _ k) by exact HJ.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?pcX) _ _) _) _ =>
    replace pcX with (pc_wrap_malloc (as_code B)) by (rewrite <- (pal_malloc B TL); reflexivity) end.
  eapply SRr_bind.
  { eapply (aj_gx_malloc_d SK SEGS B MT LAWS pa_segs_low MALLOC G XO OUT W (ms_regs msA) (ms_mem msA) STK sp0 FP ly S
      W0 mem0 md0 own lyc Sc _ k (cap + 1) _ ch HJ).
    - rewrite R10; unfold w64; f_equal; unfold cap, aarg, argZ; lia.
    - unfold MALLOC_MAX; lia.
    - unfold TEXT_BUF_LIVE in Hlive; lia.
    - rewrite Hspa; lia.
    - rewrite Hspa; change ASTACK with 16384; lia.
    - rewrite Hspa; lia.
    - rewrite Hspa; lia.
    - rewrite R3; exact Hgp.
    - rewrite R4; exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; lia.
    - lia.
    - apply (achain_chain_pre lyc _ (spZ regs) (s0Z regs) ch (ms_regs msA)).
      + apply (achain_kept lyc (aview SEGS (w_H W) memc) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | rewrite Etop; lia |].
        intros a Ha. apply UN; [lia | unfold lf_Zs; lia].
      + rewrite Hspa. lia.
      + unfold s0Z. rewrite R8. reflexivity.
      + unfold raZ. rewrite R1, VB. rewrite unsigned_lit_small by lia. lia.
    - unfold call_trace0. rewrite tb_unwind_spine.
      specialize (HTR _ HCTX). cbn [tl] in HTR.
      replace (raZ (ms_regs msA)) with TEXT_BUF_MALLOC_RA; [exact HTR|].
      unfold raZ. rewrite R1, VB. rewrite unsigned_lit_small by lia. reflexivity.
    - apply (mo_ok_le MT MTL Sc _ (mo_malloc MT TEXT_BUF_LIVE)); [exact Hmo |].
      apply (mo_malloc_mono MT MTL). unfold TEXT_BUF_LIVE. lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hres & Hfr & H4096 & Hbl & HKC
    & MLE & HD & Hfd2 & Hfs2).
  set (n := cap + 1) in *.
  assert (Hn2 : 2 <= n <= 40) by (unfold n; lia).
  assert (Hrq : req_size n = n) by (unfold req_size; replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
  pose proof HKC as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6).
  rewrite Hspa in KC1, KC5, KC6. change ASTACK with 16384 in KC1, KC5, KC6.
  (* the window's presence at the call *)
  assert (PRA : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) (ms_mem msA) a).
  { intros a Ha. pose proof HJ as (_ & _ & (memSA & HJAi & _) & _).
    pose proof HJAi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpA & _). apply HpA. lia. }
  (* the frame region survives the call *)
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
  lazymatch type of HS2 with ?Q -> _ => assert (HKEEP : Q) end.
  { apply Forall_cons; [|apply Forall_nil]. unfold region_kept.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val stack_region].
    rewrite ?ew_ewset_other by lia. rewrite Usp. cbn [ms_mem restrict]. split.
    - intros a Ha. apply tb_mbyte2. apply KC1; lia.
    - intros a Ha _. apply apresent_writable. apply KC5; [lia | lia | apply PRA; lia]. }
  specialize (HS2 HKEEP). clear HKEEP HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?EV _ _ => set (Ev2 := EV) in * end.
  assert (EW2 : forall a, (a < 40)%nat -> ew Ev2 a = ew E a)
    by (intros a Ha; unfold Ev2; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (E44 : ew Ev2 44 = getr regs2 10) by (unfold Ev2; reflexivity).
  assert (HEI2 : img_env VAL A_LIM Ev2)
    by (unfold Ev2; apply img_env_havoc; [first [exact HEI | apply img_env_ewset_hi; [exact HEI | cbv; lia]] | cbv; lia]).
  assert (Usp2 : bv_unsigned (ew Ev2 2) = spZ regs) by (rewrite EW2 by lia; exact Usp).
  assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] Ev2 (mrestrict (w_H W2) mem2)) by constructor.
  clear SHOK.
  pose proof HJ2 as (_ & _ & (memS2 & HJ2i & _) & _).
  pose proof HJ2i as (HAR2 & _).
  assert (HinP : In (res, n) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res n HAR2 HinP) as (_ & _ & Hbc & _ & _ & _ & _).
  rewrite Hrq in Hbc.
  (* the call's trace is fixed *)
  assert (HTRc : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs msA) ch) (u_fix (as_universe B))).
  { unfold call_trace0. rewrite tb_unwind_spine.
    specialize (HTR _ HCTX). cbn [tl] in HTR.
    replace (raZ (ms_regs msA)) with TEXT_BUF_MALLOC_RA; [exact HTR|].
    unfold raZ. rewrite R1, VB. rewrite unsigned_lit_small by lia. reflexivity. }
  clear Hc.
  (* +0x20 `beqz a0`: the block is not 0 *)
  psrr_branch_tok RUN BR HS SHOK2 Bspan.
  { exfalso. rewrite branch_eq_U, lf_U_reg, U_SLit in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite E44, Hres in Hc.
    unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia. change (zcanon 0) with 0 in Hc.
    apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  (* +0x24 .. +0x30: the arguments of checked_memset *)
  assert (UNB : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 16416 (spZ regs) a ->
            aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a) by reflexivity.
  assert (HGB : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) mem2)) by apply mem_grows_refl.
  paj_run_tok RUN HS HJ2 SHOK2 Bspan; [lf_awr |].
  lf_kept HFr W2 16416 (spZ regs) UNk. clear HF HFr. lf_fold UNB HGB UNk HG W2 mem2 16416 (spZ regs).
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into msB end.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  rewrite ?ew_ewset_other in Q2, Q3, Q4, Q10, Q12 by lia.
  rewrite Usp2 in Q2. rewrite EW2, E3 in Q3 by lia. rewrite EW2, E4 in Q4 by lia. rewrite E44, Hres in Q10.
  rewrite EW2, E10 in Q12 by lia.
  assert (Hspb : spZ (ms_regs msB) = spZ regs - 32)
    by (unfold spZ at 1; rewrite Q2; apply unsigned_lit_small; lia).
  pose proof HJ2 as (_ & _ & (memSB & HJBi & _) & _).
  pose proof HJBi as (HARB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpB & _).
  pose proof HJ as (_ & _ & (memSA2 & HJAi2 & _) & _).
  pose proof HJAi2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
  (* the block is no block of the call's state *)
  assert (HnotSc : ~ In (res, n) (ablocks B lyc Sc)).
  { intros Hin. apply in_split in Hin as (l1 & l2 & El).
    pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (res, n) (res, n) l1 l2 [] HAR2
      ltac:(rewrite Hbl, El, <- app_assoc; reflexivity)) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia. }
  eapply SRr_bind.
  { eapply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OSet _ MEMSET G XO OUT W2 (ms_regs msB) (ms_mem msB)
      STK sp0 FP ly S W0 mem0 md0 own ly2 S2 _ (k + 1) res 90 n _ HGX HJ2).
    - exact Q10.
    - exact Q11.
    - rewrite Q12. unfold w64. f_equal.
    - lia.
    - lia.
    - lia.
    - rewrite Hspb; lia.
    - rewrite Hspb; change ESTACK with 4096; lia.
    - rewrite Hspb; lia.
    - rewrite Q3; exact Hgp.
    - rewrite Q4; exact Htp.
    - exact Q1.
    - apply ret_ok_codeptr_v; lia.
    - intros a Ha. left. split; [|split; [lia | rewrite Hspb; change ESTACK with 4096; lia]].
      unfold awr_byte. right.
      destruct (in_dec tb_dec (res, n) (ablocks B ly S)) as [Hin0|Hin0].
      + left. split.
        * replace a with (res + (a - res)) by lia. apply (Hgone res n (a - res) Hin0 HnotSc). lia.
        * exists res, n. split; [exact HinP | lia].
      + right. left. exists res, n. split; [exact HinP|]. split; [exact Hin0 | lia].
    - exact (amem_range_of_block SEGS B LAWS ly2 S2 W2 (ms_mem msB) _ res n res n HARB HinP ltac:(lia) ltac:(lia)).
    - exact (range_addressable_of_block SEGS B LAWS ly2 S2 W2 (ms_mem msB) _ res n res n HARB HinP ltac:(lia) ltac:(lia)).
    - intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 (ms_mem msB) _ res n res n HARB HinP
        ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact I. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hr3 & Hset & Hkeep3 & Hpres3 & Hsm3).
  rewrite Hspb in Hkeep3. change ESTACK with 4096 in Hkeep3.
  jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0]%nat HS3.
  lazymatch type of HS3 with ?Q -> _ => assert (HKEEP : Q) end.
  { apply Forall_cons; [|apply Forall_nil]. unfold region_kept.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val stack_region].
    rewrite ?ew_ewset_other by lia. rewrite Usp2. cbn [ms_mem restrict]. split.
    - intros a Ha. apply tb_mbyte2. apply Hkeep3; lia.
    - intros a Ha _. apply apresent_writable. apply Hpres3. apply HpB. lia. }
  specialize (HS3 HKEEP). clear HKEEP HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?EV _ _ => set (Ev3 := EV) in * end.
  assert (EW3 : forall a, (a < 64)%nat -> ew Ev3 a = ew Ev2 a)
    by (intros a Ha; unfold Ev3; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (HEIv3 : img_env VAL A_LIM Ev3)
    by (unfold Ev3; apply img_env_havoc; [first [exact HEI2 | apply img_env_ewset_hi; [exact HEI2 | cbv; lia]] | cbv; lia]).
  assert (Usp3 : bv_unsigned (ew Ev3 2) = spZ regs) by (rewrite EW3 by lia; exact Usp2).
  assert (SHOK3 : sh_ok SEGS (SOff 32 0) [] Ev3 (mrestrict (w_H W2) mem3)) by constructor.
  clear SHOK2.
  (* +0x34 .. +0x50: a0 := the block, restore, pop, ret *)
  assert (UNC : forall a, 0 <= a < 2 ^ 64 -> ~ lf_Zs 16416 (spZ regs) a ->
            aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem3 a) by reflexivity.
  assert (HGC : mem_grows (mrestrict (w_H W2) mem3) (mrestrict (w_H W2) mem3)) by apply mem_grows_refl.
  paj_run_tok RUN HS HJ3 SHOK3 Bspan; [lf_awr |].
  lf_kept HFr W2 16416 (spZ regs) UNk. clear HF HFr. lf_fold UNC HGC UNk HG W2 mem3 16416 (spZ regs).
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ (restrict _ ?msF) =>
    rename msF into msD;
    assert (HAEf : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) Ef)
      by (split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; unfold Ev3; rewrite ew_havoc_old by lia;
                  rewrite ?ew_ewset_other by lia; unfold Ev2; rewrite ew_havoc_old by lia;
                  rewrite ?ew_ewset_other by lia; exact (proj1 HAE nn Hnn) | exact (proj2 HAE)]);
    pose proof (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs [Z_to_bv 64 SB] HS HAEf ltac:(vm_compute; reflexivity)) as HPr
  end.
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
  rewrite ?ew_ewset_other in P10 by lia. rewrite EW3, E44, Hres in P10 by lia.
  eapply (paj_ret_at (PL := PL_link) (PI := PI) W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  rewrite P1; rewrite ?ew_ewset_other by lia; rewrite EW3 by lia; rewrite EW2 by lia; rewrite E1, Hret.
  (* the end state *)
  pose proof HJ3 as (_ & _ & (memSF & HJFi & _) & _).
  pose proof HJFi as (HARF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpF & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res n HARF HinP) as (_ & _ & _ & _ & HpoF & _ & _).
  assert (UNF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16416 <= a < spZ regs) -> ~ (res <= a < res + n) ->
            aview SEGS (w_H W2) (ms_mem msD) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hw Hb. rewrite (UNC a Ha Hw). rewrite (Hkeep3 a Ha Hb ltac:(lia)). exact (UNB a Ha Hw). }
  assert (GRF : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msD) a)
    by (intros a Ha; apply (tb_grow _ _ _ HGC); apply Hpres3; apply (tb_grow _ _ _ HGB); exact Ha).
  set (Efr := fun a : Z => inFP [] a \/ res <= a < res + req_size n).
  (* the kept clause: the entry run, then malloc, then the run after it, the fresh block excepted *)
  assert (KA : akept SEGS B lyc Sc W memc W (ms_mem msA) (spZ regs - 16416) (spZ regs) (fun _ => False)).
  { apply (akept_run SEGS B LAWS pa_segs_low lyc Sc W memc mdc W (ms_mem msA) (spZ regs - 16416) (spZ regs)
      (fun _ => False) HAR); [lia | lia | | | ].
    - intros a Ha Hw _. exact (UN a Ha Hw).
    - intros a Ha. exact (tb_grow _ _ _ HGc a Ha).
    - intros a Ha. apply PRA. lia. }
  assert (KB : akept SEGS B lyc Sc W (ms_mem msA) W2 mem2 (spZ regs - 16416) (spZ regs - 32) Efr).
  { apply (akept_of_acall_kept SK SEGS B LAWS pa_segs_low lyc Sc W (ms_mem msA) W2 mem2 _ _
      (fun a => res <= a < res + req_size n) Efr); [|intros a Ha; right; exact Ha].
    rewrite Hspa in HKC. change ASTACK with 16384 in HKC. replace (spZ regs - 16416) with (spZ regs - 32 - 16384) by lia.
    exact HKC. }
  assert (KC : akept SEGS B ly2 S2 W2 mem2 W2 (ms_mem msD) (spZ regs - 16416) (spZ regs) Efr).
  { apply (akept_run SEGS B LAWS pa_segs_low ly2 S2 W2 mem2 md2 W2 (ms_mem msD) (spZ regs - 16416) (spZ regs)
      Efr HAR2); [lia | lia | | | ].
    - intros a Ha Hw HnE. apply UNF; [exact Ha | exact Hw | intros Hb; apply HnE; right; rewrite Hrq; exact Hb].
    - exact GRF.
    - intros a Ha. apply HpF. lia. }
  assert (KAB : akept SEGS B lyc Sc W memc W2 mem2 (spZ regs - 16416) (spZ regs) Efr).
  { apply (akept_trans SK SEGS B LAWS pa_segs_low lyc Sc W memc Sc W (ms_mem msA) W2 mem2
      (spZ regs - 16416) (spZ regs) (spZ regs - 16416) (spZ regs - 32) (fun _ => False) Efr Efr);
      [lia | lia | exact KA | exact KB | lia | lia | tauto | tauto | intros a [] | tauto]. }
  assert (Hfa : forall c p, frame_addr ly2 c p = frame_addr lyc c p).
  { intros c p.
    rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 _
                     _ (k + 1) c p HJ2)).
    rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
                     mdc k c p HJ0)). reflexivity. }
  assert (KF : akept SEGS B lyc Sc W memc W2 (ms_mem msD) (spZ regs - 16416) (spZ regs) Efr).
  { apply (akept_trans_ly SK SEGS B LAWS pa_segs_low lyc Sc W memc ly2 S2 W2 mem2 W2 (ms_mem msD)
      (spZ regs - 16416) (spZ regs) (spZ regs - 16416) (spZ regs) Efr Efr Efr);
      [lia | lia | exact KAB | exact KC | lia | lia | | | exact Hfa | tauto | tauto].
    - intros b m Hb. rewrite Hbl. apply in_or_app. left. exact Hb.
    - intros f Hf. rewrite Hfr. exact Hf. }
  pose proof (akept_drop_block SK SEGS B LAWS pa_segs_low lyc Sc W memc W2 (ms_mem msD) (spZ regs - 16416) (spZ regs)
    (fun a => inFP [] a) ly2 S2 W2 mem2 md2 res n HAR2 Hbl Hfr Hfa KF) as KD.
  eexists ly2, S2, (ms_regs msD), (ms_mem msD), _.
  split; [reflexivity|].
  split.
  { first [ exact HJ3 | (repeat rewrite wvb_collapse in HJ3); exact HJ3
          | apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low);
            first [exact HJ3 | (repeat rewrite wvb_collapse in HJ3); exact HJ3] ]. }
  split; [exact HPr|].
  split; [exact Hfr|].
  split.
  { repeat rewrite (proj1 (wvb_fds_fs _ _ _)). rewrite (same_but_materialized_wvb _ _ Hsm3).
    repeat rewrite (proj1 (wvb_fds_fs _ _ _)). rewrite Hfd2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity. }
  split.
  { repeat rewrite (proj2 (wvb_fds_fs _ _ _)). rewrite (same_but_materialized_wvb _ _ Hsm3).
    repeat rewrite (proj2 (wvb_fds_fs _ _ _)). rewrite Hfs2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity. }
  split; [exact KD|].
  split; [exact (ashadow_kept_AR SK SEGS B LAWS pa_segs_low lyc Sc ly2 S2 W memc mdc W2 (ms_mem msD) _ HAR HARF)|].
  unfold tb_Q. split.
  { apply (mo_le_mono MT MTL Sc S2 (mo_malloc MT n)); [exact MLE|].
    apply (mo_malloc_mono MT MTL). unfold TEXT_BUF_LIVE. lia. }
  split.
  { unfold text_buf_ledpost. exact (alc_depot_fixed (as_universe B) _ _ _ HD HTRc). }
  unfold text_buf_apostA. split.
  { intros H0. exfalso. exact (Hcnz H0). }
  intros _. exists res.
  split; [exact P10|]. split; [exact H4096|]. split; [exact Hbl|].
  unfold atbuf_at, au8arr. rewrite length_app, repeat_length. cbn [length].
  split; [|lia].
  split.
  + unfold abytes. rewrite length_app, repeat_length. cbn [length].
    split; [lia|]. split; [lia|].
    intros i Hi. rewrite tb_nth_rep by lia.
    apply tb_mbyte_some.
    rewrite (UNC (res + Z.of_nat i) ltac:(lia) ltac:(unfold lf_Zs; lia)).
    rewrite (Hset (Z.of_nat i) ltac:(lia)). reflexivity.
  + unfold awrange. intros i Hi. apply apresent_writable. apply HpoF. rewrite Hrq. lia.
Qed.
End w.
