(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* reac_headamp_tx_next (fuzz_grant.asan 0x850cc): the walk of its entry segment, from the
   first slot to the head of the edge scan LOOPD (0x8514c) or to the return when the table
   is idle (src/reac_headamp_tx.c:111-112), and the theorem that the whole function meets
   theadamp_tx_next_spec once the edge scan's cut (NextEdge.v) and the after-scan's cut
   (NextAfter.v) are given.

   The entry segment writes only the ten saved registers into its own machine-stack window:
   it is seated with the table's ten scalar fields read-only, so each run's frame keeps every
   byte outside that window, and the table and the three caller bytes come out unchanged. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI67.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaJournal GrantPaLib GrantBase YC1h.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import NextArith HeadampTxEffective HeadampTxNext.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The entry segment's regions: its own machine-stack window, the two image words the
   shadow base is read through, and the table's ten scalar fields, read-only. *)
Definition TXSro : YP09.region := YP09.mkRegion (Some 10%nat) 432 460 432 432 (YP09.r_chunks TXS).
Definition nx_regs_ro : list YP09.region :=
  [ stack_region NEXT_STK; got_regionP; bcell_regionP 32; TXSro ].
Definition ss_ro : sstate :=
  mkSS AF_reac_headamp_tx_next sr_atoms nx_regs_ro None (mkFacts nx_atoms [] []).

(* The machine-stack window is the only window of these regions that is written. *)
Lemma nx_wrange_ro : forall (E : env) (rs : smem) (sp a : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_ro)) ->
  bv_unsigned (ew E 2) = sp -> in_wrange E rs a -> sp - NEXT_STK <= a < sp.
Proof.
  intros E rs sp a Hsk E2 (r & Hin & Ha).
  pose proof (Hsk r Hin) as Hs.
  unfold nx_regs_ro, stack_region, got_regionP, bcell_regionP, TXSro, skeleton in Hs.
  cbn [map skel YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hs.
  unfold NEXT_STK in *.
  destruct Hs as [Hs|[Hs|[Hs|[Hs|Hs]]]]; try (exfalso; exact Hs);
    symmetry in Hs; unfold skel in Hs;
    injection Hs as H1 H2 H3 H4 H5;
    rewrite ?H1, ?H2, ?H3, ?H4, ?H5 in Ha; cbn [base_val] in Ha.
  - rewrite E2 in Ha. lia.
  - lia.
  - lia.
  - lia.
Qed.

(* What the entry segment has changed so far: nothing outside its machine-stack window. *)
Definition nx_stk_same {segs : list Segment} (W : world segs) (memc m : word -> option byte) (sp : Z) : Prop :=
  forall x : word, ~ (sp - NEXT_STK <= bv_unsigned x < sp) ->
    mrestrict (w_H W) m x = mrestrict (w_H W) memc x.

Lemma nx_stk_same_step : forall {segs : list Segment} (W : world segs) memc m1 m2 (E : env) (rs : smem) (sp : Z),
  nx_stk_same W memc m1 sp ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_ro)) ->
  bv_unsigned (ew E 2) = sp ->
  nx_stk_same W memc m2 sp.
Proof.
  intros segs W memc m1 m2 E rs sp HS HF Hsk E2 x Hx.
  rewrite (HF x); [exact (HS x Hx)|].
  intros Hw. exact (Hx (nx_wrange_ro E rs sp (bv_unsigned x) Hsk E2 Hw)).
Qed.

Lemma nx_apresent_grow : forall (H : word -> bool) m1 m2 a,
  mem_grows (mrestrict H m1) (mrestrict H m2) -> apresent H m1 a -> apresent H m2 a.
Proof.
  intros H m1 m2 a HG (Hh & b & Hb). split; [exact Hh|].
  pose proof (HG (Z_to_bv 64 a)) as G. unfold mrestrict in G. rewrite Hh in G.
  destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:E2; [exists b'; reflexivity|].
  exfalso. apply G; [rewrite Hb; discriminate | reflexivity].
Qed.

Ltac nx_skel_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; vm_compute in Hr;
  repeat (destruct Hr as [Hr | Hr];
          [subst r; vm_compute; repeat (first [left; reflexivity | right]) |]);
  destruct Hr.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

(* The edge scan's cut, as NextEdge.v proves it. *)
Definition nx_dloop_stmt : Prop :=
  forall (n : nat) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
     memc mdc k (regs regsj : bvmap 5 word) memj mdj (tx chp parp valp : Z) (T : list byte) (i : Z),
   nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
   nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) ->
   nx_saved W memj regs (spZ regs) ->
   obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals T) ->
   ~ (u32at T 432 = 0 /\ tb T 437 = 0) ->
   0 <= i < 144 -> Z.of_nat n = 144 - i ->
   (forall l, 0 <= l < i -> tb T (288 + l) = 0) ->
   (forall (regsA : bvmap 5 word) memA mdA,
      nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memA mdA tx chp parp valp (tx + 432) ->
      nx_saved W memA regs (spZ regs) ->
      (forall r : bv 5, In r [3; 4; 25; 26; 27]%bv -> getr regsA r = getr regs r) ->
      obj_at SEGS (mrestrict (w_H W) memA) tx LAY_TX (tx_vals T) ->
      (forall l, 0 <= l < 144 -> tb T (288 + l) = 0) ->
      getr regsA 2 = w64 (spZ regs - 80) -> getr regsA 5 = w64 SB_NX ->
      getr regsA 10 = w64 tx -> getr regsA 11 = w64 chp ->
      getr regsA 12 = w64 parp -> getr regsA 13 = w64 valp ->
      SRr SEGS W (cfg_at SEGS (BASE + AFTR) regsA memA mdA)
        (tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T)) ->
   (forall r : bv 5, In r [3; 4; 25; 26; 27]%bv -> getr regsj r = getr regs r) ->
   getr regsj 2 = w64 (spZ regs - 80) -> getr regsj 5 = w64 SB_NX ->
   getr regsj 7 = w64 i -> getr regsj 28 = w64 (tx + 288) ->
   getr regsj 29 = w64 171 -> getr regsj 30 = w64 144 ->
   getr regsj 10 = w64 tx -> getr regsj 11 = w64 chp ->
   getr regsj 12 = w64 parp -> getr regsj 13 = w64 valp ->
   SRr SEGS W (cfg_at SEGS (BASE + LOOPD) regsj memj mdj)
     (tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

(* The after-scan's cut, as NextAfter.v proves it (nx_after_spec there). *)
Definition nx_after_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs regsA : bvmap 5 word) memA mdA (tx chp parp valp : Z) (T : list byte),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memA mdA tx chp parp valp (tx + 432) ->
  nx_saved W memA regs (spZ regs) ->
  (forall r : bv 5, In r [3; 4; 25; 26; 27]%bv -> getr regsA r = getr regs r) ->
  obj_at SEGS (mrestrict (w_H W) memA) tx LAY_TX (tx_vals T) ->
  ~ (u32at T 432 = 0 /\ tb T 437 = 0) ->
  (forall l, 0 <= l < 144 -> tb T (288 + l) = 0) ->
  getr regsA 2 = w64 (spZ regs - NEXT_STK) -> getr regsA 5 = w64 SB_NX ->
  getr regsA 10 = w64 tx -> getr regsA 11 = w64 chp ->
  getr regsA 12 = w64 parp -> getr regsA 13 = w64 valp ->
  SRr SEGS W (cfg_at SEGS (BASE + AFTR) regsA memA mdA)
    (tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

(* The entry state, with the table's fields read-only. *)
Lemma nx_entry_ro : forall lyc Sc (W : world SEGS) (regs : bvmap 5 word) memc mdc
    (tx chp parp valp : Z) (T : list byte),
  AR SEGS B lyc Sc W memc mdc ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 chp ->
  getr regs 12 = w64 parp -> getr regs 13 = w64 valp ->
  spZ regs mod 16 = 0 -> 2 ^ 46 <= spZ regs <= 2 ^ 47 ->
  alloc_ceiling <= spZ regs - NEXT_STK ->
  (forall a, spZ regs - NEXT_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  In (tx, TX_SIZE) (ablocks B lyc Sc) ->
  length T = 460%nat -> I1 T ->
  obj_at SEGS (mrestrict (w_H W) memc) tx LAY_TX (tx_vals T) ->
  nx_out_ok (spZ regs) tx chp -> nx_out_ok (spZ regs) tx parp -> nx_out_ok (spZ regs) tx valp ->
  chp <> parp -> chp <> valp -> parp <> valp ->
  apresent (w_H W) memc chp -> apresent (w_H W) memc parp -> apresent (w_H W) memc valp ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF chp 1 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF parp 1 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF valp 1 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (nx_extra tx T))) ss_ro
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_next)) memc (seg_rom SEGS)))
  /\ sh_ok SEGS BxN nx_SH (Eimg (Ereg regs (nx_extra tx T))) (mrestrict (w_H W) memc).
Proof.
  intros lyc Sc W regs memc mdc tx chp parp valp T HAR H10 H11 H12 H13 Hsp16 Hspr Hac Hpres
    Hg HL HI Hobj Hoc Hop Hov Dcp Dcv Dpv Pc Pp Pv Rc Rp Rv.
  destruct (nx_entry B LAWS TL lyc Sc W regs memc mdc tx chp parp valp T HAR H10 H11 H12 H13
    Hsp16 Hspr Hac Hpres Hg HL HI Hobj Hoc Hop Hov Dcp Dcv Dpv Pc Pp Pv Rc Rp Rv) as [HS SHOK].
  split; [|exact SHOK].
  pose proof (st_ok_pi_submem _ ss_nx _ nx_regs_ro HS) as H.
  apply H.
  - unfold nx_regs_ro, nx_regs0, ss_nx. cbn [ss_mem].
    apply submem_keep; [repeat split; auto; lia|].
    apply submem_keep; [repeat split; auto; lia|].
    apply submem_keep; [repeat split; auto; lia|].
    apply submem_keep; [|apply submem_nil].
    unfold TXSro, TXS. repeat split; cbn; try lia; auto.
  - vm_compute. reflexivity.
Qed.

(* The awr obligation of a run of the entry segment: only its own machine-stack window. *)
Lemma nx_awr_ro : forall (E : env) STK sp0 FP ly S lyc Sc own (rs : smem) (sp : Z),
  (forall r, In r rs -> In (skel r) (skeleton nx_regs_ro)) ->
  bv_unsigned (ew E 2) = sp -> sp0 - STK <= sp - NEXT_STK -> sp <= sp0 ->
  awr_ok E rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
  intros E STK sp0 FP ly S lyc Sc own rs sp Hsk E2 Hlo Hhi a Hw.
  pose proof (nx_wrange_ro E rs sp a Hsk E2 Hw) as Ha.
  left. unfold NEXT_STK in *. lia.
Qed.

(* The bytes the entry segment leaves give back the table it was handed. *)
Lemma nx_obj_kept : forall (W : world SEGS) memc m sp tx T,
  nx_stk_same W memc m sp -> 0 <= tx -> tx + 460 <= sp - NEXT_STK -> sp <= 2 ^ 47 ->
  obj_at SEGS (mrestrict (w_H W) memc) tx LAY_TX (tx_vals T) ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals T).
Proof.
  intros W memc m sp tx T HS Htx Hsp Hsp47 HO.
  apply (proj2 (tx_obj_bytes SEGS (mrestrict (w_H W) m) tx T)).
  intros i Hi. pose proof (tx_fbyte_range i Hi) as Hir.
  rewrite <- (proj1 (tx_obj_bytes SEGS (mrestrict (w_H W) memc) tx T) HO i Hi).
  unfold mbyte. rewrite (HS (Z_to_bv 64 (tx + i))); [reflexivity|].
  assert (Hu : bv_unsigned (Z_to_bv 64 (tx + i)) = tx + i)
    by (apply unsigned_lit_small; unfold NEXT_STK in *; lia).
  rewrite Hu. unfold NEXT_STK in *. lia.
Qed.

Ltac nx_reg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = sv_denot Ex e)
      by exact (st_ok_pi_restrict_reg Hh Ex ss ms r HS)
  end.

(* After each run: fold the run's frame into what the segment has kept so far. *)
Ltac nx_acc Usp :=
  repeat match goal with
  | H : frame_of _ _ (ms_mem _) (ms_mem _) |- _ => clear H
  | H : frame_of _ _ ?m0 ?m1 |- _ =>
      lazymatch m0 with mrestrict _ _ => fail | _ => clear H end
  end;
  match goal with
  | ACC : nx_stk_same _ _ ?m1 _,
    HFr : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2),
    HG : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2),
    GRO : mem_grows _ (mrestrict _ ?m1) |- _ =>
    let ACC' := fresh "ACC" in let GRO' := fresh "GRO" in
    pose proof (nx_stk_same_step _ _ _ _ Ex rs _ ACC HFr ltac:(nx_skel_tac) Usp) as ACC';
    pose proof (mem_grows_trans _ _ _ GRO HG) as GRO';
    clear ACC HFr HG GRO; rename ACC' into ACC; rename GRO' into GRO
  end.

Theorem nx_walk : nx_dloop_stmt -> nx_after_stmt -> theadamp_tx_next_spec B.
Proof.
  intros DLOOP AFTER. unfold theadamp_tx_next_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs tx chp parp valp T ch
    HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 H13 Hchain Hsp16 Hlo Hhi Hpres Hg HL HI Hobj Hwtab
    Hoc Hop Hov Dcp Dcv Dpv Wc Wp Wv Pc Pp Pv Rc Rp Rv.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & Hstk & _ & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  assert (Hspr : 2 ^ 46 <= spZ regs <= 2 ^ 47).
  { clear - C1 Hceil Hslo Hshi H47 Hlo Hhi Hstk0. unfold NEXT_STK in *. lia. }
  assert (Hac : alloc_ceiling <= spZ regs - NEXT_STK).
  { clear - Hceil Hslo Hlo Hstk0. unfold NEXT_STK in *. lia. }
  assert (Hctx : nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T).
  { exact (conj HAR (conj Hg (conj Hoc (conj Hop (conj Hov (conj Dcp (conj Dcv (conj Dpv
      (conj Pc (conj Pp (conj Pv (conj Rc (conj Rp (conj Rv (conj Hspr (conj Hac (conj Hsp16
      (conj Hlo (conj Hhi (conj Hwtab (conj Wc (conj Wp (conj Wv (conj Hra (conj Hra4 (conj Hgp
      (conj Htp (conj H10 (conj H11 (conj H12 (conj H13 (conj HL (conj HI (conj Hobj Hpres)))))))))))))))))))))))))))))))))). }
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc tx TX_SIZE HAR Hg)
    as (Hg16 & Hg4096 & Hgceil & _ & _ & _).
  change (req_size TX_SIZE) with 460 in Hgceil.
  destruct (nx_entry_ro lyc Sc W regs memc mdc tx chp parp valp T HAR H10 H11 H12 H13
    Hsp16 Hspr Hac Hpres Hg HL HI Hobj Hoc Hop Hov Dcp Dcv Dpv Pc Pp Pv Rc Rp Rv) as [HS SHOK].
  remember (Eimg (Ereg regs (nx_extra tx T))) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (nx_extra tx T)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E1 : ew E 1 = getr regs 1)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = getr regs 2)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 tx)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 chp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 parp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E13 : ew E 13 = Z_to_bv 64 valp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
  assert (E32 : ew E 32 = Z_to_bv 64 SB_NX)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (u32at T 432))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E35 : ew E 35 = Z_to_bv 64 (tb T 437))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (HAE : env_agree 32 (Ereg regs (nx_extra tx T)) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  clear HEdef EL.
  pose proof (u32at_range T 432) as R33.
  pose proof (HeadampTxEffective.tb_range T 437) as R35.
  assert (ACC : nx_stk_same W memc memc (spZ regs)) by (intros x _; reflexivity).
  assert (GRO : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by (apply mem_grows_refl).
  (* The facts every LOOPD exit hands the edge scan, from the machine at LOOPD. *)
  assert (TOLOOP : forall (msL : machine_state) mdL ssL,
    st_ok_pi SEGS VAL E ssL (restrict (w_H W) msL) -> ss_resv ssL = None ->
    ss_pc ssL = LOOPD ->
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msL) mdL k ->
    nx_stk_same W memc (ms_mem msL) (spZ regs) ->
    mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem msL)) ->
    nx_saved W (ms_mem msL) regs (spZ regs) ->
    (forall r : bv 5, In r [3; 4; 25; 26; 27]%bv -> getr (ms_regs msL) r = getr regs r) ->
    getr (ms_regs msL) 2 = w64 (spZ regs - 80) -> getr (ms_regs msL) 5 = w64 SB_NX ->
    getr (ms_regs msL) 7 = w64 0 -> getr (ms_regs msL) 28 = w64 (tx + 288) ->
    getr (ms_regs msL) 29 = w64 171 -> getr (ms_regs msL) 30 = w64 144 ->
    getr (ms_regs msL) 10 = w64 tx -> getr (ms_regs msL) 11 = w64 chp ->
    getr (ms_regs msL) 12 = w64 parp -> getr (ms_regs msL) 13 = w64 valp ->
    ~ (u32at T 432 = 0 /\ tb T 437 = 0) ->
    SRr SEGS W (mkCfg msL mdL)
      (tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T)).
  { intros msL mdL ssL HSL Hrv Hpc HJL ACCL GROL HSV HKG R2 R5 R7 R28 R29 R30 R10 R11 R12 R13 Hact.
    rewrite (st_ok_pi_restrict_mkst _ _ _ _ HSL Hrv), Hpc.
    change (SRr SEGS W (cfg_at SEGS (BASE + LOOPD) (ms_regs msL) (ms_mem msL) mdL)
      (tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T)).
    refine (DLOOP 144%nat STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msL)
      (ms_mem msL) mdL tx chp parp valp T 0 Hctx _ HSV _ Hact ltac:(lia) eq_refl
      ltac:(intros l Hl; lia) _ HKG R2 R5 R7 R28 R29 R30 R10 R11 R12 R13).
    - (* nx_mid *)
      split; [exact HJL|]. split; [|split].
      + intros x Hx Htc. exact (ACCL x Hx).
      + pose proof HJL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJLp & _).
        intros a Ha. apply HJLp. unfold NEXT_STK in *. lia.
      + intros a Ha. exact (nx_apresent_grow _ _ _ a GROL Ha).
    - (* the table *)
      exact (nx_obj_kept W memc (ms_mem msL) (spZ regs) tx T ACCL ltac:(lia)
        ltac:(unfold NEXT_STK in *; lia) ltac:(lia) Hobj).
    - (* the after-scan's cut *)
      intros regsA memA mdA HmA HsA HkA HoA HdA RA2 RA5 RA10 RA11 RA12 RA13.
      exact (AFTER STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsA memA mdA
        tx chp parp valp T Hctx HmA HsA HkA HoA Hact HdA RA2 RA5 RA10 RA11 RA12 RA13). }
  (* The saved registers, from the machine-stack region of a state the prologue has run. *)
  assert (SAVED : forall (ms : machine_state) ss,
    st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
    nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0
      [ YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
        YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
        YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
        YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
        YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0)) ]) ->
    nx_saved W (ms_mem ms) regs (spZ regs)).
  { intros ms ss HSs Hnth.
    assert (V : forall (n : nat) (r : bv 5) d, Z.of_nat n = bv_unsigned r ->
      In (YP09.mkChunk (- d) (CVal 8 (SOff n 0)))
        [ YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
          YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
          YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
          YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
          YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0)) ] ->
      ew E n = getr regs r ->
      val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - d) 8 (bv_unsigned (getr regs r))).
    { intros n r d Hn Hin Hew.
      pose proof (st_chunk_val SEGS E (abs_ss VAL ss) (restrict (w_H W) ms) 0 _ 2 (- d) 8
        (SOff n 0) (spZ regs) (bv_unsigned (getr regs r)) HSs ltac:(destruct ss; exact Hnth)
        eq_refl Hin Usp) as Hv.
      replace (spZ regs - d) with (spZ regs + - d) by lia.
      apply Hv.
      - cbn [sv_denot]. rewrite Hew, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hr.
        change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hr.
      - lia. }
    assert (G : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
    { intros n r Hn Hr. rewrite (proj1 HAE n Hn). exact (ew_Ereg_nat regs _ n r Hr). }
    unfold nx_saved.
    split; [apply (V 1%nat 1%bv 8); [reflexivity | cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 8%nat 8%bv 16); [reflexivity | cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 9%nat 9%bv 24); [reflexivity | cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 18%nat 18%bv 32); [reflexivity | cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 19%nat 19%bv 40); [reflexivity | cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 20%nat 20%bv 48); [reflexivity | cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 21%nat 21%bv 56); [reflexivity | cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 22%nat 22%bv 64); [reflexivity | cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 23%nat 23%bv 72); [reflexivity | cbn; tauto | apply G; [lia | reflexivity]]|].
    apply (V 24%nat 24%bv 80); [reflexivity | cbn; tauto | apply G; [lia | reflexivity]]. }
  (* The registers at LOOPD, read off the symbolic state. *)
  assert (REGS : forall (ms : machine_state) ss,
    st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
    sr_get (ss_regs ss) 2%bv = SOff 2 (-80) -> sr_get (ss_regs ss) 5%bv = SOff 32 0 ->
    sr_get (ss_regs ss) 7%bv = SLit 0 -> sr_get (ss_regs ss) 28%bv = SOff 10 288 ->
    sr_get (ss_regs ss) 29%bv = SLit 171 -> sr_get (ss_regs ss) 30%bv = SLit 144 ->
    sr_get (ss_regs ss) 10%bv = SOff 10 0 -> sr_get (ss_regs ss) 11%bv = SOff 11 0 ->
    sr_get (ss_regs ss) 12%bv = SOff 12 0 -> sr_get (ss_regs ss) 13%bv = SOff 13 0 ->
    forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
      [3; 4; 25; 26; 27]%bv = true ->
    (forall r : bv 5, In r [3; 4; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r) /\
    getr (ms_regs ms) 2 = w64 (spZ regs - 80) /\ getr (ms_regs ms) 5 = w64 SB_NX /\
    getr (ms_regs ms) 7 = w64 0 /\ getr (ms_regs ms) 28 = w64 (tx + 288) /\
    getr (ms_regs ms) 29 = w64 171 /\ getr (ms_regs ms) 30 = w64 144 /\
    getr (ms_regs ms) 10 = w64 tx /\ getr (ms_regs ms) 11 = w64 chp /\
    getr (ms_regs ms) 12 = w64 parp /\ getr (ms_regs ms) 13 = w64 valp).
  { intros ms ss HSs S2 S5 S7 S28 S29 S30 S10 S11 S12 S13 SKG.
    pose proof (fun r => st_ok_pi_restrict_reg (w_H W) E ss ms r HSs) as RG.
    split; [exact (regs_kept_of_st_ok_pi E ss (restrict (w_H W) ms) regs (nx_extra tx T) _ HSs HAE SKG)|].
    rewrite (RG 2%bv), (RG 5%bv), (RG 7%bv), (RG 28%bv), (RG 29%bv), (RG 30%bv),
      (RG 10%bv), (RG 11%bv), (RG 12%bv), (RG 13%bv),
      S2, S5, S7, S28, S29, S30, S10, S11, S12, S13.
    cbn [sv_denot]. rewrite Usp, E32, E10, E11, E12, E13.
    rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned.
    rewrite (unsigned_lit_small tx) by lia.
    replace (spZ regs + -80) with (spZ regs - 80) by lia.
    repeat split; reflexivity. }
  unfold cfg_at, A_reac_headamp_tx_nextP.
  change (w64 (BASE + AF_reac_headamp_tx_next)) with (Z_to_bv 64 (BASE + AF_reac_headamp_tx_next)).
  (* the prologue, the load of active, and its test *)
  paj_run_tok RUN HS HJ SHOK BspanN;
    [eapply nx_awr_ro; [nx_skel_tac | exact Usp | exact Hlo | exact Hhi] |].
  nx_acc Usp.
  psrr_branch_tok RUN BR HS SHOK BspanN.
  - (* active <> 0: on to the edge scan *)
    rewrite branch_ne_U, (U_atom E 33 (u32at T 432) E33), U_SLit, (zcanon_id 0) in Hc
      by (unfold M64; lia).
    apply (proj1 (negb_true_iff _)), Z.eqb_neq in Hc. rename Hc into Hact.
    paj_run_to_tok RUNTO HS HJ SHOK BspanN LOOPD;
      [eapply nx_awr_ro; [nx_skel_tac | exact Usp | exact Hlo | exact Hhi] |].
    nx_acc Usp.
    lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
      destruct (REGS msx ssx HSx eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
        eq_refl eq_refl eq_refl eq_refl eq_refl)
        as (KG & R2 & R5 & R7 & R28 & R29 & R30 & R10 & R11 & R12 & R13);
      exact (TOLOOP msx _ ssx HSx eq_refl eq_refl HJ ACC GRO (SAVED msx ssx HSx eq_refl)
        KG R2 R5 R7 R28 R29 R30 R10 R11 R12 R13 ltac:(intros [X _]; exact (Hact X)))
    end.
  - (* active = 0: the replay width decides *)
    rewrite branch_ne_U, (U_atom E 33 (u32at T 432) E33), U_SLit, (zcanon_id 0) in Hc
      by (unfold M64; lia).
    apply (proj1 (negb_false_iff _)), Z.eqb_eq in Hc. rename Hc into Hact0.
    paj_run_tok RUN HS HJ SHOK BspanN;
      [eapply nx_awr_ro; [nx_skel_tac | exact Usp | exact Hlo | exact Hhi] |].
    nx_acc Usp.
    psrr_branch_tok RUN BR HS SHOK BspanN.
    + (* replay_width = 0: idle, return 0 *)
      rewrite branch_eq_U, (U_atom E 35 (tb T 437) E35), U_SLit, (zcanon_id 0) in Hc
        by (unfold M64; lia).
      apply Z.eqb_eq in Hc. rename Hc into Hw0.
      paj_run_tok RUN HS HJ SHOK BspanN;
        [eapply nx_awr_ro; [nx_skel_tac | exact Usp | exact Hlo | exact Hhi] |].
      nx_acc Usp.
      lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
        nx_reg HSx (1%bv : bv 5) R1; nx_reg HSx (10%bv : bv 5) R10;
        eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
        let matR := fresh "matR" in intros matR; cbn [ms_regs ms_mem];
        rewrite R1; cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned, Hra;
        eapply (nx_finish B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
          regs (ms_regs msx) (ms_mem msx) _ tx chp parp valp (tx + 432) T T 0 0 0 0);
        [ unfold TX_SIZE; lia | exact HAR | exact Hg | exact Hoc | exact Hop | exact Hov
        | exact Hspr | exact Hac
        | exact (nx_model_silent T tx Hact0 Hw0)
        | apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ
        | eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (nx_extra tx T) HSx);
          [exact HAE | vm_compute; reflexivity]
        | intros x Hx Htc; exact (ACC x Hx)
        | pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJxp & _);
          intros a Ha; apply HJxp; unfold NEXT_STK in *; lia
        | intros a Ha; exact (nx_apresent_grow _ _ _ a GRO Ha)
        | rewrite R10; reflexivity
        | exact (nx_obj_kept W memc (ms_mem msx) (spZ regs) tx T ACC ltac:(lia)
            ltac:(unfold NEXT_STK in *; lia) ltac:(lia) Hobj)
        | intros X; discriminate X ]
      end.
    + (* replay_width <> 0: on to the edge scan *)
      rewrite branch_eq_U, (U_atom E 35 (tb T 437) E35), U_SLit, (zcanon_id 0) in Hc
        by (unfold M64; lia).
      apply Z.eqb_neq in Hc. rename Hc into Hw.
      paj_run_to_tok RUNTO HS HJ SHOK BspanN LOOPD;
        [eapply nx_awr_ro; [nx_skel_tac | exact Usp | exact Hlo | exact Hhi] |].
      nx_acc Usp.
      lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
        destruct (REGS msx ssx HSx eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
          eq_refl eq_refl eq_refl eq_refl eq_refl)
          as (KG & R2 & R5 & R7 & R28 & R29 & R30 & R10 & R11 & R12 & R13);
        exact (TOLOOP msx _ ssx HSx eq_refl eq_refl HJ ACC GRO (SAVED msx ssx HSx eq_refl)
          KG R2 R5 R7 R28 R29 R30 R10 R11 R12 R13 ltac:(intros [_ X]; exact (Hw X)))
      end.
Qed.

End h.
End f.
End d.
