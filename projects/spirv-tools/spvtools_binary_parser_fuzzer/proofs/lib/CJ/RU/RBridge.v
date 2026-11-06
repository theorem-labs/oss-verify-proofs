(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr PropExec MState Mem Cells Frame.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocBlocks MallocHINV Malloc_iface MallocFacts_A.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require MallocFacts_inv2.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.RU Require Import RMallocRep RImage RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require MallocFacts_mng.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog MI_Kit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import AcLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition mng_static (a : Z) : Prop :=
  (RMLOCK <= a < RCTX + 928) \/ a = RNEED_LOCKS \/ (RPAGE_SIZE <= a < RPAGE_SIZE + 8)
  \/ (RSSP_GUARD <= a < RSSP_GUARD + 8) \/ (RVMLOCK <= a < RVMLOCK + 4).

Definition rowned (LB : list block) (a : Z) : Prop :=
  mng_static a \/ ((a < RIMG_LO \/ RIMG_HI <= a) /\ 0 < a < alloc_ceiling /\ ~ in_block LB a).

Lemma mng_static_img a : mng_static a -> RRW_LO <= a < RIMG_HI.
Proof. unfold mng_static, RMLOCK, RCTX, RNEED_LOCKS, RPAGE_SIZE, RSSP_GUARD, RVMLOCK, RRW_LO, RIMG_HI. lia. Qed.

Lemma rrepfoot_rowned st LB0 m a :
  MFACTS_g (resv:=ref_reserved) st LB0 -> rmrep st m -> rrepfoot st a ->
  (RGOT_SSP <= a < RGOT_SSP + 8) \/ rowned LB0 a.
Proof.
  intros MF MR RF. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (rrepfoot_where st m a MR RF) as [AC AW].
  assert (NB : forall b, In b LB0 -> blk_addr b <= a < blk_addr b + blk_size b -> False).
  { intros b INb Hab.
    destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
    destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
    + unfold RCTX in R1. lia.
    + unfold RMLOCK in R2. lia.
    + unfold RNEED_LOCKS in R3. lia.
    + unfold RPAGE_SIZE in R4'. lia.
    + destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
      destruct (DJ _ _ _ _ Hra Hr NEr); lia.
    + destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
      * rewrite E, Hr in Hrb. inversion Hrb; subst rb.
        pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
      * pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
    + destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
      * rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
      * pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
    + unfold RGOT_SSP in R8. lia.
    + unfold RSSP_GUARD, RVMLOCK in R9. lia. }
  assert (NIB : ~ in_block LB0 a) by (intros (b & Hb & Hab); exact (NB b Hb Hab)).

  assert (POS : 0 < a /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ a = RNEED_LOCKS \/ RPAGE_SIZE <= a < RPAGE_SIZE + 8
                          \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8 \/ RVMLOCK <= a < RVMLOCK + 4
                          \/ a < 0x10000 \/ 0x124000 <= a)).
  { destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
      try (unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RVMLOCK in *; lia).
    - destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & S0 & S1 & Smod & NK & RB0 & RBAL & RBC).
      pose proof (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa ltac:(lia)). lia.
    - destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & S0 & S1 & Smod & RB0 & RBC).
      pose proof (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb ltac:(lia)). lia.
    - pose proof (WR _ _ Hq) as (RB0 & _ & _ & _ & RFq). pose proof (round_up_pg_ge (r_len rq)). pose proof (rreserved_disjoint1 _ _ RFq ltac:(lia)). lia. }
  destruct POS as [P0 CASES]. unfold rowned, mng_static, RIMG_LO, RIMG_HI. unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RVMLOCK, RLIBC in *.
  destruct (Z_lt_le_dec a 0x10000) as [LO|GE]; [right; right; split; [lia|]; split; [lia| exact NIB]|].
  destruct (Z_lt_le_dec a 0x124000) as [LT|GE2]; [| right; right; split; [lia|]; split; [lia| exact NIB]].
  lia.
Qed.

Definition in_got (a : Z) : Prop := RGOT_SSP <= a < RGOT_SSP + 8.

Lemma rmrep_transport_pw : forall st m m',
  rmrep st m ->
  (forall a, rrepfoot st a -> ~ in_got a -> m' (wa a) = m (wa a)) ->
  (forall a : word, RGOT_SSP <= bv_unsigned a < RGOT_SSP + 8 -> m' a = None) ->
  wmono rsegs m m' -> rmrep st m'.
Proof.
  intros st m m' (WF & CX & GL & AR & GR & SH) PW NONEG WM.
  pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a /\ ~ in_got a) -> rw_cells rsegs m' A cs).
  { intros A cs H HP. eapply rrw_cells_agree; eauto. intros a Ha. destruct (HP a Ha) as [H1 H2]. apply PW; assumption. }

  assert (OFFR : forall rid r a, s_regions st !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> 0 < round_up_pg (r_len r) -> ~ in_got a).
  { intros rid r a Hr Ha Hn G. pose proof (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint1 _ _ RF Hn). unfold in_got, RGOT_SSP in G. lia. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3.
    pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
    assert (CTXP : forall a, RCTX <= a < RCTX + 928 -> rrepfoot st a /\ ~ in_got a).
    { intros a Ha. split; [apply rrepfoot_ctx; exact Ha| unfold in_got, RGOT_SSP, RCTX in *; lia]. }
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply CTXP. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree; eauto. intros a Ha. rewrite ?L1 in *. destruct (CTXP a ltac:(unfold RCTX in *; lia)) as [H1 H2]. apply PW; assumption.
    + eapply ru64arr_agree; eauto. intros a Ha. rewrite ?L2 in *. destruct (CTXP a ltac:(unfold RCTX in *; lia)) as [H1 H2]. apply PW; assumption.
    + eapply ru8arr_agree; eauto. intros a Ha. rewrite ?L3 in *. destruct (CTXP a ltac:(unfold RCTX in *; lia)) as [H1 H2]. apply PW; assumption.
    + eapply ru8arr_agree; eauto. intros a Ha. rewrite ?L4 in *. destruct (CTXP a ltac:(unfold RCTX in *; lia)) as [H1 H2]. apply PW; assumption.
    + apply TC; [exact C6 |]. intros a Ha. apply CTXP. cbn in Ha. unfold RCTX in *. lia.
  - destruct GL as (G1 & G2 & G3 & G4 & G5 & G6). split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact G1 |]. intros a Ha. cbn in Ha. split; [apply rrepfoot_mlock; unfold RMLOCK in *; lia| unfold in_got, RGOT_SSP, RMLOCK in *; lia].
    + apply TC; [exact G2 |]. intros a Ha. cbn in Ha. split; [apply rrepfoot_nl; unfold RNEED_LOCKS in *; lia| unfold in_got, RGOT_SSP, RNEED_LOCKS in *; lia].
    + apply TC; [exact G3 |]. intros a Ha. cbn in Ha. split; [apply rrepfoot_pgsz; unfold RPAGE_SIZE in *; lia| unfold in_got, RGOT_SSP, RPAGE_SIZE in *; lia].
    +
      clear - NONEG. unfold RGOT_SSP in NONEG.
      let v := eval cbv in RGOT_SSP in rimg_chunk NONEG m' v [C8 (wz RSSP_GUARD)] GOT.
      exact GOT.
    + apply TC; [exact G5 |]. intros a Ha. cbn in Ha. split; [apply rrepfoot_guard; unfold RSSP_GUARD in *; lia| unfold in_got, RGOT_SSP, RSSP_GUARD in *; lia].
    + apply TC; [exact G6 |]. intros a Ha. cbn in Ha. split; [apply rrepfoot_vmlock; unfold RVMLOCK in *; lia| unfold in_got, RGOT_SSP, RVMLOCK in *; lia].
  - intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
    destruct (rarea_conc st ak ar WF Ha) as (ra & Hra & Ca & S0 & S1 & Smod & NK & RB0 & RBAL & RBC).
    assert (AP : forall a, conc st ak <= a < conc st ak + 4096 -> rrepfoot st a /\ ~ in_got a).
    { intros a H. split; [eapply rrepfoot_area; [exact Ha| lia]|]. eapply (OFFR _ _ a Hra); lia. }
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. apply AP. lia.
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. apply AP. lia.
    + apply TC; [exact A3 |]. intros a H. cbn in H. apply AP. lia.
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & S0 & S1 & Smod & RB0 & RBC).
    apply TC; [exact R |]. intros a H. cbn in H. split; [eapply rrepfoot_group; [exact Hb|lia]|]. eapply (OFFR _ _ a Hrb); lia.
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. split.
    + eapply wr_at_transport; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      pose proof Bt as (B0 & B1 & _). cbn in B1.
      eapply rbytes_at_agree; [exact Bt|]. intros a Ha. cbn in Ha.
      apply PW.
      * eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
      * eapply (OFFR _ _ a Hr); lia.
Qed.

Lemma mem_inv_of_clear (M : mem) :
  (forall w : word, RIMG_LO <= bv_unsigned w < RIMG_HI -> ~ (RRW_LO <= bv_unsigned w < RIMG_HI) -> M w = None) ->
  mem_inv rsegs M.
Proof.
  intros H a b Hab. destruct (ro_addr rsegs a) eqn:E; [| reflexivity]. exfalso.
  pose proof (ref_ro_addr_true_range a E). unfold RIMG_LO, RIMG_HI, RRO_HI, RRW_LO in *. rewrite (H a) in Hab; [discriminate| lia| lia].
Qed.

Lemma wmono_of_def (m m' : mem) : (forall a : word, m a <> None -> m' a <> None) -> wmono rsegs m m'.
Proof.
  intros H x Hx. unfold wview in *. destruct (m x) eqn:E.
  - destruct (m' x) eqn:E'; [discriminate|]. exfalso. apply (H x); congruence.
  - destruct (m' x); [discriminate| exact Hx].
Qed.

Lemma in_block_perm LB LB' a : Permutation LB LB' -> in_block LB a -> in_block LB' a.
Proof. intros P (b & Hb & H). exists b. split; [eapply Permutation_in; eauto| exact H]. Qed.

Lemma RHEAP_frame_pw : forall s LB (m m' : mem),
  RHEAP s LB m ->
  (forall a, rowned LB a -> m' (wa a) = m (wa a)) ->
  (forall a : word, RGOT_SSP <= bv_unsigned a < RGOT_SSP + 8 -> m' a = None) ->
  wmono rsegs m m' -> RHEAP s LB m'.
Proof.
  intros s LB m m' (st & LB0 & HP & Hst & MR & HI) PW NONEG WM. exists st, LB0. split; [exact HP|]. split; [exact Hst|].
  split; [|exact HI].
  destruct HI as [_ AR]. pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  apply (rmrep_transport_pw st m m' MR); [| exact NONEG| exact WM].
  intros a RF NG. destruct (rrepfoot_rowned st LB0 m a MF MR RF) as [G|OW]; [exfalso; exact (NG G)|].
  apply PW. destruct OW as [S|(A & B & C)]; [left; exact S| right]. split; [exact A|]. split; [exact B|].
  intros IB. apply C. eapply in_block_perm; [apply Permutation_sym; exact HP| exact IB].
Qed.

Lemma RHEAP_block_bytes : forall s LB m b a, RHEAP s LB m -> In b LB ->
  blk_addr b <= a < blk_addr b + blk_size b -> m (wa a) <> None.
Proof.
  intros s LB m b a (st & LB0 & HP & Hst & MR & [_ AR]) Hb Ha.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
  destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
  pose proof MR as (WF & CX & GL & ARs & GR & SH). destruct (SH _ r Hr Hk) as [HWr _].
  destruct HWr as (W0 & W1 & W). specialize (W (a - r_base r) ltac:(lia)). replace (r_base r + (a - r_base r)) with a in W by lia.
  rewrite ref_wview_overlay in W; [exact W|]. unfold wa. rewrite unsigned_lit by (pose proof ac_bounds_lit as ?ACBL; lia). lia.
Qed.

Lemma RHEAP_block_range : forall s LB m b, RHEAP s LB m -> In b LB ->
  0 <= blk_size b /\ blk_addr b mod 16 = 0 /\ 0 < blk_addr b /\ blk_addr b + blk_size b <= alloc_ceiling
  /\ (blk_addr b + blk_size b <= RIMG_LO \/ RIMG_HI <= blk_addr b).
Proof.
  intros s LB m b HH Hb. destruct (RHEAP_block_range_proof s LB m b HH Hb) as (P1 & P2 & P3 & P4 & P5).
  unfold RIMG_LO, RIMG_HI. repeat split; try lia.
Qed.

Lemma nodup_map_inj {A B} (f : A -> B) (l : list A) x y : List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|b l IH]; [intros _ []|]. cbn. intros ND I1 I2 E. inversion ND as [|x' l' NI ND']; subst.
  destruct I1 as [<-|I1], I2 as [<-|I2]; [reflexivity| | | exact (IH ND' I1 I2 E)].
  - exfalso. apply NI. rewrite E. apply in_map. exact I2.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact I1.
Qed.

Lemma RHEAP_block_addr_inj : forall s LB m b1 b2, RHEAP s LB m -> In b1 LB -> In b2 LB ->
  blk_addr b1 = blk_addr b2 -> b1 = b2.
Proof.
  intros s LB m b1 b2 (st & LB0 & HP & Hst & MR & [_ AR]) I1 I2 EA.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN1 : In b1 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I1]).
  assert (IN2 : In b2 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I2]).
  pose proof (MallocFacts_mng.areach_blocks_addr_inj st LB0 b1 b2 AR IN1 IN2 EA) as ES.
  exact (nodup_map_inj blk_slot LB0 b1 b2 (mf_nodup _ _ MF) IN1 IN2 ES).
Qed.

Lemma RHEAP_addr_nodup : forall s LB m, RHEAP s LB m -> List.NoDup (map blk_addr LB).
Proof.
  intros s LB m HH. pose proof (RHEAP_blocks_nodup_proof s LB m HH) as ND.
  assert (INJ : forall b1 b2, In b1 LB -> In b2 LB -> blk_addr b1 = blk_addr b2 -> b1 = b2) by (intros; eapply RHEAP_block_addr_inj; eauto).
  clear HH. induction LB as [|b LB IH]; cbn; [constructor|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
  constructor.
  - intros HI. apply in_map_iff in HI. destruct HI as (b' & E & Hb').
    pose proof (INJ b' b (or_intror Hb') (or_introl eq_refl) E) as ->. apply NI. apply in_map. exact Hb'.
  - apply IH; [exact ND'|]. intros b1 b2 H1 H2 E. apply INJ; [right; exact H1| right; exact H2| exact E].
Qed.

Lemma RHEAP_blocks_disjoint : forall s LB m b1 b2, RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_addr b1 <> blk_addr b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros s LB m b1 b2 HH I1 I2 NE. apply (RHEAP_blocks_disjoint_proof s LB m b1 b2 HH I1 I2).
  intros EI. apply NE. pose proof (RHEAP_blocks_nodup_proof s LB m HH) as ND.
  rewrite (nodup_map_inj blk_id LB b1 b2 ND I1 I2 EI). reflexivity.
Qed.

Lemma byte_lor_shift_low (b : byte) (c : Z) : 0 <= c -> Z_to_bv 8 (Z.lor (bv_unsigned b) (Z.shiftl c 8)) = b.
Proof.
  intros Hc. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.iter Z.mul].
  change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
  rewrite Z.land_lor_distr_l. rewrite (Z.land_ones (bv_unsigned b)) by lia. rewrite Z.mod_small by lia.
  replace (Z.land (Z.shiftl c 8) (Z.ones (Z.of_N 8))) with 0; [rewrite Z.lor_0_r; reflexivity|].
  symmetry. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0. change (Z.of_N 8) with 8.
  destruct (Z.lt_ge_cases n 8).
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. apply andb_false_r.
Qed.

Lemma lor_shift_high (b : byte) (c : Z) : 0 <= c -> Z.shiftr (Z.lor (bv_unsigned b) (Z.shiftl c 8)) 8 = c.
Proof.
  intros Hc. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb.
  rewrite Z.shiftr_lor. rewrite Z.shiftr_shiftl_l by lia. cbn [Z.sub]. rewrite Z.shiftl_0_r.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma bytes_le_to_Z_nonneg' : forall bs : list byte, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn; [lia|]. apply Z.lor_nonneg. split; [pose proof (bv_unsigned_in_range 8 b); lia|].
  apply Z.shiftl_nonneg. exact IH.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  rewrite byte_lor_shift_low by apply bytes_le_to_Z_nonneg'. rewrite lor_shift_high by apply bytes_le_to_Z_nonneg'.
  rewrite IH. reflexivity.
Qed.

Lemma rw_cell_C4_any : forall (m : mem) A,
  (forall i, (i < 4)%nat -> seg_rom rsegs (wa (A + Z.of_nat i)) <> None /\ wview rsegs (fun _ => None) (wa (A + Z.of_nat i)) <> None) ->
  0 <= A -> A + 4 <= 2^64 -> exists v, rw_cells rsegs m A [C4 v].
Proof.
  intros m A SEG A0 A4.
  set (rd := fun i => match mrd rsegs m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  set (bs := [rd 0%nat; rd 1%nat; rd 2%nat; rd 3%nat]).
  assert (RD : forall i, (i < 4)%nat -> mrd rsegs m (wa (A + Z.of_nat i)) = Some (rd i)).
  { intros i Hi. subst rd. cbn beta. unfold mrd. destruct (m (wa (A + Z.of_nat i))); [reflexivity|].
    destruct (SEG i Hi) as [S1 _]. destruct (seg_rom rsegs (wa (A + Z.of_nat i))); [reflexivity| congruence]. }
  exists (le_bytes_to_word bs).
  assert (LE : le4 (le_bytes_to_word bs) = bs).
  { unfold le4, le_bytes_to_word. pose proof (bytes_le_to_Z_nonneg' bs).
    assert (bytes_le_to_Z bs < 2 ^ 32).
    { pose proof (PropExec.bytes_le_to_Z_bound bs) as B. subst bs. cbn [length Nat.mul] in B. lia. }
    rewrite unsigned_lit by lia. exact (Z_to_le_bytes_to_Z bs). }
  split; [split|].
  - cbn. exact (conj I I).
  - cbn [cells_bytes cbytes app]. change (Mem.le4 ?x) with (le4 x). rewrite LE, app_nil_r. split; [lia|]. split; [subst bs; cbn [length]; lia|].
    intros i Hi. subst bs. cbn [length] in Hi. rewrite (RD i Hi).
    destruct i as [|[|[|[|i]]]]; try reflexivity. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct (SEG (Z.to_nat i) ltac:(lia)) as [_ W]. rewrite Z2Nat.id in W by lia.
    unfold wview in *. destruct (m (wa (A + i))); [discriminate| exact W].
Qed.

Lemma errno_cell_any : forall m : mem, exists v, rw_cells rsegs m RERRNO [C4 v].
Proof.
  intros m. apply rw_cell_C4_any; [| unfold RERRNO; lia| unfold RERRNO; lia].
  intros i Hi. unfold RERRNO.
  destruct i as [|[|[|[|i]]]]; [| | | | lia]; (split; [vm_compute; discriminate| vm_compute; discriminate]).
Qed.

Lemma stk_of_store_ok : forall (m : mem) lo n,
  store_ok rsegs m (Z_to_bv 64 lo) n = true -> 0 <= lo -> lo + Z.of_nat n <= 2^64 -> RIMG_HI <= lo ->
  stk rsegs m lo (lo + Z.of_nat n).
Proof.
  intros m lo n SO L0 L1 OFF. split; [lia|]. split; [lia|]. intros a Ha.
  pose proof (store_ok_wview rsegs m (Z_to_bv 64 lo) n (Z.to_nat (a - lo)) SO ltac:(lia)) as W.
  rewrite unsigned_lit in W by lia. rewrite Z2Nat.id in W by lia. replace (lo + (a - lo)) with a in W by lia.
  split; [exact W|].
  rewrite ref_wview_overlay in W by (unfold wa; rewrite unsigned_lit by lia; unfold RIMG_HI in OFF; lia).
  unfold mrd. destruct (m (wa a)) as [b|]; [exists b; reflexivity| congruence].
Qed.

Lemma got_wview_any : forall (m : mem) a, RGOT_SSP <= a < RGOT_SSP + 8 -> wview rsegs m (wa a) <> None.
Proof.
  intros m a Ha. unfold wview. destruct (m (wa a)); [discriminate|].
  assert (E : exists i, (i < 8)%nat /\ a = RGOT_SSP + Z.of_nat i) by (exists (Z.to_nat (a - RGOT_SSP)); split; [lia| lia]).
  destruct E as (i & Hi & ->). unfold RGOT_SSP.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [| | | | | | | | lia];
    match goal with |- ?x <> None => let y := eval vm_compute in x in change x with y end; discriminate.
Qed.

Lemma bptr_eqb_eq (p q : bptr) : bptr_eqb p q = true <-> p = q.
Proof.
  unfold bptr_eqb. rewrite andb_true_iff, aptr_eqb_eq, Z.eqb_eq. destruct p, q; cbn.
  split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

Lemma lb_remove_cons_keep q x LB : bptr_eqb (blk_id x) q = false -> lb_remove q (x :: LB) = x :: lb_remove q LB.
Proof. intros E. unfold lb_remove. rewrite filter_cons. rewrite E. cbn. reflexivity. Qed.
Lemma lb_remove_cons_drop q x LB : bptr_eqb (blk_id x) q = true -> lb_remove q (x :: LB) = lb_remove q LB.
Proof. intros E. unfold lb_remove. rewrite filter_cons. rewrite E. cbn. reflexivity. Qed.

Lemma lb_remove_notin LB q : ~ In q (map blk_id LB) -> lb_remove q LB = LB.
Proof.
  induction LB as [|x LB IH]; intros NI; [reflexivity|].
  destruct (bptr_eqb (blk_id x) q) eqn:E.
  - apply bptr_eqb_eq in E. exfalso. apply NI. left. exact E.
  - rewrite lb_remove_cons_keep by exact E. f_equal. apply IH. intros H. apply NI. right. exact H.
Qed.

Lemma lb_remove_perm_cons LB b : List.NoDup (map blk_id LB) -> In b LB -> Permutation LB (b :: lb_remove (blk_id b) LB).
Proof.
  intros ND Hin. induction LB as [|x LB IH]; [destruct Hin|]. cbn in ND. inversion ND as [|y l NI ND']; subst.
  destruct Hin as [<-|Hin].
  - rewrite lb_remove_cons_drop by (apply bptr_eqb_eq; reflexivity). rewrite lb_remove_notin by exact NI. apply Permutation_refl.
  - destruct (bptr_eqb (blk_id x) (blk_id b)) eqn:E.
    + apply bptr_eqb_eq in E. exfalso. apply NI. rewrite E. apply in_map. exact Hin.
    + rewrite lb_remove_cons_keep by exact E. eapply Permutation_trans; [apply perm_skip; apply IH; [exact ND'| exact Hin]|]. apply perm_swap.
Qed.

Lemma In_lb_remove LB q b : In b (lb_remove q LB) <-> In b LB /\ blk_id b <> q.
Proof.
  unfold lb_remove. rewrite <- !list_elem_of_In. rewrite list_elem_of_filter.
  split; intros [H1 H2]; split; try assumption.
  - intros E. rewrite E, (proj2 (bptr_eqb_eq _ _) eq_refl) in H1. exact H1.
  - destruct (bptr_eqb (blk_id b) q) eqn:E; [| exact I]. apply bptr_eqb_eq in E. contradiction.
Qed.

Definition in_blockb (LB : list block) (a : Z) : bool :=
  existsb (fun b => (blk_addr b <=? a) && (a <? blk_addr b + blk_size b)) LB.

Lemma in_blockb_spec LB a : in_blockb LB a = true <-> in_block LB a.
Proof.
  unfold in_blockb, in_block. rewrite existsb_exists. split.
  - intros (b & Hb & H). apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists b. auto.
  - intros (b & Hb & H). exists b. split; [exact Hb|]. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma rframe_cases LBX lo sp (M m' : mem) a : rframe LBX lo sp M m' -> 0 <= a < 2 ^ 64 ->
  (m' (wa a) = M (wa a) /\ (wview rsegs M (wa a) <> None -> wview rsegs m' (wa a) <> None))
  \/ lo <= a < sp \/ (RERRNO <= a < RERRNO + 4) \/ (RCTX <= a < RCTX + 928)
  \/ ((a < RIMG_LO \/ RIMG_HI <= a) /\ 0 < a < alloc_ceiling /\ ~ in_block LBX a).
Proof.
  intros (FP & PE & FPC) Ha.
  assert (NFP : ~ FP a -> m' (wa a) = M (wa a) /\ (wview rsegs M (wa a) <> None -> wview rsegs m' (wa a) <> None)) by (intros N; exact (PE a Ha N)).
  assert (D1 : {lo <= a < sp} + {~ (lo <= a < sp)}) by (destruct (Z_le_gt_dec lo a); destruct (Z_lt_ge_dec a sp); first [left; lia | right; lia]).
  assert (D2 : {RERRNO <= a < RERRNO + 4} + {~ (RERRNO <= a < RERRNO + 4)}) by (destruct (Z_le_gt_dec RERRNO a); destruct (Z_lt_ge_dec a (RERRNO + 4)); first [left; lia | right; lia]).
  assert (D3 : {RCTX <= a < RCTX + 928} + {~ (RCTX <= a < RCTX + 928)}) by (destruct (Z_le_gt_dec RCTX a); destruct (Z_lt_ge_dec a (RCTX + 928)); first [left; lia | right; lia]).
  assert (D4 : {(a < RIMG_LO \/ RIMG_HI <= a) /\ 0 < a < alloc_ceiling} + {~ ((a < RIMG_LO \/ RIMG_HI <= a) /\ 0 < a < alloc_ceiling)})
    by (destruct (Z_lt_ge_dec a RIMG_LO); destruct (Z_le_gt_dec RIMG_HI a); destruct (Z_lt_ge_dec 0 a); destruct (Z_lt_ge_dec a alloc_ceiling); first [left; lia | right; lia]).
  destruct D1 as [Y1|N1]; [right; left; exact Y1|].
  destruct D2 as [Y2|N2]; [right; right; left; exact Y2|].
  destruct D3 as [Y3|N3]; [right; right; right; left; exact Y3|].
  destruct D4 as [Y4|N4].
  - destruct (in_blockb LBX a) eqn:IB.
    + left. apply NFP. intros F. destruct (FPC a F) as [X|[X|[X|(X1 & X2 & X3)]]]; [exact (N1 X)| exact (N2 X)| exact (N3 X)|].
      apply X3. apply in_blockb_spec. exact IB.
    + do 4 right. split; [exact (proj1 Y4)|]. split; [exact (proj2 Y4)|]. intros IBP. apply in_blockb_spec in IBP. congruence.
  - left. apply NFP. intros F. destruct (FPC a F) as [X|[X|[X|(X1 & X2 & X3)]]]; [exact (N1 X)| exact (N2 X)| exact (N3 X)|].
    apply N4. split; [exact X1| exact X2].
Qed.

End AC_1.
