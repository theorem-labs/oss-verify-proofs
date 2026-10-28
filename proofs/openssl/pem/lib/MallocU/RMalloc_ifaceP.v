(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_malloc_free MallocHINV MallocFacts_A Malloc_iface InitMem F_malloc_top Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMallocKit_B RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require MallocFacts_inv2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rregion_addr_facts : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
  /\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x353000 <= r_base r).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  split; [|split; [exact RBAL| split; [exact RBC| intros Hn; exact (rreserved_disjoint1 _ _ RFr Hn)]]].
  clear RFr. Z.div_mod_to_equations. lia.
Qed.

Lemma rblock_inside st LB m blk :
  MFACTS_g (resv:=ref_reserved) st LB -> rmrep st m -> In blk LB ->
  exists r g idx, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
    /\ (s_slots st) !! (blk_slot blk) = Some (g, idx)
    /\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)
    /\ 0 <= blk_size blk
    /\ 4096 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
    /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x353000 <= r_base r).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MF MR IN.
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk IN) as [BS BR BZ].
  destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
  destruct BR as (r & Hr & Hk).
  pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
  pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof (rregion_addr_facts st m _ r MR Hr) as (R4 & _ & RC & RI1).
  exists r, g, idx. split; [exact Hr|]. split; [exact Hk|]. split; [exact SL|].
  pose proof (round_up_pg_ge (r_len r)) as RU.
  rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
  unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
  assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Esnd in EA. unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  assert (RP : 0 < round_up_pg (r_len r)) by lia. specialize (RI1 RP). lia.
Qed.

Lemma RHEAP_blocks_nodup_proof : forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros s LB m (st & LB0 & HP & _ & _ & [_ AR]). pose proof (mf_nodup _ _ (MallocFacts_inv2.areach_facts_proof _ _ AR)) as ND.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
  clear -ND. induction LB0 as [|b LB0 IH]; cbn in *; [constructor|].
  inversion ND; subst. constructor; [|apply IH; assumption].
  intros HI. apply H1. apply in_map_iff in HI. destruct HI as (b' & E & HI'). apply in_map_iff. exists b'. split; [|exact HI'].
  unfold blk_slot, blk_id in *. rewrite E. reflexivity.
Qed.

Lemma RHEAP_block_range_proof : forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros s LB m b (st & LB0 & HP & _ & MR & [_ AR]) HIN. pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
  destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) b IN0) as [BS BR _].
  destruct BS as (g' & idx' & SL' & _ & _ & _ & (off & OFF0 & EA & FIT)). rewrite SL in SL'. inversion SL'; subst g' idx'. clear SL'.
  pose proof (mf_slots _ _ MF (blk_slot b) g idx SL) as (bb & Hm & Efst & Esnd & IDX).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd, IDX.
  pose proof (mf_gmeta _ _ MF g bb Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & B16 & SPAN) & S16 & SMOD & _).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RAL & _ & RC' & RF).
  unfold sstart_of in SPAN. rewrite Hm in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT in SPAN, S16.
  assert (32 <= round_up_pg (r_len r)) by nia.
  unfold rblock_range. unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. split; [lia|]. split; [|lia].
  rewrite EA. rewrite (conc_region' st (blk_slot b) r Hr). rewrite Esnd. unfold sstart_of. rewrite Hm. cbn [default from_option id snd].
  replace (r_base r + (snd bb + UNIT + get_stride (get_meta_rec st g) * idx) + UNIT * off)
    with (r_base r + snd bb + 16 + get_stride (get_meta_rec st g) * idx + 16 * off) by (unfold UNIT; lia).
  apply (mod16_slot (r_base r) (snd bb) (get_stride (get_meta_rec st g)) idx off); try assumption; lia.
Qed.

Lemma RHEAP_blocks_disjoint_proof : forall s LB m b1 b2,
  RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros s LB m b1 b2 (st & LB0 & HP & _ & MR & [_ AR]) I1 I2 NE. pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN1 : In b1 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I1]).
  assert (IN2 : In b2 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I2]).
  destruct (decide (blk_slot b1 = blk_slot b2)) as [ES|NS].
  - exfalso. apply NE. pose proof (mf_nodup _ _ MF) as ND.
    clear -ND IN1 IN2 ES. induction LB0 as [|b LB0 IH]; [destruct IN1|]. cbn in ND. inversion ND; subst.
    destruct IN1 as [->|IN1], IN2 as [->|IN2]; [reflexivity| | | apply IH; assumption].
    + exfalso. apply H1. rewrite ES. apply in_map_iff. exists b2; auto.
    + exfalso. apply H1. rewrite <- ES. apply in_map_iff. exists b1; auto.
  - destruct (N.eq_dec (fst (blk_slot b1)) (fst (blk_slot b2))) as [EF|NF].
    + exact (mf_blocks_disjoint _ _ MF b1 b2 IN1 IN2 EF NS).
    + destruct (rblock_inside st LB0 m b1 MF MR IN1) as (r1 & g1 & i1 & Hr1 & Hk1 & _ & LO1 & HI1 & _).
      destruct (rblock_inside st LB0 m b2 MF MR IN2) as (r2 & g2 & i2 & Hr2 & Hk2 & _ & LO2 & HI2 & _).
      pose proof MR as (WF & _). pose proof WF as (_ & _ & DJ & _).
      pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
      destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rrepfoot_where st m a : rmrep st m -> rrepfoot st a ->
  a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38
                        \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8 \/ a < 0x10000 \/ 0x3520d0 <= a).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
  destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
    unfold RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RVMLOCK, OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  - lia. - lia. - lia. - lia.
  - destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
    pose proof (round_up_pg_ge (r_len ra)). lia.
  - destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
    pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
  - lia. - lia.
Qed.

Lemma RHEAP_frame_proof : forall s LB m m' W,
  RHEAP s LB m -> munch W m m' -> wmono usegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros s LB m m' W (st & LB0 & HP & Hst & MR & HI) MU WM FW. exists st, LB0. split; [exact HP|]. split; [exact Hst|].
  split; [|exact HI].
  destruct HI as [_ AR]. pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  eapply (rmrep_transport_unowned st m m' W MR MU WM).
  intros lo hi a Hin Ha RF.
  pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as CW. cbn [fst snd] in CW.
  destruct (rrepfoot_where st m a MR RF) as [AC AW].
  destruct CW as [CW|[CW|(b & Hb & B1 & B2)]]; cbn [fst snd] in *.
  - unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
  - unfold RMLOCK, RLIBC, RCTX, RERRNO, RATP, RGOT_SSP, RSSP_GUARD, RVMLOCK, OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
  - (* [comment removed for export] *)
    assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
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
    + unfold RSSP_GUARD, RVMLOCK in R9. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reservedZ_ref : reservedZ usegs = ref_reserved.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). vm_compute. reflexivity. Qed.

Lemma u64arr_of_rw_cells' : forall m A n bs k, rw_cells usegs m A [CB n bs] -> bs = u64s (repeat (wz 0) k) -> (n = 8 * k)%nat ->
  u64arr usegs m A (repeat (wz 0) k).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros m A n bs k [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  split; [exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. exact HW.
Qed.

(* [comment removed for export] *)
End WithCeiling0.
Ltac rimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells usegs m A cs);
  [ apply (rw_cells_recast usegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 usegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha; lia | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma RHEAP_init_proof : forall (m : mem) (auxv : word),
  (forall a : word, 0x350c68 <= bv_unsigned a < 0x3520d8 -> m a = None) ->
  rw_cells usegs m 0x350bf8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] ->
  rw_cells usegs m 0x350c00 [C8 auxv; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                            C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)] ->
  rw_cells usegs m 0x31c468 [C8 (Z_to_bv 64 0x3509a8)] ->
  rw_cells usegs m 0x3509a8 [C8 rr_guard] ->
  mem_inv usegs m ->
  RHEAP (ps_init (reservedZ usegs)) [] m
  /\ rw_cells usegs m RAUXV_CELL [C8 auxv].
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros m auxv NONE LC LC2 GOT GUARD MI.
  set (st0 := minit 0 ref_reserved).
  rimg_chunk NONE m 0x350c70%Z (rctx_head_cells st0) CXH.
  rimg_chunk NONE m (0x350c70 + 80)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXA.
  rimg_chunk NONE m (0x350c70 + 464)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXU.
  rimg_chunk NONE m (0x350c70 + 848)%Z [CB 32 (zeros 32)] CXS.
  rimg_chunk NONE m (0x350c70 + 880)%Z [CB 32 (zeros 32)] CXB.
  rimg_chunk NONE m (0x350c70 + 912)%Z (ctx_tail_cells st0) CXT.
  rimg_chunk NONE m 0x350c68%Z [C4 (wz 0)] ML.
  rimg_chunk NONE m 0x3520d0%Z [C4 (wz 0)] VML.
  (* [comment removed for export] *)
  pose proof (proj1 (rw_cells_app usegs m 0x350bf8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] _) LC) as [_ LC3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LC3.
  pose proof (proj1 (rw_cells_app usegs m (0x350bf8 + 3) [C1 (Z_to_bv 8 0)] _) LC3) as [NL _].
  pose proof (proj1 (rw_cells_app usegs m 0x350c00 [C8 auxv] _) LC2) as [AUXC LC16]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LC16.
  pose proof (proj1 (rw_cells_app usegs m (0x350c00 + 8) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0)] _) LC16) as [_ LC48].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in LC48.
  pose proof (proj1 (rw_cells_app usegs m _ [C8 (Z_to_bv 64 4096)] _) LC48) as [PS _].
  split.
  2:{ unfold RAUXV_CELL. exact AUXC. }
  exists st0, []. split; [apply Permutation_refl|]. split; [unfold ps_init; cbn [ps_m]; rewrite reservedZ_ref; reflexivity|].
  split.
  2:{ unfold ps_init; cbn [ps_brk]. apply HINV_from_init. }
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *) split; [reflexivity|]. split; [intros rid r H; rewrite lookup_empty in H; discriminate|].
    split; [intros ? ? ? ? H; rewrite lookup_empty in H; discriminate|].
    split; [intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate|].
    intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate.
  - unfold rmrep_ctx, RCTX. split; [exact CXH|]. split; [|split; [|split; [|split]]].
    + replace (actives st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXA| reflexivity| reflexivity].
    + replace (usages st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXU| reflexivity| reflexivity].
    + replace (unmap_seqs st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells usegs m _ 32). exact CXS.
    + replace (bouncess st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells usegs m _ 32). exact CXB.
    + exact CXT.
  - unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RVMLOCK. split; [exact ML|]. split; [|split; [|split; [|split]]].
    + match goal with |- rw_cells _ _ ?G _ => match type of NL with rw_cells _ _ ?A _ => replace G with A by reflexivity end end.
      change (b8 0) with (Z_to_bv 8 0). exact NL.
    + match goal with |- rw_cells _ _ ?G _ => match type of PS with rw_cells _ _ ?A _ => replace G with A by reflexivity end end.
      change (wz 4096) with (Z_to_bv 64 4096). exact PS.
    + change (wz 3475880) with (Z_to_bv 64 0x3509a8). exact GOT.
    + exact GUARD.
    + exact VML.
  - intros a ar H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros b gh H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros rid r H. cbn in H. rewrite lookup_empty in H. discriminate.
Qed.
End WithCeiling1.
