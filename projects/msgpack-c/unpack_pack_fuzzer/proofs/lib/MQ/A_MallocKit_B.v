(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_syscalls A_MallocRep A_F_malloc_free A_MallocTree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl.

Set Keyed Unification.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition repfoot (st : mstate) (a : Z) : Prop :=
  (CTX <= a < CTX + 928) \/ (MLOCK <= a < MLOCK + 4) \/ (NEED_LOCKS <= a < NEED_LOCKS + 1) \/ (PAGE_SIZE_A <= a < PAGE_SIZE_A + 8)
  \/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
  \/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
        /\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

Lemma repfoot_ctx st a : CTX <= a < CTX + 928 -> repfoot st a. Proof. intros; left; assumption. Qed.
Lemma repfoot_mlock st a : MLOCK <= a < MLOCK + 4 -> repfoot st a. Proof. intros; right; left; assumption. Qed.
Lemma repfoot_nl st a : NEED_LOCKS <= a < NEED_LOCKS + 1 -> repfoot st a. Proof. intros; do 2 right; left; assumption. Qed.
Lemma repfoot_pgsz st a : PAGE_SIZE_A <= a < PAGE_SIZE_A + 8 -> repfoot st a. Proof. intros; do 3 right; left; assumption. Qed.
Lemma repfoot_area st a ak ar : (s_areas st) !! ak = Some ar -> conc st ak <= a < conc st ak + 4096 -> repfoot st a.
Proof. intros; do 4 right; left. exists ak, ar. auto. Qed.
Lemma repfoot_group st a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> repfoot st a.
Proof. intros; do 5 right; left. exists b, gh. auto. Qed.
Lemma repfoot_known st a rid r v : (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  r_base r <= a < r_base r + round_up_pg (r_len r) -> cell_read (get_shadow st rid) (a - r_base r) = Known v -> repfoot st a.
Proof. intros; do 6 right. exists rid, r, v. auto. Qed.

Definition ivs_avoid (W : list (Z * Z)) (P : Z -> Prop) : Prop :=
  forall lo hi a, In (lo, hi) W -> lo <= a < hi -> ~ P a.

Lemma ivs_avoid_nil : forall P, ivs_avoid [] P.
Proof. intros P lo hi a []. Qed.

Lemma ivs_avoid_cons : forall lo hi W P,
  (forall a, lo <= a < hi -> ~ P a) -> ivs_avoid W P -> ivs_avoid ((lo, hi) :: W) P.
Proof.
  intros lo hi W P H1 H2 lo' hi' a [E|Hin] Ha.
  - inversion E; subst. apply H1. exact Ha.
  - eapply H2; eauto.
Qed.

Lemma avoid_outside : forall W P x, ivs_avoid W P -> P x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros P x HW HP; cbn; [exact I|]. split.
  - intros Hx. exact (HW lo hi x ltac:(left; reflexivity) Hx HP).
  - apply (IH P); [|exact HP]. intros lo' hi' a Hin Ha. apply (HW lo' hi'); [right; exact Hin|exact Ha].
Qed.

Definition agree_on (m m' : word -> option byte) (A n : Z) : Prop :=
  forall a, A <= a < A + n -> m' (wa a) = m (wa a).

Lemma munch_agree : forall W m m' P A n,
  munch W m m' -> ivs_avoid W P -> (forall a, A <= a < A + n -> P a) -> 0 <= A -> A + n <= 2^64 ->
  agree_on m m' A n.
Proof.
  intros W m m' P A n MU HW HP HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
  eapply avoid_outside; [exact HW| apply HP; exact Ha].
Qed.

Lemma bytes_at_agree : forall m m' A bs,
  bytes_at asegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at asegs m' A bs.
Proof.
  intros m m' A bs (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

Lemma rw_cells_agree : forall m m' A cs,
  rw_cells asegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> wmono asegs m m' -> rw_cells asegs m' A cs.
Proof.
  intros m m' A cs [[Hwf HB] HW] AG WM. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply wr_at_transport; eauto.
Qed.

Lemma u64arr_agree : forall m m' A ws,
  u64arr asegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> wmono asegs m m' -> u64arr asegs m' A ws.
Proof.
  intros m m' A ws [HB HW] AG WM. split; [|eapply wr_at_transport; eauto].
  eapply bytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
Qed.

Lemma u8arr_agree : forall m m' A bs,
  u8arr asegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> wmono asegs m m' -> u8arr asegs m' A bs.
Proof. intros m m' A bs [HB HW] AG WM. split; [eapply bytes_at_agree; eauto| eapply wr_at_transport; eauto]. Qed.

Lemma mrep_transport_unowned : forall st m m' W,
  mrep st m -> munch W m m' -> wmono asegs m m' -> ivs_avoid W (repfoot st) -> mrep st m'.
Proof.
  intros st m m' W (WF & CX & GL & AR & GR & SH) MU WM HW.
  pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (TC : forall A cs, rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> repfoot st a) -> rw_cells asegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound asegs m A cs H). eapply rw_cells_agree; eauto. eapply munch_agree; eauto; lia. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold mrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (u64arr_bound asegs m _ _ C2) as B2. pose proof (u64arr_bound asegs m _ _ C3) as B3.
    pose proof (u8arr_bound asegs m _ _ C4) as B4. pose proof (u8arr_bound asegs m _ _ C5) as B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply repfoot_ctx. cbn in Ha. unfold CTX in *. lia.
    + eapply u64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L1 in *; try lia. intros a Ha. apply repfoot_ctx. unfold CTX in *. lia.
    + eapply u64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L2 in *; try lia. intros a Ha. apply repfoot_ctx. unfold CTX in *. lia.
    + eapply u8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L3 in *; try lia. intros a Ha. apply repfoot_ctx. unfold CTX in *. lia.
    + eapply u8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L4 in *; try lia. intros a Ha. apply repfoot_ctx. unfold CTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. apply repfoot_ctx. cbn in Ha. unfold CTX in *. lia.
  - destruct GL as (G1 & G2 & G3). split; [|split].
    + apply TC; [exact G1 |]. intros a Ha. apply repfoot_mlock. cbn in Ha. unfold MLOCK in *. lia.
    + apply TC; [exact G2 |]. intros a Ha. apply repfoot_nl. cbn in Ha. unfold NEED_LOCKS in *. lia.
    + apply TC; [exact G3 |]. intros a Ha. apply repfoot_pgsz. cbn in Ha. unfold PAGE_SIZE_A in *. lia.
  - intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. eapply repfoot_area; [exact Ha|lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply repfoot_area; [exact Ha|lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. eapply repfoot_area; [exact Ha|lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. eapply repfoot_group; [exact Hb|lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. split.
    + eapply wr_at_transport; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      pose proof Bt as (B0 & B1 & _). cbn in B1.
      eapply bytes_at_agree; [exact Bt|]. eapply munch_agree; eauto; cbn; try lia. intros a Ha.
      eapply (repfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

Lemma get_meta_rec_put : forall st g mr g',
  get_meta_rec (put_meta g mr st) g' = if aptr_eqb g' g then mr else get_meta_rec st g'.
Proof.
  intros. unfold get_meta_rec at 1. unfold put_meta. cbn [s_metas set_metas].
  unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
  destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
    first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma upd_meta_put : forall st g f, upd_meta g f st = put_meta g (f (get_meta_rec st g)) st.
Proof. reflexivity. Qed.

Lemma mrep_put_meta_frame : forall st m m' g mr',
  mrep st m -> meta_slot st g ->
  munch [(conc st g, conc st g + META_SIZE)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' (conc st g) (meta_cells st mr') ->
  mrep (put_meta g mr' st) m'.
Proof.
  intros st m m' g mr' MR (a & ar & k & Ha & Hk & Eg) MU WM CH.
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  destruct (area_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). pose_ceil.
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RFa). destruct (reserved_disjoint _ _ RFa) as [_ DRa].
  pose proof (round_up_pg_ge (r_len ra)) as RU.

  assert (Hconc : forall q, conc (put_meta g mr' st) q = conc st q) by (intros; reflexivity).
  assert (Hpw : forall q, pw (put_meta g mr' st) q = pw st q) by (intros [q|]; reflexivity).
  assert (Hmc : forall mr, meta_cells (put_meta g mr' st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
  assert (TC : forall A cs, rw_cells asegs m A cs ->
            (A + Z.of_nat (cells_size cs) <= conc st g \/ conc st g + 40 <= A) -> rw_cells asegs m' A cs).
  { intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
  split; [|split; [|split; [|split; [|split]]]].
  - exact WF.
  - eapply mrep_ctx_ext; [reflexivity|exact Hconc|].
    destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold mrep_ctx. unfold CTX in *.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 | cbn; lia].
    + eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L1. split; [lia|exact I].
    + eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L2. split; [lia|exact I].
    + eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L3. split; [lia|exact I].
    + eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L4. split; [lia|exact I].
    + apply TC; [exact C6 | cbn; lia].
  - destruct GL as (G1 & G2 & G3). unfold mrep_globals, MLOCK, NEED_LOCKS, PAGE_SIZE_A in *.
    split; [|split]; (apply TC; [assumption | cbn; lia]).
  - intros a' ar' Ha'. cbn in Ha'.
    destruct (area_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
    destruct (decide (a' = a)) as [->|NEa].
    + rewrite Ha in Ha'. inversion Ha'; subst ar'.
      destruct (AR a ar Ha) as (HD & SL & PD). unfold area_rep. rewrite !Hconc, Hpw.
      split; [|split].
      * apply TC; [exact HD| cbn; lia].
      * intros k' Hk'. rewrite Hmc, get_meta_rec_put.
        destruct (Z.eq_dec k' k) as [->|NEk].
        -- rewrite <- Eg, aptr_eqb_refl.
           replace (conc st a + 24 + 40 * k) with (conc st g) by (rewrite HG; lia). exact CH.
        -- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
           2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
           apply TC; [apply SL; lia|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE. nia.
      * apply TC; [exact PD| cbn; lia].
    + assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
        assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
        Z.div_mod_to_equations. nia. }
      assert (DD : conc st a' + 4096 <= conc st g \/ conc st g + 40 <= conc st a').
      { rewrite Ca', HG, Ca. destruct PG as [NE|[E PG]].
        - pose proof (area_lr_lo st a ar ra WF Ha Hra). pose proof (area_lr_lo st a' ar' ra' WF Ha' Hra').
          destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NE); lia.
        - rewrite E, Hra in Hra'. inversion Hra'; subst ra'. lia. }
      eapply area_rep_ext; [exact Hconc| |].
      { intros k0 Hk0. rewrite get_meta_rec_put. unfold AREA_HDR, META_SIZE, NSLOTS in *.
        replace (aptr_eqb (aadd a' (24 + 40 * k0)) g) with false; [reflexivity|].
        symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn [fst snd].
        destruct PG as [NE|[E PG]].
        - rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
        - rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. lia. }
      destruct (AR a' ar' Ha') as (HD & SL & PD). split; [|split].
      * apply TC; [exact HD| cbn; lia].
      * intros k0 Hk0. apply TC; [apply SL; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE, NSLOTS in *. nia.
      * apply TC; [exact PD| cbn; lia].
  - intros b gh Hb. cbn in Hb. eapply group_rep_ext; [exact Hconc|].
    destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
    destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R|]. cbn. rewrite Cb, HG, Ca.
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
    pose proof (area_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Kb).
    destruct (DJ (fst b) rb (fst a) ra Hrb Hra NE); lia.
  - intros rid r' Hr' Hk'. cbn in Hr'. eapply shadow_rep_ext; [reflexivity|].
    destruct (SH rid r' Hr' Hk') as [HWr HB]. split; [eapply wr_at_transport; eauto|].
    intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
    eapply bytes_at_transport; eauto. cbn. split; [|exact I].
    assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    pose proof (area_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r' Hk').
    rewrite HG, Ca. destruct (DJ rid r' (fst a) ra Hr' Hra NE); lia.
Qed.

Lemma mrep_ctx_frame' : forall st st' m m',
  mrep st m -> munch [(CTX, CTX + 928)] m m' -> wmono asegs m m' ->
  s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
  s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_reserved st' = s_reserved st ->
  mrep_ctx st' m' -> mrep st' m'.
Proof.
  intros st st' m m' (WF & CX & GL & AR & GR & SH) MU WM ER EM EA EG ES ERs CX'.
  pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  assert (Hgm : forall q, get_meta_rec st' q = get_meta_rec st q) by (intros q; unfold get_meta_rec; rewrite EM; reflexivity).
  assert (Hsh : forall rid, get_shadow st' rid = get_shadow st rid) by (intros rid; unfold get_shadow; rewrite ES; reflexivity).
  assert (TC : forall A cs, rw_cells asegs m A cs -> (A + Z.of_nat (cells_size cs) <= CTX \/ CTX + 928 <= A) -> rw_cells asegs m' A cs).
  { intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
  unfold CTX in *.
  split; [|split; [exact CX'|split; [|split; [|split]]]].
  - unfold regions_wf. rewrite ER, EA, EG, ERs. exact WF.
  - destruct GL as (G1 & G2 & G3). unfold mrep_globals, MLOCK, NEED_LOCKS, PAGE_SIZE_A in *.
    split; [|split]; (apply TC; [assumption | cbn; lia]).
  - intros ak ar Ha. rewrite EA in Ha. eapply area_rep_ext; [exact Hconc| intros; apply Hgm |].
    destruct (area_conc st ak ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    destruct (WR (fst ak) ra Hra) as (_ & _ & _ & _ & RF). destruct (reserved_disjoint _ _ RF) as [_ D].
    pose proof (round_up_pg_ge (r_len ra)).
    destruct (AR ak ar Ha) as (A1 & A2 & A3). split; [|split].
    + apply TC; [exact A1| cbn; lia].
    + intros k Hk. apply TC; [apply A2; exact Hk|]. unfold meta_cells, AREA_HDR, META_SIZE, NSLOTS in *. cbn [cells_size csize Nat.add length]. lia.
    + apply TC; [exact A3| cbn; lia].
  - intros b gh Hb. rewrite EG in Hb. eapply group_rep_ext; [exact Hconc|].
    destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
    destruct (WR (fst b) rb Hrb) as (_ & _ & _ & _ & RF). destruct (reserved_disjoint _ _ RF) as [_ D].
    pose proof (round_up_pg_ge (r_len rb)).
    destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8]. apply TC; [exact R| cbn; lia].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply shadow_rep_ext; [apply Hsh|].
    destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). destruct (reserved_disjoint _ _ RF) as [_ D].
    destruct (SH rid r Hr Hk) as [HWr HB]. split; [eapply wr_at_transport; eauto|].
    intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
    eapply bytes_at_transport; eauto. cbn. split; [lia|exact I].
Qed.

Lemma mrep_del_group : forall st m p, mrep st m -> mrep (del_group p st) m.
Proof.
  intros st m p (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (Hconc : forall q, conc (del_group p st) q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
    intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb]. exact (WG b gh Hb).
  - eapply mrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
  - intros a ar Ha. eapply area_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
  - intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb].
    eapply group_rep_ext; [exact Hconc|exact (GR b gh Hb)].
  - intros rid r Hr Hk. eapply shadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

Lemma mrep_set_slots : forall st m v, mrep st m -> mrep (set_slots v st) m.
Proof.
  intros st m v (WF & CX & GL & AR & GR & SH).
  assert (Hconc : forall q, conc (set_slots v st) q = conc st q) by (intros; reflexivity).
  split; [exact WF|]. split; [|split; [exact GL|split; [|split]]].
  - eapply mrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
  - intros a ar Ha. eapply area_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
  - intros b gh Hb. eapply group_rep_ext; [exact Hconc|exact (GR b gh Hb)].
  - intros rid r Hr Hk. eapply shadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

Lemma del_slots_eq : forall p s c st, del_slots p s c st = set_slots (s_slots (del_slots p s c st)) st.
Proof. reflexivity. Qed.

Lemma mrep_del_slots : forall st m p s c, mrep st m -> mrep (del_slots p s c st) m.
Proof. intros. rewrite del_slots_eq. apply mrep_set_slots. assumption. Qed.

Lemma meta_slot_same_areas : forall st st' g, s_areas st' = s_areas st -> meta_slot st g -> meta_slot st' g.
Proof. intros st st' g E (a & ar & k & Ha & Hk & Eg). exists a, ar, k. rewrite E. auto. Qed.

Lemma nth_error_map_seq : forall {X} (f : nat -> X) n s i,
  (i < n)%nat -> nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof.
  intros X f n. induction n as [|n IH]; intros s i Hi; [lia|].
  cbn [seq map]. destruct i as [|i]; cbn [nth_error]; [f_equal; f_equal; lia|].
  rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma actives_nth : forall st sc, 0 <= sc < 48 ->
  nth_error (actives st) (Z.to_nat sc) = Some (pw st (active st sc)).
Proof.
  intros st sc H. unfold actives. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma usages_nth : forall st sc, 0 <= sc < 48 ->
  nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
  intros st sc H. unfold usages. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma bouncess_nth : forall st i, 0 <= i < 32 ->
  nth_error (bouncess st) (Z.to_nat i) = Some (b8 (bounces st i)).
Proof.
  intros st i H. unfold bouncess. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma unmap_seqs_nth : forall st i, 0 <= i < 32 ->
  nth_error (unmap_seqs st) (Z.to_nat i) = Some (b8 (unmap_seq st i)).
Proof.
  intros st i H. unfold unmap_seqs. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma actives_length st : length (actives st) = 48%nat.
Proof. unfold actives; rewrite map_length, seq_length; reflexivity. Qed.
Lemma usages_length st : length (usages st) = 48%nat.
Proof. unfold usages; rewrite map_length, seq_length; reflexivity. Qed.
Lemma bouncess_length st : length (bouncess st) = 32%nat.
Proof. unfold bouncess; rewrite map_length, seq_length; reflexivity. Qed.
Lemma unmap_seqs_length st : length (unmap_seqs st) = 32%nat.
Proof. unfold unmap_seqs; rewrite map_length, seq_length; reflexivity. Qed.

Lemma mrep_active_read : forall st m sc a, mrep st m -> 0 <= sc < 48 -> a = wa (CTX + 80 + 8 * sc) ->
  ov_read_bytes asegs m a 8 = Some (le8 (pw st (active st sc))).
Proof.
  intros st m sc a (_ & (_ & C2 & _) & _) Hsc ->.
  eapply u64arr_read; [exact C2 | apply actives_nth; exact Hsc | lia | reflexivity].
Qed.

Lemma mrep_usage_read : forall st m sc a, mrep st m -> 0 <= sc < 48 -> a = wa (CTX + 464 + 8 * sc) ->
  ov_read_bytes asegs m a 8 = Some (le8 (wz (usage st sc))).
Proof.
  intros st m sc a (_ & (_ & _ & C3 & _) & _) Hsc ->.
  eapply u64arr_read; [exact C3 | apply usages_nth; exact Hsc | lia | reflexivity].
Qed.

Lemma mrep_bounces_read : forall st m i a, mrep st m -> 0 <= i < 32 -> a = wa (CTX + 880 + i) ->
  ov_read_bytes asegs m a 1 = Some [b8 (bounces st i)].
Proof.
  intros st m i a (_ & (_ & _ & _ & _ & C5 & _) & _) Hi ->.
  eapply u8arr_read; [exact C5 | apply bouncess_nth; exact Hi | lia | reflexivity].
Qed.

Lemma mrep_seq_read : forall st m a, mrep st m -> a = wa (CTX + 912) ->
  ov_read_bytes asegs m a 1 = Some [b8 (c_seq (ctx st))].
Proof.
  intros st m a (_ & (_ & _ & _ & _ & _ & C6) & _) ->.
  apply (rw_cells_read_at asegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 _ C6); reflexivity.
Qed.

Lemma mrep_fmh_read : forall st m a, mrep st m -> a = wa (CTX + 16) ->
  ov_read_bytes asegs m a 8 = Some (le8 (pw st (c_free_meta_head (ctx st)))).
Proof.
  intros st m a (_ & (C1 & _) & _) ->.
  apply (rw_cells_read_at asegs m _ _ 16 (C8 (pw st (c_free_meta_head (ctx st)))) 8 _ C1); reflexivity.
Qed.

Lemma bytes_at_cons : forall m a b bs, bytes_at asegs m a (b :: bs) <-> bytes_at asegs m a [b] /\ bytes_at asegs m (a + 1) bs.
Proof.
  intros. change (b :: bs) with ([b] ++ bs). rewrite (bytes_at_app asegs m a [b] bs). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat]. tauto.
Qed.

Lemma put_meta_put_meta_same : forall st g a b, put_meta g a (put_meta g b st) = put_meta g a st.
Proof. intros. destruct st; unfold put_meta, set_metas; cbn. f_equal. apply insert_insert_eq. Qed.

Lemma aptr_eqb_neq : forall a b : aptr, a <> b -> aptr_eqb a b = false.
Proof.
  intros [a1 a2] [b1 b2] H. unfold aptr_eqb. cbn.
  destruct (N.eqb_spec a1 b1); destruct (Z.eqb_spec a2 b2); cbn; try reflexivity. exfalso. apply H. congruence.
Qed.

Lemma aptr_eqb_eq : forall a b : aptr, aptr_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

Lemma get_meta_rec_put_same : forall st g mr, get_meta_rec (put_meta g mr st) g = mr.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
Lemma get_meta_rec_put_other : forall st g mr q, q <> g -> get_meta_rec (put_meta g mr st) q = get_meta_rec st q.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_neq by assumption. reflexivity. Qed.

Lemma pw_put_meta : forall st g mr p, pw (put_meta g mr st) p = pw st p. Proof. reflexivity. Qed.
Lemma conc_put_meta : forall st g mr p, conc (put_meta g mr st) p = conc st p. Proof. reflexivity. Qed.
Lemma ctx_put_meta : forall st g mr, ctx (put_meta g mr st) = ctx st. Proof. reflexivity. Qed.
Lemma meta_slot_put_meta : forall st g mr q, meta_slot st q -> meta_slot (put_meta g mr st) q.
Proof. intros. eapply meta_slot_same_areas; [|eassumption]. reflexivity. Qed.
Lemma meta_cells_put_meta : forall st g mr r, meta_cells (put_meta g mr st) r = meta_cells st r. Proof. reflexivity. Qed.

Definition fm_link (st0 : mstate) (g head : aptr) : mstate :=
  let hprev := m_prev (get_meta_rec st0 head) in
  let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
  let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
  upd_meta head (m_set_prev (Some g)) st2.

Definition fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
  set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).

Definition queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
  match get_head st0 h with
  | Some head => fm_link st0 g head
  | None => fm_single st0 h g
  end.

Lemma queue_eq : forall R h g st0 (k : mstate -> M R) bail,
  m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
  queue h g st0 k bail = k (queue_st h g st0).
Proof.
  intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
  unfold queue_st, fm_link, fm_single. destruct (get_head st0 h); reflexivity.
Qed.

Definition fm_st (st : mstate) (g : aptr) : mstate := queue_st LFree g (put_meta g meta0 st).

Lemma free_meta_eq : forall R st g (k : mstate -> M R) bail, free_meta g st k bail = k (fm_st st g).
Proof.
  intros. unfold free_meta, fm_st. apply queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.

Lemma meta_slot_bounds : forall st m g, mrep st m -> meta_slot st g ->
  0 < conc st g /\ conc st g + 40 <= alloc_ceiling /\ (conc st g + 40 <= 0x10000 \/ 0x1b000 <= conc st g) /\ conc st g mod 4 = 0
  /\ conc st g mod 4096 >= 24.
Proof.
  intros st m g MR (a & ar & k & Ha & Hk & Eg). pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
  destruct (area_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2].
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose_ceil; unfold AREA_HDR, META_SIZE, NSLOTS in *. pose proof (round_up_pg_ge (r_len ra)).
  rewrite HG, Ca. repeat split; first [lia | Z.div_mod_to_equations; nia].
Qed.

Lemma group_bounds : forall st m b gh, mrep st m -> (s_groups st) !! b = Some gh ->
  0 <= conc st b /\ conc st b + 16 <= alloc_ceiling /\ (conc st b + 16 <= 0x10000 \/ 0x1b000 <= conc st b) /\ conc st b mod 16 = 0.
Proof.
  intros st m b gh MR Hb. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
  destruct (group_conc st b gh WF Hb) as (r & Hr & Cb & Kr & Sb0 & Sb1 & SbA & RB0 & RBC).
  destruct (WR (fst b) r Hr) as (_ & RAL & _ & _ & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2].
  pose_ceil. pose proof (round_up_pg_ge (r_len r)).
  rewrite Cb. repeat split; try lia. all: apply base16_mod; assumption.
Qed.

Definition free_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  (lo <= a < sp
   \/ CTX <= a < CTX + 928
   \/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r))
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 8)
  \/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
        /\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

Lemma free_fp_stack st lo sp a : lo <= a < sp -> free_fp st lo sp a.
Proof. intros; left; left; assumption. Qed.
Lemma free_fp_ctx st lo sp a : CTX <= a < CTX + 928 -> free_fp st lo sp a.
Proof. intros; left; right; left; assumption. Qed.
Lemma free_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
  lr_lo r <= a < r_base r + round_up_pg (r_len r) -> free_fp st lo sp a.
Proof. intros; left; right; right. exists rid, r. auto. Qed.
Lemma free_fp_group st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 8 -> free_fp st lo sp a.
Proof. intros; right; left. exists b, gh. auto. Qed.

Lemma free_fp_meta : forall st m lo sp q a, mrep st m -> meta_slot st q ->
  conc st q <= a < conc st q + 40 -> free_fp st lo sp a.
Proof.
  intros st m lo sp q a MR (ar & arr & k & Har & Hk & Eq) Ha. pose proof MR as (WF & _).
  destruct (area_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose proof (area_lr_lo st ar arr ra WF Har Hra).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  eapply free_fp_region; [exact Hra | exact NK | lia].
Qed.

Lemma free_fp_mono : forall st st' lo sp sp' a,
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st ->
  (forall b gh, (s_groups st') !! b = Some gh -> (s_groups st) !! b = Some gh) ->
  sp' <= sp ->
  free_fp st' lo sp' a -> free_fp st lo sp a.
Proof.
  intros st st' lo sp sp' a ER ES HG HS H.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H |].
    right; right. destruct H as (rid & r & H1 & H2 & H3). exists rid, r. rewrite <- ER. auto.
  - right; left. destruct H as (b & gh & H1 & H2). exists b, gh. rewrite <- Hconc. auto.
  - right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). exists rid, r, v.
    rewrite <- ER. unfold get_shadow. rewrite <- ES. auto.
Qed.

Lemma outside_of_cover : forall (C : Z -> Prop) W a,
  (forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) -> ~ C a -> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a HW HC; cbn; [exact I|]. split.
  - intros Ha. apply HC. apply (HW lo hi); [left; reflexivity| exact Ha].
  - apply IH; [|exact HC]. intros lo' hi' Hin x Hx. apply (HW lo' hi'); [right; exact Hin|exact Hx].
Qed.

Lemma pres_except_of_munch' : forall C W m m',
  munch W m m' -> wmono asegs m m' ->
  (forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) ->
  pres_except C m m'.
Proof.
  intros C W m m' MU WM HW. eapply pres_except_of_munch; [exact MU | exact WM |].
  intros a _ HC. eapply outside_of_cover; eauto.
Qed.

Fixpoint ivs_covered (C : Z -> Prop) (W : list (Z * Z)) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (forall x, lo <= x < hi -> C x) /\ ivs_covered C W'
  end.

Lemma ivs_covered_In : forall C W, ivs_covered C W -> forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros H lo' hi' Hin x Hx; [destruct Hin|].
  destruct H as [H1 H2]. destruct Hin as [E|Hin]; [inversion E; subst; auto| eapply IH; eauto].
Qed.

Lemma pres_except_of_munch_cov : forall C W m m',
  munch W m m' -> wmono asegs m m' -> ivs_covered C W -> pres_except C m m'.
Proof. intros. eapply pres_except_of_munch'; eauto. apply ivs_covered_In. assumption. Qed.

Lemma munch_grow2 : forall f iv W m m', munch (f :: W) m m' -> munch (f :: iv :: W) m m'.
Proof.
  intros [flo fhi] [lo hi] W m m' MU. eapply munch_weaken; [|exact MU].
  intros x Hx. cbn in Hx |- *. tauto.
Qed.

Ltac munch_grow MU iv :=
  lazymatch type of MU with
  | munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
  end.

Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MR : mrep st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.

Hypothesis WIN : forall lo hi, In (lo, hi) W -> CTX <= lo /\ hi <= CTX + 928.

Lemma ctxW_avoid : forall A n, (A + n <= CTX \/ CTX + 928 <= A) \/ (forall lo hi, In (lo, hi) W -> A + n <= lo \/ hi <= A) ->
  0 <= A -> A + n <= 2^64 -> agree_on m m' A n.
Proof.
  intros A n HD HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
  clear -WIN HD Ha. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
  - destruct HD as [HD|HD].
    + pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
    + pose proof (HD lo hi ltac:(left; reflexivity)). lia.
  - apply IH.
    + intros lo' hi' Hin. apply WIN. right; exact Hin.
    + destruct HD as [HD|HD]; [left; exact HD| right]. intros lo' hi' Hin. apply HD. right; exact Hin.
Qed.

Lemma mrep_ctx_frameW :
  (rw_cells asegs m' CTX (ctx_head_cells st') \/ (ctx_head_cells st' = ctx_head_cells st /\ forall lo hi, In (lo, hi) W -> CTX + 80 <= lo \/ hi <= CTX)) ->
  (u64arr asegs m' (CTX + 80) (actives st') \/ (actives st' = actives st /\ forall lo hi, In (lo, hi) W -> CTX + 464 <= lo \/ hi <= CTX + 80)) ->
  (u64arr asegs m' (CTX + 464) (usages st') \/ (usages st' = usages st /\ forall lo hi, In (lo, hi) W -> CTX + 848 <= lo \/ hi <= CTX + 464)) ->
  (u8arr asegs m' (CTX + 848) (unmap_seqs st') \/ (unmap_seqs st' = unmap_seqs st /\ forall lo hi, In (lo, hi) W -> CTX + 880 <= lo \/ hi <= CTX + 848)) ->
  (u8arr asegs m' (CTX + 880) (bouncess st') \/ (bouncess st' = bouncess st /\ forall lo hi, In (lo, hi) W -> CTX + 912 <= lo \/ hi <= CTX + 880)) ->
  (rw_cells asegs m' (CTX + 912) (ctx_tail_cells st') \/ (ctx_tail_cells st' = ctx_tail_cells st /\ forall lo hi, In (lo, hi) W -> CTX + 928 <= lo \/ hi <= CTX + 912)) ->
  mrep st' m'.
Proof.
  intros H1 H2 H3 H4 H5 H6.
  pose proof MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & GL & AR & GR & SH).
  assert (CX' : mrep_ctx st' m').
  { unfold mrep_ctx. split; [|split; [|split; [|split; [|split]]]].
    - destruct H1 as [H|[-> HD]]; [exact H|]. eapply rw_cells_agree; eauto. apply ctxW_avoid; [right| unfold CTX; lia| unfold CTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H2 as [H|[-> HD]]; [exact H|]. eapply u64arr_agree; eauto. rewrite actives_length. apply ctxW_avoid; [right| unfold CTX; lia| unfold CTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H3 as [H|[-> HD]]; [exact H|]. eapply u64arr_agree; eauto. rewrite usages_length. apply ctxW_avoid; [right| unfold CTX; lia| unfold CTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H4 as [H|[-> HD]]; [exact H|]. eapply u8arr_agree; eauto. rewrite unmap_seqs_length. apply ctxW_avoid; [right| unfold CTX; lia| unfold CTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H5 as [H|[-> HD]]; [exact H|]. eapply u8arr_agree; eauto. rewrite bouncess_length. apply ctxW_avoid; [right| unfold CTX; lia| unfold CTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H6 as [H|[-> HD]]; [exact H|]. eapply rw_cells_agree; eauto. apply ctxW_avoid; [right| unfold CTX; lia| unfold CTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia. }
  eapply mrep_ctx_frame'; [exact MR | | exact WM | exact ER | exact EM | exact EA | exact EG | exact ES | exact ERs | exact CX'].
  eapply munch_weaken; [|exact MU]. intros x Hx. cbn in Hx. destruct Hx as [Hx _].
  clear -WIN Hx. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
  - pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
  - apply IH. intros lo' hi' Hin. apply WIN. right; exact Hin.
Qed.
End CTXFRAME.

Lemma amo_aligned_intro : forall a : Z, 0 <= a < 2^64 -> a mod 4 = 0 -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.

Ltac amo_align AMO :=
  try (rewrite AMO; cbv beta iota delta [negb]);
  try (rewrite Z.eqb_refl; cbv iota).

Ltac amo_step AMO :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; fix_lit_store; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS ?R _ ?pc _ ?rv _ _) => idtac "=== PC" pc "RV" rv end.

Lemma sextw_sxv0 v : Z_to_bv 64 (bv_swrap 32 (sxv v + 0)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv. Qed.
Lemma sextw_sxv1 v : Z_to_bv 64 (bv_swrap 32 (sxv v)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv'. Qed.

Lemma le4_lor_sxv : forall f s, 0 <= f < 2^32 -> 0 <= s < 2^32 ->
  le4 (Z_to_bv 64 (Z.lor (sxv s) (sxv f))) = le4 (wz (Z.lor f s)).
Proof.
  intros f s Hf Hs. apply le4_congr. pose proof (lor_range64 (sxv s) (sxv f) (sxv_range _) (sxv_range _)).
  pose proof (Z_lor_range f s ltac:(lia) ltac:(lia)).
  rewrite unsigned_lit by lia. rewrite wz_unsigned.
  2:{ split; [lia|]. apply (Z.lt_le_trans _ (2^32)); [|lia]. apply Z_bounded_by_bits; [lia|lia|].
      intros k Hk. rewrite Z.lor_spec, (Z_testbit_high 32 f k), (Z_testbit_high 32 s k) by lia. reflexivity. }
  rewrite lor_sxv_mod32 by lia. rewrite Z.lor_comm. symmetry. apply Z.mod_small.
  split; [lia|]. apply Z_bounded_by_bits; [lia|lia|].
  intros k Hk. rewrite Z.lor_spec, (Z_testbit_high 32 f k), (Z_testbit_high 32 s k) by lia. reflexivity.
Qed.

Definition ntf_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (a0v a1v : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1v a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ pres_except (free_fp st lo (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ mrep st' m'.

Definition ntf_mid_post (pc : Z) (R : list cell -> word -> Prop  ) : Prop := True.

End CEIL.

Ltac munch_grow MU iv :=
  lazymatch type of MU with
  | munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
  end.
Ltac amo_align AMO :=
  try (rewrite AMO; cbv beta iota delta [negb]);
  try (rewrite Z.eqb_refl; cbv iota).
Ltac amo_step AMO :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; fix_lit_store; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS ?R _ ?pc _ ?rv _ _) => idtac "=== PC" pc "RV" rv end.
