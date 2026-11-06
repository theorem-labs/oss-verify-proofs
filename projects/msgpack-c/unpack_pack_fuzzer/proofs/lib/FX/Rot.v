(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia FunctionalExtensionality.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan EntM ValProofs MemProofs.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan EntM.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module Rot.
Section WithSegs.
Variable segs : list Segment.

Definition rot_ok (rot : rotab) : Prop :=
  IMap.bst rot /\
  forall g wd wr, IMap.find g rot = Some (wd, wr) ->
    8 * to_Z g + 8 < Mem.two62Z
    /\ (exists bs, Mem.img_bytes segs (8 * to_Z g) 8 = Some bs /\ wd = Mem.bytes_to_w64 bs)
    /\ (wr = true -> Mem.abs_writable segs (8 * to_Z g) 8 = true).

Lemma img_bytes_skip : forall n1 n2 a bs, Mem.img_bytes segs a (n1 + n2) = Some bs ->
  Mem.img_bytes segs (a + Z.of_nat n1) n2 = Some (skipn n1 bs).
Proof.
  induction n1 as [|n1 IH]; intros n2 a bs H.
  - rewrite Z.add_0_r. exact H.
  - cbn [Mem.img_bytes Nat.add] in H. destruct (memory_read segs (Z_to_bv 64 a) 1) as [[|b ?]|]; try discriminate H.
    destruct (Mem.img_bytes segs (a + 1) (n1 + n2)) as [bs'|] eqn:E; [|discriminate H]. injection H as <-.
    cbn [skipn]. replace (a + Z.of_nat (S n1)) with (a + 1 + Z.of_nat n1) by lia. apply IH. exact E.
Qed.
Lemma img_bytes_first : forall n a bs m, Mem.img_bytes segs a n = Some bs -> (m <= n)%nat ->
  Mem.img_bytes segs a m = Some (firstn m bs).
Proof.
  induction n as [|n IH]; intros a bs m H Hm.
  - replace m with 0%nat by lia. cbn in H |- *. injection H as <-. reflexivity.
  - cbn [Mem.img_bytes] in H. destruct (memory_read segs (Z_to_bv 64 a) 1) as [[|b ?]|] eqn:M; try discriminate H.
    destruct (Mem.img_bytes segs (a + 1) n) as [bs'|] eqn:E; [|discriminate H]. injection H as <-.
    destruct m as [|m]; [reflexivity|]. cbn [Mem.img_bytes firstn]. rewrite M. rewrite (IH (a + 1) bs' m E) by lia. reflexivity.
Qed.
Lemma abs_writable_bytes_sub : forall n a idx m, Mem.abs_writable_bytes segs a n = true -> (idx + m <= n)%nat ->
  Mem.abs_writable_bytes segs (a + Z.of_nat idx) m = true.
Proof.
  induction n as [|n IH]; intros a idx m H Hle.
  - replace m with 0%nat by lia. reflexivity.
  - cbn [Mem.abs_writable_bytes] in H. apply andb_prop in H as [H1 H2].
    destruct idx as [|idx].
    + rewrite Z.add_0_r. destruct m as [|m]; [reflexivity|]. cbn [Mem.abs_writable_bytes]. rewrite H1. cbn [andb].
      replace (a + 1) with (a + Z.of_nat 0 + 1) in H2 by lia.
      pose proof (IH (a + 1) 0%nat m) as X. rewrite Z.add_0_r in X. apply X; [| lia].
      replace (a + Z.of_nat 0 + 1) with (a + 1) in H2 by lia. exact H2.
    + replace (a + Z.of_nat (S idx)) with (a + 1 + Z.of_nat idx) by lia. apply (IH (a + 1) idx m H2). lia.
Qed.

Lemma rot_find_sound : forall rot o w wd wr, rot_ok rot -> 0 <= to_Z w ->
  Mem.rot_find rot o w = Some (wd, wr) ->
  to_Z o < 2 ^ 62 /\ to_Z o + to_Z w < Mem.two62Z /\ to_Z (gidx o) + to_Z w <= 8 /\
  exists bs8, Mem.img_bytes segs (8 * to_Z (granule o)) 8 = Some bs8 /\ wd = Mem.bytes_to_w64 bs8
    /\ to_Z o = 8 * to_Z (granule o) + to_Z (gidx o)
    /\ Mem.img_bytes segs (to_Z o) (Z.to_nat (to_Z w)) = Some (firstn (Z.to_nat (to_Z w)) (skipn (Z.to_nat (to_Z (gidx o))) bs8))
    /\ (wr = true -> Mem.abs_writable segs (8 * to_Z (granule o)) 8 = true).
Proof.
  intros rot o w wd wr [B OK] Hw H. unfold Mem.rot_find in H.
  destruct (PrimInt63.ltb o bit62i) eqn:L; [|discriminate H].
  destruct (PrimInt63.leb w 8%uint63) eqn:W8; [|discriminate H]. apply Uint63.leb_spec in W8. change (to_Z 8%uint63) with 8 in W8.
  destruct (PrimInt63.leb (PrimInt63.add (gidx o) w) 8%uint63) eqn:G; [|discriminate H]. cbn [andb] in H.
  destruct (OK _ _ _ H) as (R & (bs & IB & ->) & WR).
  apply Uint63.ltb_spec in L. change (to_Z bit62i) with (2 ^ 62) in L.
  destruct (MemP.gidx_ok o) as [Eg Rg].
  apply Uint63.leb_spec in G. rewrite MemP.add_small in G by (unfold two63; lia). change (to_Z 8%uint63) with 8 in G.
  assert (KO : keyZ o = to_Z o) by (unfold keyZ, Mem.keyZ; destruct (Uint63.ltbP o bit62i); [reflexivity| change (to_Z bit62i) with (2^62) in *; lia]).
  destruct (MemP.granule_gidx o ltac:(rewrite MemP.half63; apply MemP.keyZ_range)) as [GG _].
  rewrite KO in GG. rewrite MemP.two62Z_eq in R.
  assert (KG : keyZ (granule o) = to_Z (granule o)) by (destruct (MemP.keyZ_cases (granule o)) as [[_ KG]|[X _]]; [exact KG| exfalso; lia]).
  rewrite KG in GG.
  split; [lia|]. split; [rewrite MemP.two62Z_eq; lia|]. split; [exact G|].
  exists bs. split; [exact IB|]. split; [reflexivity|]. split; [exact GG|]. split; [| exact WR].
  pose proof (img_bytes_skip (Z.to_nat (to_Z (gidx o))) (8 - Z.to_nat (to_Z (gidx o))) (8 * to_Z (granule o)) bs) as SK.
  replace (Z.to_nat (to_Z (gidx o)) + (8 - Z.to_nat (to_Z (gidx o))))%nat with 8%nat in SK by lia.
  specialize (SK IB). rewrite Z2Nat.id in SK by lia. rewrite <- GG in SK.
  rewrite (img_bytes_first _ _ _ (Z.to_nat (to_Z w)) SK) by lia. reflexivity.
Qed.

Lemma wext_bytes : forall bs idx w, length bs = 8%nat -> 0 <= to_Z idx -> 1 <= to_Z w -> to_Z idx + to_Z w <= 8 ->
  wext false idx w (Mem.bytes_to_w64 bs) = Mem.bytes_to_w64 (firstn (Z.to_nat (to_Z w)) (skipn (Z.to_nat (to_Z idx)) bs)).
Proof.
  intros bs idx w Hl Hi Hw Hle. apply w2Z_inj.
  rewrite wext_ok by lia. rewrite !MemP.bytes_to_w64_ok by (rewrite ?length_firstn, ?length_skipn; lia).
  unfold ext_Z. cbv beta iota zeta. apply Z.bits_inj'. intros m Hm.
  destruct (Z_lt_le_dec m (8 * to_Z w)).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia.
    rewrite ValP.bytes_le_to_Z_firstn_tb by lia. rewrite Z2Nat.id by lia.
    replace (m <? 8 * to_Z w) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    rewrite ValP.bytes_le_to_Z_skipn_tb by lia. rewrite Z2Nat.id by lia. f_equal; lia.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite ValP.bytes_le_to_Z_firstn_tb by lia. rewrite Z2Nat.id by lia.
    replace (m <? 8 * to_Z w) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Section WithRot.
Variable rot : rotab.
Hypothesis ROK : rot_ok rot.

Lemma bg_value_r_feq : Mem.bg_value_r segs rot = Mem.bg_value segs.
Proof.
  extensionality k. extensionality r. extensionality o. extensionality w.
  unfold Mem.bg_value_r. destruct (rg_bg r) eqn:BG; try reflexivity.
  destruct (Mem.rot_lookup rot o w) as [wd'|] eqn:L; [|reflexivity].
  unfold Mem.rot_lookup in L. destruct (Mem.wok_b w) eqn:WOK; [|discriminate L].
  destruct (Mem.rot_find rot o w) as [[wd wr]|] eqn:F; [|discriminate L]. injection L as <-.
  assert (Hw : 1 <= to_Z w).
  { unfold Mem.wok_b in WOK. apply orb_prop in WOK. destruct WOK as [WOK|W8]; [apply orb_prop in WOK; destruct WOK as [WOK|W4]; [apply orb_prop in WOK; destruct WOK as [W1|W2]|]|];
    match goal with H : PrimInt63.eqb w ?c = true |- _ => apply Uint63.eqb_correct in H; subst w end;
    [change (to_Z 1%uint63) with 1| change (to_Z 2%uint63) with 2| change (to_Z 4%uint63) with 4| change (to_Z 8%uint63) with 8]; lia. }
  destruct (rot_find_sound rot o w wd wr ROK ltac:(lia) F) as (L1 & L2 & L3 & bs8 & IB8 & -> & GG & IB & _).
  unfold Mem.bg_value. rewrite BG. destruct (Uint63.ltbP o bit62i); [| change (to_Z bit62i) with (2^62) in *; lia].
  rewrite IB. f_equal. f_equal. destruct (MemP.img_bytes_spec segs _ _ _ IB8) as [Len _].
  pose proof (proj2 (MemP.gidx_ok o)). apply wext_bytes; [exact Len| lia| lia| lia].
Qed.

Lemma region_load1_r_feq : Mem.region_load1_r segs rot = Mem.region_load1 segs.
Proof.
  extensionality k. extensionality r. extensionality o. extensionality w. extensionality sx.
  unfold Mem.region_load1_r, Mem.region_load1. rewrite bg_value_r_feq. reflexivity.
Qed.

Lemma region_load_r_feq : Mem.region_load_r segs rot = Mem.region_load segs.
Proof.
  extensionality k. extensionality r. extensionality o. extensionality w. extensionality sx.
  unfold Mem.region_load_r, Mem.region_load. rewrite region_load1_r_feq. reflexivity.
Qed.

Lemma abs_readable_r_eq : forall o w, 0 <= to_Z w ->
  Mem.abs_readable_r segs rot o w = Mem.abs_readable segs (to_Z o) (to_Z w).
Proof.
  intros o w Hw. unfold Mem.abs_readable_r. destruct (Mem.rot_find rot o w) as [[wd wr]|] eqn:F; [|reflexivity].
  destruct (rot_find_sound rot o w wd wr ROK Hw F) as (L1 & L2 & L3 & bs8 & IB8 & _ & GG & IB & _).
  unfold Mem.abs_readable. rewrite IB. replace (to_Z o + to_Z w <? Mem.two62Z) with true by (symmetry; apply Z.ltb_lt; exact L2).
  reflexivity.
Qed.

Lemma abs_writable_r_eq : forall o w, 0 <= to_Z w ->
  Mem.abs_writable_r segs rot o w = Mem.abs_writable segs (to_Z o) (to_Z w).
Proof.
  intros o w Hw. unfold Mem.abs_writable_r. destruct (Mem.rot_find rot o w) as [[wd [|]]|] eqn:F; try reflexivity.
  destruct (rot_find_sound rot o w wd true ROK Hw F) as (L1 & L2 & L3 & bs8 & IB8 & _ & GG & IB & WR). specialize (WR eq_refl).
  symmetry. unfold Mem.abs_writable in WR |- *. apply andb_prop in WR as [W1 W2].
  apply andb_true_intro. split; [apply Z.ltb_lt; lia|].
  rewrite GG. rewrite <- (Z2Nat.id (to_Z (gidx o))) at 1 by (pose proof (proj2 (MemP.gidx_ok o)); lia).
  apply (abs_writable_bytes_sub 8); [exact W2| pose proof (proj2 (MemP.gidx_ok o)); lia].
Qed.

Lemma can_read_r_feq : can_read_r segs rot = can_read segs.
Proof.
  extensionality fs. extensionality priv. extensionality k. extensionality r. extensionality key. extensionality w.
  unfold can_read_r, can_read. destruct (PrimInt63.eqb k 0%uint63); [|reflexivity].
  pose proof (to_Z_bounded w). rewrite abs_readable_r_eq by lia. reflexivity.
Qed.

Lemma can_write_r_feq : can_write_r segs rot = can_write segs.
Proof.
  extensionality fs. extensionality priv. extensionality k. extensionality r. extensionality key. extensionality w.
  unfold can_write_r, can_write. rewrite can_read_r_feq. destruct (PrimInt63.eqb k 0%uint63); [|reflexivity].
  pose proof (to_Z_bounded w). rewrite abs_writable_r_eq by lia. reflexivity.
Qed.

Lemma do_load_r_feq : do_load_r segs rot = do_load segs.
Proof.
  extensionality st. extensionality a. extensionality w. extensionality sx.
  unfold do_load_r, do_load. rewrite can_read_r_feq, region_load_r_feq. reflexivity.
Qed.

Lemma do_store_r_feq : do_store_r segs rot = do_store segs.
Proof.
  extensionality st. extensionality a. extensionality w. extensionality v.
  unfold do_store_r, do_store. rewrite can_write_r_feq. reflexivity.
Qed.

Lemma exec_r_feq : exec_r segs rot = exec segs.
Proof.
  extensionality fi. extensionality st. unfold exec_r, exec. rewrite do_load_r_feq, do_store_r_feq. reflexivity.
Qed.

Lemma step_r_feq : step_r segs rot = step segs.
Proof. extensionality it. extensionality st. unfold step_r, step. rewrite exec_r_feq. reflexivity. Qed.

Lemma step1_r_feq : step1_r segs rot = step1 segs.
Proof. extensionality it. extensionality stops. extensionality st. unfold step1_r, step1. rewrite step_r_feq. reflexivity. Qed.

Lemma runP_r_feq : runP_r segs rot = runP segs.
Proof.
  extensionality p. extensionality it. extensionality stops. extensionality st. revert st.
  induction p as [q IH|q IH|]; intros st; cbn [runP_r runP]; rewrite ?step1_r_feq, ?IH; try reflexivity.
  all: destruct (runP segs q it stops st); rewrite ?IH, ?step1_r_feq; try reflexivity.
  all: destruct (runP segs q it stops _); rewrite ?step1_r_feq; reflexivity.
Qed.

Lemma run_r_feq : run_r segs rot = run segs.
Proof. extensionality it. extensionality stops. extensionality st. unfold run_r, run. rewrite runP_r_feq. reflexivity. Qed.

Lemma check_r_feq : check_r segs rot = check segs.
Proof.
  extensionality C. extensionality p. extensionality st.
  unfold check_r, check. rewrite run_r_feq. reflexivity.
Qed.

Lemma entails_m_feq : EntM.entails_m = entails.
Proof. extensionality st. extensionality T. extensionality sg. apply EntM.entails_m_eq. Qed.
Lemma check_rm_feq : EntM.check_rm segs rot = check segs.
Proof.
  extensionality C. extensionality p. extensionality st.
  unfold EntM.check_rm, check. rewrite run_r_feq, entails_m_feq. reflexivity.
Qed.

Lemma check_r_eq : forall C p st, check segs C p st = EntM.check_rm segs rot C p st.
Proof. intros. rewrite check_rm_feq. reflexivity. Qed.
End WithRot.

Lemma build_rot_ok : forall gs acc, rot_ok acc -> rot_ok (Mem.build_rot segs gs acc).
Proof.
  induction gs as [|g gs IH]; intros acc OK; cbn [Mem.build_rot]; [exact OK|].
  apply IH. destruct (Mem.img_bytes segs (8 * to_Z g) 8) as [bs|] eqn:IB; [|exact OK].
  destruct (Z.ltb_spec (8 * to_Z g + 8) Mem.two62Z); [|exact OK].
  destruct OK as [B OK]. split; [apply IMap.bst_add; exact B|].
  intros g' bs' wr' F. destruct (Uint63.eqb g' g) eqn:E.
  - apply Uint63.eqb_correct in E. subst g'. rewrite IMap.find_add_same in F by exact B. injection F as <- <-.
    split; [exact H|]. split; [exists bs; split; [exact IB| reflexivity]|]. intros W. exact W.
  - apply Uint63.eqb_false_spec in E. rewrite IMap.find_add_other in F; [| exact B| congruence]. exact (OK g' bs' wr' F).
Qed.

Lemma rot_ok_empty : rot_ok IMap.empty.
Proof. split; [apply IMap.bst_empty|]. intros g bs wr F. rewrite IMap.find_empty in F. discriminate F. Qed.

Lemma build_rot_ok_of_eq : forall gs rot, Mem.build_rot segs gs IMap.empty = rot -> rot_ok rot.
Proof. intros gs rot <-. apply build_rot_ok. apply rot_ok_empty. Qed.

End WithSegs.
End Rot.
