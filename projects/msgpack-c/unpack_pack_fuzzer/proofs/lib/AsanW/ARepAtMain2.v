(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase AProto ALayout ARep ABytes ARepQ AQConst ASec AExh AEmbRep AHeapP ADepot_iface ADepot AFake_iface AInstance AInstanceU AInstanceU2 APristLaw ABssZero ARepAtMain. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainExport MainFactsAsan MainEntry.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainExport.
Module MF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainFactsAsan.
Module MA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntry.

Definition ov0 : annOV := {| ann_ov := fun _ => None; ann_ovs := fun _ => None |}.

Section AtMain2.
Context {rc : runConstT}.
Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
Hypothesis HV : forall n, 0 <= V n < 2 ^ 64.
Hypothesis HMF : Forall (ME.mfact_ok asegs V m) MF.asan_mem_facts.
Hypothesis HMFw : Forall (ME.mfact_ok asegs V m) (MA.asan_mem_facts_w w).
Hypothesis HPF : Forall (ME.pfact_ok V) MF.asan_pure_facts.
Hypothesis MINV : mem_inv asegs m.
Hypothesis HUSP : usp_pin V.
Hypothesis HSH0 : MA.ashadow0 V m.
Hypothesis HU : univ_ok U.

Local Notation L := (L0 V w U).
Local Notation sta := (st0 V w U).
Local Existing Instance ov0.

Local Notation HF := (hf V m HMF).
Local Notation HP := (hp V HPF).
Tactic Notation "hfact" constr(F) ident(H) := pose proof (HF F ltac:(vm_compute; reflexivity)) as H; cbn [ME.mfact_ok ME.zv ME.cellw] in H.
Tactic Notation "hpf" constr(k) ident(H) := pose proof (HP k _ eq_refl) as H; cbn [ME.pfact_ok ME.zv] in H.
Ltac hcell A W X :=
  let H := fresh "HC" in
  pose proof (HF (ME.MCell (ME.ZLit A) W (ME.ZLit X)) ltac:(vm_compute; reflexivity)) as H;
  cbn [ME.mfact_ok ME.zv ME.cellw] in H.
Local Notation RIZ := (ri_zrun V w U m HMF).
Local Notation THZ := (thr_zrun V w U m HMF).
Local Notation ALO := (alayout_ok_main V w U HV HPF HUSP HU).

Lemma zrun0 : forall A, 0 <= A <= 2 ^ 64 -> zrun m A 0.
Proof. intros A HA. split; [intros i Hi; lia|]. split; [lia|]. split; [lia|]. intros i Hi. lia. Qed.

Lemma shlen_0 : shlen 0 = 0. Proof. reflexivity. Qed.

Lemma aregion_info_eq : forall c, aregion_info L c = al_space_beg L + K_SPACE_SIZE + c * 128.
Proof. intros c. reflexivity. Qed.

Lemma space_facts : 0x10007fff8000 <= al_space_beg L /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP /\ al_space_beg L mod K_ALIGN = 0
  /\ 0 <= al_space_beg L < 2^47.
Proof. exact (alayout_space L ALO). Qed.

Lemma aregion_cells_main : forall c, 1 <= c < K_NUM_CLASSES -> aregion_cells L sta m c.
Proof.
  intros c Hc. unfold aregion_cells. rewrite get_cls_st0. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user aclass0].
  rewrite aregion_info_eq. unfold K_NUM_CLASSES in Hc. pose proof RIZ as Z0.
  split. { apply zrun_cells; [cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity|]. cbn [cells_size csize Nat.add]. apply (zrun_sub _ _ _ _ _ Z0); lia. }
  split. { apply zrun_cells; [cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity|]. cbn [cells_size csize Nat.add]. apply (zrun_sub _ _ _ _ _ Z0); lia. }
  split. { apply zrun_junk; [| lia]. apply (zrun_sub _ _ _ _ _ Z0); lia. }
  split.
  { unfold aflag_cell. rewrite aregion_info_eq. destruct (Z.eqb_spec c K_BATCH_CLASS) as [E|NE].
    - apply zrun_cells; [cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity|]. cbn [cells_size csize Nat.add]. apply (zrun_sub _ _ _ _ _ Z0); lia.
    - apply zrun_junk; [| lia]. apply (zrun_sub _ _ _ _ _ Z0); lia. }
  apply zrun_junk; [| lia]. apply (zrun_sub _ _ _ _ _ Z0); lia.
Qed.

Lemma afreearray_main : forall c, 1 <= c < K_NUM_CLASSES -> afreearray L sta X0 m c.
Proof.
  intros c Hc. unfold afreearray. rewrite get_cls_st0. cbn [c_num_freed c_mapped_free_array aclass0 x_cls X0 xc_free xc0 map].
  pose proof space_facts as (S1 & S2 & _ & S4). unfold K_NUM_CLASSES in Hc. unfold K_SPACE_SIZE, K_SPACE_EXTRA in S2. pose proof atop_range as AR.
  assert (B : 0 <= afreearr L c /\ afreearr L c + 0 <= 2 ^ 64).
  { unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. nia. }
  split. { change (@nil word) with (repeat (Z_to_bv 64 0) 0). apply zrun_u32arr. apply zrun0. lia. }
  split. { replace (afreearr L c + 4 * 0) with (afreearr L c) by lia. replace (0 - 4 * 0) with 0 by lia. apply zrun_junk; [apply zrun0; lia| lia]. }
  rewrite shlen_0. apply zrun_junk; [| lia]. apply zrun0. rewrite shad_div. unfold ASHOFF. clear -B. Z.div_mod_to_equations. lia.
Qed.

Lemma aslots_main : forall c, 1 <= c < K_NUM_CLASSES -> aslots L sta X0 m c.
Proof.
  intros c Hc. unfold aslots. rewrite ndist_st0, get_cls_st0. cbn [c_allocated_user c_mapped_user aclass0].
  split; [intros k Hk; lia|].
  pose proof space_facts as (S1 & S2 & _ & S4). unfold K_NUM_CLASSES in Hc. unfold K_SPACE_SIZE, K_SPACE_EXTRA in S2. pose proof atop_range as AR.
  replace (0 - 0) with 0 by lia. apply zrun_junk; [| lia]. apply zrun0. unfold aregion, K_REGION. nia.
Qed.

Lemma aslot_shadow_main : forall c, 1 <= c < K_NUM_CLASSES -> aslot_shadow L sta X0 m c.
Proof.
  intros c Hc. unfold aslot_shadow. rewrite ndist_st0, get_cls_st0. cbn [c_allocated_user c_mapped_user aclass0].
  split; [intros k Hk; lia|].
  pose proof space_facts as (S1 & S2 & _ & S4). unfold K_NUM_CLASSES in Hc. unfold K_SPACE_SIZE, K_SPACE_EXTRA in S2. pose proof atop_range as AR.
  replace (0 - 0) with 0 by lia. rewrite shlen_0. unfold fill_at. cbn [Z.to_nat repeat]. apply rw_cells_nil0.
  assert (B : 0 <= aregion L c + 0 <= 2 ^ 64) by (unfold aregion, K_REGION; nia).
  rewrite shad_div. unfold ASHOFF. clear -B. Z.div_mod_to_equations. lia.
Qed.

Lemma res_clear_vis : forall bn, In bn MF.asan_vis_app ->
  let B := ME.zv V (fst bn) in let N := ME.zv V (snd bn) in
  B + N <= al_res L + 4096 \/ al_space_beg L + K_SPACE_SIZE <= B.
Proof.
  intros bn Hin. pose proof (ao_space L ALO) as SP. pose proof (ao_res_hi L ALO) as RH. revert SP RH. rewrite al_res_eq, al_space_beg_eq. intros SP RH.
  unfold K_SPACE_SIZE. change (2 ^ 37) with 137438953472.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 10%nat) as B10. pose proof (HV 6%nat) as B6.
  unfold MF.asan_vis_app in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [fst snd ME.zv].
  - hpf 90%nat D. lia.
  - hpf 89%nat D. lia.
  - hpf 88%nat D. lia.
  - hpf 87%nat D. lia.
  - hpf 85%nat D. lia.
  - hpf 84%nat D. lia.
  - hpf 83%nat D. lia.
  - hpf 82%nat D. lia.
  - right. lia.
  - hpf 67%nat D. lia.
  - hpf 177%nat D. lia.
  - left. lia.
  - hpf 79%nat D. lia.
Qed.

Lemma prim_shadow_clear : forall a, shad (al_res L + 4096) <= a < shad (al_space_beg L + K_SPACE_SIZE) ->
  MA.ashadow a /\ ~ MA.ashadow_vis V a.
Proof.
  intros a Ha. pose proof (ao_space L ALO) as SP. pose proof (ao_res_hi L ALO) as RH. pose proof space_facts as (S1 & S2 & _ & S4).
  pose proof atop_range as AR. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. rewrite !shad_div in Ha. unfold ASHOFF in Ha.
  split.
  - unfold MA.ashadow. right. clear -Ha SP RH S2 AR. Z.div_mod_to_equations. lia.
  - intros (bn & Hin & R). pose proof (res_clear_vis bn Hin) as D. cbn zeta in D. unfold MA.ASHOFF in R. unfold K_SPACE_SIZE in D.
    set (B := ME.zv V (fst bn)) in *. set (N := ME.zv V (snd bn)) in *. clearbody B N. clear -Ha SP D R.
    Z.div_mod_to_equations. lia.
Qed.

Lemma prim_azero : forall A n, al_res L + 4096 <= A -> A + n <= al_space_beg L + K_SPACE_SIZE -> A mod 8 = 0 -> 8 <= n ->
  azero m (shad A) (shlen n).
Proof.
  intros A n HA Hn A8 N8. pose proof (ao_space L ALO) as SP.
  assert (SL : 0 < shlen n /\ shad A + shlen n <= shad (al_space_beg L + K_SPACE_SIZE) /\ shad (al_res L + 4096) <= shad A).
  { unfold shlen. rewrite !shad_div, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear -HA Hn A8 N8. Z.div_mod_to_equations. lia. }
  destruct SL as (SL1 & SL2 & SL3).
  destruct (MA.ashadow0_range V m (shad A) (shlen n) HSH0 SL1) as (Z1 & W1 & _).
  { intros a Ha. apply prim_shadow_clear. lia. }
  split; [exact Z1| exact W1].
Qed.

Lemma ashadow_avail_main : forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L sta m c.
Proof.
  intros c Hc. unfold ashadow_avail. rewrite get_cls_st0. cbn [c_mapped_user c_mapped_free_array aclass0].
  pose proof (ao_space L ALO) as SP. pose proof space_facts as (S1 & S2 & S3 & S4). unfold K_NUM_CLASSES in Hc.
  unfold K_ALIGN in S3. rewrite !Z.add_0_r, !Z.sub_0_r.
  split.
  - apply prim_azero; unfold aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE in *; [nia| nia| | lia].
    change (2 ^ 32) with 4294967296. clear -S3. Z.div_mod_to_equations. lia.
  - apply prim_azero; unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, K_SPACE_SIZE in *; [nia| nia| | lia].
    change (2 ^ 32) with 4294967296. clear -S3. Z.div_mod_to_equations. lia.
Qed.

Lemma aprim0_main : aprim0 L m.
Proof.
  unfold aprim0. pose proof (ao_space L ALO) as SP. pose proof space_facts as (S1 & S2 & S3 & S4). unfold K_ALIGN in S3.
  apply prim_azero; unfold K_REGION, K_SPACE_SIZE in *; [lia| lia| | lia].
  clear -S3. Z.div_mod_to_equations. lia.
Qed.

Lemma awf_main : awf L sta X0.
Proof.
  unfold awf. pose proof space_facts as (S1 & S2 & S3 & S4).
  split; [reflexivity|]. split; [reflexivity|]. split; [exact S3|]. split; [exact S1|]. split; [exact S2|].
  split.
  { intros c Hc. rewrite get_cls_st0, max_count_st0, ndist_st0.
    cbn [c_allocated_user c_mapped_user c_num_freed c_mapped_free_array c_count aclass0 x_cls X0 xc_free xc_cache xc0 length Z.of_nat app busy_slots x_busy List.filter map].
    unfold K_FREEARR_OFF, K_FREEARR_MAX, K_USER_MAP, K_FREEARR_MAP.
    repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity.
    - constructor.
    - intros k [].  }
  split. { intros c _. apply get_cls_st0. }
  split. { intros b []. }
  split. { intros p c n H. cbn [st0 ainit a_live] in H. rewrite lookup_empty in H. discriminate H. }
  split. { intros p ch H. cbn [st0 ainit a_live] in H. rewrite lookup_empty in H. discriminate H. }
  intros b1 b2 [].
Qed.

Lemma ablocks_main : ablocks L sta X0 [].
Proof.
  split; [intros p A n []|]. split; [intros cls A n []|]. split; constructor.
Qed.

Lemma hq_max : rw_cells asegs m 878448 [C8 (Z_to_bv 64 268435456); C8 (Z_to_bv 64 241591905); C8 (Z_to_bv 64 1048576)].
Proof.
  hcell 878448 8%nat 268435456. rename HC into K0.
  hcell 878456 8%nat 241591905. rename HC into K1.
  hcell 878464 8%nat 1048576. rename HC into K2.
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K2.
Qed.

Lemma hq_mutex : rw_cells asegs m 878536 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  hcell 878536 1%nat 0. rename HC into K0.
  hcell 878537 1%nat 0. rename HC into K1.
  assert (K2 : rw_cells asegs m 878538 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast asegs m 878538 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 878538 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 878538 881272); [vm_compute; reflexivity| lia]. }
  assert (K3 : rw_cells asegs m 878539 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast asegs m 878539 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 878539 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 878538 881272); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K3.
Qed.

Lemma hq_gcache : rw_cells asegs m 878544 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells asegs m 878544 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 878544 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 878544 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 878538 881272); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells asegs m 878552 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 878552 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 878552 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 878538 881272); [vm_compute; reflexivity| lia]. }
  assert (K2 : rw_cells asegs m 878560 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 878560 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 878560 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 878538 881272); [vm_compute; reflexivity| lia]. }
  assert (K3 : rw_cells asegs m 878568 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 878568 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 878568 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 878538 881272); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K3.
Qed.

Lemma hq_iaflag : rw_cells asegs m 1480008 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  assert (K0 : rw_cells asegs m 1480008 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast asegs m 1480008 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 1480008 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 1424674 1480016); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells asegs m 1480009 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast asegs m 1480009 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 1480009 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 1424674 1480016); [vm_compute; reflexivity| lia]. }
  assert (K2 : rw_cells asegs m 1480010 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast asegs m 1480010 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 1480010 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 1424674 1480016); [vm_compute; reflexivity| lia]. }
  assert (K3 : rw_cells asegs m 1480011 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast asegs m 1480011 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 1480011 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 1424674 1480016); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K3.
Qed.

Lemma hs_sorted : rw_cells asegs m 877784 [C1 (Z_to_bv 8 0)].
Proof.
  assert (K0 : rw_cells asegs m 877784 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast asegs m 877784 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 877784 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 877760 878336); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma hx_toolname : rw_cells asegs m 865392 [C8 (Z_to_bv 64 139268)].
Proof.
  hcell 865392 8%nat 139268. rename HC into K0.
  exact K0.
Qed.

Lemma hx_cf64 : rw_cells asegs m 1488424 [C1 (Z_to_bv 8 0)].
Proof.
  hcell 1488424 8%nat 0. rename HC into HW0.
  apply (rw_cells_recast asegs m 1488424 _ [C1 (Z_to_bv 8 0); CB 7%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in HW0; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app asegs m _ [_] _)) in HW0 as [HW0 _].
  rename HW0 into K0.
  exact K0.
Qed.

Lemma hx_cb : rw_cells asegs m 1488848 [C8 (Z_to_bv 64 396776)].
Proof.
  hcell 1488848 8%nat 396776. rename HC into K0.
  exact K0.
Qed.

Lemma he_16 : rw_cells asegs m 889656 [C8 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells asegs m 889656 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 889656 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 889656 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 889640 891576); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma he_0 : rw_cells asegs m 889640 [C8 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells asegs m 889640 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 889640 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 889640 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 889640 891576); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma he_32 : rw_cells asegs m 889672 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells asegs m 889672 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 889672 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 889672 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 889640 891576); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells asegs m 889680 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 889680 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 889680 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 889640 891576); [vm_compute; reflexivity| lia]. }
  assert (K2 : rw_cells asegs m 889688 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast asegs m 889688 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 889688 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 889640 891576); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app asegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K2.
Qed.

Lemma hd_nuniq : rw_cells asegs m 6011288 [C4 (Z_to_bv 64 1)].
Proof.
  hcell 6011288 4%nat 1. rename HC into K0.
  exact K0.
Qed.

Lemma hf_tga : rw_cells asegs m 865112 [C8 (Z_to_bv 64 819348)].
Proof.
  assert (K0 : rw_cells asegs m 865112 [C8 (Z_to_bv 64 819348)]).
  { apply (rw_cells_recast asegs m 865112 [CB 8%nat [Z_to_bv 8 148; Z_to_bv 8 128; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 asegs m 865112 [Z_to_bv 8 148; Z_to_bv 8 128; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 65536 865384); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma hf_dtv : rw_cells asegs m 6343800 [C8 (Z_to_bv 64 6343840)].
Proof.
  hcell 6343800 8%nat 6343840. rename HC into K0.
  exact K0.
Qed.

Lemma hf_dtv1 : rw_cells asegs m 6343848 [C8 (Z_to_bv 64 6345856)].
Proof.
  hcell 6343848 8%nat 6345856. rename HC into K0.
  exact K0.
Qed.

Lemma hf_itga : rw_cells asegs m 1488497 [C1 (Z_to_bv 8 1)].
Proof.
  hcell 1488496 8%nat 256. rename HC into HW0.
  apply (rw_cells_recast asegs m 1488496 _ [CB 1%nat [Z_to_bv 8 0]; C1 (Z_to_bv 8 1); CB 6%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in HW0; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app asegs m _ [_] _)) in HW0 as [_ HW0]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in HW0.
  apply (proj1 (rw_cells_app asegs m _ [_] _)) in HW0 as [HW0 _].
  rename HW0 into K0.
  exact K0.
Qed.

Lemma hf_verb : rw_cells asegs m 1480024 [C4 (Z_to_bv 64 0)].
Proof.
  hcell 1480024 4%nat 0. rename HC into K0.
  exact K0.
Qed.

Lemma hs_stats : junk_at m 877792 32.
Proof.
  exists [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]. change (Z.to_nat 32) with 32%nat.
  apply (rw_cells_image0 asegs m 877792 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
  intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 877760 878336); [vm_compute; reflexivity| lia].
Qed.

Lemma hs_bylog : junk_at m 877824 512.
Proof.
  exists [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]. change (Z.to_nat 512) with 512%nat.
  apply (rw_cells_image0 asegs m 877824 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
  intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 877760 878336); [vm_compute; reflexivity| lia].
Qed.

Lemma hs_gstats : junk_at m 878360 16.
Proof.
  exists [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]. change (Z.to_nat 16) with 16%nat.
  apply (rw_cells_image0 asegs m 878360 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
  intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 878340 878448); [vm_compute; reflexivity| lia].
Qed.

Lemma wr_at_sub0 : forall A n A' n', wr_at asegs m A n -> A <= A' -> A' + n' <= A + n -> wr_at asegs m A' n'.
Proof.
  intros A n A' n' (Ha & Hn & H) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
Qed.
Lemma zrun_of : forall A n A0 n0, (forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) -> wr_at asegs m A0 n0 ->
  A0 <= A -> A + n <= A0 + n0 -> zrun m A n.
Proof. intros A n A0 n0 Z0 W H1 H2. split; [exact Z0| eapply wr_at_sub0; [exact W| lia| lia]]. Qed.

Lemma fake_zrun : zrun m (al_fake L + 96) 11571104.
Proof.
  hfact (ME.MZero (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 377)) (ME.ZLit 96)) 11571104) HZ.
  hfact (ME.MWr (ME.ZMul (ME.ZLit 4096) (ME.ZV 377)) 11571200) HW.
  rewrite al_fake_eq. eapply zrun_of; [exact HZ| exact HW| lia| lia].
Qed.
Lemma fake_sh_zrun : zrun m (shad (al_fake L)) (shlen FAKESZ).
Proof.
  hfact (ME.MZero (ME.ZAdd (ME.ZMul (ME.ZLit 512) (ME.ZV 377)) (ME.ZLit 2147450880)) 1446400) HZ.
  hfact (ME.MWr (ME.ZAdd (ME.ZMul (ME.ZLit 512) (ME.ZV 377)) (ME.ZLit 2147450880)) 1446400) HW.
  rewrite al_fake_eq, shad_div. unfold ASHOFF, FAKESZ, shlen. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  replace (2147450880 + 4096 * V 377%nat / 8) with (512 * V 377%nat + 2147450880) by (Z.div_mod_to_equations; lia).
  change (11571200 / 8) with 1446400. eapply zrun_of; [exact HZ| exact HW| lia| lia].
Qed.

Lemma afake_geom_main : afake_geom L.
Proof.
  unfold afake_geom. pose proof (ao_fake L ALO) as (F1 & F2 & F3 & F4 & F5). pose proof (ao_dtls L ALO) as (D1 & D2 & D3 & D4 & D5).
  pose proof (ao_t L ALO) as (T1 & T2 & T3 & T4 & T5).
  pose proof (ad_fake_dtls L ALO) as X1. pose proof (ad_t_dtls L ALO) as X2. pose proof (ad_t_fake L ALO) as X3. unfold adisj, FAKESZ in *.
  split; [exact F1|]. split.
  { unfold ablk, sclr, iclr, AIMG_LO, AIMG_HI, KLS in *. lia. }
  repeat (split; [tauto|]). tauto.
Qed.

Lemma afake_cells_main : afake_cells L m.
Proof.
  unfold afake_cells.
  split; [exact hf_tga|].
  split. { hfact (ME.MCell (ME.ZLit 6343808) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 377))) HC. rewrite al_fake_eq.
           apply (rw_cells_glue m _ 8 [_]); [exact hf_dtv| exact HC| reflexivity]. }
  split. { hfact (ME.MCell (ME.ZLit 6343816) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 310))) HC. unfold al_dtls. cbn [al_V L0 VL]. exact HC. }
  split; [exact hf_dtv1|].
  split. { hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 310)) (ME.ZLit 24)) 8%nat (ME.ZLit 6343808)) HC. unfold al_dtls. cbn [al_V L0 VL]. exact HC. }
  split; [exact hf_itga|]. split; [exact hf_verb|].
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 48)) 8%nat (ME.ZLit 6345656)) H48.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 56)) 8%nat (ME.ZLit 6345876)) H56.
  exists (cells_bytes [C8 (Z_to_bv 64 6345656); C8 (Z_to_bv 64 6345876)]). rewrite al_t_eq.
  apply (rw_cells_recast asegs m _ [C8 (Z_to_bv 64 6345656); C8 (Z_to_bv 64 6345876)]); [| cbn; split; [reflexivity| exact I]| reflexivity| reflexivity].
  apply (rw_cells_glue m _ 8 [_]); [exact H48| | reflexivity].
  replace (4096 * V 227%nat + 56) with (4096 * V 227%nat + 48 + 8) in H56 by lia. exact H56.
Qed.

Theorem afake_main : AFAKE (gb := false) L [] m.
Proof.
  unfold AFAKE. split; [exact afake_geom_main|]. split; [exact afake_cells_main|].
  split. { hfact (ME.MZeroC (ME.ZMul (ME.ZLit 4096) (ME.ZV 377)) 88) HZ. rewrite al_fake_eq.
           exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (ME.zeros 64).
           apply (rw_cells_recast asegs m _ [CB (Z.to_nat 88) (ME.zeros 88)]); [exact HZ| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity]. }
  split. { hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 377)) (ME.ZLit 88)) 8%nat (ME.ZLit 20)) HC. rewrite al_fake_eq. exact HC. }
  split. { cbn [gcbit]. apply zrun_cells; [cbn; tauto| reflexivity|]. cbn [cells_size csize Nat.add]. apply (zrun_sub _ _ _ _ _ fake_zrun); lia. }
  split. { exists (ME.zeros (FAKESZ - 4096)). apply zrun_CB; [| unfold FAKESZ; lia]. apply (zrun_sub _ _ _ _ _ fake_zrun); unfold FAKESZ; lia. }
  split. { exists (ME.zeros (shlen FAKESZ)). apply zrun_CB; [exact fake_sh_zrun| unfold FAKESZ, shlen; rewrite Z.shiftr_div_pow2 by lia; cbn; lia]. }
  split.
  { intros c pos b Hc Hp Hb NZ. exfalso. apply NZ. pose proof (fk_flag_range L c pos Hc Hp) as R.
    destruct fake_zrun as [Z0 _]. specialize (Z0 (fk_flag L c pos - (al_fake L + 96)) ltac:(lia)).
    replace (al_fake L + 96 + (fk_flag L c pos - (al_fake L + 96))) with (fk_flag L c pos) in Z0 by lia. congruence. }
  split; [intros c F n []|].
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 72)) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 377))) HC. rewrite al_t_eq, al_fake_eq. exact HC.
Qed.

Theorem aquar_main : AQUAR L sta X0 m.
Proof.
  exists qconc0. unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend qconc0 st0 ainit a_qloc a_qglob a_qloc_bytes a_qglob_bytes].
  split. { split; [exact hq_max| exact hq_mutex]. }
  split. { split; [| exact I]. cbn [length Z.of_nat qfirst qlast qaddrs map hd List.last]. unfold aq_tcache.
           apply zrun_cells; [cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity|]. cbn [cells_size csize Nat.add]. apply (zrun_sub _ _ _ _ _ THZ); lia. }
  split. { split; [| exact I]. cbn [length Z.of_nat qfirst qlast qaddrs map hd List.last]. exact hq_gcache. }
  split. { split; [exact hq_iaflag|]. split; [| intros X; discriminate X]. apply rw2_stk; unfold AIA_BASE, AIA_SIZE; lia. }
  split.
  { unfold qcoupled. cbn.
    split; [reflexivity|]. split; [reflexivity|]. split; [constructor|]. split; [constructor|]. split; [constructor|].
    split. { intros k. split; [intros []| intros (b & [] & _)]. }
    split. { intros c k. split; [intros []| intros (b & [] & _)]. }
    constructor. }
  unfold qnum. cbn. unfold Q_CACHE, Q_MAX.
  split; [reflexivity|]. split; [reflexivity|]. split; [constructor|]. lia.
Qed.

Lemma achunks_st0 : achunks sta = [].
Proof. unfold achunks. cbn [st0 ainit a_live a_qloc a_qglob app flat_map]. rewrite map_to_list_empty. reflexivity. Qed.
Lemma sec_chunks_st0 : sec_chunks_of sta = [].
Proof. unfold sec_chunks_of. rewrite achunks_st0. reflexivity. Qed.

Lemma asec_wf_main : asec_wf L sta [].
Proof.
  unfold asec_wf. split; [exact ALO|]. split; [reflexivity|]. cbn [st0 ainit a_nres a_nsec length Z.of_nat].
  split; [split; [reflexivity| lia]|]. split; [reflexivity|]. split; [lia|]. split; [constructor| exact sec_disjoint_nil].
Qed.

Lemma asec_arr_main : asec_arr L sta [] m.
Proof.
  unfold asec_arr. exists []. split; [apply Permutation_refl|]. cbn [map st0 ainit a_nsec a_nres].
  pose proof (ao_ptr L ALO) as (P1 & P2 & P3 & _). pose proof atop_range as AR.
  split. { change (@nil word) with (repeat (Z_to_bv 64 0) 0). apply zrun_u64arr. apply zrun0. lia. }
  split. { replace (al_ptr_array L + 8 * 0) with (al_ptr_array L) by lia. replace (8 * (0 - 0)) with 0 by lia. apply zrun_junk; [apply zrun0; lia| lia]. }
  intros [|i] ch H; discriminate H.
Qed.

Lemma asec_inst_main : asec_inst L m.
Proof.
  unfold asec_inst.
  split. { hfact (ME.MCell (ME.ZLit 877736) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 226))) HC. unfold al_ptr_array. cbn [al_V L0 VL]. exact HC. }
  split. { exists (Z_to_bv 8 0). exact hs_sorted. }
  split; [exact hs_stats|]. split; [exact hs_bylog|].
  split. { hfact (ME.MZeroC (ME.ZLit 878337) 3) HZ.
           apply (rw_cells_recast asegs m _ [CB (Z.to_nat 3) (ME.zeros 3)]); [exact HZ| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity]. }
  exact hs_gstats.
Qed.

Lemma ashz_main : ashz L [] m.
Proof.
  intros x Hx HH _. pose proof (ao_space L ALO) as SP. pose proof (ao_res_hi L ALO) as RH. pose proof atop_range as AR.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 10%nat) as B10. pose proof (HV 6%nat) as B6.
  unfold astartup_hulls in HH. unfold al_store, al_nodes, al_fake, al_dtls, al_ctx, al_t, al_res, al_ptr_array in HH. cbn [al_V L0 VL] in HH.
  revert SP. rewrite al_res_eq, al_space_beg_eq. intros SP.
  apply Forall_cons_iff in HH as [U1 HH]. apply Forall_cons_iff in HH as [U2 HH]. apply Forall_cons_iff in HH as [U3 HH]. apply Forall_cons_iff in HH as [U4 HH].
  apply Forall_cons_iff in HH as [U5 HH]. apply Forall_cons_iff in HH as [U6 HH]. apply Forall_cons_iff in HH as [U7 HH]. apply Forall_cons_iff in HH as [U8 HH].
  apply Forall_cons_iff in HH as [U9 HH]. apply Forall_cons_iff in HH as [U10 HH]. apply Forall_cons_iff in HH as [U11 HH]. apply Forall_cons_iff in HH as [U12 HH].
  apply Forall_cons_iff in HH as [U13 _]. cbn [fst snd] in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13.
  unfold AIMG_HI, KLS, K_HIGH_MEM in Hx.
  destruct (Z_lt_ge_dec x (32768 * V 0%nat + 4096 * V 10%nat + -8388608)) as [LO|HI].
  - apply HSH0.
    + unfold MA.ashadow. rewrite shad_div. unfold ASHOFF. clear -Hx AR. Z.div_mod_to_equations. lia.
    + intros (bn & Hin & R). unfold MA.ASHOFF in R. rewrite shad_div in R. unfold ASHOFF in R.
      unfold MF.asan_vis_app in Hin. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [fst snd ME.zv] in R.
      * clear -R U1. Z.div_mod_to_equations. lia.
      * clear -R U3. Z.div_mod_to_equations. lia.
      * clear -R U4. Z.div_mod_to_equations. lia.
      * clear -R U5. Z.div_mod_to_equations. lia.
      * clear -R U6. Z.div_mod_to_equations. lia.
      * clear -R U2. Z.div_mod_to_equations. lia.
      * clear -R U8. Z.div_mod_to_equations. lia.
      * clear -R U9. Z.div_mod_to_equations. lia.
      * clear -R U10 SP. Z.div_mod_to_equations. lia.
      * clear -R U11. Z.div_mod_to_equations. lia.
      * clear -R U12. Z.div_mod_to_equations. lia.
      * clear -R Hx. Z.div_mod_to_equations. lia.
      * clear -R LO B0 B10. Z.div_mod_to_equations. lia.
  - hfact (ME.MZeroS (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 0)) (ME.ZMul (ME.ZLit 512) (ME.ZV 10))) (ME.ZLit 2146402304))
                     (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit (-4096)) (ME.ZV 0)) (ME.ZMul (ME.ZLit (-512)) (ME.ZV 10))) (ME.ZLit 17592187092992))) HZ.
    specialize (HZ (shad x - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))).
    replace (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (shad x - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))) with (shad x) in HZ by lia.
    apply HZ. rewrite shad_div. unfold ASHOFF. clear -Hx HI HU0 AR B0 B10 B6. Z.div_mod_to_equations. lia.
Qed.

Lemma aexh_main : AEXHc [] L sta m.
Proof.
  unfold AEXHc.
  split. { unfold exh_cells, F_ammap.F_ammap.rmap_cells.
           split; [split; [exact (rt1 V m HMF)| split; [exact (rt19 V m HMF)| split; [exact (rt2 V m HMF)| split; [exact (rtb1 V m HMF)| exact (rtb2 V m HMF)]]]]|].
           split; [exact hx_toolname|]. split; [exact hx_cf64| exact hx_cb]. }
  split. { unfold emb_cells. cbn [st0 ainit a_emb Z.eqb]. unfold AEMB. split; [exact he_16|]. split; [exact he_0|]. split; [reflexivity| exact he_32]. }
  split. { intros c Hc NB. unfold axflag. replace (exh_mem c sta) with false by reflexivity. rewrite aregion_info_eq. unfold K_NUM_CLASSES in Hc.
           apply zrun_cells; [cbn; tauto| reflexivity|]. cbn [cells_size csize Nat.add]. apply (zrun_sub _ _ _ _ _ RIZ); lia. }
  split. { unfold emb_clrK. cbn [st0 ainit a_emb]. intros a Ha. lia. }
  unfold emb_clrC. cbn [st0 ainit a_emb]. left. reflexivity.
Qed.

Theorem asec_main : ASEC_of L sta X0 m.
Proof.
  unfold ASEC_of. rewrite sec_chunks_st0. unfold ASECc.
  split; [exact asec_wf_main|]. split; [exact asec_arr_main|]. split; [exact asec_inst_main|]. split; [exact aprim0_main|].
  split; [exact ashz_main| exact aexh_main].
Qed.

Lemma stk_of_wr : forall A n, wr_at asegs m A n -> (forall a, A <= a < A + n -> exists b, mrd asegs m (wa a) = Some b) -> stk asegs m A (A + n).
Proof.
  intros A n (W1 & W2 & W3) R. split; [lia|]. split; [lia|]. intros a Ha. split; [| exact (R a Ha)].
  replace a with (A + (a - A)) by lia. apply W3. lia.
Qed.
Lemma zrun_mrd : forall A n a, zrun m A n -> A <= a < A + n -> exists b, mrd asegs m (wa a) = Some b.
Proof.
  intros A n a [Z0 _] Ha. exists (Z_to_bv 8 0). unfold mrd. specialize (Z0 (a - A) ltac:(lia)). replace (A + (a - A)) with a in Z0 by lia. rewrite Z0. reflexivity.
Qed.
Lemma cells_mrd : forall A cs a, rw_cells asegs m A cs -> A <= a < A + Z.of_nat (cells_size cs) -> exists b, mrd asegs m (wa a) = Some b.
Proof.
  intros A cs a [[WF (B1 & B2 & B3)] _] Ha. pose proof (cells_bytes_length cs WF) as LEN.
  specialize (B3 (Z.to_nat (a - A)) ltac:(rewrite LEN; lia)). replace (A + Z.of_nat (Z.to_nat (a - A))) with a in B3 by lia.
  rewrite B3. destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. rewrite LEN in E. lia.
Qed.
Lemma zrun_stk : forall A n, zrun m A n -> stk asegs m A (A + n).
Proof. intros A n ZR. apply stk_of_wr; [exact (proj2 ZR)| intros a Ha; exact (zrun_mrd A n a ZR Ha)]. Qed.

Lemma BUD_le_usum : forall Ul hs n, BUD Ul hs n <= usum Ul.
Proof. induction Ul as [|u Ul IH]; intros hs n; cbn [BUD usum fold_right]; [lia|]. unfold ucost. specialize (IH hs n). fold (usum Ul). destruct (has_hash hs n (hashU u)); lia. Qed.
Lemma CNT_le_len : forall Ul hs n, CNT Ul hs n <= Z.of_nat (length Ul).
Proof. induction Ul as [|u Ul IH]; intros hs n; cbn [CNT length]; [lia|]. specialize (IH hs n). destruct (has_hash hs n (hashU u)); lia. Qed.

Lemma dlayout_main : dlayout L.
Proof.
  unfold dlayout. pose proof (alayout_depot L ALO) as (_ & D2 & D3 & _ & D5 & D6 & _). pose proof (ao_nodes L ALO) as (N1 & _). pose proof (ao_store L ALO) as (ST1 & _).
  pose proof (ad_nodes_store L ALO) as NS. unfold adisj in NS. repeat (split; [assumption|]). exact NS.
Qed.

Section Depot.
Variables h tf BA : Z.
Hypothesis Hh : 0 <= h < 2 ^ 64.
Hypothesis Htf : 0 <= tf <= 3.
Hypothesis HBA : BA = TAB + 4 * bkt h.
Hypothesis Fh : rw_cells asegs m (al_nodes L + 16) [C8 (Z_to_bv 64 h)].
Hypothesis Ftf8 : rw_cells asegs m SSTF [C8 (Z_to_bv 64 tf)].
Hypothesis Ftf4 : rw_cells asegs m SSST [C4 (Z_to_bv 64 tf)].
Hypothesis Fbkt : rw_cells asegs m BA [C4 (Z_to_bv 64 1)].
Hypothesis Fimg1 : forall i, 0x1ab9a8 <= i < BA -> m (wa i) = None.
Hypothesis Fimg2 : forall i, BA + 4 <= i < 0x5bb998 -> m (wa i) = None.
Hypothesis Fstore : stk asegs m (al_store L) (al_store L + 8388608).

Definition D0 : dstate := mkD 1 (fun b => if b =? bkt h then 1 else 0) (fun _ => h) (fun _ => 0) (fun _ => 1) tf.

Lemma dwf_main : dwf (al_U L) D0.
Proof.
  unfold dwf, D0. cbn [dN dhd dhs dlk dsid dtf al_U L0]. pose proof HU as HU1. unfold univ_ok in HU1.
  assert (BK : 0 <= bkt h < 1048576) by (unfold bkt; apply Z.mod_pos_bound; lia).
  split; [lia|]. split; [intros i Hi; lia|].
  split. { intros b Hb. destruct (Z.eqb_spec b (bkt h)) as [->|NE]; [split; [lia| intros _; reflexivity]| split; [lia| intros X; exfalso; exact (X eq_refl)]]. }
  split. { intros i Hi. split; [exact Hh|]. split; [lia|]. intros X. exfalso. exact (X eq_refl). }
  split. { intros i Hi. rewrite Z.eqb_refl. assert (E : i = 1) by lia. subst i.
           rewrite (chain_cons (fun _ => 0) 1 1) by (try (intros j Hj); lia). left. reflexivity. }
  pose proof (BUD_le_usum U (fun _ => h) (Z.to_nat 1)) as B1. pose proof (CNT_le_len U (fun _ => h) (Z.to_nat 1)) as C1. lia.
Qed.

Lemma dcells_main : dcells L D0 m.
Proof.
  unfold dcells, D0. cbn [dN dhd dhs dlk dsid dtf].
  split; [exact Ftf8|].
  split. { hfact (ME.MCell (ME.ZLit 1751448) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 454))) HC. unfold SSPTR, al_store. cbn [al_V L0 VL]. exact HC. }
  split; [exact Ftf4|]. split; [exact hd_nuniq|].
  split. { hfact (ME.MCell (ME.ZLit 6011304) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 453))) HC. unfold MAP1, al_nodes. cbn [al_V L0 VL]. exact HC. }
  assert (BK : 0 <= bkt h < 1048576) by (unfold bkt; apply Z.mod_pos_bound; lia).
  split.
  { intros b Hb. destruct (Z.eqb_spec b (bkt h)) as [->|NE]; [rewrite <- HBA; exact Fbkt|]. unfold TAB in *.
    apply rw_cells_bss0_as; [unfold BSS0_LO; lia| unfold BSS0_HI; cbn [cells_size csize Nat.add]; lia| cbn; tauto| reflexivity|].
    cbn [cells_size csize Nat.add]. intros i Hi. destruct (Z_lt_ge_dec b (bkt h)); [apply Fimg1; lia| apply Fimg2; lia]. }
  split.
  { intros i Hi. assert (E : i = 1) by lia. subst i.
    hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 453)) (ME.ZLit 24)) 4%nat (ME.ZLit 0)) H24.
    hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 453)) (ME.ZLit 28)) 4%nat (ME.ZLit 1)) H28.
    revert Fh. unfold al_nodes. cbn [al_V L0 VL]. intros Fh0. replace (4096 * V 453%nat + 16 * 1) with (4096 * V 453%nat + 16) by lia.
    apply (rw_cells_glue m _ 8 [_]); [exact Fh0| | reflexivity]. replace (4096 * V 453%nat + 16 + 8) with (4096 * V 453%nat + 24) by lia.
    apply (rw_cells_glue m _ 4 [_]); [exact H24| | reflexivity]. replace (4096 * V 453%nat + 24 + 4) with (4096 * V 453%nat + 28) by lia. exact H28. }
  split; [| exact Fstore].
  hfact (ME.MZero (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 453)) (ME.ZLit 32)) 1048544) HZ.
  hfact (ME.MWr (ME.ZMul (ME.ZLit 4096) (ME.ZV 453)) 1048576) HW.
  unfold al_nodes. cbn [al_V L0 VL]. replace (4096 * V 453%nat + 16 * (1 + 1)) with (4096 * V 453%nat + 32) by lia.
  replace (4096 * V 453%nat + 1048576) with (4096 * V 453%nat + 32 + 1048544) by lia.
  apply zrun_stk. eapply zrun_of; [exact HZ| exact HW| lia| lia].
Qed.

Lemma adepot_gen : ADEPOTi L m.
Proof. exists D0. split; [exact dwf_main|]. split; [exact dcells_main| exact dlayout_main]. Qed.
End Depot.

Lemma store_stk : stk asegs m (al_store L) (al_store L + 8388608).
Proof.
  hfact (ME.MWr (ME.ZMul (ME.ZLit 4096) (ME.ZV 454)) 8388608) HW.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 454)) (ME.ZLit 8)) 8%nat (ME.ZLit 303348)) H8.
  unfold al_store. cbn [al_V L0 VL]. apply stk_of_wr; [exact HW|]. intros a Ha.
  assert (Ew : w = true \/ w = false) by (destruct w; auto).
  destruct Ew as [Ew|Ew]; pose proof HMFw as HMW; rewrite Ew in HMW.
  - pose proof (ME.mfacts_nth asegs V m _ 6 _ HMW eq_refl) as H0. pose proof (ME.mfacts_nth asegs V m _ 7 _ HMW eq_refl) as H16.
    pose proof (ME.mfacts_nth asegs V m _ 8 _ HMW eq_refl) as HZ. cbn [ME.mfact_ok ME.zv ME.cellw] in H0, H16, HZ.
    destruct (Z_lt_ge_dec a (4096 * V 454%nat + 8)); [apply (cells_mrd _ _ a H0); cbn; lia|].
    destruct (Z_lt_ge_dec a (4096 * V 454%nat + 16)); [apply (cells_mrd _ _ a H8); cbn; lia|].
    destruct (Z_lt_ge_dec a (4096 * V 454%nat + 24)); [apply (cells_mrd _ _ a H16); cbn; lia|].
    exists (Z_to_bv 8 0). unfold mrd. specialize (HZ (a - (4096 * V 454%nat + 24)) ltac:(lia)).
    replace (4096 * V 454%nat + 24 + (a - (4096 * V 454%nat + 24))) with a in HZ by lia. rewrite HZ. reflexivity.
  - pose proof (ME.mfacts_nth asegs V m _ 6 _ HMW eq_refl) as H0. pose proof (ME.mfacts_nth asegs V m _ 7 _ HMW eq_refl) as HZ.
    cbn [ME.mfact_ok ME.zv ME.cellw] in H0, HZ.
    destruct (Z_lt_ge_dec a (4096 * V 454%nat + 8)); [apply (cells_mrd _ _ a H0); cbn; lia|].
    destruct (Z_lt_ge_dec a (4096 * V 454%nat + 16)); [apply (cells_mrd _ _ a H8); cbn; lia|].
    exists (Z_to_bv 8 0). unfold mrd. specialize (HZ (a - (4096 * V 454%nat + 16)) ltac:(lia)).
    replace (4096 * V 454%nat + 16 + (a - (4096 * V 454%nat + 16))) with a in HZ by lia. rewrite HZ. reflexivity.
Qed.

Theorem adepot_main : ADEPOTi L m.
Proof.
  assert (Ew : w = true \/ w = false) by (destruct w; auto).
  destruct Ew as [Ew|Ew]; pose proof HMFw as HW; rewrite Ew in HW.
  - pose proof (ME.mfacts_nth asegs V m _ 0 _ HW eq_refl) as F0. pose proof (ME.mfacts_nth asegs V m _ 1 _ HW eq_refl) as F1.
    pose proof (ME.mfacts_nth asegs V m _ 2 _ HW eq_refl) as F2. pose proof (ME.mfacts_nth asegs V m _ 3 _ HW eq_refl) as F3.
    pose proof (ME.mfacts_nth asegs V m _ 4 _ HW eq_refl) as F4. pose proof (ME.mfacts_nth asegs V m _ 5 _ HW eq_refl) as F5.
    cbn [ME.mfact_ok ME.zv ME.cellw] in F0, F1, F2, F3, F4, F5.
    apply (adepot_gen 896777266038058978 3 3963168); try assumption.
    + lia. + lia. + reflexivity.
    + exact store_stk.
  - pose proof (ME.mfacts_nth asegs V m _ 0 _ HW eq_refl) as F0. pose proof (ME.mfacts_nth asegs V m _ 1 _ HW eq_refl) as F1.
    pose proof (ME.mfacts_nth asegs V m _ 2 _ HW eq_refl) as F2. pose proof (ME.mfacts_nth asegs V m _ 3 _ HW eq_refl) as F3.
    pose proof (ME.mfacts_nth asegs V m _ 4 _ HW eq_refl) as F4. pose proof (ME.mfacts_nth asegs V m _ 5 _ HW eq_refl) as F5.
    cbn [ME.mfact_ok ME.zv ME.cellw] in F0, F1, F2, F3, F4, F5.
    apply (adepot_gen 18431315423844088295 2 3842356); try assumption.
    + lia. + lia. + reflexivity.
    + exact store_stk.
Qed.

Theorem arep_main : AREP (AHI (gb := false)) L sta X0 m.
Proof.
  unfold AREP. cbn [AHI ah_quar ah_sec ah_depot].
  split; [exact awf_main|]. split; [exact (arep_rt_main V w U m HMF)|]. split; [exact (ainstance_main V w U m HMF)|].
  split; [exact (athread_main V w U m HMF HPF)|].
  split. { intros c Hc. split; [exact (aregion_cells_main c Hc)|]. split; [exact (afreearray_main c Hc)|]. split; [exact (aslots_main c Hc)| exact (aslot_shadow_main c Hc)]. }
  split; [exact aquar_main|]. split; [exact asec_main|]. split; [exact adepot_main|].
  split; [exact (arelro_main V m HMF)|]. split; [exact (arep_rt2_main V m HMF)|].
  split; [exact ashadow_avail_main| exact (arep_rt3_main V m HMF)].
Qed.

Definition arng0 (Lx : alayout) (RNG : footprint) : Prop :=
     rng RNG 0x10000 0x61f000
  /\ rng RNG (al_t Lx) 4096 /\ rng RNG (al_ctx Lx) 65536 /\ rng RNG (al_nodes Lx) 1048576 /\ rng RNG (al_store Lx) 8388608
  /\ rng RNG (al_space_beg Lx + K_SPACE_SIZE) K_SPACE_EXTRA
  /\ rng RNG (al_fake Lx) 11571200 /\ rng RNG (shad (al_fake Lx)) (shlen 11571200) /\ rng RNG (al_dtls Lx) 4096
  /\ rng RNG (shad (al_space_beg Lx)) (shlen K_SPACE_SIZE).

Lemma rng0 : forall lz AL A, 0 <= A <= 2 ^ 64 -> rng (fp_ok lz AL) A 0.
Proof. intros lz AL A HA. split; [lia|]. split; [lia|]. intros b j Hb Hj k Hk. lia. Qed.

Lemma arng_main : forall lz AL, arng0 L (fp_ok lz AL) -> arng L (fp_ok lz AL) sta.
Proof.
  intros lz AL (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10). unfold arng.
  pose proof space_facts as (S1 & S2 & S3 & S4). pose proof (ao_ptr L ALO) as (P1 & P2 & P3 & _). pose proof atop_range as AR.
  unfold K_SPACE_SIZE, K_SPACE_EXTRA in S2.
  repeat (split; [assumption|]).
  split.
  { intros c Hc. rewrite get_cls_st0. cbn [c_mapped_user c_mapped_free_array aclass0]. rewrite shlen_0. unfold K_NUM_CLASSES in Hc.
    assert (B : 0 <= aregion L c /\ afreearr L c + 0 <= 2 ^ 64 /\ aregion L c <= afreearr L c) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; nia).
    split; [apply rng0; lia|]. split; [apply rng0; rewrite shad_div; unfold ASHOFF; clear -B; Z.div_mod_to_equations; lia|].
    split; [apply rng0; lia|]. apply rng0; rewrite shad_div; unfold ASHOFF; clear -B; Z.div_mod_to_equations; lia. }
  split. { cbn [st0 ainit a_nres]. replace (8 * 0) with 0 by lia. apply rng0. lia. }
  split; [rewrite sec_chunks_st0; constructor| exact R10].
Qed.

Theorem aheapP_main : forall lz AL, arng0 L (fp_ok lz AL) -> AHEAP_P (AHI (gb := false)) L (fp_ok lz AL) sta [] m.
Proof.
  intros lz AL R. split; [exact ALO|]. split; [exact (arng_main lz AL R)|].
  split; [exists X0; split; [exact arep_main| exact ablocks_main]|]. cbn [AHI ah_fake]. exact afake_main.
Qed.

Theorem aheapu2_main : forall lz AL, arng0 L (fp_ok lz AL) -> AHEAPu2 L (fp_ok lz AL) sta [] m.
Proof.
  intros lz AL R. exists ov0. split; [exists false; exact (aheapP_main lz AL R)|]. intros q Hq. exfalso. exact (Hq eq_refl).
Qed.

Lemma aprist_main : APristLaw.aprist sta.
Proof. intros c Hc NB. rewrite get_cls_st0. split; reflexivity. Qed.
Lemma al_U_main : al_U L = U. Proof. reflexivity. Qed.
Lemma a_space_beg_main : a_space_beg sta = al_space_beg L /\ a_ptr_array sta = al_ptr_array L. Proof. split; reflexivity. Qed.

End AtMain2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require MainFactsBoth MainEntryBoth.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import ABase.TwinB AProto.TwinB ALayout.TwinB ARep.TwinB ABytes.TwinB ARepQ.TwinB AQConst.TwinB ASec.TwinB AExh.TwinB AEmbRep.TwinB AHeapP.TwinB ADepot_iface.TwinB ADepot.TwinB AFake_iface.TwinB AInstance.TwinB AInstanceU.TwinB AInstanceU2.TwinB APristLaw.TwinB ABssZero.TwinB ARepAtMain.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ME := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainExport.
Module MF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainFactsBoth.
Module MA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.MainEntryBoth.

Definition ov0 : annOV := {| ann_ov := fun _ => None; ann_ovs := fun _ => None |}.

Section AtMain2.
Context {rc : runConstT}.
Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
Hypothesis HV : forall n, 0 <= V n < 2 ^ 64.
Hypothesis HMF : Forall (ME.mfact_ok bsegs V m) MF.both_mem_facts.
Hypothesis HMFw : Forall (ME.mfact_ok bsegs V m) (MA.both_mem_facts_w w).
Hypothesis HPF : Forall (ME.pfact_ok V) MF.both_pure_facts.
Hypothesis MINV : mem_inv bsegs m.
Hypothesis HUSP : usp_pin V.
Hypothesis HSH0 : MA.bshadow0 V m.
Hypothesis HU : univ_ok U.

Local Notation L := (L0 V w U).
Local Notation sta := (st0 V w U).
Local Existing Instance ov0.

Local Notation HF := (hf V m HMF).
Local Notation HP := (hp V HPF).
Tactic Notation "hfact" constr(F) ident(H) := pose proof (HF F ltac:(vm_compute; reflexivity)) as H; cbn [ME.mfact_ok ME.zv ME.cellw] in H.
Tactic Notation "hpf" constr(k) ident(H) := pose proof (HP k _ eq_refl) as H; cbn [ME.pfact_ok ME.zv] in H.
Ltac hcell A W X :=
  let H := fresh "HC" in
  pose proof (HF (ME.MCell (ME.ZLit A) W (ME.ZLit X)) ltac:(vm_compute; reflexivity)) as H;
  cbn [ME.mfact_ok ME.zv ME.cellw] in H.
Local Notation RIZ := (ri_zrun V w U m HMF).
Local Notation THZ := (thr_zrun V w U m HMF).
Local Notation ALO := (alayout_ok_main V w U HV HPF HUSP HU).

Lemma zrun0 : forall A, 0 <= A <= 2 ^ 64 -> zrun m A 0.
Proof. intros A HA. split; [intros i Hi; lia|]. split; [lia|]. split; [lia|]. intros i Hi. lia. Qed.

Lemma shlen_0 : shlen 0 = 0. Proof. reflexivity. Qed.

Lemma aregion_info_eq : forall c, aregion_info L c = al_space_beg L + K_SPACE_SIZE + c * 128.
Proof. intros c. reflexivity. Qed.

Lemma space_facts : 0x10007fff8000 <= al_space_beg L /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP /\ al_space_beg L mod K_ALIGN = 0
  /\ 0 <= al_space_beg L < 2^47.
Proof. exact (alayout_space L ALO). Qed.

Lemma aregion_cells_main : forall c, 1 <= c < K_NUM_CLASSES -> aregion_cells L sta m c.
Proof.
  intros c Hc. unfold aregion_cells. rewrite get_cls_st0. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user aclass0].
  rewrite aregion_info_eq. unfold K_NUM_CLASSES in Hc. pose proof RIZ as Z0.
  split. { apply zrun_cells; [cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity|]. cbn [cells_size csize Nat.add]. apply (zrun_sub _ _ _ _ _ Z0); lia. }
  split. { apply zrun_cells; [cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity|]. cbn [cells_size csize Nat.add]. apply (zrun_sub _ _ _ _ _ Z0); lia. }
  split. { apply zrun_junk; [| lia]. apply (zrun_sub _ _ _ _ _ Z0); lia. }
  split.
  { unfold aflag_cell. rewrite aregion_info_eq. destruct (Z.eqb_spec c K_BATCH_CLASS) as [E|NE].
    - apply zrun_cells; [cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity|]. cbn [cells_size csize Nat.add]. apply (zrun_sub _ _ _ _ _ Z0); lia.
    - apply zrun_junk; [| lia]. apply (zrun_sub _ _ _ _ _ Z0); lia. }
  apply zrun_junk; [| lia]. apply (zrun_sub _ _ _ _ _ Z0); lia.
Qed.

Lemma afreearray_main : forall c, 1 <= c < K_NUM_CLASSES -> afreearray L sta X0 m c.
Proof.
  intros c Hc. unfold afreearray. rewrite get_cls_st0. cbn [c_num_freed c_mapped_free_array aclass0 x_cls X0 xc_free xc0 map].
  pose proof space_facts as (S1 & S2 & _ & S4). unfold K_NUM_CLASSES in Hc. unfold K_SPACE_SIZE, K_SPACE_EXTRA in S2. pose proof atop_range as AR.
  assert (B : 0 <= afreearr L c /\ afreearr L c + 0 <= 2 ^ 64).
  { unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. nia. }
  split. { change (@nil word) with (repeat (Z_to_bv 64 0) 0). apply zrun_u32arr. apply zrun0. lia. }
  split. { replace (afreearr L c + 4 * 0) with (afreearr L c) by lia. replace (0 - 4 * 0) with 0 by lia. apply zrun_junk; [apply zrun0; lia| lia]. }
  rewrite shlen_0. apply zrun_junk; [| lia]. apply zrun0. rewrite shad_div. unfold ASHOFF. clear -B. Z.div_mod_to_equations. lia.
Qed.

Lemma aslots_main : forall c, 1 <= c < K_NUM_CLASSES -> aslots L sta X0 m c.
Proof.
  intros c Hc. unfold aslots. rewrite ndist_st0, get_cls_st0. cbn [c_allocated_user c_mapped_user aclass0].
  split; [intros k Hk; lia|].
  pose proof space_facts as (S1 & S2 & _ & S4). unfold K_NUM_CLASSES in Hc. unfold K_SPACE_SIZE, K_SPACE_EXTRA in S2. pose proof atop_range as AR.
  replace (0 - 0) with 0 by lia. apply zrun_junk; [| lia]. apply zrun0. unfold aregion, K_REGION. nia.
Qed.

Lemma aslot_shadow_main : forall c, 1 <= c < K_NUM_CLASSES -> aslot_shadow L sta X0 m c.
Proof.
  intros c Hc. unfold aslot_shadow. rewrite ndist_st0, get_cls_st0. cbn [c_allocated_user c_mapped_user aclass0].
  split; [intros k Hk; lia|].
  pose proof space_facts as (S1 & S2 & _ & S4). unfold K_NUM_CLASSES in Hc. unfold K_SPACE_SIZE, K_SPACE_EXTRA in S2. pose proof atop_range as AR.
  replace (0 - 0) with 0 by lia. rewrite shlen_0. unfold fill_at. cbn [Z.to_nat repeat]. apply rw_cells_nil0.
  assert (B : 0 <= aregion L c + 0 <= 2 ^ 64) by (unfold aregion, K_REGION; nia).
  rewrite shad_div. unfold ASHOFF. clear -B. Z.div_mod_to_equations. lia.
Qed.

Lemma res_clear_vis : forall bn, In bn MF.both_vis_app ->
  let B := ME.zv V (fst bn) in let N := ME.zv V (snd bn) in
  B + N <= al_res L + 4096 \/ al_space_beg L + K_SPACE_SIZE <= B.
Proof.
  intros bn Hin. pose proof (ao_space L ALO) as SP. pose proof (ao_res_hi L ALO) as RH. revert SP RH. rewrite al_res_eq, al_space_beg_eq. intros SP RH.
  unfold K_SPACE_SIZE. change (2 ^ 37) with 137438953472.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 10%nat) as B10. pose proof (HV 6%nat) as B6.
  unfold MF.both_vis_app in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [fst snd ME.zv].
  - hpf 90%nat D. lia.
  - hpf 89%nat D. lia.
  - hpf 88%nat D. lia.
  - hpf 87%nat D. lia.
  - hpf 85%nat D. lia.
  - hpf 84%nat D. lia.
  - hpf 83%nat D. lia.
  - hpf 82%nat D. lia.
  - right. lia.
  - hpf 67%nat D. lia.
  - hpf 177%nat D. lia.
  - left. lia.
  - hpf 79%nat D. lia.
Qed.

Lemma prim_shadow_clear : forall a, shad (al_res L + 4096) <= a < shad (al_space_beg L + K_SPACE_SIZE) ->
  MA.bshadow a /\ ~ MA.bshadow_vis V a.
Proof.
  intros a Ha. pose proof (ao_space L ALO) as SP. pose proof (ao_res_hi L ALO) as RH. pose proof space_facts as (S1 & S2 & _ & S4).
  pose proof atop_range as AR. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. rewrite !shad_div in Ha. unfold ASHOFF in Ha.
  split.
  - unfold MA.bshadow. right. clear -Ha SP RH S2 AR. Z.div_mod_to_equations. lia.
  - intros (bn & Hin & R). pose proof (res_clear_vis bn Hin) as D. cbn zeta in D. unfold MA.ASHOFF in R. unfold K_SPACE_SIZE in D.
    set (B := ME.zv V (fst bn)) in *. set (N := ME.zv V (snd bn)) in *. clearbody B N. clear -Ha SP D R.
    Z.div_mod_to_equations. lia.
Qed.

Lemma prim_azero : forall A n, al_res L + 4096 <= A -> A + n <= al_space_beg L + K_SPACE_SIZE -> A mod 8 = 0 -> 8 <= n ->
  azero m (shad A) (shlen n).
Proof.
  intros A n HA Hn A8 N8. pose proof (ao_space L ALO) as SP.
  assert (SL : 0 < shlen n /\ shad A + shlen n <= shad (al_space_beg L + K_SPACE_SIZE) /\ shad (al_res L + 4096) <= shad A).
  { unfold shlen. rewrite !shad_div, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear -HA Hn A8 N8. Z.div_mod_to_equations. lia. }
  destruct SL as (SL1 & SL2 & SL3).
  destruct (MA.bshadow0_range V m (shad A) (shlen n) HSH0 SL1) as (Z1 & W1 & _).
  { intros a Ha. apply prim_shadow_clear. lia. }
  split; [exact Z1| exact W1].
Qed.

Lemma ashadow_avail_main : forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L sta m c.
Proof.
  intros c Hc. unfold ashadow_avail. rewrite get_cls_st0. cbn [c_mapped_user c_mapped_free_array aclass0].
  pose proof (ao_space L ALO) as SP. pose proof space_facts as (S1 & S2 & S3 & S4). unfold K_NUM_CLASSES in Hc.
  unfold K_ALIGN in S3. rewrite !Z.add_0_r, !Z.sub_0_r.
  split.
  - apply prim_azero; unfold aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE in *; [nia| nia| | lia].
    change (2 ^ 32) with 4294967296. clear -S3. Z.div_mod_to_equations. lia.
  - apply prim_azero; unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, K_SPACE_SIZE in *; [nia| nia| | lia].
    change (2 ^ 32) with 4294967296. clear -S3. Z.div_mod_to_equations. lia.
Qed.

Lemma aprim0_main : aprim0 L m.
Proof.
  unfold aprim0. pose proof (ao_space L ALO) as SP. pose proof space_facts as (S1 & S2 & S3 & S4). unfold K_ALIGN in S3.
  apply prim_azero; unfold K_REGION, K_SPACE_SIZE in *; [lia| lia| | lia].
  clear -S3. Z.div_mod_to_equations. lia.
Qed.

Lemma awf_main : awf L sta X0.
Proof.
  unfold awf. pose proof space_facts as (S1 & S2 & S3 & S4).
  split; [reflexivity|]. split; [reflexivity|]. split; [exact S3|]. split; [exact S1|]. split; [exact S2|].
  split.
  { intros c Hc. rewrite get_cls_st0, max_count_st0, ndist_st0.
    cbn [c_allocated_user c_mapped_user c_num_freed c_mapped_free_array c_count aclass0 x_cls X0 xc_free xc_cache xc0 length Z.of_nat app busy_slots x_busy List.filter map].
    unfold K_FREEARR_OFF, K_FREEARR_MAX, K_USER_MAP, K_FREEARR_MAP.
    repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity.
    - constructor.
    - intros k [].  }
  split. { intros c _. apply get_cls_st0. }
  split. { intros b []. }
  split. { intros p c n H. cbn [st0 ainit a_live] in H. rewrite lookup_empty in H. discriminate H. }
  split. { intros p ch H. cbn [st0 ainit a_live] in H. rewrite lookup_empty in H. discriminate H. }
  intros b1 b2 [].
Qed.

Lemma ablocks_main : ablocks L sta X0 [].
Proof.
  split; [intros p A n []|]. split; [intros cls A n []|]. split; constructor.
Qed.

Lemma hq_max : rw_cells bsegs m 887088 [C8 (Z_to_bv 64 268435456); C8 (Z_to_bv 64 241591905); C8 (Z_to_bv 64 1048576)].
Proof.
  hcell 887088 8%nat 268435456. rename HC into K0.
  hcell 887096 8%nat 241591905. rename HC into K1.
  hcell 887104 8%nat 1048576. rename HC into K2.
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K2.
Qed.

Lemma hq_mutex : rw_cells bsegs m 887176 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  hcell 887176 1%nat 0. rename HC into K0.
  hcell 887177 1%nat 0. rename HC into K1.
  assert (K2 : rw_cells bsegs m 887178 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast bsegs m 887178 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 887178 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 887178 889912); [vm_compute; reflexivity| lia]. }
  assert (K3 : rw_cells bsegs m 887179 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast bsegs m 887179 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 887179 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 887178 889912); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K3.
Qed.

Lemma hq_gcache : rw_cells bsegs m 887184 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells bsegs m 887184 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 887184 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 887184 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 887178 889912); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells bsegs m 887192 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 887192 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 887192 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 887178 889912); [vm_compute; reflexivity| lia]. }
  assert (K2 : rw_cells bsegs m 887200 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 887200 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 887200 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 887178 889912); [vm_compute; reflexivity| lia]. }
  assert (K3 : rw_cells bsegs m 887208 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 887208 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 887208 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 887178 889912); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K3.
Qed.

Lemma hq_iaflag : rw_cells bsegs m 1488648 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  assert (K0 : rw_cells bsegs m 1488648 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast bsegs m 1488648 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 1488648 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 1433314 1488656); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells bsegs m 1488649 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast bsegs m 1488649 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 1488649 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 1433314 1488656); [vm_compute; reflexivity| lia]. }
  assert (K2 : rw_cells bsegs m 1488650 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast bsegs m 1488650 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 1488650 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 1433314 1488656); [vm_compute; reflexivity| lia]. }
  assert (K3 : rw_cells bsegs m 1488651 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast bsegs m 1488651 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 1488651 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 1433314 1488656); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K3.
Qed.

Lemma hs_sorted : rw_cells bsegs m 886424 [C1 (Z_to_bv 8 0)].
Proof.
  assert (K0 : rw_cells bsegs m 886424 [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_recast bsegs m 886424 [CB 1%nat [Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 886424 [Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 886400 886976); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma hx_toolname : rw_cells bsegs m 873864 [C8 (Z_to_bv 64 139426)].
Proof.
  hcell 873864 8%nat 139426. rename HC into K0.
  exact K0.
Qed.

Lemma hx_cf64 : rw_cells bsegs m 1497064 [C1 (Z_to_bv 8 0)].
Proof.
  hcell 1497064 8%nat 0. rename HC into HW0.
  apply (rw_cells_recast bsegs m 1497064 _ [C1 (Z_to_bv 8 0); CB 7%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in HW0; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app bsegs m _ [_] _)) in HW0 as [HW0 _].
  rename HW0 into K0.
  exact K0.
Qed.

Lemma hx_cb : rw_cells bsegs m 1497488 [C8 (Z_to_bv 64 399224)].
Proof.
  hcell 1497488 8%nat 399224. rename HC into K0.
  exact K0.
Qed.

Lemma he_16 : rw_cells bsegs m 898296 [C8 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells bsegs m 898296 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 898296 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 898296 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 898280 900216); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma he_0 : rw_cells bsegs m 898280 [C8 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells bsegs m 898280 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 898280 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 898280 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 898280 900216); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma he_32 : rw_cells bsegs m 898312 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  assert (K0 : rw_cells bsegs m 898312 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 898312 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 898312 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 898280 900216); [vm_compute; reflexivity| lia]. }
  assert (K1 : rw_cells bsegs m 898320 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 898320 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 898320 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 898280 900216); [vm_compute; reflexivity| lia]. }
  assert (K2 : rw_cells bsegs m 898328 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_recast bsegs m 898328 [CB 8%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 898328 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 898280 900216); [vm_compute; reflexivity| lia]. }
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add].
  exact K2.
Qed.

Lemma hd_nuniq : rw_cells bsegs m 6019928 [C4 (Z_to_bv 64 1)].
Proof.
  hcell 6019928 4%nat 1. rename HC into K0.
  exact K0.
Qed.

Lemma hf_tga : rw_cells bsegs m 873584 [C8 (Z_to_bv 64 827824)].
Proof.
  assert (K0 : rw_cells bsegs m 873584 [C8 (Z_to_bv 64 827824)]).
  { apply (rw_cells_recast bsegs m 873584 [CB 8%nat [Z_to_bv 8 176; Z_to_bv 8 161; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]); [| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
    apply (rw_cells_image0 bsegs m 873584 [Z_to_bv 8 176; Z_to_bv 8 161; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
    intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 65536 873856); [vm_compute; reflexivity| lia]. }
  exact K0.
Qed.

Lemma hf_dtv : rw_cells bsegs m 6352440 [C8 (Z_to_bv 64 6352480)].
Proof.
  hcell 6352440 8%nat 6352480. rename HC into K0.
  exact K0.
Qed.

Lemma hf_dtv1 : rw_cells bsegs m 6352488 [C8 (Z_to_bv 64 6354496)].
Proof.
  hcell 6352488 8%nat 6354496. rename HC into K0.
  exact K0.
Qed.

Lemma hf_itga : rw_cells bsegs m 1497137 [C1 (Z_to_bv 8 1)].
Proof.
  hcell 1497136 8%nat 256. rename HC into HW0.
  apply (rw_cells_recast bsegs m 1497136 _ [CB 1%nat [Z_to_bv 8 0]; C1 (Z_to_bv 8 1); CB 6%nat [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in HW0; [| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity].
  apply (proj1 (rw_cells_app bsegs m _ [_] _)) in HW0 as [_ HW0]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in HW0.
  apply (proj1 (rw_cells_app bsegs m _ [_] _)) in HW0 as [HW0 _].
  rename HW0 into K0.
  exact K0.
Qed.

Lemma hf_verb : rw_cells bsegs m 1488664 [C4 (Z_to_bv 64 0)].
Proof.
  hcell 1488664 4%nat 0. rename HC into K0.
  exact K0.
Qed.

Lemma hs_stats : junk_at m 886432 32.
Proof.
  exists [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]. change (Z.to_nat 32) with 32%nat.
  apply (rw_cells_image0 bsegs m 886432 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
  intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 886400 886976); [vm_compute; reflexivity| lia].
Qed.

Lemma hs_bylog : junk_at m 886464 512.
Proof.
  exists [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]. change (Z.to_nat 512) with 512%nat.
  apply (rw_cells_image0 bsegs m 886464 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
  intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 886400 886976); [vm_compute; reflexivity| lia].
Qed.

Lemma hs_gstats : junk_at m 887000 16.
Proof.
  exists [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]. change (Z.to_nat 16) with 16%nat.
  apply (rw_cells_image0 bsegs m 887000 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]); [| vm_compute; reflexivity| lia| cbn; lia].
  intros a Ha. cbn [length] in Ha. replace a with (wa (bv_unsigned a)) by (unfold wa; apply Z_to_bv_bv_unsigned). apply (himg V m HMF 886980 887088); [vm_compute; reflexivity| lia].
Qed.

Lemma wr_at_sub0 : forall A n A' n', wr_at bsegs m A n -> A <= A' -> A' + n' <= A + n -> wr_at bsegs m A' n'.
Proof.
  intros A n A' n' (Ha & Hn & H) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
Qed.
Lemma zrun_of : forall A n A0 n0, (forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) -> wr_at bsegs m A0 n0 ->
  A0 <= A -> A + n <= A0 + n0 -> zrun m A n.
Proof. intros A n A0 n0 Z0 W H1 H2. split; [exact Z0| eapply wr_at_sub0; [exact W| lia| lia]]. Qed.

Lemma fake_zrun : zrun m (al_fake L + 96) 11571104.
Proof.
  hfact (ME.MZero (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 377)) (ME.ZLit 96)) 11571104) HZ.
  hfact (ME.MWr (ME.ZMul (ME.ZLit 4096) (ME.ZV 377)) 11571200) HW.
  rewrite al_fake_eq. eapply zrun_of; [exact HZ| exact HW| lia| lia].
Qed.
Lemma fake_sh_zrun : zrun m (shad (al_fake L)) (shlen FAKESZ).
Proof.
  hfact (ME.MZero (ME.ZAdd (ME.ZMul (ME.ZLit 512) (ME.ZV 377)) (ME.ZLit 2147450880)) 1446400) HZ.
  hfact (ME.MWr (ME.ZAdd (ME.ZMul (ME.ZLit 512) (ME.ZV 377)) (ME.ZLit 2147450880)) 1446400) HW.
  rewrite al_fake_eq, shad_div. unfold ASHOFF, FAKESZ, shlen. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  replace (2147450880 + 4096 * V 377%nat / 8) with (512 * V 377%nat + 2147450880) by (Z.div_mod_to_equations; lia).
  change (11571200 / 8) with 1446400. eapply zrun_of; [exact HZ| exact HW| lia| lia].
Qed.

Lemma afake_geom_main : afake_geom L.
Proof.
  unfold afake_geom. pose proof (ao_fake L ALO) as (F1 & F2 & F3 & F4 & F5). pose proof (ao_dtls L ALO) as (D1 & D2 & D3 & D4 & D5).
  pose proof (ao_t L ALO) as (T1 & T2 & T3 & T4 & T5).
  pose proof (ad_fake_dtls L ALO) as X1. pose proof (ad_t_dtls L ALO) as X2. pose proof (ad_t_fake L ALO) as X3. unfold adisj, FAKESZ in *.
  split; [exact F1|]. split.
  { unfold ablk, sclr, iclr, AIMG_LO, AIMG_HI, KLS in *. lia. }
  repeat (split; [tauto|]). tauto.
Qed.

Lemma afake_cells_main : afake_cells L m.
Proof.
  unfold afake_cells.
  split; [exact hf_tga|].
  split. { hfact (ME.MCell (ME.ZLit 6352448) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 377))) HC. rewrite al_fake_eq.
           apply (rw_cells_glue m _ 8 [_]); [exact hf_dtv| exact HC| reflexivity]. }
  split. { hfact (ME.MCell (ME.ZLit 6352456) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 310))) HC. unfold al_dtls. cbn [al_V L0 VL]. exact HC. }
  split; [exact hf_dtv1|].
  split. { hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 310)) (ME.ZLit 24)) 8%nat (ME.ZLit 6352448)) HC. unfold al_dtls. cbn [al_V L0 VL]. exact HC. }
  split; [exact hf_itga|]. split; [exact hf_verb|].
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 48)) 8%nat (ME.ZLit 6354296)) H48.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 56)) 8%nat (ME.ZLit 6354516)) H56.
  exists (cells_bytes [C8 (Z_to_bv 64 6354296); C8 (Z_to_bv 64 6354516)]). rewrite al_t_eq.
  apply (rw_cells_recast bsegs m _ [C8 (Z_to_bv 64 6354296); C8 (Z_to_bv 64 6354516)]); [| cbn; split; [reflexivity| exact I]| reflexivity| reflexivity].
  apply (rw_cells_glue m _ 8 [_]); [exact H48| | reflexivity].
  replace (4096 * V 227%nat + 56) with (4096 * V 227%nat + 48 + 8) in H56 by lia. exact H56.
Qed.

Theorem afake_main : AFAKE (gb := false) L [] m.
Proof.
  unfold AFAKE. split; [exact afake_geom_main|]. split; [exact afake_cells_main|].
  split. { hfact (ME.MZeroC (ME.ZMul (ME.ZLit 4096) (ME.ZV 377)) 88) HZ. rewrite al_fake_eq.
           exists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (ME.zeros 64).
           apply (rw_cells_recast bsegs m _ [CB (Z.to_nat 88) (ME.zeros 88)]); [exact HZ| cbn; repeat split; reflexivity| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity]. }
  split. { hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 377)) (ME.ZLit 88)) 8%nat (ME.ZLit 20)) HC. rewrite al_fake_eq. exact HC. }
  split. { cbn [gcbit]. apply zrun_cells; [cbn; tauto| reflexivity|]. cbn [cells_size csize Nat.add]. apply (zrun_sub _ _ _ _ _ fake_zrun); lia. }
  split. { exists (ME.zeros (FAKESZ - 4096)). apply zrun_CB; [| unfold FAKESZ; lia]. apply (zrun_sub _ _ _ _ _ fake_zrun); unfold FAKESZ; lia. }
  split. { exists (ME.zeros (shlen FAKESZ)). apply zrun_CB; [exact fake_sh_zrun| unfold FAKESZ, shlen; rewrite Z.shiftr_div_pow2 by lia; cbn; lia]. }
  split.
  { intros c pos b Hc Hp Hb NZ. exfalso. apply NZ. pose proof (fk_flag_range L c pos Hc Hp) as R.
    destruct fake_zrun as [Z0 _]. specialize (Z0 (fk_flag L c pos - (al_fake L + 96)) ltac:(lia)).
    replace (al_fake L + 96 + (fk_flag L c pos - (al_fake L + 96))) with (fk_flag L c pos) in Z0 by lia. congruence. }
  split; [intros c F n []|].
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 227)) (ME.ZLit 72)) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 377))) HC. rewrite al_t_eq, al_fake_eq. exact HC.
Qed.

Theorem aquar_main : AQUAR L sta X0 m.
Proof.
  exists qconc0. unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend qconc0 st0 ainit a_qloc a_qglob a_qloc_bytes a_qglob_bytes].
  split. { split; [exact hq_max| exact hq_mutex]. }
  split. { split; [| exact I]. cbn [length Z.of_nat qfirst qlast qaddrs map hd List.last]. unfold aq_tcache.
           apply zrun_cells; [cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity|]. cbn [cells_size csize Nat.add]. apply (zrun_sub _ _ _ _ _ THZ); lia. }
  split. { split; [| exact I]. cbn [length Z.of_nat qfirst qlast qaddrs map hd List.last]. exact hq_gcache. }
  split. { split; [exact hq_iaflag|]. split; [| intros X; discriminate X]. apply rw2_stk; unfold AIA_BASE, AIA_SIZE; lia. }
  split.
  { unfold qcoupled. cbn.
    split; [reflexivity|]. split; [reflexivity|]. split; [constructor|]. split; [constructor|]. split; [constructor|].
    split. { intros k. split; [intros []| intros (b & [] & _)]. }
    split. { intros c k. split; [intros []| intros (b & [] & _)]. }
    constructor. }
  unfold qnum. cbn. unfold Q_CACHE, Q_MAX.
  split; [reflexivity|]. split; [reflexivity|]. split; [constructor|]. lia.
Qed.

Lemma achunks_st0 : achunks sta = [].
Proof. unfold achunks. cbn [st0 ainit a_live a_qloc a_qglob app flat_map]. rewrite map_to_list_empty. reflexivity. Qed.
Lemma sec_chunks_st0 : sec_chunks_of sta = [].
Proof. unfold sec_chunks_of. rewrite achunks_st0. reflexivity. Qed.

Lemma asec_wf_main : asec_wf L sta [].
Proof.
  unfold asec_wf. split; [exact ALO|]. split; [reflexivity|]. cbn [st0 ainit a_nres a_nsec length Z.of_nat].
  split; [split; [reflexivity| lia]|]. split; [reflexivity|]. split; [lia|]. split; [constructor| exact sec_disjoint_nil].
Qed.

Lemma asec_arr_main : asec_arr L sta [] m.
Proof.
  unfold asec_arr. exists []. split; [apply Permutation_refl|]. cbn [map st0 ainit a_nsec a_nres].
  pose proof (ao_ptr L ALO) as (P1 & P2 & P3 & _). pose proof atop_range as AR.
  split. { change (@nil word) with (repeat (Z_to_bv 64 0) 0). apply zrun_u64arr. apply zrun0. lia. }
  split. { replace (al_ptr_array L + 8 * 0) with (al_ptr_array L) by lia. replace (8 * (0 - 0)) with 0 by lia. apply zrun_junk; [apply zrun0; lia| lia]. }
  intros [|i] ch H; discriminate H.
Qed.

Lemma asec_inst_main : asec_inst L m.
Proof.
  unfold asec_inst.
  split. { hfact (ME.MCell (ME.ZLit 886376) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 226))) HC. unfold al_ptr_array. cbn [al_V L0 VL]. exact HC. }
  split. { exists (Z_to_bv 8 0). exact hs_sorted. }
  split; [exact hs_stats|]. split; [exact hs_bylog|].
  split. { hfact (ME.MZeroC (ME.ZLit 886977) 3) HZ.
           apply (rw_cells_recast bsegs m _ [CB (Z.to_nat 3) (ME.zeros 3)]); [exact HZ| cbn; tauto| apply bytes_eq_unsigned; vm_compute; reflexivity| reflexivity]. }
  exact hs_gstats.
Qed.

Lemma ashz_main : ashz L [] m.
Proof.
  intros x Hx HH _. pose proof (ao_space L ALO) as SP. pose proof (ao_res_hi L ALO) as RH. pose proof atop_range as AR.
  pose proof HUSP as HU0. unfold usp_pin in HU0. pose proof (HV 0%nat) as B0. pose proof (HV 10%nat) as B10. pose proof (HV 6%nat) as B6.
  unfold astartup_hulls in HH. unfold al_store, al_nodes, al_fake, al_dtls, al_ctx, al_t, al_res, al_ptr_array in HH. cbn [al_V L0 VL] in HH.
  revert SP. rewrite al_res_eq, al_space_beg_eq. intros SP.
  apply Forall_cons_iff in HH as [U1 HH]. apply Forall_cons_iff in HH as [U2 HH]. apply Forall_cons_iff in HH as [U3 HH]. apply Forall_cons_iff in HH as [U4 HH].
  apply Forall_cons_iff in HH as [U5 HH]. apply Forall_cons_iff in HH as [U6 HH]. apply Forall_cons_iff in HH as [U7 HH]. apply Forall_cons_iff in HH as [U8 HH].
  apply Forall_cons_iff in HH as [U9 HH]. apply Forall_cons_iff in HH as [U10 HH]. apply Forall_cons_iff in HH as [U11 HH]. apply Forall_cons_iff in HH as [U12 HH].
  apply Forall_cons_iff in HH as [U13 _]. cbn [fst snd] in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13.
  unfold AIMG_HI, KLS, K_HIGH_MEM in Hx.
  destruct (Z_lt_ge_dec x (32768 * V 0%nat + 4096 * V 10%nat + -8388608)) as [LO|HI].
  - apply HSH0.
    + unfold MA.bshadow. rewrite shad_div. unfold ASHOFF. clear -Hx AR. Z.div_mod_to_equations. lia.
    + intros (bn & Hin & R). unfold MA.ASHOFF in R. rewrite shad_div in R. unfold ASHOFF in R.
      unfold MF.both_vis_app in Hin. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [fst snd ME.zv] in R.
      * clear -R U1. Z.div_mod_to_equations. lia.
      * clear -R U3. Z.div_mod_to_equations. lia.
      * clear -R U4. Z.div_mod_to_equations. lia.
      * clear -R U5. Z.div_mod_to_equations. lia.
      * clear -R U6. Z.div_mod_to_equations. lia.
      * clear -R U2. Z.div_mod_to_equations. lia.
      * clear -R U8. Z.div_mod_to_equations. lia.
      * clear -R U9. Z.div_mod_to_equations. lia.
      * clear -R U10 SP. Z.div_mod_to_equations. lia.
      * clear -R U11. Z.div_mod_to_equations. lia.
      * clear -R U12. Z.div_mod_to_equations. lia.
      * clear -R Hx. Z.div_mod_to_equations. lia.
      * clear -R LO B0 B10. Z.div_mod_to_equations. lia.
  - hfact (ME.MZeroS (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 0)) (ME.ZMul (ME.ZLit 512) (ME.ZV 10))) (ME.ZLit 2146402304))
                     (ME.ZAdd (ME.ZAdd (ME.ZMul (ME.ZLit (-4096)) (ME.ZV 0)) (ME.ZMul (ME.ZLit (-512)) (ME.ZV 10))) (ME.ZLit 17592187092992))) HZ.
    specialize (HZ (shad x - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))).
    replace (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (shad x - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))) with (shad x) in HZ by lia.
    apply HZ. rewrite shad_div. unfold ASHOFF. clear -Hx HI HU0 AR B0 B10 B6. Z.div_mod_to_equations. lia.
Qed.

Lemma aexh_main : AEXHc [] L sta m.
Proof.
  unfold AEXHc.
  split. { unfold exh_cells, F_ammap.TwinB.F_ammap.rmap_cells.
           split; [split; [exact (rt1 V m HMF)| split; [exact (rt19 V m HMF)| split; [exact (rt2 V m HMF)| split; [exact (rtb1 V m HMF)| exact (rtb2 V m HMF)]]]]|].
           split; [exact hx_toolname|]. split; [exact hx_cf64| exact hx_cb]. }
  split. { unfold emb_cells. cbn [st0 ainit a_emb Z.eqb]. unfold AEMB. split; [exact he_16|]. split; [exact he_0|]. split; [reflexivity| exact he_32]. }
  split. { intros c Hc NB. unfold axflag. replace (exh_mem c sta) with false by reflexivity. rewrite aregion_info_eq. unfold K_NUM_CLASSES in Hc.
           apply zrun_cells; [cbn; tauto| reflexivity|]. cbn [cells_size csize Nat.add]. apply (zrun_sub _ _ _ _ _ RIZ); lia. }
  split. { unfold emb_clrK. cbn [st0 ainit a_emb]. intros a Ha. lia. }
  unfold emb_clrC. cbn [st0 ainit a_emb]. left. reflexivity.
Qed.

Theorem asec_main : ASEC_of L sta X0 m.
Proof.
  unfold ASEC_of. rewrite sec_chunks_st0. unfold ASECc.
  split; [exact asec_wf_main|]. split; [exact asec_arr_main|]. split; [exact asec_inst_main|]. split; [exact aprim0_main|].
  split; [exact ashz_main| exact aexh_main].
Qed.

Lemma stk_of_wr : forall A n, wr_at bsegs m A n -> (forall a, A <= a < A + n -> exists b, mrd bsegs m (wa a) = Some b) -> stk bsegs m A (A + n).
Proof.
  intros A n (W1 & W2 & W3) R. split; [lia|]. split; [lia|]. intros a Ha. split; [| exact (R a Ha)].
  replace a with (A + (a - A)) by lia. apply W3. lia.
Qed.
Lemma zrun_mrd : forall A n a, zrun m A n -> A <= a < A + n -> exists b, mrd bsegs m (wa a) = Some b.
Proof.
  intros A n a [Z0 _] Ha. exists (Z_to_bv 8 0). unfold mrd. specialize (Z0 (a - A) ltac:(lia)). replace (A + (a - A)) with a in Z0 by lia. rewrite Z0. reflexivity.
Qed.
Lemma cells_mrd : forall A cs a, rw_cells bsegs m A cs -> A <= a < A + Z.of_nat (cells_size cs) -> exists b, mrd bsegs m (wa a) = Some b.
Proof.
  intros A cs a [[WF (B1 & B2 & B3)] _] Ha. pose proof (cells_bytes_length cs WF) as LEN.
  specialize (B3 (Z.to_nat (a - A)) ltac:(rewrite LEN; lia)). replace (A + Z.of_nat (Z.to_nat (a - A))) with a in B3 by lia.
  rewrite B3. destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. rewrite LEN in E. lia.
Qed.
Lemma zrun_stk : forall A n, zrun m A n -> stk bsegs m A (A + n).
Proof. intros A n ZR. apply stk_of_wr; [exact (proj2 ZR)| intros a Ha; exact (zrun_mrd A n a ZR Ha)]. Qed.

Lemma BUD_le_usum : forall Ul hs n, BUD Ul hs n <= usum Ul.
Proof. induction Ul as [|u Ul IH]; intros hs n; cbn [BUD usum fold_right]; [lia|]. unfold ucost. specialize (IH hs n). fold (usum Ul). destruct (has_hash hs n (hashU u)); lia. Qed.
Lemma CNT_le_len : forall Ul hs n, CNT Ul hs n <= Z.of_nat (length Ul).
Proof. induction Ul as [|u Ul IH]; intros hs n; cbn [CNT length]; [lia|]. specialize (IH hs n). destruct (has_hash hs n (hashU u)); lia. Qed.

Lemma dlayout_main : dlayout L.
Proof.
  unfold dlayout. pose proof (alayout_depot L ALO) as (_ & D2 & D3 & _ & D5 & D6 & _). pose proof (ao_nodes L ALO) as (N1 & _). pose proof (ao_store L ALO) as (ST1 & _).
  pose proof (ad_nodes_store L ALO) as NS. unfold adisj in NS. repeat (split; [assumption|]). exact NS.
Qed.

Section Depot.
Variables h tf BA : Z.
Hypothesis Hh : 0 <= h < 2 ^ 64.
Hypothesis Htf : 0 <= tf <= 3.
Hypothesis HBA : BA = TAB + 4 * bkt h.
Hypothesis Fh : rw_cells bsegs m (al_nodes L + 16) [C8 (Z_to_bv 64 h)].
Hypothesis Ftf8 : rw_cells bsegs m SSTF [C8 (Z_to_bv 64 tf)].
Hypothesis Ftf4 : rw_cells bsegs m SSST [C4 (Z_to_bv 64 tf)].
Hypothesis Fbkt : rw_cells bsegs m BA [C4 (Z_to_bv 64 1)].
Hypothesis Fimg1 : forall i, 0x1adb68 <= i < BA -> m (wa i) = None.
Hypothesis Fimg2 : forall i, BA + 4 <= i < 0x5bdb58 -> m (wa i) = None.
Hypothesis Fstore : stk bsegs m (al_store L) (al_store L + 8388608).

Definition D0 : dstate := mkD 1 (fun b => if b =? bkt h then 1 else 0) (fun _ => h) (fun _ => 0) (fun _ => 1) tf.

Lemma dwf_main : dwf (al_U L) D0.
Proof.
  unfold dwf, D0. cbn [dN dhd dhs dlk dsid dtf al_U L0]. pose proof HU as HU1. unfold univ_ok in HU1.
  assert (BK : 0 <= bkt h < 1048576) by (unfold bkt; apply Z.mod_pos_bound; lia).
  split; [lia|]. split; [intros i Hi; lia|].
  split. { intros b Hb. destruct (Z.eqb_spec b (bkt h)) as [->|NE]; [split; [lia| intros _; reflexivity]| split; [lia| intros X; exfalso; exact (X eq_refl)]]. }
  split. { intros i Hi. split; [exact Hh|]. split; [lia|]. intros X. exfalso. exact (X eq_refl). }
  split. { intros i Hi. rewrite Z.eqb_refl. assert (E : i = 1) by lia. subst i.
           rewrite (chain_cons (fun _ => 0) 1 1) by (try (intros j Hj); lia). left. reflexivity. }
  pose proof (BUD_le_usum U (fun _ => h) (Z.to_nat 1)) as B1. pose proof (CNT_le_len U (fun _ => h) (Z.to_nat 1)) as C1. lia.
Qed.

Lemma dcells_main : dcells L D0 m.
Proof.
  unfold dcells, D0. cbn [dN dhd dhs dlk dsid dtf].
  split; [exact Ftf8|].
  split. { hfact (ME.MCell (ME.ZLit 1760088) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 454))) HC. unfold SSPTR, al_store. cbn [al_V L0 VL]. exact HC. }
  split; [exact Ftf4|]. split; [exact hd_nuniq|].
  split. { hfact (ME.MCell (ME.ZLit 6019944) 8%nat (ME.ZMul (ME.ZLit 4096) (ME.ZV 453))) HC. unfold MAP1, al_nodes. cbn [al_V L0 VL]. exact HC. }
  assert (BK : 0 <= bkt h < 1048576) by (unfold bkt; apply Z.mod_pos_bound; lia).
  split.
  { intros b Hb. destruct (Z.eqb_spec b (bkt h)) as [->|NE]; [rewrite <- HBA; exact Fbkt|]. unfold TAB in *.
    apply rw_cells_bss0_as; [unfold BSS0_LO; lia| unfold BSS0_HI; cbn [cells_size csize Nat.add]; lia| cbn; tauto| reflexivity|].
    cbn [cells_size csize Nat.add]. intros i Hi. destruct (Z_lt_ge_dec b (bkt h)); [apply Fimg1; lia| apply Fimg2; lia]. }
  split.
  { intros i Hi. assert (E : i = 1) by lia. subst i.
    hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 453)) (ME.ZLit 24)) 4%nat (ME.ZLit 0)) H24.
    hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 453)) (ME.ZLit 28)) 4%nat (ME.ZLit 1)) H28.
    revert Fh. unfold al_nodes. cbn [al_V L0 VL]. intros Fh0. replace (4096 * V 453%nat + 16 * 1) with (4096 * V 453%nat + 16) by lia.
    apply (rw_cells_glue m _ 8 [_]); [exact Fh0| | reflexivity]. replace (4096 * V 453%nat + 16 + 8) with (4096 * V 453%nat + 24) by lia.
    apply (rw_cells_glue m _ 4 [_]); [exact H24| | reflexivity]. replace (4096 * V 453%nat + 24 + 4) with (4096 * V 453%nat + 28) by lia. exact H28. }
  split; [| exact Fstore].
  hfact (ME.MZero (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 453)) (ME.ZLit 32)) 1048544) HZ.
  hfact (ME.MWr (ME.ZMul (ME.ZLit 4096) (ME.ZV 453)) 1048576) HW.
  unfold al_nodes. cbn [al_V L0 VL]. replace (4096 * V 453%nat + 16 * (1 + 1)) with (4096 * V 453%nat + 32) by lia.
  replace (4096 * V 453%nat + 1048576) with (4096 * V 453%nat + 32 + 1048544) by lia.
  apply zrun_stk. eapply zrun_of; [exact HZ| exact HW| lia| lia].
Qed.

Lemma adepot_gen : ADEPOTi L m.
Proof. exists D0. split; [exact dwf_main|]. split; [exact dcells_main| exact dlayout_main]. Qed.
End Depot.

Lemma store_stk : stk bsegs m (al_store L) (al_store L + 8388608).
Proof.
  hfact (ME.MWr (ME.ZMul (ME.ZLit 4096) (ME.ZV 454)) 8388608) HW.
  hfact (ME.MCell (ME.ZAdd (ME.ZMul (ME.ZLit 4096) (ME.ZV 454)) (ME.ZLit 8)) 8%nat (ME.ZLit 305796)) H8.
  unfold al_store. cbn [al_V L0 VL]. apply stk_of_wr; [exact HW|]. intros a Ha.
  assert (Ew : w = true \/ w = false) by (destruct w; auto).
  destruct Ew as [Ew|Ew]; pose proof HMFw as HMW; rewrite Ew in HMW.
  - pose proof (ME.mfacts_nth bsegs V m _ 6 _ HMW eq_refl) as H0. pose proof (ME.mfacts_nth bsegs V m _ 7 _ HMW eq_refl) as H16.
    pose proof (ME.mfacts_nth bsegs V m _ 8 _ HMW eq_refl) as HZ. cbn [ME.mfact_ok ME.zv ME.cellw] in H0, H16, HZ.
    destruct (Z_lt_ge_dec a (4096 * V 454%nat + 8)); [apply (cells_mrd _ _ a H0); cbn; lia|].
    destruct (Z_lt_ge_dec a (4096 * V 454%nat + 16)); [apply (cells_mrd _ _ a H8); cbn; lia|].
    destruct (Z_lt_ge_dec a (4096 * V 454%nat + 24)); [apply (cells_mrd _ _ a H16); cbn; lia|].
    exists (Z_to_bv 8 0). unfold mrd. specialize (HZ (a - (4096 * V 454%nat + 24)) ltac:(lia)).
    replace (4096 * V 454%nat + 24 + (a - (4096 * V 454%nat + 24))) with a in HZ by lia. rewrite HZ. reflexivity.
  - pose proof (ME.mfacts_nth bsegs V m _ 6 _ HMW eq_refl) as H0. pose proof (ME.mfacts_nth bsegs V m _ 7 _ HMW eq_refl) as HZ.
    cbn [ME.mfact_ok ME.zv ME.cellw] in H0, HZ.
    destruct (Z_lt_ge_dec a (4096 * V 454%nat + 8)); [apply (cells_mrd _ _ a H0); cbn; lia|].
    destruct (Z_lt_ge_dec a (4096 * V 454%nat + 16)); [apply (cells_mrd _ _ a H8); cbn; lia|].
    exists (Z_to_bv 8 0). unfold mrd. specialize (HZ (a - (4096 * V 454%nat + 16)) ltac:(lia)).
    replace (4096 * V 454%nat + 16 + (a - (4096 * V 454%nat + 16))) with a in HZ by lia. rewrite HZ. reflexivity.
Qed.

Theorem adepot_main : ADEPOTi L m.
Proof.
  assert (Ew : w = true \/ w = false) by (destruct w; auto).
  destruct Ew as [Ew|Ew]; pose proof HMFw as HW; rewrite Ew in HW.
  - pose proof (ME.mfacts_nth bsegs V m _ 0 _ HW eq_refl) as F0. pose proof (ME.mfacts_nth bsegs V m _ 1 _ HW eq_refl) as F1.
    pose proof (ME.mfacts_nth bsegs V m _ 2 _ HW eq_refl) as F2. pose proof (ME.mfacts_nth bsegs V m _ 3 _ HW eq_refl) as F3.
    pose proof (ME.mfacts_nth bsegs V m _ 4 _ HW eq_refl) as F4. pose proof (ME.mfacts_nth bsegs V m _ 5 _ HW eq_refl) as F5.
    cbn [ME.mfact_ok ME.zv ME.cellw] in F0, F1, F2, F3, F4, F5.
    apply (adepot_gen 4995340661115012345 3 2682684); try assumption.
    + lia. + lia. + reflexivity.
    + exact store_stk.
  - pose proof (ME.mfacts_nth bsegs V m _ 0 _ HW eq_refl) as F0. pose proof (ME.mfacts_nth bsegs V m _ 1 _ HW eq_refl) as F1.
    pose proof (ME.mfacts_nth bsegs V m _ 2 _ HW eq_refl) as F2. pose proof (ME.mfacts_nth bsegs V m _ 3 _ HW eq_refl) as F3.
    pose proof (ME.mfacts_nth bsegs V m _ 4 _ HW eq_refl) as F4. pose proof (ME.mfacts_nth bsegs V m _ 5 _ HW eq_refl) as F5.
    cbn [ME.mfact_ok ME.zv ME.cellw] in F0, F1, F2, F3, F4, F5.
    apply (adepot_gen 3212005880834824158 2 1850064); try assumption.
    + lia. + lia. + reflexivity.
    + exact store_stk.
Qed.

Theorem arep_main : AREP (AHI (gb := false)) L sta X0 m.
Proof.
  unfold AREP. cbn [AHI ah_quar ah_sec ah_depot].
  split; [exact awf_main|]. split; [exact (arep_rt_main V w U m HMF)|]. split; [exact (ainstance_main V w U m HMF)|].
  split; [exact (athread_main V w U m HMF HPF)|].
  split. { intros c Hc. split; [exact (aregion_cells_main c Hc)|]. split; [exact (afreearray_main c Hc)|]. split; [exact (aslots_main c Hc)| exact (aslot_shadow_main c Hc)]. }
  split; [exact aquar_main|]. split; [exact asec_main|]. split; [exact adepot_main|].
  split; [exact (arelro_main V m HMF)|]. split; [exact (arep_rt2_main V m HMF)|].
  split; [exact ashadow_avail_main| exact (arep_rt3_main V m HMF)].
Qed.

Definition arng0 (Lx : alayout) (RNG : footprint) : Prop :=
     rng RNG 0x10000 0x621000
  /\ rng RNG (al_t Lx) 4096 /\ rng RNG (al_ctx Lx) 65536 /\ rng RNG (al_nodes Lx) 1048576 /\ rng RNG (al_store Lx) 8388608
  /\ rng RNG (al_space_beg Lx + K_SPACE_SIZE) K_SPACE_EXTRA
  /\ rng RNG (al_fake Lx) 11571200 /\ rng RNG (shad (al_fake Lx)) (shlen 11571200) /\ rng RNG (al_dtls Lx) 4096
  /\ rng RNG (shad (al_space_beg Lx)) (shlen K_SPACE_SIZE).

Lemma rng0 : forall lz AL A, 0 <= A <= 2 ^ 64 -> rng (fp_ok lz AL) A 0.
Proof. intros lz AL A HA. split; [lia|]. split; [lia|]. intros b j Hb Hj k Hk. lia. Qed.

Lemma arng_main : forall lz AL, arng0 L (fp_ok lz AL) -> arng L (fp_ok lz AL) sta.
Proof.
  intros lz AL (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10). unfold arng.
  pose proof space_facts as (S1 & S2 & S3 & S4). pose proof (ao_ptr L ALO) as (P1 & P2 & P3 & _). pose proof atop_range as AR.
  unfold K_SPACE_SIZE, K_SPACE_EXTRA in S2.
  repeat (split; [assumption|]).
  split.
  { intros c Hc. rewrite get_cls_st0. cbn [c_mapped_user c_mapped_free_array aclass0]. rewrite shlen_0. unfold K_NUM_CLASSES in Hc.
    assert (B : 0 <= aregion L c /\ afreearr L c + 0 <= 2 ^ 64 /\ aregion L c <= afreearr L c) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; nia).
    split; [apply rng0; lia|]. split; [apply rng0; rewrite shad_div; unfold ASHOFF; clear -B; Z.div_mod_to_equations; lia|].
    split; [apply rng0; lia|]. apply rng0; rewrite shad_div; unfold ASHOFF; clear -B; Z.div_mod_to_equations; lia. }
  split. { cbn [st0 ainit a_nres]. replace (8 * 0) with 0 by lia. apply rng0. lia. }
  split; [rewrite sec_chunks_st0; constructor| exact R10].
Qed.

Theorem aheapP_main : forall lz AL, arng0 L (fp_ok lz AL) -> AHEAP_P (AHI (gb := false)) L (fp_ok lz AL) sta [] m.
Proof.
  intros lz AL R. split; [exact ALO|]. split; [exact (arng_main lz AL R)|].
  split; [exists X0; split; [exact arep_main| exact ablocks_main]|]. cbn [AHI ah_fake]. exact afake_main.
Qed.

Theorem aheapu2_main : forall lz AL, arng0 L (fp_ok lz AL) -> AHEAPu2 L (fp_ok lz AL) sta [] m.
Proof.
  intros lz AL R. exists ov0. split; [exists false; exact (aheapP_main lz AL R)|]. intros q Hq. exfalso. exact (Hq eq_refl).
Qed.

Lemma aprist_main : APristLaw.TwinB.aprist sta.
Proof. intros c Hc NB. rewrite get_cls_st0. split; reflexivity. Qed.
Lemma al_U_main : al_U L = U. Proof. reflexivity. Qed.
Lemma a_space_beg_main : a_space_beg sta = al_space_beg L /\ a_ptr_array sta = al_ptr_array L. Proof. split; reflexivity. Qed.

End AtMain2.
End TwinB.
