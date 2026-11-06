(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem State MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem St MemP UB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module TR.

Fixpoint obj_bodies (o : obj) : list (Z * Z) :=
  match o with
  | OStr p n | OBin p n => if p =? 0 then [] else [(p, n)]
  | OExt p n => [(p, n + 1)]
  | OArr _ kids | OMap _ kids =>
      (fix bs (l : list obj) : list (Z * Z) := match l with [] => [] | o' :: l' => obj_bodies o' ++ bs l' end) kids
  | _ => []
  end.
Definition objs_bodies (l : list obj) : list (Z * Z) := flat_map obj_bodies l.
Lemma obj_bodies_kids : forall kids,
  (fix bs (l : list obj) : list (Z * Z) := match l with [] => [] | o' :: l' => obj_bodies o' ++ bs l' end) kids = objs_bodies kids.
Proof. induction kids as [|o l IH]; [reflexivity|]. cbn [objs_bodies flat_map]. rewrite IH. reflexivity. Qed.
Lemma obj_bodies_arr : forall p kids, obj_bodies (OArr p kids) = objs_bodies kids.
Proof. intros. cbn [obj_bodies]. apply obj_bodies_kids. Qed.
Lemma obj_bodies_map : forall p kids, obj_bodies (OMap p kids) = objs_bodies kids.
Proof. intros. cbn [obj_bodies]. apply obj_bodies_kids. Qed.

Definition range_ok (z : zoneg) (ls : list level) (r : Z * Z) : Prop :=
  0 <= snd r /\ in_alloc z (fst r) (snd r) /\ forall l, In l ls -> rdisj (fst r) (snd r) (lv_slot l) (lv_unfilled l).
Definition bodies_ok (z : zoneg) (ls : list level) (o : obj) : Prop := Forall (range_ok z ls) (obj_bodies o).

Definition completed_ok (bm : bmem) (z : zoneg) (ls : list level) : Prop :=
  forall l, In l ls -> forall i, 0 <= i < lv_k l ->
    exists o, tree_at bm z (lv_P l + OBJ_SIZE * i) o /\
              (forall c, In c (obj_cells (lv_P l + OBJ_SIZE * i) o) -> Inv.cell_ok z ls c) /\ bodies_ok z ls o.

Lemma completed_ok_wf : forall bm z ls, completed_ok bm z ls -> completed_wf bm z ls.
Proof. intros bm z ls H l Hl i Hi. destruct (H l Hl i Hi) as (o & A & B & _). eauto. Qed.

Definition hdr_at (bm : bmem) (a : Z) (o : obj) : Prop :=
  u32_at bm a (obj_type o) /\
  match o with
  | ONil => True
  | OBool b => u8_at bm (a + 8) (if b then 1 else 0)
  | OPos u => u64_at bm (a + 8) u
  | ONeg i => u64_at bm (a + 8) (enc64 i)
  | OF32 bits => u64_at bm (a + 8) bits
  | OF64 bits => u64_at bm (a + 8) bits
  | OStr p n | OBin p n | OExt p n => u32_at bm (a + 8) n /\ u64_at bm (a + 16) p
  | OArr p kids => u32_at bm (a + 8) (Z.of_nat (length kids)) /\ u64_at bm (a + 16) p
  | OMap p kids => u32_at bm (a + 8) (Z.of_nat (length kids) / 2) /\ u64_at bm (a + 16) p
  end.
Definition kids_at (bm : bmem) (o : obj) : Prop :=
  match o with OArr p kids | OMap p kids => objs_at bm p kids | _ => True end.

Lemma obj_at_split : forall bm a o, obj_at bm a o <-> hdr_at bm a o /\ kids_at bm o.
Proof.
  intros bm a o. destruct o; first [rewrite obj_at_arr | rewrite obj_at_map | idtac]; unfold hdr_at, kids_at; cbn [obj_at obj_type]; tauto.
Qed.

Lemma kids_at_frame : forall m m' a o,
  (forall c, In c (tl (obj_cells a o)) -> agree_on m m' c OBJ_SIZE) -> kids_at m o -> kids_at m' o.
Proof.
  intros m m' a o AG K. destruct o; unfold kids_at in *; try exact I.
  all: first [rewrite obj_cells_arr in AG| rewrite obj_cells_map in AG]; cbn [tl] in AG;
    apply objs_at_nth; intros i o Hi; apply (obj_at_frame m m'); [| exact (proj1 (objs_at_nth _ _ _) K i o Hi)];
    intros c Hc; apply AG; apply in_kids_cells; eauto.
Qed.

Lemma readable_agree : forall (m m' : bmem) a n, agree_on m m' a (Z.of_nat n) -> readable m a n -> readable m' a n.
Proof. intros m m' a n A [v Hv]. exists v. rewrite (rdZ_agree m m' a n A). exact Hv. Qed.

Lemma removelast_snoc : forall {A} (l : list A) x, removelast (l ++ [x]) = l.
Proof. intros A l x. unfold removelast. rewrite rev_app_distr. cbn. apply rev_involutive. Qed.
Lemma removelast_nil : forall {A}, removelast (@nil A) = [].
Proof. reflexivity. Qed.

Lemma tree_wf_agree : forall (m m' : bmem) z o,
  (forall b, In b (obj_bodies o) -> agree_on m m' (fst b) (snd b)) -> tree_wf m z o -> tree_wf m' z o.
Proof.
  intros m m' z. apply (obj_ind_size (fun o => (forall b, In b (obj_bodies o) -> agree_on m m' (fst b) (snd b)) -> tree_wf m z o -> tree_wf m' z o)).
  intros o IH AG H. destruct o; try exact H.
  -   cbn [tree_wf] in H |- *. destruct H as (A & B & C). split; [exact A|]. split; [exact B|].
    intros Hp. destruct (C Hp) as [C1 C2]. split; [exact C1|].
    eapply readable_agree; [|exact C2]. rewrite Z2Nat.id by lia. apply (AG (p, n)). cbn [obj_bodies].
    destruct (Z.eqb_spec p 0); [contradiction| left; reflexivity].
  -   cbn [tree_wf] in H |- *. destruct H as (A & B & C). split; [exact A|]. split; [exact B|].
    intros Hp. destruct (C Hp) as [C1 C2]. split; [exact C1|].
    eapply readable_agree; [|exact C2]. rewrite Z2Nat.id by lia. apply (AG (p, n)). cbn [obj_bodies].
    destruct (Z.eqb_spec p 0); [contradiction| left; reflexivity].
  -   cbn [tree_wf] in H |- *. destruct H as (A & B & C & D & E). repeat split; try assumption.
    eapply readable_agree; [|exact E]. rewrite Z2Nat.id by lia. apply (AG (p, n + 1)). cbn [obj_bodies]. left; reflexivity.
  -   apply tree_wf_arr in H. apply tree_wf_arr. destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    apply trees_wf_forall. intros k Hk. apply IH.
    + rewrite obj_size_arr. pose proof (in_kids_size k kids Hk). lia.
    + intros b Hb. apply AG. rewrite obj_bodies_arr. unfold objs_bodies. apply in_flat_map. eauto.
    + exact (proj1 (trees_wf_forall _ _ _) H4 k Hk).
  -   apply tree_wf_map in H. apply tree_wf_map. destruct H as (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|].
    split; [exact H2|]. split; [exact H3|].
    apply trees_wf_forall. intros k Hk. apply IH.
    + rewrite obj_size_map. pose proof (in_kids_size k kids Hk). lia.
    + intros b Hb. apply AG. rewrite obj_bodies_map. unfold objs_bodies. apply in_flat_map. eauto.
    + exact (proj1 (trees_wf_forall _ _ _) H4 k Hk).
Qed.

Lemma tree_at_agree : forall (m m' : bmem) z a o,
  (forall c, In c (obj_cells a o) -> agree_on m m' c OBJ_SIZE) ->
  (forall b, In b (obj_bodies o) -> agree_on m m' (fst b) (snd b)) ->
  tree_at m z a o -> tree_at m' z a o.
Proof.
  intros m m' z a o AC AB [H1 H2]. split; [eapply obj_at_frame; eauto| eapply tree_wf_agree; eauto].
Qed.

Definition obj_cnt (o : obj) : Z :=
  match o with
  | OArr _ kids => Z.of_nat (length kids)
  | OMap _ kids => Z.of_nat (length kids) / 2
  | OStr _ n | OBin _ n | OExt _ n => n
  | _ => 0
  end.

End TR.
