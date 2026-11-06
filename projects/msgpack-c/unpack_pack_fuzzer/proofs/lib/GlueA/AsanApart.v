(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AInstanceM AInstanceU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2 AInstanceU2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import AsanImgx.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require AsanRun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RootAsan2 RootAsanN.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Module R2 := RootAsan2.RootAsan2.
Module RN := RootAsanN.RootAsanN.

Fixpoint covers (lo hi : Z) (l : list (Z * Z)) : bool :=
  match l with
  | [] => hi <=? lo
  | (a, b) :: t => (a <=? lo) && covers (Z.max lo b) hi t
  end.
Lemma covers_spec : forall l lo hi, covers lo hi l = true -> forall x, lo <= x < hi -> exists v, In v l /\ fst v <= x < snd v.
Proof.
  induction l as [|[a b] t IH]; intros lo hi H x Hx; cbn [covers] in H.
  - apply Z.leb_le in H. lia.
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
    destruct (Z_lt_le_dec x b) as [L|G].
    + exists (a, b). split; [left; reflexivity| cbn [fst snd]; lia].
    + destruct (IH (Z.max lo b) hi H2 x ltac:(lia)) as (v & Hv & R). exists v. split; [right; exact Hv| exact R].
Qed.

Fixpoint ins (v : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => [v]
  | w :: t => if fst v <=? fst w then v :: l else w :: ins v t
  end.
Definition sortiv (l : list (Z * Z)) : list (Z * Z) := fold_right ins [] l.
Lemma ins_in : forall v l w, In w (ins v l) -> w = v \/ In w l.
Proof.
  induction l as [|u t IH]; intros w H; cbn [ins] in H.
  - destruct H as [<-|[]]. left; reflexivity.
  - destruct (fst v <=? fst u).
    + destruct H as [<-|H]; [left; reflexivity| right; exact H].
    + destruct H as [<-|H]; [right; left; reflexivity|]. destruct (IH w H) as [->|H']; [left; reflexivity| right; right; exact H'].
Qed.
Lemma sortiv_in : forall l w, In w (sortiv l) -> In w l.
Proof.
  induction l as [|u t IH]; intros w H; cbn [sortiv fold_right] in H; [exact H|].
  change (fold_right ins [] t) with (sortiv t) in H.
  destruct (ins_in u (sortiv t) w H) as [->|H']; [left; reflexivity| right; exact (IH w H')].
Qed.

Definition privZ (P : list (int * int)) : list (Z * Z) := map (fun p => (to_Z (fst p), to_Z (snd p))) P.
Lemma privZ_in_priv : forall P v x, In v (privZ P) -> fst v <= x < snd v -> OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.St.in_priv P x.
Proof.
  intros P v x Hv Hx. unfold privZ in Hv. apply in_map_iff in Hv as (p & <- & Hp). cbn [fst snd] in Hx.
  unfold OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.St.in_priv. apply Exists_exists. exists p. split; [exact Hp| exact Hx].
Qed.

Lemma img_range : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> 0x10000 <= a < 0x62f000.
Proof.
  intros a [seg Hs]. split.
  - apply (AsanRun.find_segment_lo asegs a 1 seg 0x10000); [vm_compute; reflexivity| exact Hs].
  - destruct (Z_lt_le_dec a 0x62f000) as [L|G]; [exact L|]. exfalso. rewrite (UnreggPre.no_seg_above a G) in Hs. discriminate Hs.
Qed.

Section Apart.
Context {rc : runConstT}.

Lemma apart_of_cover : forall (P : list (int * int)),
  covers 0x10000 0x62f000 (sortiv (aci_I ++ privZ P)) = true ->
  forall a, (exists seg, find_segment asegs a 1 = Some seg) -> ~ in_ivs IMGX_A a -> OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.St.in_priv P a.
Proof.
  intros P COV a SEG NX. pose proof (img_range a SEG) as R.
  destruct (covers_spec _ _ _ COV a R) as (v & Hv & Hx). apply sortiv_in in Hv. apply in_app_or in Hv as [Hv|Hv].
  - exfalso. apply NX. exact (in_aci_img v a Hv Hx).
  - exact (privZ_in_priv P v a Hv Hx).
Qed.

Lemma cover2 : covers 0x10000 0x62f000 (sortiv (aci_I ++ privZ R2.PRIV)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma coverN : covers 0x10000 0x62f000 (sortiv (aci_I ++ privZ RN.PRIV)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem IMGX_A_apart2 : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> ~ in_ivs IMGX_A a ->
  OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.St.in_priv R2.PRIV a.
Proof. exact (apart_of_cover R2.PRIV cover2). Qed.
Theorem IMGX_A_apartN : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> ~ in_ivs IMGX_A a ->
  OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.St.in_priv RN.PRIV a.
Proof. exact (apart_of_cover RN.PRIV coverN). Qed.
End Apart.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RootBoth2 RootBothN.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AInstanceM.TwinB AInstanceU.TwinB.
Import AMalloc_iface2.TwinB AInstanceU2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import Ledger.TwinB Op.TwinB.
Import AsanImgx.TwinB.

Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Module R2 := RootBoth2.RootBoth2.
Module RN := RootBothN.RootBothN.

Fixpoint covers (lo hi : Z) (l : list (Z * Z)) : bool :=
  match l with
  | [] => hi <=? lo
  | (a, b) :: t => (a <=? lo) && covers (Z.max lo b) hi t
  end.
Lemma covers_spec : forall l lo hi, covers lo hi l = true -> forall x, lo <= x < hi -> exists v, In v l /\ fst v <= x < snd v.
Proof.
  induction l as [|[a b] t IH]; intros lo hi H x Hx; cbn [covers] in H.
  - apply Z.leb_le in H. lia.
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
    destruct (Z_lt_le_dec x b) as [L|G].
    + exists (a, b). split; [left; reflexivity| cbn [fst snd]; lia].
    + destruct (IH (Z.max lo b) hi H2 x ltac:(lia)) as (v & Hv & R). exists v. split; [right; exact Hv| exact R].
Qed.

Fixpoint ins (v : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => [v]
  | w :: t => if fst v <=? fst w then v :: l else w :: ins v t
  end.
Definition sortiv (l : list (Z * Z)) : list (Z * Z) := fold_right ins [] l.
Lemma ins_in : forall v l w, In w (ins v l) -> w = v \/ In w l.
Proof.
  induction l as [|u t IH]; intros w H; cbn [ins] in H.
  - destruct H as [<-|[]]. left; reflexivity.
  - destruct (fst v <=? fst u).
    + destruct H as [<-|H]; [left; reflexivity| right; exact H].
    + destruct H as [<-|H]; [right; left; reflexivity|]. destruct (IH w H) as [->|H']; [left; reflexivity| right; right; exact H'].
Qed.
Lemma sortiv_in : forall l w, In w (sortiv l) -> In w l.
Proof.
  induction l as [|u t IH]; intros w H; cbn [sortiv fold_right] in H; [exact H|].
  change (fold_right ins [] t) with (sortiv t) in H.
  destruct (ins_in u (sortiv t) w H) as [->|H']; [left; reflexivity| right; exact (IH w H')].
Qed.

Definition privZ (P : list (int * int)) : list (Z * Z) := map (fun p => (to_Z (fst p), to_Z (snd p))) P.
Lemma privZ_in_priv : forall P v x, In v (privZ P) -> fst v <= x < snd v -> OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.St.in_priv P x.
Proof.
  intros P v x Hv Hx. unfold privZ in Hv. apply in_map_iff in Hv as (p & <- & Hp). cbn [fst snd] in Hx.
  unfold OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.St.in_priv. apply Exists_exists. exists p. split; [exact Hp| exact Hx].
Qed.

Lemma img_range : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> 0x10000 <= a < 0x631000.
Proof.
  intros a [seg Hs]. split.
  - apply (AsanRun.TwinB.find_segment_lo bsegs a 1 seg 0x10000); [vm_compute; reflexivity| exact Hs].
  - destruct (Z_lt_le_dec a 0x631000) as [L|G]; [exact L|]. exfalso. rewrite (UnreggPre.TwinB.no_seg_above a G) in Hs. discriminate Hs.
Qed.

Section Apart.
Context {rc : runConstT}.

Lemma apart_of_cover : forall (P : list (int * int)),
  covers 0x10000 0x631000 (sortiv (aci_I ++ privZ P)) = true ->
  forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> ~ in_ivs IMGX_A a -> OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.St.in_priv P a.
Proof.
  intros P COV a SEG NX. pose proof (img_range a SEG) as R.
  destruct (covers_spec _ _ _ COV a R) as (v & Hv & Hx). apply sortiv_in in Hv. apply in_app_or in Hv as [Hv|Hv].
  - exfalso. apply NX. exact (in_aci_img v a Hv Hx).
  - exact (privZ_in_priv P v a Hv Hx).
Qed.

Lemma cover2 : covers 0x10000 0x631000 (sortiv (aci_I ++ privZ R2.PRIV)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma coverN : covers 0x10000 0x631000 (sortiv (aci_I ++ privZ RN.PRIV)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem IMGX_A_apart2 : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> ~ in_ivs IMGX_A a ->
  OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.St.in_priv R2.PRIV a.
Proof. exact (apart_of_cover R2.PRIV cover2). Qed.
Theorem IMGX_A_apartN : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> ~ in_ivs IMGX_A a ->
  OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.St.in_priv RN.PRIV a.
Proof. exact (apart_of_cover RN.PRIV coverN). Qed.
End Apart.
End TwinB.
