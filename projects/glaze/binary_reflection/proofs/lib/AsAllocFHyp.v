(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDepotImg.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Import OSSVerify.glaze.binary_reflection.images.Asan.
   (* [comment removed for export] *)
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.

Fixpoint rwseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match find_segment segs (U a) 1 with
      | Some seg =>
          (seg_readable seg && seg_writable seg
           && match segment_byte_at (seg_bytes seg) (Z.to_N (U a - Z.of_N (seg_base seg))) with Some _ => true | None => false end
           && rwseg_ok segs (a + 1)%bv n')%bool
      | None => false
      end
  end.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma rwseg_head : forall segs (a : word) n (m : word -> option byte), rwseg_ok segs a (S n) = true ->
  (exists b, rdn segs m a 1 = Some [b]) /\ wview segs m a <> None /\ rwseg_ok segs (a + 1)%bv n = true.
Proof using.
  intros segs a n m H. cbn [rwseg_ok] in H.
  destruct (find_segment segs (U a) 1) as [seg|] eqn:Hseg; [|discriminate].
  apply andb_true_iff in H as [H Hrec]. apply andb_true_iff in H as [H Hbyte]. apply andb_true_iff in H as [Hrd Hwr].
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (U a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb; [|discriminate].
  split; [|split; [|exact Hrec]].
  - (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). destruct (m a) as [b0|]; [wd_eexists; reflexivity|].
    (lazymatch goal with |- ?G => let G' := eval unfold seg_rom, memory_read in G in change_no_check G' end). change (Z.of_N 1) with 1. rewrite Hseg, Hrd. change (N.to_nat 1) with 1%nat. (lazymatch goal with |- ?G => let G' := eval cbn [segment_read_bytes] in G in change_no_check G' end).
    rewrite Hb. wd_eexists; reflexivity.
  - (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (m a) as [b0|]; [discriminate|]. rewrite Hseg, Hwr, Hb. discriminate.
Qed.

Lemma rwseg_byte : forall segs n (a : word) (m : word -> option byte), rwseg_ok segs a n = true -> (U a + Z.of_nat n <= 2 ^ 64) ->
  forall x : word, U a <= U x < U a + Z.of_nat n -> (exists b, rdn segs m x 1 = Some [b]) /\ wview segs m x <> None.
Proof using.
  intros segs n. induction n as [|n IH]; intros a m H Hnw x Hx; [lia|].
  destruct (rwseg_head segs a n m H) as (Hr & Hw & Hrec).
  destruct (Z.eq_dec (U x) (U a)) as [E|NE].
  - apply bv_eq in E. subst x. split; assumption.
  - pose proof (u64_range a). pose proof (u64_range x).
    assert (Ua1 : U (a + 1)%bv = U a + 1) by (apply u_add1; lia).
    apply (IH (a + 1)%bv m Hrec); rewrite ?Ua1; lia.
Qed.

Lemma rdn_of_bytes : forall segs (m : word -> option byte) n (a : word), (U a + Z.of_nat n <= 2 ^ 64) ->
  (forall x : word, U a <= U x < U a + Z.of_nat n -> exists b, rdn segs m x 1 = Some [b]) ->
  exists bs, rdn segs m a n = Some bs /\ length bs = n.
Proof using.
  intros segs m n. induction n as [|n IH]; intros a Hnw Hall; [exists []; split; reflexivity|].
  pose proof (u64_range a). destruct (Hall a ltac:(lia)) as [b Hb].
  destruct n as [|n'].
  - exists [b]. split; [exact Hb | reflexivity].
  - assert (Ua1 : U (a + 1)%bv = U a + 1) by (apply u_add1; lia).
    destruct (IH (a + 1)%bv ltac:(rewrite Ua1; lia)) as [r [Hr Hl]].
    { intros x Hx. apply Hall. rewrite Ua1 in Hx. lia. }
    cbn [rdn] in Hb |- *. cbn [rdn] in Hr.
    destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate Hb].
    injection Hb as ->. rewrite Hr. exists (b :: r). split; [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite Hl; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma rwseg_rdn : forall segs N (lo : word) (m : word -> option byte) (a : word) n, rwseg_ok segs lo N = true -> (U lo + Z.of_nat N <= 2 ^ 64) ->
  U lo <= U a -> U a + Z.of_nat n <= U lo + Z.of_nat N -> exists bs, rdn segs m a n = Some bs /\ length bs = n.
Proof using.
  intros segs N lo m a n H Hnw H1 H2. apply rdn_of_bytes; [lia|].
  intros x Hx. apply (rwseg_byte segs N lo m H Hnw x). lia.
Qed.
Lemma rwseg_store_ok : forall segs N (lo : word) (m : word -> option byte) (a : word) n, rwseg_ok segs lo N = true -> (U lo + Z.of_nat N <= 2 ^ 64) ->
  U lo <= U a -> U a + Z.of_nat n <= U lo + Z.of_nat N -> store_ok segs m a n = true.
Proof using.
  intros segs N lo m a n H Hnw H1 H2. apply store_ok_of_all; [lia|].
  intros x Hx. apply (rwseg_byte segs N lo m H Hnw x). lia.
Qed.
End FPGen.

(* [comment removed for export] *)
Definition rwseg_fast (segs : list Segment) (a : word) (n : nat) : bool :=
  (match StoreOk.WsegFast.wf_first_seg segs (U a) (U a + Z.of_nat n) with Some seg => seg_readable seg | None => false end
   && StoreOk.WsegFast.wseg_fast segs a n)%bool.
Lemma rwseg_of_wseg : forall segs seg n (a : word), U a + Z.of_nat n < 2 ^ 64 ->
  (forall z, U a <= z -> z < U a + Z.of_nat n -> find_segment segs z 1 = Some seg) ->
  seg_readable seg = true -> AllocSim.StreamSim.wseg_ok segs a n = true -> rwseg_ok segs a n = true.
Proof.
  intros segs seg n. induction n as [|n IH]; intros a Hr Hf Hrd Hw; [reflexivity|].
  cbn [AllocSim.StreamSim.wseg_ok] in Hw. cbn [rwseg_ok]. rewrite (Hf (U a) ltac:(lia) ltac:(lia)) in Hw |- *. rewrite Hrd. cbn [andb].
  destruct (seg_writable seg); [|discriminate Hw]. cbn [andb] in Hw |- *.
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (U a - Z.of_N (seg_base seg)))); [|discriminate Hw]. cbn [andb] in Hw |- *.
  assert (Ua : U (a + 1)%bv = U a + 1).
  { rewrite bv_add_unsigned. rewrite bv_wrap_small; [reflexivity|]. pose proof (bv_unsigned_in_range 64 a).
    change (U (1%bv : bv 64)) with 1. unfold bv_modulus. lia. }
  apply IH; rewrite ?Ua; [lia | intros z H1 H2; apply Hf; lia | exact Hrd | exact Hw].
Qed.
Lemma rwseg_fast_ok : forall segs a n, rwseg_fast segs a n = true -> rwseg_ok segs a n = true.
Proof.
  intros segs a n H. unfold rwseg_fast in H. apply andb_true_iff in H as [Hrd Hw].
  destruct (StoreOk.WsegFast.wf_first_seg segs (U a) (U a + Z.of_nat n)) as [seg|] eqn:E; [|discriminate Hrd].
  pose proof (StoreOk.WsegFast.wseg_fast_ok segs a n Hw) as Hw'.
  unfold StoreOk.WsegFast.wseg_fast in Hw. apply andb_true_iff in Hw as [Hr _]. apply Z.ltb_lt in Hr.
  apply (rwseg_of_wseg segs seg); [exact Hr | | exact Hrd | exact Hw'].
  intros z H1 H2. apply (StoreOk.WsegFast.wf_first_seg_find segs _ _ seg E z); lia.
Qed.

(* [comment removed for export] *)
Lemma ss_img_ok : rwseg_ok ASEGS (Z_to_bv 64 0x1d9448) 65552 = true.
Proof. apply rwseg_fast_ok. vm_cast_no_check (eq_refl true). Qed.
(* [comment removed for export] *)
Lemma mu_img_ok : rwseg_ok ASEGS (Z_to_bv 64 0x5e9458) 16 = true.
Proof. apply rwseg_fast_ok. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition segs_rw_above (segs : list Segment) (lo : Z) : bool :=
  forallb (fun seg => (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? lo) || seg_writable seg)%bool segs.

Lemma find_seg_writable : forall segs lo z seg, segs_rw_above segs lo = true -> find_segment segs z 1 = Some seg -> lo <= z -> seg_writable seg = true.
Proof.
  induction segs as [|sg l IH]; intros lo z seg Hb Hf Hz; [discriminate Hf|].
  cbn [segs_rw_above forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl]. cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base sg)) z && Z.leb (z + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:E.
  - injection Hf as <-. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    apply orb_true_iff in Hs as [Hs | Hs]; [apply Z.leb_le in Hs; lia | exact Hs].
  - exact (IH lo z seg Hl Hf Hz).
Qed.

Section FPGen2.
Context {fx : FPState}.
Lemma readable_store_ok1 : forall segs lo (m : word -> option byte) (a : word) b, segs_rw_above segs lo = true -> lo <= U a ->
  rdn segs m a 1 = Some [b] -> wview segs m a <> None.
Proof using.
  intros segs lo m a b Hrw Ha Hr. (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). cbn [rdn] in Hr. destruct (m a) as [b0|]; [discriminate|].
  unfold seg_rom, memory_read in Hr. change (Z.of_N 1) with 1 in Hr.
  destruct (find_segment segs (U a) 1) as [seg|] eqn:Hseg; [|discriminate Hr].
  rewrite (find_seg_writable segs lo (U a) seg Hrw Hseg Ha).
  destruct (seg_readable seg); [|discriminate Hr]. change (N.to_nat 1) with 1%nat in Hr. cbn [segment_read_bytes] in Hr.
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (U a - Z.of_N (seg_base seg)))) as [b1|]; [discriminate | discriminate Hr].
Qed.

Lemma rdn_bytes : forall segs (m : word -> option byte) n (a : word) bs, rdn segs m a n = Some bs -> U a + Z.of_nat n <= 2 ^ 64 ->
  forall x : word, U a <= U x < U a + Z.of_nat n -> exists b, rdn segs m x 1 = Some [b].
Proof using.
  intros segs m n. induction n as [|n IH]; intros a bs Hr Hnw x Hx; [lia|].
  pose proof (u64_range a). pose proof (u64_range x).
  cbn [rdn] in Hr. destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|] eqn:E0; [|discriminate Hr].
  destruct (rdn segs m (a + 1)%bv n) as [r|] eqn:E1; [|discriminate Hr].
  destruct (Z.eq_dec (U x) (U a)) as [E|NE].
  - apply bv_eq in E. subst x. exists b0. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). rewrite E0. reflexivity.
  - assert (Ua1 : U (a + 1)%bv = U a + 1) by (apply u_add1; lia).
    apply (IH (a + 1)%bv r E1); rewrite ?Ua1; lia.
Qed.

(* [comment removed for export] *)
Lemma readable_store_ok : forall segs lo (m : word -> option byte) (a : word) n bs, segs_rw_above segs lo = true -> lo <= U a ->
  U a + Z.of_nat n <= 2 ^ 64 -> rdn segs m a n = Some bs -> store_ok segs m a n = true.
Proof using.
  intros segs lo m a n bs Hrw Ha Hnw Hr. apply store_ok_of_all; [exact Hnw|].
  intros x Hx. destruct (rdn_bytes segs m n a bs Hr Hnw x Hx) as [b Hb]. apply (readable_store_ok1 segs lo m x b Hrw ltac:(lia) Hb).
Qed.
End FPGen2.

(* [comment removed for export] *)
Lemma asan_rw_above : segs_rw_above ASEGS 0x100000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End AsDepotImg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMTag.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Abbreviation U := bv_unsigned.

Lemma le8_split_small : forall v : word, U v < 2 ^ 32 ->
  word_to_le_bytes 8 v = word_to_le_bytes 4 v ++ word_to_le_bytes 4 (Z_to_bv 64 0).
Proof.
  intros v Hv. pose proof (u64_range v). (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes in G in change_no_check G' end).
  assert (E : Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (U v) 8) 8) 8) 8 = 0).
  { rewrite !Z.shiftr_shiftr by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
  (lazymatch goal with |- ?G => let G' := eval cbn [Z_to_le_bytes app] in G in change_no_check G' end). rewrite E. reflexivity.
Qed.

Section FPGen.
Context {fx : FPState}.
Lemma bsz_val : forall segs (M : word -> option byte) (a : word) (bsz : list byte) (s : Z),
  rdn segs M a 8 = Some bsz -> rdn segs M a 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 s)) ->
  rdn segs M (at_ a 4) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) -> 0 <= s < 2 ^ 32 -> U a + 8 < 2 ^ 64 ->
  bytes_le_to_Z bsz = s.
Proof using.
  intros segs M a bsz s R8 R4 RT Hs Ha.
  pose proof (rdn_cat segs M a 4 4 _ _ R4 RT ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)) as RC. change (4 + 4)%nat with 8%nat in RC.
  assert (Eb : bsz = word_to_le_bytes 4 (Z_to_bv 64 s) ++ word_to_le_bytes 4 (Z_to_bv 64 0)) by congruence.
  pose proof (le8_split_small (Z_to_bv 64 s) ltac:(first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ])) as E8.
  rewrite Eb, <- E8. rewrite bytes_le_to_Z_8. rewrite u_Z2bv by lia. reflexivity.
Qed.
End FPGen.
End AsAllocMTag.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AsRtLib AsAllocFTac.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam. Export OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFKeep0.   (* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.
Lemma find_segment1_none_outside : forall segs lo hi x,
  segs_in_hull_b segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
  induction segs as [|sg l IH]; intros lo hi x Hb Hx; [reflexivity|].
  cbn [segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  (lazymatch goal with |- ?G => let G' := eval cbn [find_segment] in G in change_no_check G' end).
  replace (Z.leb (Z.of_N (seg_base sg)) x && Z.leb (x + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool with false.
  - exact (IH lo hi x Hl Hx).
  - symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.
Lemma asanF_segs_in_hull : segs_in_hull_b ASEGS 0x10000 0x65d000 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asanF_segs_hi : forall a : word, 0x65d000 <= bv_unsigned a -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof. intros a H. apply (find_segment1_none_outside ASEGS 0x10000 0x65d000); [exact asanF_segs_in_hull | right; exact H]. Qed.
Lemma asanF_segs_off : forall a : word, (bv_unsigned a + 1 <= 0x10000 \/ 0x65d000 <= bv_unsigned a) -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof. intros a [H|H]; apply (find_segment1_none_outside ASEGS 0x10000 0x65d000); [exact asanF_segs_in_hull | left; lia | exact asanF_segs_in_hull | right; exact H]. Qed.
Lemma asanF_segs_wx : wx_segs_nowrap ASEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma asanF_segs_hull : forall a, find_segment ASEGS a 1 <> None -> 0x10000 <= a < 0x65d000.
Proof.
  intros a Ha. destruct (Z_lt_le_dec a 0x10000) as [L|G].
  - exfalso. apply Ha. apply (find_segment1_none_outside ASEGS 0x10000 0x65d000 a asanF_segs_in_hull). left; exact L.
  - destruct (Z_lt_le_dec a 0x65d000) as [L2|G2]; [lia|]. exfalso. apply Ha.
    apply (find_segment1_none_outside ASEGS 0x10000 0x65d000 a asanF_segs_in_hull). right; exact G2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition free_cells (bt : as_boot) (TP TSDP PGP FL MIDEND CPM : Z) : Prop :=
  In (0x10827c, 4%nat, 30) (bt_consts bt)                      (* [comment removed for export] *)
  /\ In (0xff260, 8%nat, 0x1990a8) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x1990ca, 1%nat, 1) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x108258, 1%nat, 1) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0xff250, 8%nat, PGP) (bt_consts bt)                  (* [comment removed for export] *)
  /\ In (PGP, 8%nat, 4096) (bt_consts bt)
  /\ In (0x106de0, 1%nat, 1) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x106de4, 4%nat, 0) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (TP - 88, 8%nat, TSDP) (bt_consts bt)                  (* [comment removed for export] *)
  /\ In (TSDP, 8%nat, bt_tctx bt) (bt_consts bt)               (* [comment removed for export] *)
  /\ In (0x199048, 8%nat, 0) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x103f18 + 808, 8%nat, 2 ^ 20) (bt_consts bt)         (* [comment removed for export] *)
  /\ In (0x103f18 + 792, 8%nat, 2 ^ 28) (bt_consts bt)         (* [comment removed for export] *)
  /\ In (0xff268, 8%nat, FL) (bt_consts bt)                   (* [comment removed for export] *)
  /\ In (FL + 48, 4%nat, 0) (bt_consts bt)                     (* [comment removed for export] *)
  /\ In (0xff270, 8%nat, 0x107578) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0xff278, 8%nat, 0x108268) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x108268, 8%nat, 0) (bt_consts bt)
  /\ In (0xff280, 8%nat, 0x108270) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x108270, 8%nat, MIDEND) (bt_consts bt)
  /\ In (0xff288, 8%nat, 0x108260) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x108260, 8%nat, 0x7fffffffffff) (bt_consts bt)
  /\ In (0xff290, 8%nat, 0x1011b0) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x1011b0, 8%nat, 0xf56e4) (bt_consts bt)
  /\ In (0x106ddc, 1%nat, CPM) (bt_consts bt)                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ (AIMGLO <= TSDP /\ TSDP + 8 <= AIMGHI /\ AIMGLO <= PGP /\ PGP + 8 <= AIMGHI /\ AIMGLO <= FL /\ FL + 4096 <= AIMGHI
      /\ 0 <= MIDEND < 2 ^ 64 /\ 1 <= CPM < 256 /\ AIMGLO + 88 <= TP /\ TP + 8 <= AIMGHI).

Section WithCeil.
Context {RC : run_ceil}.

(* [comment removed for export] *)
Definition free_boot_geom (bt : as_boot) : Prop :=
  (bt_tctx bt + 0x10000 <= bt_thread bt \/ bt_thread bt + PG <= bt_tctx bt)
  /\ 4096 <= bt_stack_top bt <= 2 ^ 47 /\ 0 <= bt_stack_bottom bt < bt_stack_top bt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RepX (bt : as_boot) (X : Z -> Prop) (st : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl : Model) : Prop :=
  exists M0, Rep bt st Lc FF M0 mdl /\ (forall a : word, M a <> M0 a -> X (U a) /\ M a <> None).
(* [comment removed for export] *)
Definition depot_foot (bt : as_boot) (KD : Z) (st' : ast) (sp : Z) (a : Z) : Prop :=
  foot_depot_static bt a
  \/ (exists b, In b (node_blocks bt (a_dep st')) /\ b <= a < b + 2 ^ 20)
  \/ (exists b, In b (store_blocks bt (a_dep st')) /\ b <= a < b + 2 ^ 23)
  \/ (sp - KD <= a < sp)
  \/ (SSOBJ bt + 8 <= a < SSOBJ bt + 16) \/ (DEPOT_NIDS bt + 8 <= a < DEPOT_NIDS bt + 12).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition depot_st (st : ast) (d' : depot) (naa : list (Z * Z)) : ast :=
  AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) d' (a_hint st) (a_ialloc st)
      (a_aa st ++ naa) (a_kact st) (a_shsec st).
(* [comment removed for export] *)
Definition depot_post (bt : as_boot) (FXOK : FPState -> Prop) (KD : Z) (X : Z -> Prop) (st : ast) (Lc FF : list (Z * Z))
           (M : mem) (mdl : Model) (R : bvmap 5 word) (sp ret : word) (c' : config) : Prop :=
  exists fx' st' (M' : mem) mdl' (R' : bvmap 5 word) (id : Z),
    c' = mkCfg (@mkst fx' R' ret M' (seg_rom ASEGS)) mdl'
    /\ FXOK fx' /\ (exists d' naa, st' = depot_st st d' naa)
    /\ WF bt st' Lc FF /\ RepX bt X st' Lc FF M' mdl'
    /\ (forall a : word, X (U a) -> (U sp <= U a \/ U a < U sp - KD) -> M' a = M a)          (* [comment removed for export] *)
    /\ (forall a : word, M' a <> M a -> depot_foot bt KD st' (U sp) (U a) /\ M' a <> None)
    /\ (forall a : word, M' a <> M a -> (U sp - KD <= U a < U sp) \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
    /\ regs_kept R R' /\ getr R' 10 = Z_to_bv 64 id /\ 0 <= id < 2 ^ 32
    /\ same_except_vm mdl mdl'
    /\ (forall a, 0 <= a < 2 ^ 64 -> lzb mdl' a = lzb mdl a                                   (* [comment removed for export] *)
               \/ (exists b, In b (dp_storeblocks (a_dep st')) /\ ~ In b (dp_storeblocks (a_dep st)) /\ b <= a < b + 2 ^ 23))
    /\ m_halted mdl' = None
    /\ BackingAlgebra.model_ivs_wf mdl'.                                                      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition HYP_DEPOT_stmt (bt : as_boot) (FXOK : FPState -> Prop) (KD : Z) : Prop :=
  forall fx (X : Z -> Prop) st Lc FF (M : mem) mdl (R : bvmap 5 word) (sp buf szw ret : word) (sz : Z),
    FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    WF bt st Lc FF -> RepX bt X st Lc FF M mdl ->
    (forall a, X a -> ~ (ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))                 (* [comment removed for export] *)
               /\ (forall id, 1 <= id <= dp_nids (a_dep st) -> ~ foot_node bt (a_dep st) id a)) ->
    (forall a, X a -> CEIL <= a \/ exists lo hi, In (lo, hi) (bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st))
                                    /\ lo <= a < hi /\ lo <> bt_nodes0 bt /\ lo <> bt_store0 bt) ->     (* [comment removed for export] *)
    (exists h : option Z, holes_le h st) ->                                                 (* [comment removed for export] *)
    dp_nids (a_dep st) + 1 <= dp_nids (bt_dep0 bt) + a_kact st / EVT ->
    dp_frames (a_dep st) + FRW <= dp_frames (bt_dep0 bt) + FRW * (a_kact st / EVT) + FRW * Z.of_nat (length (dp_storeblocks (a_dep st))) ->   (* [comment removed for export] *)
    getr R 1 = ret -> getr R 2 = sp -> getr R 10 = buf -> getr R 11 = szw ->
    U sp mod 16 = 0 -> CEIL + KD <= U sp -> U sp + 2192 <= PTRHI -> ret_ok ret ->
    (forall a : word, U sp - KD <= U a < U sp -> M a <> None /\ store_ok ASEGS M a 1%nat = true) ->
    1 <= sz <= 8 -> U szw mod 2 ^ 32 = sz -> U szw / 2 ^ 32 < 256 ->                       (* [comment removed for export] *)
    a_kact st <= KCAP ->                                                                   (* [comment removed for export] *)
    (forall i, U buf <= i < U buf + 8 * sz -> M (Z_to_bv 64 i) <> None) -> CEIL <= U buf ->
    U sp <= U buf -> U buf + 8 * sz < 2 ^ 64 ->                                             (* [comment removed for export] *)
    katD ASEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x8ea80) M (seg_rom ASEGS)) mdl)
         (depot_post bt FXOK KD X st Lc FF M mdl R sp ret).


End WithCeil.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Xd (S p T : Z) (z : Z) : Prop :=
  z = p - 16 \/ (p <= z < p + 8) \/ (T + 2824 <= z < T + 2840) \/ (S - 2304 <= z < S).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma page_base_le3 : forall a : word,
  U (page_base a) <= U a /\ U a < U (page_base a) + 4096 /\ U (page_base a) mod 4096 = 0.
Proof.
  intros a. (lazymatch goal with |- ?G => let G' := eval unfold page_base, page_base_of, page_size in G in change_no_check G' end). pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= U a / 4096 * 4096 <= U a) by lia.
  rewrite u_Z2bv by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Qed.

Lemma hid_off_of : forall (Hd : word -> bool) lo n,
  (forall z, lo <= z < lo + n -> 0 <= z < 2 ^ 64 /\ Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo n.
Proof.
  intros Hd lo n F x Hx. destruct (F (U x) Hx) as [R E]. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

Lemma cellZ_restrict : forall (Hd : word -> bool) M a n v,
  cellZ ASEGS M a n v -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> hid_off Hd a (Z.of_nat n) ->
  rdn ASEGS (mrestrict Hd M) (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof.
  intros Hd M a n v C Ha Hn HO. unfold cellZ, cellN in C. rewrite rdn_mrestrict; [exact C | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact HO].
Qed.

Lemma const_cell : forall bt M c n v, cells_hold ASEGS M (bt_consts bt) -> In (c, n, v) (bt_consts bt) -> cellZ ASEGS M c n v.
Proof. intros bt M c n v CH Hin. unfold cells_hold in CH. rewrite Forall_forall in CH. exact (CH _ Hin). Qed.

Lemma store_ok_bytes : forall M (a : word) (n : nat),
  (forall x : word, U a <= U x < U a + Z.of_nat n -> store_ok ASEGS M x 1%nat = true) ->
  U a + Z.of_nat n <= 2 ^ 64 -> store_ok ASEGS M a n = true.
Proof.
  intros M a n F Hnw. apply store_ok_of_all; [exact Hnw|]. intros x Hx.
  apply (store_ok_all ASEGS M 1 x); [pose proof (u64_range x); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (F x Hx) | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
Qed.
Lemma writableZ_store_ok : forall M lo hi (a : word) (n : nat),
  writableZ ASEGS M lo hi -> lo <= U a -> U a + Z.of_nat n <= hi -> hi <= 2 ^ 64 -> store_ok ASEGS M a n = true.
Proof.
  intros M lo hi a n W H1 H2 H3. apply store_ok_bytes; [|lia]. intros x Hx.
  destruct (W (U x) ltac:(lia)) as [_ S]. rewrite Z_to_bv_bv_unsigned in S. exact S.
Qed.
Lemma writableZ_def : forall M lo hi i, writableZ ASEGS M lo hi -> lo <= i < hi -> M (Z_to_bv 64 i) <> None.
Proof. intros M lo hi i W Hi. exact (proj1 (W i Hi)). Qed.

Lemma mrestrict_off : forall (Hd : word -> bool) M (a : word), Hd a = false -> mrestrict Hd M a = M a.
Proof. intros Hd M a E. (lazymatch goal with |- ?G => let G' := eval unfold mrestrict in G in change_no_check G' end). rewrite E. reflexivity. Qed.
Lemma munrestrict_off : forall (Hd : word -> bool) F M (a : word), Hd a = false -> munrestrict Hd F M a = M a.
Proof. intros Hd F M a E. (lazymatch goal with |- ?G => let G' := eval unfold munrestrict in G in change_no_check G' end). rewrite E. reflexivity. Qed.
Lemma munrestrict_on : forall (Hd : word -> bool) F M (a : word), Hd a = true -> munrestrict Hd F M a = F a.
Proof. intros Hd F M a E. (lazymatch goal with |- ?G => let G' := eval unfold munrestrict in G in change_no_check G' end). rewrite E. reflexivity. Qed.

Lemma unrestrict_mkst : forall {fx : FPState} (Hd : word -> bool) full (r : bvmap 5 word) pc m rom,
  unrestrict Hd full (@mkst fx r pc m rom) = @mkst fx r pc (munrestrict Hd full m) rom.
Proof. intros. reflexivity. Qed.

Lemma same_but_materialized_except_vm : forall m m', same_but_materialized m m' -> same_except_vm m m'.
Proof. intros m m' ->. (lazymatch goal with |- ?G => let G' := eval unfold same_except_vm in G in change_no_check G' end). destruct m; reflexivity. Qed.

Lemma rdn1_heap : forall (m : mem) (a : word) b, 0x65d000 <= U a -> rdn ASEGS m a 1 = Some [b] -> m a = Some b.
Proof.
  intros m a b Ha R. cbn [rdn] in R. destruct (m a) as [b'|] eqn:E.
  - cbn in R. congruence.
  - unfold seg_rom, memory_read in R. change (Z.of_N 1) with 1 in R. rewrite (asanF_segs_hi a Ha) in R. discriminate R.
Qed.
Lemma store_ok1_heap : forall (m : mem) (a : word), 0x65d000 <= U a -> store_ok ASEGS m a 1%nat = true -> m a <> None.
Proof.
  intros m a Ha S. pose proof (store_ok_all ASEGS m 1 a ltac:(pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) S a ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)) as W.
  unfold wview in W. destruct (m a); [discriminate | ]. rewrite (asanF_segs_hi a Ha) in W. exact W.
Qed.

(* [comment removed for export] *)
Lemma rdn1_offimg : forall (m : mem) (a : word) b, (U a + 1 <= 0x10000 \/ 0x65d000 <= U a) -> rdn ASEGS m a 1 = Some [b] -> m a = Some b.
Proof.
  intros m a b Ha R. cbn [rdn] in R. destruct (m a) as [b'|] eqn:E.
  - cbn in R. congruence.
  - unfold seg_rom, memory_read in R. change (Z.of_N 1) with 1 in R. rewrite (asanF_segs_off a Ha) in R. discriminate R.
Qed.


Lemma meter_div : forall k, 0 <= k -> (k + EVT) / EVT = k / EVT + 1.
Proof. intros k Hk. (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end). lia. Qed.

(* [comment removed for export] *)
Lemma in_cs : forall r, existsb (Z.eqb r) as_callee_saved = true -> In r as_callee_saved.
Proof. intros r H. apply existsb_exists in H. destruct H as (x & Hin & E). apply Z.eqb_eq in E. subst x. exact Hin. Qed.

(* [comment removed for export] *)
Lemma lez_low32 : forall segs (m : mem) (a : word) (bs : list byte) (v : Z),
  rdn segs m a 8 = Some bs -> rdn segs m a 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 v)) -> 0 <= v < 2 ^ 32 ->
  bytes_le_to_Z bs mod 2 ^ 32 = v.
Proof.
  intros segs m a bs v R8 R4 Hv.
  pose proof (rdn_firstn segs m 8 a bs 4 R8 ltac:(lia)) as F. rewrite R4 in F. injection F as F'.
  transitivity (bytes_le_to_Z (firstn 4 bs)).
  - apply Z.bits_inj'. intros i Hi. rewrite testbit_lez_firstn by lia.
    replace (8 * Z.of_nat 4) with 32 by reflexivity.
    destruct (Z.ltb_spec i 32).
    + rewrite Z.mod_pow2_bits_low by lia. reflexivity.
    + rewrite Z.mod_pow2_bits_high by lia. reflexivity.
  - rewrite <- F'. rewrite bytes4_small by lia. unorm. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lez_high32_0 : forall segs (m : mem) (a : word) (bs : list byte),
  rdn segs m a 8 = Some bs -> rdn segs m (at_ a 4) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  bytes_le_to_Z bs / 2 ^ 32 = 0.
Proof.
  intros segs m a bs R8 R4.
  pose proof (MemsetLibF.RefMemcpyLib.rdn_skipn segs m 8 a bs 4 R8 ltac:(lia)) as F.
  change (Z.of_nat 4) with 4 in F. change (8 - 4)%nat with 4%nat in F. rewrite R4 in F. injection F as F'.
  apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0. rewrite Z.div_pow2_bits by lia.
  pose proof (testbit_lez_skipn 4 bs i Hi) as T. change (8 * Z.of_nat 4) with 32 in T. rewrite <- T, <- F'.
  replace (word_to_le_bytes 4 (Z_to_bv 64 0)) with [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] by (vm_compute; reflexivity).
  change (Z.testbit 0 i = false). apply Z.bits_0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HIDSEC.
  Context {RC : run_ceil}.
  Variable bt : as_boot.

  (* [comment removed for export] *)
  Lemma lazy_zone : forall st mdl z, rep_ledger bt st mdl -> 0 <= z < 2 ^ 64 -> lzb mdl z = true ->
    0 < z < CEIL /\ ~ (ia_img_lo (bt_ia bt) <= z < ia_img_hi (bt_ia bt)).
  Proof using.
    intros st mdl z (_ & _ & _ & FA & _) Hz L. unfold lzb, page_in_ranges in L.
    apply existsb_exists in L as (iv & Hin & Hb). rewrite Forall_forall in FA. destruct (FA iv Hin) as (A1 & A2 & A3 & A4 & A5).
    apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
    pose proof (page_base_le3 (Z_to_bv 64 z)) as (P1 & P2 & P3). rewrite u_Z2bv in P1, P2 by lia.
    unfold page_size in B2. unfold PG in *.
    split; [lia|]. intros [I1 I2]. destruct A5 as [A5|A5]; Z.div_mod_to_equations; lia.
  Qed.

  Definition HID (st : ast) (mdl : Model) : word -> bool := mkH (m_vm_lazy mdl) (a_aa st).

  Lemma HID_lazy : forall st mdl (a : word), HID st mdl a = true -> lzb mdl (U a) = true.
  Proof using.
    intros st mdl a H. unfold HID, mkH in H. apply andb_prop in H as [H _]. (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite Z_to_bv_bv_unsigned. exact H.
  Qed.
  Lemma HID_notlazy : forall st mdl z, 0 <= z < 2 ^ 64 -> lzb mdl z = false -> HID st mdl (Z_to_bv 64 z) = false.
  Proof using.
    intros st mdl z Hz L. destruct (HID st mdl (Z_to_bv 64 z)) eqn:E; [|reflexivity].
    apply HID_lazy in E. rewrite u_Z2bv in E by lia. congruence.
  Qed.
  Lemma HID_allowed : forall st mdl z, page_allowedb (a_aa st) (page_base (Z_to_bv 64 z)) = true -> HID st mdl (Z_to_bv 64 z) = false.
  Proof using. intros st mdl z A. (lazymatch goal with |- ?G => let G' := eval unfold HID, mkH in G in change_no_check G' end). rewrite A. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). apply andb_false_r. Qed.
  (* [comment removed for export] *)
  Lemma HID_off_zone : forall st mdl z, rep_ledger bt st mdl -> 0 <= z < 2 ^ 64 ->
    (CEIL <= z \/ (ia_img_lo (bt_ia bt) <= z < ia_img_hi (bt_ia bt)) \/ z = 0) -> HID st mdl (Z_to_bv 64 z) = false.
  Proof using.
    intros st mdl z RL Hz Hr. apply HID_notlazy; [exact Hz|]. destruct (lzb mdl z) eqn:E; [|reflexivity].
    exfalso. pose proof (lazy_zone st mdl z RL Hz E). lia.
  Qed.
  Lemma lazy_cover_HID : forall st mdl, lazy_cover (HID st mdl) (m_vm_lazy mdl) (a_aa st).
  Proof using. intros st mdl. (lazymatch goal with |- ?G => let G' := eval unfold HID in G in change_no_check G' end). apply lazy_cover_mkH. intros x Hx; exact Hx. Qed.
  Lemma rep_ledger_of : forall st Lc FF M mdl, Rep bt st Lc FF M mdl -> rep_ledger bt st mdl.
  Proof using. intros st Lc FF M mdl RP. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RP))))))))))))). Qed.
  Lemma HID_off_segments : forall st Lc FF M mdl, bt_ia bt = asan_addrs -> Rep bt st Lc FF M mdl -> H_off_segments ASEGS (HID st mdl).
  Proof using.
    intros st Lc FF M mdl BI RP a Ha. pose proof (rep_ledger_of st Lc FF M mdl RP) as RL.
    apply HID_lazy in Ha. pose proof (u64_range a). destruct (lazy_zone st mdl (U a) RL ltac:(lia) Ha) as [Z1 Z2].
    rewrite BI in Z2. cbn [ia_img_lo ia_img_hi asan_addrs] in Z2.
    destruct (find_segment ASEGS (U a) 1) eqn:E; [|reflexivity]. exfalso. apply Z2. apply asanF_segs_hull. rewrite E. discriminate.
  Qed.

End HIDSEC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma w2b1 : forall z, 0 <= z < 2 ^ 64 -> word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. (lazymatch goal with |- ?G => let G' := eval cbn [word_to_le_bytes Z_to_le_bytes] in G in change_no_check G' end). rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma heap_rdn1 : forall (m : mem) (a : word) b, 0x65d000 <= U a -> m a = Some b -> rdn ASEGS m a 1 = Some [b].
Proof. intros m a b Ha E. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). rewrite E. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). reflexivity. Qed.

Lemma PHI_nonneg : forall L, (forall q n, In (q, n) L -> 1 <= n) -> 0 <= PHI L.
Proof.
  induction L as [|[q n] L IH]; intros H; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); [lia|].
  assert (1 <= n) by (apply (H q n); left; reflexivity). (lazymatch goal with |- ?G => let G' := eval unfold MBLK in G in change_no_check G' end). assert (0 <= PHI L) by (apply IH; intros q' n' Hin; apply (H q' n'); right; exact Hin). lia.
Qed.

Lemma app_visible_mono : forall {RC : run_ceil} IA L1 x L2 FF a,
  app_visible IA (L1 ++ L2) FF a -> app_visible IA (L1 ++ x :: L2) FF a.
Proof.
  intros RC IA L1 x L2 FF a V. unfold app_visible, in_blocks, in_block_shadow in *.
  assert (SUB : forall y, In y (L1 ++ L2) -> In y (L1 ++ x :: L2)).
  { intros y Hy. apply in_app_iff in Hy. apply in_app_iff. destruct Hy; [left; assumption | right; right; assumption]. }
  destruct V as [(b0 & n0 & Hin & R0)|[V|[(b0 & n0 & Hin & R0)|V]]].
  - left. exists b0, n0. split; [apply SUB; exact Hin | exact R0].
  - right; left; exact V.
  - right; right; left. exists b0, n0. split; [apply SUB; exact Hin | exact R0].
  - right; right; right. exact V.
Qed.

Lemma regs_kept_intro : forall R R' : bvmap 5 word,
  getr R' 2 = getr R 2 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 -> getr R' 8 = getr R 8 -> getr R' 9 = getr R 9 ->
  getr R' 18 = getr R 18 -> getr R' 19 = getr R 19 -> getr R' 20 = getr R 20 -> getr R' 21 = getr R 21 -> getr R' 22 = getr R 22 ->
  getr R' 23 = getr R 23 -> getr R' 24 = getr R 24 -> getr R' 25 = getr R 25 -> getr R' 26 = getr R 26 -> getr R' 27 = getr R 27 ->
  regs_kept R R'.
Proof.
  intros R R' E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 r Hr. unfold as_callee_saved in Hr. cbn in Hr.
  Ltac onecs E :=
    lazymatch type of E with getr _ ?kb = _ =>
      lazymatch goal with |- getr _ ?x = _ => replace x with kb by (apply bv_eq; reflexivity); exact E end end.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
    [ onecs E2 | onecs E3 | onecs E4 | onecs E8 | onecs E9 | onecs E18 | onecs E19 | onecs E20
    | onecs E21 | onecs E22 | onecs E23 | onecs E24 | onecs E25 | onecs E26 | onecs E27 ].
Qed.

(* [comment removed for export] *)
Lemma ba_bytes_ge : forall b, (forall m n, In (m, n) (ba_items b) -> 1 <= n) -> BATCHSZ <= ba_bytes b.
Proof.
  intros b H. (lazymatch goal with |- ?G => let G' := eval unfold ba_bytes in G in change_no_check G' end).
  assert (G : forall l : list (Z * Z), (forall m n, In (m, n) l -> 1 <= n) -> 0 <= fold_right (fun (it : Z * Z) acc => snd it + acc) 0 l).
  { induction l as [|[m n] l IH]; intros Hl; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); [lia|].
    assert (1 <= n) by (apply (Hl m n); left; reflexivity).
    assert (0 <= fold_right (fun it acc => snd it + acc) 0 l) by (apply IH; intros m' n' Hin; apply (Hl m' n'); right; exact Hin). lia. }
  pose proof (G _ H). lia.
Qed.
Lemma q_bytes_ge : forall q, (forall b, In b q -> forall m n, In (m, n) (ba_items b) -> 1 <= n) -> BATCHSZ * Z.of_nat (length q) <= q_bytes q.
Proof.
  induction q as [|b q IH]; intros H; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  change (q_bytes (b :: q)) with (ba_bytes b + q_bytes q). (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end).
  assert (BATCHSZ <= ba_bytes b) by (apply ba_bytes_ge; intros m n Hin; exact (H b ltac:(left; reflexivity) m n Hin)).
  assert (BATCHSZ * Z.of_nat (length q) <= q_bytes q) by (apply IH; intros b' Hb'; apply H; right; exact Hb').
  unfold BATCHSZ in *. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sh_up8 : forall p n, p mod 8 = 0 -> 1 <= n -> SB + p / 8 + up8 n / 8 = sh_hi p n /\ sh_lo p = SB + p / 8.
Proof. intros p n Hp Hn. (lazymatch goal with |- ?G => let G' := eval unfold sh_hi, sh_lo, up8 in G in change_no_check G' end). split; [|reflexivity]. lia. Qed.
Lemma granule_idx : forall p n g, p mod 8 = 0 -> user_granule p n g -> 0 <= g - p / 8 < up8 n / 8.
Proof. intros p n g Hp [G1 G2]. (lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end). lia. Qed.
Lemma sp_facts16 : forall s, s mod 16 = 0 -> (s + -2176) mod 16 = 0 /\ (s + -2208) mod 16 = 0.
Proof. intros s Hs. split; lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition hide (P : Prop) : Prop := P.
Ltac hidehyp H := lazymatch type of H with ?T => change T with (hide T) in H end.
