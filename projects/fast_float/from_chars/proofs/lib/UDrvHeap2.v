(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StoreOk DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvData UDrvMain UDrvCall UDrvHeap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition isub1 (lo hi : Z) (r : ivl) : list ivl :=
  let '(a, b) := r in
  (if Z.ltb a (Z.min b lo) then [(a, Z.min b lo)] else []) ++ (if Z.ltb (Z.max a hi) b then [(Z.max a hi, b)] else []).
Definition isub (lo hi : Z) (W : list ivl) : list ivl := flat_map (isub1 lo hi) W.
Definition icompl (L : list ivl) : list ivl := fold_right (fun r W => isub (fst r) (snd r) W) [(0, 2 ^ 64)] L.

Lemma ioutside_app : forall A B x, ioutside (A ++ B) x <-> ioutside A x /\ ioutside B x.
Proof. exact HIface.outside_app. Qed.

Lemma isub1_spec : forall lo hi a b x, ~ ioutside (isub1 lo hi (a, b)) x <-> (a <= x < b /\ ~ (lo <= x < hi)).
Proof.
  intros lo hi a b x. unfold isub1. rewrite ioutside_app.
  destruct (Z.ltb a (Z.min b lo)) eqn:H1; destruct (Z.ltb (Z.max a hi) b) eqn:H2; cbn [ioutside];
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *; split; intros H; try tauto; lia.
Qed.

Lemma nout_app : forall A B x, ~ ioutside (A ++ B) x <-> (~ ioutside A x \/ ~ ioutside B x).
Proof.
  intros A B x. rewrite ioutside_app. destruct (HIface.outside_dec A x) as [HA|HA]; destruct (HIface.outside_dec B x) as [HB|HB]; tauto.
Qed.

Lemma isub_spec : forall lo hi W x, ~ ioutside (isub lo hi W) x <-> (~ ioutside W x /\ ~ (lo <= x < hi)).
Proof.
  intros lo hi W x. induction W as [|[a b] W IH]; [cbn; tauto|].
  unfold isub. cbn [flat_map]. fold (isub lo hi W). rewrite nout_app, IH, isub1_spec.
  change ((a, b) :: W) with ([(a, b)] ++ W). rewrite nout_app. cbn [ioutside].
  split; [intros [A|A]; [split; [left; tauto | tauto] | tauto] | intros [[A|A] B]; [left; split; [lia | exact B] | right; tauto]].
Qed.

Lemma icompl_spec : forall L x, 0 <= x < 2 ^ 64 -> (~ ioutside (icompl L) x <-> ioutside L x).
Proof.
  intros L x Hx. induction L as [|[lo hi] L IH]; cbn [icompl fold_right ioutside].
  - split; [intros _; exact I | intros _ [C _]; lia].
  - fold (icompl L). cbn [fst snd]. rewrite isub_spec, IH. tauto.
Qed.

Lemma icompl_range : forall L x, ~ ioutside (icompl L) x -> 0 <= x < 2 ^ 64.
Proof.
  induction L as [|[lo hi] L IH]; intros x H; cbn [icompl fold_right] in H.
  - cbn [ioutside] in H. assert (D : (0 <= x < 2 ^ 64) \/ ~ (0 <= x < 2 ^ 64)) by lia. destruct D as [D|D]; [exact D|].
    exfalso. apply H. split; [exact D | exact I].
  - fold (icompl L) in H. cbn [fst snd] in H. apply isub_spec in H as [H _]. exact (IH x H).
Qed.

Lemma outside_or_in : forall E rgs x, outside E rgs x \/ exists i R, nth_error rgs i = Some R /\ in_rg E R x.
Proof.
  intros E rgs x. induction rgs as [|R rs IH]; [left; constructor|].
  destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned (lden E (rg_base R)))) as [A|A];
  [| destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R)) + rsz E R) (bv_unsigned x)) as [B|B]].
  - destruct IH as [IH|(i & R' & Hi & Hin)]; [left; constructor; [left; exact A | exact IH] | right; exists (S i), R'; split; [exact Hi | exact Hin]].
  - destruct IH as [IH|(i & R' & Hi & Hin)]; [left; constructor; [right; exact B | exact IH] | right; exists (S i), R'; split; [exact Hi | exact Hin]].
  - right. exists 0%nat, R. split; [reflexivity|]. unfold in_rg. lia.
Qed.


Section HeapSeg.
Variable HI : heap_iface.
Variables GP TP : word.
Variables IMG_LO IMG_END HTOP : Z.
Variable STATIC : list ivl.
Hypothesis HOK : heap_ok PSEGS DCFG HI GP TP IMG_LO IMG_END HTOP STATIC CELLS_NE 0x530c8 8192 0x52f88 8192.
(* [comment removed for export] *)
Hypothesis HERR : forall hs m m' md, hi_Heap HI hs m md -> munch ERRC m m' -> mem_grows m m' -> hi_Heap HI hs m' md.

(* [comment removed for export] *)
Hypothesis HCELL : forall hs m m' md, hi_Heap HI hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x65b58 <= a < 0x65b60 \/ 0x97c00 <= a < 0x97c08 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> hi_Heap HI hs m' md.


Definition cellb (L : list ivl) (x : word) : bool := if HIface.outside_dec L (bv_unsigned x) then false else true.
#[using="Type"] Lemma cellb_true : forall L x, cellb L x = true <-> ~ ioutside L (bv_unsigned x).
Proof. LiaFast.lf_pins LiaFast.u0. intros L x. unfold cellb. destruct (HIface.outside_dec L (bv_unsigned x)); split; intros H; try tauto; discriminate. Qed.
#[using="Type"] Lemma cellb_false : forall L x, cellb L x = false <-> ioutside L (bv_unsigned x).
Proof. LiaFast.lf_pins LiaFast.u0. intros L x. unfold cellb. destruct (HIface.outside_dec L (bv_unsigned x)); split; intros H; try tauto; try discriminate; exfalso; tauto. Qed.

#[using="GP TP HOK HERR HCELL"] Theorem heap_seg : forall E rgs hs m m' md,
  hi_Heap HI hs m md ->
  (forall x, outside E rgs x -> m' x = m x) -> mem_grows m m' ->
  (forall a, ~ ioutside CELLS_NE a -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) ->
  avoid_heap3 IMG_LO IMG_END HTOP STATIC E rgs ->
  hi_Heap HI hs m' md.
Proof. LiaFast.lf_pins (fun (GP TP HOK HERR HCELL : LiaFast.U) => LiaFast.u0).
  intros E rgs hs m m' md Hh Hfr Hgr Hcel Hav.
  pose proof HOK as (_ & _ & _ & Hframe & Hblk).
  set (m1 := fun x : word => if cellb (CELLS_NE ++ ERRC) x then m x else m' x).
  set (m2 := fun x : word => if cellb ERRC x then m x else m' x).
  assert (H1 : hi_Heap HI hs m1 md).
  { apply (Hframe hs m m1 md (icompl (hi_owned HI hs)) Hh).
    - intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx. unfold bv_modulus in Rx. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
      assert (Hown : ~ ioutside (hi_owned HI hs) (bv_unsigned x)) by (intros Ho; apply (proj2 (icompl_spec _ _ Rx)) in Ho; exact (Ho Hx)).
      unfold m1. destruct (cellb (CELLS_NE ++ ERRC) x) eqn:Hc; [reflexivity|]. apply cellb_false in Hc.
      destruct (outside_or_in E rgs x) as [Ho|(i & R & Hi & Hin)]; [exact (Hfr x Ho)|].
      exfalso. destruct (Hblk hs m md Hh) as (_ & Hown'). destruct (Hown' _ Hown) as (B1 & B2).
      destruct (Hav i R x Hi Hin Hc) as [Q|(Q1 & Q2)]; [lia|]. destruct B2 as [B2|[B2|B2]]; [exact (B2 Q2) | lia | lia].
    - intros x Hx. unfold m1. destruct (cellb (CELLS_NE ++ ERRC) x); [exact Hx | exact (Hgr x Hx)].
    - intros x Hx. pose proof (icompl_range _ _ Hx) as Rx. exact (proj1 (icompl_spec _ _ Rx) Hx). }
  assert (H2 : hi_Heap HI hs m2 md).
  { apply (HCELL hs m1 m2 md H1).
    - intros x Hx. unfold m1, m2. destruct (cellb ERRC x) eqn:He.
      + apply cellb_true in He. replace (cellb (CELLS_NE ++ ERRC) x) with true; [reflexivity|]. symmetry. apply cellb_true.
        rewrite ioutside_app. tauto.
      + apply cellb_false in He. replace (cellb (CELLS_NE ++ ERRC) x) with false; [reflexivity|]. symmetry. apply cellb_false.
        rewrite ioutside_app. tauto.
    - intros x Hx. unfold m1, m2 in *. destruct (cellb ERRC x) eqn:He.
      + replace (cellb (CELLS_NE ++ ERRC) x) with true in Hx; [exact Hx|]. symmetry. apply cellb_true. apply cellb_true in He.
        rewrite ioutside_app. tauto.
      + destruct (cellb (CELLS_NE ++ ERRC) x); [exact (Hgr x Hx) | exact Hx].
    - intros a Ha0.
      assert (Ha : ~ ioutside CELLS_NE a) by (cbn [ioutside CELLS_NE]; intros (A & B & _); destruct Ha0 as [Q|Q]; [exact (A Q) | exact (B Q)]).
      pose proof (Hcel a Ha) as Hv. unfold mrd in *. unfold m1, m2.
      assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_small64; unfold two64; lia).
      assert (He : cellb ERRC (Z_to_bv 64 a) = false).
      { apply cellb_false. cbn [ioutside ERRC]. split; [|exact I]. rewrite Ua. lia. }
      assert (Hce : cellb (CELLS_NE ++ ERRC) (Z_to_bv 64 a) = true).
      { apply cellb_true. rewrite ioutside_app. intros [A _]. apply Ha. rewrite Ua in A. exact A. }
      rewrite He, Hce. exact Hv. }
  apply (HERR hs m2 m' md H2).
  - intros x Hx. unfold m2. destruct (cellb ERRC x) eqn:Hie; [|reflexivity]. apply cellb_true in Hie. exfalso. exact (Hie Hx).
  - intros x Hx. unfold m2 in Hx. destruct (cellb ERRC x); [exact (Hgr x Hx) | exact Hx].
Qed.
End HeapSeg.
