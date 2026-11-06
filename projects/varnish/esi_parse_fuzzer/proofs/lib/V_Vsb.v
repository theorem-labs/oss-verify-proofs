(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7 V_AKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vsb_dbl_ge_ns : forall k ns sz, 0 < ns -> ns <= vsb_dbl k ns sz.
Proof.
  induction k as [|k IH]; intros ns sz Hns; cbn [vsb_dbl]; [lia|].
  destruct (Z.ltb ns sz); [|lia]. specialize (IH (2 * ns) sz ltac:(lia)). lia.
Qed.
Lemma vsb_dbl_mono : forall k ns s1 s2, 0 < ns -> s1 <= s2 -> vsb_dbl k ns s1 <= vsb_dbl k ns s2.
Proof.
  induction k as [|k IH]; intros ns s1 s2 Hns Hs; cbn [vsb_dbl]; [lia|].
  destruct (Z.ltb_spec ns s1) as [L1|G1]; destruct (Z.ltb_spec ns s2) as [L2|G2]; try lia.
  - apply IH; lia.
  - pose proof (vsb_dbl_ge_ns k (2 * ns) s2 ltac:(lia)). lia.
Qed.
Lemma vsb_extendsize_mono : forall a b, a <= b -> vsb_extendsize a <= vsb_extendsize b.
Proof.
  intros a b Hab. unfold vsb_extendsize.
  destruct (Z.ltb_spec a 4096) as [La|Ga]; destruct (Z.ltb_spec b 4096) as [Lb|Gb].
  - apply vsb_dbl_mono; lia.
  - eapply Z.le_trans with (m := vsb_dbl 9 16 4096).
    + apply vsb_dbl_mono; lia.
    + change (vsb_dbl 9 16 4096) with 4096.
      pose proof (Z.div_mod (b + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (b + 4095) 4096 ltac:(lia)). lia.
  - lia.
  - pose proof (Z.div_mod (a + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (a + 4095) 4096 ltac:(lia)).
    pose proof (Z.div_mod (b + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (b + 4095) 4096 ltac:(lia)).
    assert ((a + 4095) / 4096 <= (b + 4095) / 4096) by (apply Z.div_le_mono; lia). lia.
Qed.

(* [comment removed for export] *)
Definition vsb_fresh (b : Z) : vsb_rec := VSBR 0 b 16 0 VSB_FLAGS_LIVE 0.

Section S.
  Context {Clg : Ceiling} (L : AllocLayout) {AI : AllocSpec L}.   (* [comment removed for export] *)
  Let segs := al_segs L.

  Definition vsb_buf_ok (m : mem) (v : vsb_rec) (fin : bool) : Prop :=
    exists bs, u8arr segs m (vb_buf v) bs /\ Z.of_nat (length bs) = vb_size v /\
               (fin = true -> nth_error bs (Z.to_nat (vb_len v)) = Some (Z_to_bv 8 0)).

  Definition vsb_obj (A : AS) (m : mem) (S : Z) (v : vsb_rec) (fin : bool) : Prop :=
    rw_cells segs m S (vsb_cells v) /\ vsb_inv v fin /\
    a_live A S = Some 40 /\ a_live A (vb_buf v) = Some (vb_size v) /\ S <> vb_buf v /\
    vsb_buf_ok m v fin.

  (* [comment removed for export] *)
  Lemma vsb_obj_geom : forall A m md S v fin,
    ainv A m md -> vsb_obj A m S v fin ->
    S mod 16 = 0 /\ 4096 <= S /\ S + 40 <= alloc_ceiling /\ off_image L S 40 /\
    vb_buf v mod 16 = 0 /\ 4096 <= vb_buf v /\ vb_buf v + vb_size v <= alloc_ceiling /\
    off_image L (vb_buf v) (vb_size v) /\
    (S + 40 <= vb_buf v \/ vb_buf v + vb_size v <= S) /\
    mapped m S 40 /\ mapped m (vb_buf v) (vb_size v).
  Proof.
    (intros A m md S v fin AI0; (first [ intro dR_5; dand6 dR_5 as VC VI LS LB NE _ | intros (VC & VI & LS & LB & NE & _) ])).
    (first [ pose proof ((as_live_ok A m md _ _ AI0 LS)) as dR_1; dand7 dR_1 as _ a1 a2 a3 a4 a5 _ | destruct (as_live_ok A m md _ _ AI0 LS) as (_ & a1 & a2 & a3 & a4 & a5 & _) ]).
    (first [ pose proof ((as_live_ok A m md _ _ AI0 LB)) as dR_2; dand7 dR_2 as _ b1 b2 b3 b4 b5 _ | destruct (as_live_ok A m md _ _ AI0 LB) as (_ & b1 & b2 & b3 & b4 & b5 & _) ]).
    pose proof (as_live_disjoint A m md _ _ _ _ AI0 LS LB NE).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End S.

(* [comment removed for export] *)
Ltac vsb_open H :=
  lazymatch type of H with
  | vsb_obj _ _ _ _ _ _ =>
      let VC := fresh "VSBC" in let VI := fresh "VINV" in let LS := fresh "VLS" in
      let LB := fresh "VLB" in let NE := fresh "VNE" in let BU := fresh "VBUF" in
      (first [ dand6 H as VC VI LS LB NE BU | destruct H as (VC & VI & LS & LB & NE & BU) ]); unfold vsb_cells in VC; fold_al_segs
  end.

(* [comment removed for export] *)
Ltac vsb_close :=
  lazymatch goal with
  | |- vsb_obj _ _ _ _ _ _ =>
      split; [ eassumption |];
      split; [ first [ assumption
                     | unfold vsb_inv, ENOMEM, VSB_FLAGS_LIVE, VSB_FLAGS_FIN in *;
                       cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf vsb_set_len vsb_set_error vsb_set_buf_size vsb_set_flags] in *; lia ] |];
      split; [ first [ eassumption | cbn; eassumption ] |];
      split; [ first [ eassumption | cbn; eassumption ] |];
      split; [ first [ assumption | cbn; assumption | cbn; lia ] |];
      eexists; split; [ eassumption |]; split;
      [ try rewrite !upd_length; cbn [vb_size vb_len vsb_set_len vsb_set_error vsb_set_buf_size vsb_set_flags]; lia
      | first [ intros X; discriminate X | assumption | idtac ] ]
  end.
