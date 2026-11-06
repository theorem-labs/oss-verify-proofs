(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim StoreOk Hoare Frame LibDefs LibFrame.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsLibShadow.
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Implicit Types (mem : word -> option byte) (rs : list (word * Z)).

(* [comment removed for export] *)
Lemma bytes_frame : forall mem (mem' : word -> option byte) rs (data : word) len (bs : list byte),
  frame_mod mem mem' rs -> bv_unsigned data + len <= 2 ^ 64 -> apart (bv_unsigned data) len rs ->
  (forall i, 0 <= i < len -> mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
  (forall i, 0 <= i < len -> mem' (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
Proof.
  intros mem mem' rs data len bs Hf Hw Hap Hb i Hi. pose proof (u64_range data).
  rewrite (byte_frame mem mem' rs (bv_unsigned data + i) Hf ltac:(lia)).
  - apply Hb. exact Hi.
  - eapply apart_sub; [exact Hap | lia | lia | lia].
Qed.

Lemma shz_frame : forall mem (mem' : word -> option byte) rs a m,
  frame_mod mem mem' rs -> shz mem a m -> 0 <= a < 2 ^ 47 -> 0 <= m <= 2 ^ 47 ->
  apart (SB + a / 8) m rs -> shz mem' a m.
Proof.
  intros mem mem' rs a m Hf [Hal Hz] Ha Hm Hap. split; [exact Hal|].
  intros j Hj. unfold SB in *.
  assert (0 <= a / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (byte_frame mem mem' rs (2147450880 + a / 8 + j) Hf ltac:(lia)).
  - apply Hz. exact Hj.
  - eapply apart_sub; [exact Hap | lia | lia | lia].
Qed.

Lemma shbyte_frame : forall mem (mem' : word -> option byte) rs a v,
  frame_mod mem mem' rs -> shbyte mem a v -> 0 <= a < 2 ^ 47 ->
  apart (SB + a / 8) 1 rs -> shbyte mem' a v.
Proof.
  intros mem mem' rs a v Hf Hb Ha Hap. unfold shbyte, SB in *.
  assert (0 <= a / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (byte_frame mem mem' rs (2147450880 + a / 8) Hf ltac:(lia) Hap). exact Hb.
Qed.

(* [comment removed for export] *)
Lemma shdata_frame : forall mem (mem' : word -> option byte) rs d n,
  frame_mod mem mem' rs -> shdata mem d n -> 0 <= d -> 0 <= n -> d + n < 2 ^ 47 ->
  apart (SB + d / 8) (n / 8 + 1) rs -> shdata mem' d n.
Proof.
  intros mem mem' rs d n Hf [Hal Hs] Hd Hn Hdn Hap. split; [exact Hal|].
  intros g Hg1 Hg2. unfold SB in *.
  assert (0 <= d / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (g <= (d + n - 1) / 8) by (apply Z.div_le_lower_bound; lia).
  assert ((d + n - 1) / 8 <= d / 8 + n / 8).
  { replace (d + n - 1) with (8 * (d / 8) + (n - 1)) by (rewrite Hal at 1 || idtac; pose proof (Z.div_mod d 8 ltac:(lia)); lia).
    rewrite Z.add_comm, Z.mul_comm, Z.div_add by lia.
    assert ((n - 1) / 8 <= n / 8) by (apply Z.div_le_mono; lia). lia. }
  rewrite (byte_frame mem mem' rs (2147450880 + g) Hf ltac:(lia)).
  - apply Hs; assumption.
  - eapply apart_sub; [exact Hap | lia | lia | lia].
Qed.

Lemma sbcell_frame : forall mem (mem' : word -> option byte) rs got cellp,
  frame_mod mem mem' rs -> sbcell segs got cellp mem ->
  0 <= got -> got + 8 <= 2 ^ 64 -> 0 <= cellp -> cellp + 8 <= 2 ^ 64 ->
  apart got 8 rs -> apart cellp 8 rs -> sbcell segs got cellp mem'.
Proof.
  intros mem mem' rs got cellp Hf [H1 H2] Hg0 Hg8 Hc0 Hc8 Ha1 Ha2. split.
  - eapply cell64_frame; eauto.
  - eapply cell64_frame; eauto.
Qed.

(* [comment removed for export] *)
Lemma store_ok_frame : forall mem (mem' : word -> option byte) rs a n,
  frame_mod mem mem' rs -> RiscvSemantics.store_ok segs mem a n = true ->
  RiscvSemantics.store_ok segs mem' a n = true.
Proof. intros. eapply frame_mod_store_ok; eassumption. Qed.

End WithSegs.
