(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibShadow AsLibDefs AsLibEnv.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
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
Open Scope Z_scope.

Definition both_abi : as_abi := AA
  0x7ff14 0x5da040 3584 0x5da970 0x5fbd18 0x5da990
  [(0x20cf8, 0x20f00); (0x10338, 0x10340)]%Z
  [ (0x9f920, 0xa79b8); (0xa79b8, AS_SB);          (* [comment removed for export] *)
    (0x9f978, 0xa79c0);                              (* [comment removed for export] *)
    (0x9f940, 0xa1780); (0xa1780, 0x99050);        (* [comment removed for export] *)
    (0xa1778, 0x98c4c);                              (* [comment removed for export] *)
    (0xa0488, 0xa8699);                              (* [comment removed for export] *)
    (0xa16b8, 0x99840);                              (* [comment removed for export] *)
    (0xa0600, 1); (0xa0608, 0xfffffffffffff800);     (* [comment removed for export] *)
    (0x9f928, 0xa86a8); (0xa86a8, 0);               (* [comment removed for export] *)
    (0x9f930, 0xa86b0);                              (* [comment removed for export] *)
    (0x9f938, 0xa86a0); (0xa86a0, 0x7fffffffffff);  (* [comment removed for export] *)
    (0x9f910, 0x1394e8);                              (* [comment removed for export] *)
    (0x9f970, 0x137458);                              (* [comment removed for export] *)
    (0xa0610, 0x8);                                   (* [comment removed for export] *)
    (0x5da968, 0x5da990); (0x5da998, 0x5db170);        (* [comment removed for export] *)
    (0x5da918, 0x5fbd18) ]%Z                           (* [comment removed for export] *)
  [ (0xa79c0, 1);                                     (* [comment removed for export] *)
    (0xa7224, 0);                                     (* [comment removed for export] *)
    (0x137458, 0) ]%Z                                  (* [comment removed for export] *)
  [ (0xa8698, 1);                                     (* [comment removed for export] *)
    (0xa8699, 1);                                     (* [comment removed for export] *)
    (0xa7220, 1);                                     (* [comment removed for export] *)
    (0x139571, 1) ]%Z                                  (* [comment removed for export] *)
  [ 0xa86b0 ]%Z
  [ (0x7fffc1d0, 0); (0x7fffc1d1, 0); (0x7fffc1d2, 4) ]%Z.   (* [comment removed for export] *)

Definition as_both : as_lib := AL both_abi
  0x7ff14 0x803c4 0x80714 0x80b50 0x80f60
  0x8125c 0x815e0 0x818d8 0x81c30 0x829d4
  0x83c78 0x83d78 0x857cc 0x874f0 0x878cc
  0x87b8c 0x87d64 0x8822c 0x8834c 0x88514
  0x3c900 0x3ca74 0x3cc80
  0x53f20 0x54040 0x514fc 0x51060
  0x99050 0x98c4c
  0x20e80 0x20e0c 0x10338.

Section WithSegs.
Variable segs : list Segment.
Lemma as_sb_both : forall mem, as_sb segs as_both mem <-> sbcell segs 0x9f920 0xa79b8 mem.
Proof.
  intros mem. unfold as_sb. cbn. split.
  - intros (got & cellp & H1 & H2 & H). congruence.
  - intros H. exists 0x9f920%Z, 0xa79b8%Z. auto.
Qed.
End WithSegs.

Lemma both_abi_low : abi_low both_abi.
Proof.
  unfold abi_low. cbn -[in_env_zone Z.pow Z.le Z.add Z.sub Z.div].
  repeat split; intros;
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] | H : False |- _ => destruct H end;
  try match goal with H : (_, _) = (_, _) |- _ => injection H as <- <- end; try subst;
  unfold in_env_zone, AS_IMGLO, AS_IMGHI, AS_SIMGLO, AS_SIMGHI; first [left; lia | right; lia].
Qed.
