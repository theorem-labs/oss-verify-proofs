(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame LibDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibShadow AsLibDefs BoBase.
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

Section WithSegs.
Variable segs : list Segment.

Lemma both_cells64 : forall mem, env_cells segs both_abi mem ->
  acell segs mem 0x9f920 8 0xa79b8 /\ acell segs mem 0xa79b8 8 AS_SB /\ acell segs mem 0x9f978 8 0xa79c0 /\
  acell segs mem 0x9f940 8 0xa1780 /\ acell segs mem 0xa1780 8 0x99050 /\ acell segs mem 0xa1778 8 0x98c4c /\
  acell segs mem 0xa0488 8 0xa8699 /\ acell segs mem 0xa16b8 8 0x99840 /\ acell segs mem 0xa0600 8 1 /\
  acell segs mem 0xa0608 8 0xfffffffffffff800 /\ acell segs mem 0x9f928 8 0xa86a8 /\ acell segs mem 0xa86a8 8 0 /\
  acell segs mem 0x9f930 8 0xa86b0 /\ acell segs mem 0x9f938 8 0xa86a0 /\ acell segs mem 0xa86a0 8 0x7fffffffffff /\
  acell segs mem 0x9f910 8 0x1394e8 /\ acell segs mem 0x9f970 8 0x137458 /\ acell segs mem 0xa0610 8 0x8 /\
  acell segs mem 0x5da968 8 0x5da990 /\ acell segs mem 0x5da998 8 0x5db170 /\ acell segs mem 0x5da918 8 0x5fbd18 /\
  acell segs mem 0xa79c0 4 1 /\ acell segs mem 0xa7224 4 0 /\ acell segs mem 0x137458 4 0 /\
  acell segs mem 0xa8698 1 1 /\ acell segs mem 0xa8699 1 1 /\ acell segs mem 0xa7220 1 1 /\ acell segs mem 0x139571 1 1 /\
  areadable segs mem 0xa86b0 8.
Proof using segs.
  intros mem (C64 & C32 & C8 & R64).
  repeat lazymatch goal with
  | |- acell _ _ _ 8 _ /\ _ => split; [apply C64; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | ]
  | |- acell _ _ _ 4 _ /\ _ => split; [apply C32; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | ]
  | |- acell _ _ _ 1 _ /\ _ => split; [apply C8; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | ]
  | |- areadable _ _ _ _ => apply R64; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]
  end.
Qed.

End WithSegs.
