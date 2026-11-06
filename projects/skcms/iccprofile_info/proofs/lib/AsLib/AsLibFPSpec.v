(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame LibDefs LibFPSpec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibShadow AsLibDefs AsRtSpec.
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

Section Specs.
Variable segs : list Segment.
Variable L : as_lib.
Variable ceil : Z.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eval_curve_pre_as (data : word) (len : Z) (bs : list byte)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  exists (c t8 t16 : word) (n : Z),
    getr regs 10 = c /\ (bv_unsigned c mod 8 = 0) /\ heapish ceil (bv_unsigned c) 32 /\
    table_curve segs mem data len (bv_unsigned c) n t8 t16 /\
    as_data_ok ceil mem data len bs /\ env_ro (al_abi L) mem /\
    shz mem (bv_unsigned c) 3 /\ as_sb segs L mem /\
    (exists sp, getr regs 2 = sp /\ as_frame segs ceil mem sp 16).

Definition eval_curve_post_as
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned (getr regs 2) - 16), 16%Z)].

Definition eval_curve_contract_as : Prop :=
  forall data len bs,
    fn_contract segs (al_evalcurve L) (eval_curve_pre_as data len bs) eval_curve_post_as.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FITLIN_D : Z := 432.

Definition fitlin_pre_as (data : word) (len : Z) (bs : list byte)
    (sp C : word) (n : Z) (t8 t16 : word) (fs : Z) (hc : word) (ch : chain)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let s := bv_unsigned sp in
  let c := bv_unsigned C in
  let A := al_abi L in
  let Fc := frame0 fs (pos0 hc) in
  let h := Z_to_bv 64 (bv_unsigned hc + 1) in
  getr regs 2 = sp /\ getr regs 10 = C /\ getr regs 11 = Z_to_bv 64 n /\
  getr regs 12 = Z_to_bv 64 (s + 28) /\ getr regs 13 = Z_to_bv 64 (s + 24) /\
  getr regs 14 = Z_to_bv 64 (Fc + 32) /\ getr regs 4 = Z_to_bv 64 (aa_tp A) /\
  (s mod 32 = 0) /\ stackish ceil (s - FITLIN_D) (FITLIN_D + 32) /\ writable segs mem (s - FITLIN_D) (FITLIN_D + 32) /\
  shz mem (s + 24) 1 /\ (exists w, cell segs mem (s + 28) 4 w) /\
  writable segs mem (Fc + 32) 4 /\ acell segs mem (AS_SB + (Fc + 32) / 8) 1 4 /\
  (c mod 8 = 0) /\ heapish ceil c 32 /\ shz mem c 3 /\ (fs + FS_FRAMES5 <= c) /\ (c + 32 <= fs + FS_SIZE) /\
  table_curve segs mem data len c n t8 t16 /\
  as_data_ok ceil mem data len bs /\ (bv_unsigned data + len <= fs \/ fs + FS_SIZE <= bv_unsigned data) /\
  as_env segs ceil A fs ch mem /\ fs_hdr segs ceil A fs mem /\ fs_writable segs fs mem /\
  acellw segs mem (fs + FS_HINT0) h /\ fs_flags0_but fs [pos0 hc] mem.

Definition fitlin_post_as (data : word) (len : Z) (bs : list byte)
    (sp C : word) (n : Z) (t8 t16 : word) (fs : Z) (hc : word) (ch : chain)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let s := bv_unsigned sp in
  let Fc := frame0 fs (pos0 hc) in
  let h := Z_to_bv 64 (bv_unsigned hc + 1) in
  let Ff := frame0 fs (pos0 h) in
  frame_mod mem mem' [(Z_to_bv 64 (s - FITLIN_D), FITLIN_D + 32); (Z_to_bv 64 (Fc + 32), 4);
                      (Z_to_bv 64 (fs + FS_HINT0), 8); (Z_to_bv 64 (fs + FS_FLAGS0 + pos0 h), 1);
                      (Z_to_bv 64 Ff, 64); (Z_to_bv 64 (AS_SB + Ff / 8), 8)] /\
  (exists w, cell segs mem' (s + 28) 4 w) /\ (exists w, cell segs mem' (Fc + 32) 4 w) /\
  acellw segs mem' (fs + FS_HINT0) (Z_to_bv 64 (bv_unsigned hc + 2)) /\
  mem' (Z_to_bv 64 (fs + FS_FLAGS0 + pos0 h)) = Some (Z_to_bv 8 0) /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ 1 <= r <= n.

Definition fit_linear_contract_as : Prop :=
  forall data len bs sp C n t8 t16 fs hc ch,
    fn_contract segs (al_fitlin L)
      (fitlin_pre_as data len bs sp C n t8 t16 fs hc ch)
      (fitlin_post_as data len bs sp C n t8 t16 fs hc ch).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CANON_D : Z := 2272.

Definition canon_pre_as (data : word) (len : Z) (bs : list byte) (sp C : word)
    (fs : Z) (h : word) (ch : chain)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let s := bv_unsigned sp in
  let c := bv_unsigned C in
  let A := al_abi L in
  getr regs 2 = sp /\ getr regs 10 = C /\ getr regs 4 = Z_to_bv 64 (aa_tp A) /\
  as_frame segs ceil mem sp CANON_D /\ shz mem (s - CANON_D) (CANON_D / 8) /\
  (c mod 8 = 0) /\ heapish ceil c 32 /\ writable segs mem c 32 /\ shz mem c 4 /\ shwz mem (c + 12) 20 /\
  (fs + FS_FRAMES5 <= c) /\ (c + 32 <= fs + FS_SIZE) /\
  curve_ok segs mem data len c /\
  as_data_ok ceil mem data len bs /\ (bv_unsigned data + len <= fs \/ fs + FS_SIZE <= bv_unsigned data) /\
  (bv_unsigned data + len <= c \/ c + 32 <= bv_unsigned data) /\
  as_env segs ceil A fs ch mem /\ fs_hdr segs ceil A fs mem /\ fs_writable segs fs mem /\
  acellw segs mem (fs + FS_HINT0) h /\ fs_flags0_but fs [] mem.

Definition canon_post_as (data : word) (len : Z) (bs : list byte) (sp C : word)
    (fs : Z) (h : word) (ch : chain)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' ([(Z_to_bv 64 (bv_unsigned sp - CANON_D), CANON_D); (C, 32)] ++ fs_mod0 fs) /\
  curve_ok segs mem' data len (bv_unsigned C) /\
  fs_flags0_but fs [] mem' /\ (exists h', acellw segs mem' (fs + FS_HINT0) h').

Definition canonicalize_contract_as : Prop :=
  forall data len bs sp C fs h ch,
    fn_contract segs (al_canon L) (canon_pre_as data len bs sp C fs h ch) (canon_post_as data len bs sp C fs h ch).

End Specs.
