(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame LibDefs.
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

Definition CLASSIFY_D : Z := 16.
Definition RCURVE_D : Z := 2208.
Definition RCURVES_D : Z := 2288.

Section Specs.
Variable segs : list Segment.
Variable L : as_lib.
Variable ceil : Z.   (* [comment removed for export] *)

#[local] Notation cell := (cell segs).
#[local] Notation cell32 := (cell32 segs).
#[local] Notation writable := (writable segs).
#[local] Notation curve_ok := (curve_ok segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition classify_pre_as (sp C : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let c := bv_unsigned C in
  getr regs 2 = sp /\ getr regs 10 = Z_to_bv 64 (c + 4) /\
  getr regs 11 = Z_to_bv 64 0 /\ getr regs 12 = Z_to_bv 64 0 /\
  (exists g a b cc d e f : word,
     cell mem (c + 4) 4 g /\ cell mem (c + 8) 4 a /\ cell mem (c + 12) 4 b /\
     cell mem (c + 16) 4 cc /\ cell mem (c + 20) 4 d /\ cell mem (c + 24) 4 e /\
     cell mem (c + 28) 4 f) /\
  (c mod 8 = 0) /\ heapish ceil c 32 /\ shz mem c 4 /\
  env_ro (al_abi L) mem /\ as_sb segs L mem /\ as_frame segs ceil mem sp CLASSIFY_D.

Definition classify_post_as (sp C : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - CLASSIFY_D), CLASSIFY_D)].

Definition classify_contract_as : Prop :=
  forall sp C, fn_contract segs (al_classify L) (classify_pre_as sp C) (classify_post_as sp C).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rcurve_pre_as (data : word) (len : Z) (bs : list byte)
    (sp buf C cs : word) (size : Z)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let c := bv_unsigned C in
  let A := al_abi L in
  getr regs 2 = sp /\ getr regs 10 = buf /\ getr regs 11 = Z_to_bv 64 size /\
  getr regs 12 = C /\ getr regs 13 = cs /\
  as_data_ok ceil mem data len bs /\ 0 <= size < 2 ^ 32 /\ inDATA data len (bv_unsigned buf) size /\
  writable mem c 32 /\ (c mod 8 = 0) /\ heapish ceil c 32 /\ shz mem c 4 /\ shwz mem (c + 12) 20 /\
  (bv_unsigned data + len <= c \/ c + 32 <= bv_unsigned data) /\
  env_ro A mem /\ env_shb A mem /\ env_cells segs A mem /\
  as_frame segs ceil mem sp RCURVE_D /\
  (bv_unsigned cs = 0 \/
   (writable mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0) /\ stackish ceil (bv_unsigned cs) 4 /\
    shbyte mem (bv_unsigned cs) 0 /\ bv_unsigned sp <= bv_unsigned cs)).

Definition rcurve_post_as (data : word) (len : Z) (bs : list byte)
    (sp buf C cs : word) (size : Z)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let c := bv_unsigned C in
  frame_mod mem mem'
    ((Z_to_bv 64 (bv_unsigned sp - RCURVE_D), RCURVE_D) :: (C, 32)
      :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4)])) /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
    (r = 1 -> curve_ok mem' data len c) /\
    (curve_ok mem data len c -> curve_ok mem' data len c) /\
    (bv_unsigned cs <> 0 -> r = 1 -> exists v, cell32 mem' (bv_unsigned cs) v).

Definition read_curve_contract_as : Prop :=
  forall data len bs sp buf C cs size,
    fn_contract segs (al_rcurve L)
      (rcurve_pre_as data len bs sp buf C cs size)
      (rcurve_post_as data len bs sp buf C cs size).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rcurves_pre_as (data : word) (len : Z) (bs : list byte)
    (sp buf C : word) (size : Z) (offw : word) (k : Z)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let c := bv_unsigned C in
  let A := al_abi L in
  getr regs 2 = sp /\ getr regs 10 = buf /\ getr regs 11 = Z_to_bv 64 size /\
  getr regs 12 = offw /\ getr regs 13 = Z_to_bv 64 k /\ getr regs 14 = C /\
  as_data_ok ceil mem data len bs /\ 0 <= size < 2 ^ 32 /\
  inDATA data len (bv_unsigned buf) size /\
  0 <= k <= 4 /\ (0 < k -> writable mem c (32 * k)) /\ (c mod 8 = 0) /\
  (0 < k -> heapish ceil c (32 * k) /\ shz mem c (4 * k) /\ forall i, 0 <= i < k -> shwz mem (c + 32 * i + 12) 20) /\
  (bv_unsigned data + len <= c \/ c + 32 * k <= bv_unsigned data) /\
  env_ro A mem /\ env_shb A mem /\ env_cells segs A mem /\
  as_frame segs ceil mem sp RCURVES_D /\ shz mem (bv_unsigned sp - 80) 10.

Definition rcurves_post_as (data : word) (len : Z) (bs : list byte)
    (sp buf C : word) (size : Z) (offw : word) (k : Z)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let c := bv_unsigned C in
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - RCURVES_D), RCURVES_D); (Z_to_bv 64 c, 32 * k)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 -> forall i, 0 <= i < k -> curve_ok mem' data len (c + 32 * i)).

Definition read_curves_contract_as : Prop :=
  forall data len bs sp buf C size offw k,
    fn_contract segs (al_rcurves L)
      (rcurves_pre_as data len bs sp buf C size offw k)
      (rcurves_post_as data len bs sp buf C size offw k).

End Specs.
