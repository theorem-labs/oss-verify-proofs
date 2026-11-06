(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame LibDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibShadow AsLibDefs.
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

#[local] Notation cell32 := (cell32 segs).
#[local] Notation cell64 := (cell64 segs).
#[local] Notation cell8 := (cell8 segs).
#[local] Notation writable := (writable segs).
#[local] Notation tag_ok := (tag_ok segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gettag_pre_as (data : word) (len : Z) (bs : list byte)
    (P : word) (tc psz sig : Z) (T : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let p := bv_unsigned P in
  let t := bv_unsigned T in
  getr regs 10 = P /\ getr regs 11 = Z_to_bv 64 sig /\ getr regs 12 = T /\
  0 <= sig < 2 ^ 32 /\
  as_data_ok ceil mem data len bs /\
  cell64 mem p data /\ cell32 mem (p + 20) tc /\ tags_ok len bs tc psz /\
  (p mod 8 = 0) /\ heapish ceil p 24 /\ shz mem p 3 /\
  (t mod 8 = 0) /\ stackish ceil t 24 /\ writable mem t 24 /\ shz mem t 3 /\
  as_sb segs L mem /\
  (exists sp, getr regs 2 = sp /\ as_frame segs ceil mem sp 16 /\
              (t + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= t)).

Definition gettag_post_as (data : word) (len : Z) (bs : list byte)
    (P : word) (tc psz sig : Z) (T : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let t := bv_unsigned T in
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned (getr regs 2) - 16), 16); (T, 24)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
    (r = 1 ->
       tag_ok mem' data len t /\ cell32 mem' t sig /\ (exists ty, cell32 mem' (t + 4) ty)).

Definition gettag_contract_as : Prop :=
  forall data len bs P tc psz sig T,
    fn_contract segs (al_gettag L)
      (gettag_pre_as data len bs P tc psz sig T)
      (gettag_post_as data len bs P tc psz sig T).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition getidx_pre_as (data : word) (len : Z) (bs : list byte)
    (P : word) (tc psz idx : Z) (T : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let p := bv_unsigned P in
  let t := bv_unsigned T in
  getr regs 10 = P /\ getr regs 11 = Z_to_bv 64 idx /\ getr regs 12 = T /\
  0 <= idx < tc /\
  as_data_ok ceil mem data len bs /\
  cell64 mem p data /\ cell32 mem (p + 20) tc /\ tags_ok len bs tc psz /\
  (p mod 8 = 0) /\ heapish ceil p 24 /\ shz mem p 3 /\
  (t mod 8 = 0) /\ heapish ceil t 24 /\ writable mem t 24 /\ shz mem t 3 /\
  (bv_unsigned data + len <= t \/ t + 24 <= bv_unsigned data) /\
  (p + 24 <= t \/ t + 24 <= p) /\
  as_sb segs L mem /\
  (exists sp, getr regs 2 = sp /\ as_frame segs ceil mem sp 16).

Definition getidx_post_as (data : word) (len : Z) (bs : list byte)
    (P : word) (tc psz idx : Z) (T : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let t := bv_unsigned T in
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned (getr regs 2) - 16), 16); (T, 24)] /\
  tag_ok mem' data len t /\ (exists s, cell32 mem' t s) /\ (exists ty, cell32 mem' (t + 4) ty).

Definition getidx_contract_as : Prop :=
  forall data len bs P tc psz idx T,
    fn_contract segs (al_getidx L)
      (getidx_pre_as data len bs P tc psz idx T)
      (getidx_post_as data len bs P tc psz idx T).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fcell_ok_as (mem : word -> option byte) (data : word) (len : Z) (X : word) : Prop :=
  let x := bv_unsigned X in
  writable mem x 4 /\ (x mod 4 = 0) /\ heapish ceil x 4 /\ shbyte mem x 0 /\
  (bv_unsigned data + len <= x \/ x + 4 <= bv_unsigned data).

Definition tagxyz_pre_as (data : word) (len : Z) (bs : list byte) (T X Y Zc : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let t := bv_unsigned T in
  getr regs 10 = T /\ getr regs 11 = X /\ getr regs 12 = Y /\ getr regs 13 = Zc /\
  as_data_ok ceil mem data len bs /\
  (exists ty, cell32 mem (t + 4) ty) /\ tag_ok mem data len t /\
  (t mod 8 = 0) /\ stackish ceil t 24 /\ shz mem t 3 /\
  fcell_ok_as mem data len X /\ fcell_ok_as mem data len Y /\ fcell_ok_as mem data len Zc /\
  as_sb segs L mem /\
  (exists sp, getr regs 2 = sp /\ as_frame segs ceil mem sp 16 /\
              (t + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= t)).

Definition tagxyz_post_as (data : word) (len : Z) (bs : list byte) (T X Y Zc : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned (getr regs 2) - 16), 16); (X, 4); (Y, 4); (Zc, 4)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1).

Definition tagxyz_contract_as : Prop :=
  forall data len bs T X Y Zc,
    fn_contract segs (al_tagxyz L)
      (tagxyz_pre_as data len bs T X Y Zc)
      (tagxyz_post_as data len bs T X Y Zc).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition XYZD50_D : Z := 48.

Definition xtag_ok_as (mem : word -> option byte) (data : word) (len : Z) (sp : word) (T : word) : Prop :=
  let t := bv_unsigned T in
  (exists ty, cell32 mem (t + 4) ty) /\ tag_ok mem data len t /\
  (t mod 8 = 0) /\ stackish ceil t 24 /\ shz mem t 3 /\
  (bv_unsigned sp <= t \/ t + 24 <= bv_unsigned sp - XYZD50_D).

Definition xyzd50_pre_as (data : word) (len : Z) (bs : list byte) (sp T1 T2 T3 M : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let m := bv_unsigned M in
  getr regs 2 = sp /\ getr regs 10 = T1 /\ getr regs 11 = T2 /\ getr regs 12 = T3 /\ getr regs 13 = M /\
  as_data_ok ceil mem data len bs /\
  xtag_ok_as mem data len sp T1 /\ xtag_ok_as mem data len sp T2 /\ xtag_ok_as mem data len sp T3 /\
  writable mem m 36 /\ (m mod 4 = 0) /\ heapish ceil m 36 /\ shz mem (m - m mod 8) 5 /\
  (bv_unsigned data + len <= m \/ m + 36 <= bv_unsigned data) /\
  as_sb segs L mem /\ as_frame segs ceil mem sp XYZD50_D.

Definition xyzd50_post_as (data : word) (len : Z) (bs : list byte) (sp T1 T2 T3 M : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - XYZD50_D), XYZD50_D); (M, 36)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1).

Definition xyzd50_contract_as : Prop :=
  forall data len bs sp T1 T2 T3 M,
    fn_contract segs (al_xyzd50 L)
      (xyzd50_pre_as data len bs sp T1 T2 T3 M)
      (xyzd50_post_as data len bs sp T1 T2 T3 M).

End Specs.
