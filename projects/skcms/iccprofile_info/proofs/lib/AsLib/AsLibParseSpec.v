(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame LibDefs LibTagsSpec.
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

Definition PARSE_D : Z := 2896.

Section Specs.
Variable segs : list Segment.
Variable L : as_lib.
Variable ceil : Z.   (* [comment removed for export] *)

Definition parse_pre_as (data : word) (len : Z) (bs : list byte) (sp prio P : word) (fs : Z) (ch : chain)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let p := bv_unsigned P in
  let q := bv_unsigned prio in
  let s := bv_unsigned sp in
  let A := al_abi L in
  getr regs 2 = sp /\ getr regs 10 = data /\ getr regs 11 = Z_to_bv 64 len /\
  getr regs 12 = prio /\ getr regs 13 = Z_to_bv 64 2 /\ getr regs 14 = P /\ getr regs 4 = Z_to_bv 64 (aa_tp A) /\
  as_data_ok ceil mem data len bs /\ (bv_unsigned data + len <= fs \/ fs + FS_SIZE <= bv_unsigned data) /\
  (* [comment removed for export] *)
  cell32 segs mem q 0 /\ cell32 segs mem (q + 4) 1 /\ (q mod 8 = 0) /\ heapish ceil q 8 /\ shz mem q 1 /\
  (fs + FS_FRAMES5 <= q) /\ (q + 8 <= fs + FS_SIZE) /\ (q + 8 <= p \/ p + 976 <= q) /\
  (* [comment removed for export] *)
  writable segs mem p 976 /\ (p mod 64 = 0) /\ heapish ceil p 976 /\ shz mem p 122 /\
  (fs + FS_FRAMES5 <= p) /\ (p + 976 <= fs + FS_SIZE) /\
  (* [comment removed for export] *)
  as_frame segs ceil mem sp PARSE_D /\ shz mem (s - PARSE_D) (PARSE_D / 8) /\
  (* [comment removed for export] *)
  as_env segs ceil A fs ch mem /\ fs_hdr segs ceil A fs mem /\ fs_writable segs fs mem /\
  (exists h, acellw segs mem (fs + FS_HINT0) h) /\ fs_flags0_but fs [] mem.

Definition parse_post_as (data : word) (len : Z) (bs : list byte) (sp prio P : word) (fs : Z) (ch : chain)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' ([(Z_to_bv 64 (bv_unsigned sp - PARSE_D), PARSE_D); (P, 976)] ++ fs_mod0 fs) /\
  fs_flags0_but fs [] mem' /\ (exists h', acellw segs mem' (fs + FS_HINT0) h') /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
    (r = 1 -> parsed_ok segs mem' data len bs (bv_unsigned P)).

Definition parse_contract_as : Prop :=
  forall data len bs sp prio P fs ch,
    fn_contract segs (al_parse L)
      (parse_pre_as data len bs sp prio P fs ch)
      (parse_post_as data len bs sp prio P fs ch).

End Specs.
