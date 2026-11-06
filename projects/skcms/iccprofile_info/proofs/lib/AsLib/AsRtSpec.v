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

Section Specs.
Variable segs : list Segment.
Variable L : as_lib.
Variable ceil : Z.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition setsh_pre (d : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  getr regs 10 = d /\ getr regs 11 = Z_to_bv 64 122 /\
  (bv_unsigned d mod 8 = 0)%Z /\ writable segs mem (bv_unsigned d) 122 /\ env_cells segs (al_abi L) mem.

Definition setsh00_post (d : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(d, 122%Z)] /\
  (forall i, (0 <= i < 122)%Z -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0)).

Definition setshf8_post (d : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(d, 122%Z)].

Definition setsh00_contract : Prop := forall d, fn_contract segs (al_setsh00 L) (setsh_pre d) (setsh00_post d).
Definition setshf8_contract : Prop := forall d, fn_contract segs (al_setshf8 L) (setsh_pre d) (setshf8_post d).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stkfree5_pre (F flagp : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  getr regs 10 = F /\ (bv_unsigned F mod 2048 = 0)%Z /\ heapish ceil (bv_unsigned F) 2048 /\
  acellw segs mem (bv_unsigned F + 2040) flagp /\ heapish ceil (bv_unsigned flagp) 1 /\ writable segs mem (bv_unsigned flagp) 1 /\
  writable segs mem (AS_SB + bv_unsigned F / 8) 256 /\
  env_cells segs (al_abi L) mem /\ env_ro (al_abi L) mem /\
  (exists sp, getr regs 2 = sp /\ as_frame segs ceil mem sp 16).

Definition stkfree5_post (F flagp : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned (getr regs 2) - 16), 16%Z); (flagp, 1%Z);
                      (Z_to_bv 64 (AS_SB + bv_unsigned F / 8), 256%Z)] /\
  mem' flagp = Some (Z_to_bv 8 0).

Definition stkfree5_contract : Prop :=
  forall F flagp, fn_contract segs (al_stkfree5 L) (stkfree5_pre F flagp) (stkfree5_post F flagp).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sm_pos (nfr : Z) (h : word) : Z := (bv_unsigned h mod nfr)%Z.
Definition sm_frame (cid fsz fs pos : Z) : Z := (fs + FS_FRAMES0 + cid * 2 ^ 20 + fsz * pos)%Z.
Definition sm_flag (foff fs pos : Z) : Z := (fs + FS_FLAGS0 + foff + pos)%Z.

Definition stkmalloc_pre (cid nfr fsz foff : Z) (fs : Z) (h : word) (c : chain)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let pos := sm_pos nfr h in let F := sm_frame cid fsz fs pos in let fa := sm_flag foff fs pos in
  getr regs 4 = Z_to_bv 64 (aa_tp (al_abi L)) /\
  as_env segs ceil (al_abi L) fs c mem /\ fs_hdr segs ceil (al_abi L) fs mem /\
  acellw segs mem (fs + 8 * cid) h /\ mem (Z_to_bv 64 fa) = Some (Z_to_bv 8 0) /\
  writable segs mem (fs + 8 * cid) 8 /\ writable segs mem fa 1 /\
  writable segs mem F fsz /\ writable segs mem (AS_SB + F / 8) (fsz / 8) /\
  (exists sp, getr regs 2 = sp /\ as_frame segs ceil mem sp 208).

Definition stkmalloc_post (cid nfr fsz foff : Z) (fs : Z) (h : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let pos := sm_pos nfr h in let F := sm_frame cid fsz fs pos in let fa := sm_flag foff fs pos in
  getr regs' 10 = Z_to_bv 64 F /\
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned (getr regs 2) - 208), 208%Z); (Z_to_bv 64 (fs + 8 * cid), 8%Z);
                      (Z_to_bv 64 fa, 1%Z); (Z_to_bv 64 (F + 24), 8%Z); (Z_to_bv 64 (F + fsz - 8), 8%Z);
                      (Z_to_bv 64 (AS_SB + F / 8), fsz / 8)%Z] /\
  acellw segs mem' (fs + 8 * cid) (Z_to_bv 64 (bv_unsigned h + 1)) /\
  acell segs mem' (F + fsz - 8) 8 fa.
  (* [comment removed for export] *)

Definition stkmalloc0_contract : Prop :=
  forall fs h c, fn_contract segs (al_stkmalloc0 L) (stkmalloc_pre 0 16384 64 0 fs h c) (stkmalloc_post 0 16384 64 0 fs h).
Definition stkmalloc5_contract : Prop :=
  forall fs h c, fn_contract segs (al_stkmalloc5 L) (stkmalloc_pre 5 512 2048 0x7c00 fs h c) (stkmalloc_post 5 512 2048 0x7c00 fs h).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shwz (mem : word -> option byte) (a n : Z) : Prop :=
  forall x, (8 * ((AS_SB + a / 8) / 8) <= x < 8 * ((AS_SB + (a + n - 1) / 8) / 8) + 8)%Z -> mem (Z_to_bv 64 x) = Some (Z_to_bv 8 0).

Definition imemset_pre (n al fd : Z) (d : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  getr regs 10 = d /\ getr regs 11 = Z_to_bv 64 0 /\ getr regs 12 = Z_to_bv 64 n /\
  (bv_unsigned d mod al = 0)%Z /\ heapish ceil (bv_unsigned d) n /\ writable segs mem (bv_unsigned d) n /\
  (if (Z.leb n 64) then shwz mem (bv_unsigned d) n else shz mem (bv_unsigned d) 122) /\
  env_cells segs (al_abi L) mem /\
  (exists sp, getr regs 2 = sp /\ as_frame segs ceil mem sp fd).

Definition imemset_post (n fd : Z) (d : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned (getr regs 2) - fd), fd); (d, n)] /\
  (forall i, (0 <= i < n)%Z -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0)) /\
  getr regs' 10 = d.

Definition imemset976_contract : Prop := forall d, fn_contract segs (al_imemset L) (imemset_pre 976 64 2208 d) (imemset_post 976 2208 d).
Definition imemset20_contract : Prop := forall d, fn_contract segs (al_imemset L) (imemset_pre 20 4 2128 d) (imemset_post 20 2128 d).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition imemcpy32_pre (o : Z) (P w0 w1 w2 w3 : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  getr regs 10 = Z_to_bv 64 (bv_unsigned P + o) /\ getr regs 11 = Z_to_bv 64 (bv_unsigned P + 24) /\
  getr regs 12 = Z_to_bv 64 32 /\
  (bv_unsigned P mod 64 = 0)%Z /\ heapish ceil (bv_unsigned P) 976 /\ writable segs mem (bv_unsigned P + o) 32 /\
  shz mem (bv_unsigned P) 122 /\
  cell64 segs mem (bv_unsigned P + 24) w0 /\ cell64 segs mem (bv_unsigned P + 32) w1 /\
  cell64 segs mem (bv_unsigned P + 40) w2 /\ cell64 segs mem (bv_unsigned P + 48) w3 /\
  env_cells segs (al_abi L) mem /\
  (exists sp, getr regs 2 = sp /\ as_frame segs ceil mem sp 2144).

Definition imemcpy32_post (o : Z) (P w0 w1 w2 w3 : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned (getr regs 2) - 2144), 2144%Z); (Z_to_bv 64 (bv_unsigned P + o), 32%Z)] /\
  cell64 segs mem' (bv_unsigned P + o) w0 /\ cell64 segs mem' (bv_unsigned P + o + 8) w1 /\
  cell64 segs mem' (bv_unsigned P + o + 16) w2 /\ cell64 segs mem' (bv_unsigned P + o + 24) w3 /\
  getr regs' 10 = Z_to_bv 64 (bv_unsigned P + o).

Definition imemcpy32_contract : Prop :=
  forall o P w0 w1 w2 w3, (o = 56%Z \/ o = 88%Z) ->
    fn_contract segs (al_imemcpy L) (imemcpy32_pre o P w0 w1 w2 w3) (imemcpy32_post o P w0 w1 w2 w3).

End Specs.
