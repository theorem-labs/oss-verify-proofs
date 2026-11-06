(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import STRW_tac Images RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Local Ltac xastep := lstep; try (first [if_true | if_false]).
Local Ltac xat_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Local Ltac xsteps_to p := repeat (tryif xat_pc p then fail else xastep).

Notation RATX := 0x54d88%Z (only parsing).          (* [comment removed for export] *)
Notation RATX_BUILTIN := 0x54da0%Z (only parsing).  (* [comment removed for export] *)
Notation RATX_CALL := 0x17578%Z (only parsing).     (* [comment removed for export] *)
Notation RATXFLAG := 0x34c40%Z (only parsing).          (* [comment removed for export] *)
Notation RATXFLAG_GUARD := 0x138fc%Z (only parsing).    (* [comment removed for export] *)
Notation RXLIBC := 0x54fd0%Z (only parsing).        (* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Definition atx_cells (reg : bool) (p3 p4 FJ AJ : list byte) : list cell :=
  [C1 (Z_to_bv 8 0); CB 3 p3; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (if reg then 1 else 0)); CB 4 p4;
   C8 (Z_to_bv 64 (if reg then RATX_BUILTIN else 0)); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 (if reg then RATX_CALL else 0)); CB 248 FJ;
   C8 (Z_to_bv 64 (if reg then RATXFLAG_GUARD else 0)); CB 248 AJ].

Definition ratexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' p3 p4 FJ AJ,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (RATX, RATX + 544)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' RATX (atx_cells true p3 p4 FJ AJ).

Lemma ratexit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (p3 p4 FJ AJ : list byte) (cdt thr sec : byte) (tm1 : word),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m RATX (atx_cells false p3 p4 FJ AJ) ->
  rw_cells rsegs m RXLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 RATXFLAG_GUARD ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x56000 <= lo)%Z ->
  evt rsegs (ratexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x174b4) fc None m (seg_rom rsegs)).
Proof.
  intros until tm1. intros ST ATX LCH MI -> LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (RATX, RATX + 544)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold atx_cells in ATX.
  carve_frame 48%nat ST.
  xsteps_to 0x224b8%Z.
  xsteps_to 0x174e4%Z.
  xsteps_to 0x17504%Z.
  replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  xsteps_to 0x22740%Z.
  xsteps_to 0x17558%Z.
  xsteps_to 0x17574%Z.
  release_frame FR ST (bv_unsigned sp). xastep.
  unfold ratexit_post. sys_finish.
  exact ATX.
Time Qed.

(* [comment removed for export] *)
Definition rfoe_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (RATX, RATX + 544)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma rfoe_spec : forall (reg : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (p3 p4 FJ AJ : list byte) (cdt thr sec : byte) (tm1 : word),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m RATX (atx_cells reg p3 p4 FJ AJ) ->
  rw_cells rsegs m (RATXFLAG + 4) [C1 (Z_to_bv 8 0)] ->
  rw_cells rsegs m RXLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x56000 <= lo)%Z ->
  evt rsegs (rfoe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x173e8) fc None m (seg_rom rsegs)).
Proof.
  intros until tm1. intros ST ATX FLG LCH MI LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (RATX, RATX + 544)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold atx_cells in ATX. change (RATXFLAG + 4)%Z with 0x34c44%Z in FLG.
  destruct reg; cbv iota in ATX.
  - (* [comment removed for export] *)
    carve_frame 48%nat ST.
    xsteps_to 0x224b8%Z. xsteps_to 0x17414%Z.
    xsteps_to 0x17420%Z.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    xsteps_to 0x17440%Z.
    xastep.
    xsteps_to 0x22740%Z. xsteps_to 0x17460%Z.
    xsteps_to 0x17578%Z. xsteps_to 0x138fc%Z. xsteps_to 0x17468%Z.
    xsteps_to 0x224b8%Z. xsteps_to 0x17470%Z.
    xastep.
    replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
    xsteps_to 0x17494%Z.
    xsteps_to 0x22740%Z. release_frame FR ST (bv_unsigned sp).
    xsteps_to 0x22748%Z. xastep.
    unfold rfoe_post. sys_finish.
  - (* [comment removed for export] *)
    carve_frame 48%nat ST.
    xsteps_to 0x224b8%Z. xsteps_to 0x17414%Z.
    xsteps_to 0x17494%Z.
    xsteps_to 0x22740%Z. release_frame FR ST (bv_unsigned sp).
    xsteps_to 0x22748%Z. xastep.
    unfold rfoe_post. sys_finish.
Time Qed.
End RC__1.
