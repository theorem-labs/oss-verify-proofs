(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import StrFun STRW_tac Startup_kit Amo_tac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg F_syscalls Startup_A PAtexit_cells.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation rsegs := PImg.psegs.

(* [comment removed for export] *)
Definition ATEXIT_W (sp : Z) : list (Z * Z) := [(sp - 48, sp); (0x103a70, 0x103c90)]%Z.

Definition atexit1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo func : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x103a70, 0x103c90)]%Z m m'     (* [comment removed for export] *)
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ patx_table 2 PCALL_THUNK func 0 0 m'.

(* [comment removed for export] *)
Lemma atexit1_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m PNEED_LOCKS_ROW [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->      (* [comment removed for export] *)
  patexit_main m ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 PAEF_GUARD ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x105000 <= lo)%Z ->
  evt rsegs (atexit1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo PAEF_GUARD m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PATEXIT) fc None m (seg_rom rsegs)).
Proof.
  intros until tm1. intros ST LIBC (HDR & TBL & F2 & ARGS & A2) MI -> LO LOLO.
  unfold PNEED_LOCKS_ROW in LIBC. unfold PAEF_GUARD, PATEXIT.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x103a70, 0x103c90)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  (* [comment removed for export] *)
  steps_to 0xc5028%Z.          (* [comment removed for export] *)
  steps_to 0xb3568%Z.          (* [comment removed for export] *)
  steps_to 0xb3588%Z.          (* [comment removed for export] *)
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
  steps_to 0xc52b0%Z.          (* [comment removed for export] *)
  steps_to 0xb35dc%Z.          (* [comment removed for export] *)
  do 6 astep.
  release_frame FR ST (bv_unsigned sp)%Z.
  astep. astep.
  unfold atexit1_post. apply evt_done.
  do 15 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  unfold patx_table, PCALL_THUNK.
  repeat match goal with |- _ /\ _ => split end; hyp_by_addr.
Qed.
