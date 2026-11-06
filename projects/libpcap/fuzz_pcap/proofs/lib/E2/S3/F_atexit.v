(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.AmoStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation ATEXIT_ENTRY := 0x18344%Z (only parsing).
Notation ATEXIT := 0x53ae0%Z (only parsing).           (* [comment removed for export] *)
Notation BUILTIN := 0x53af8%Z (only parsing).          (* [comment removed for export] *)
Notation LIBC := 0x53d28%Z (only parsing).
Notation CALL_THUNK := 0x18408%Z (only parsing).

Section WithCeil.
Context {CEILV : CEIL}.

Definition atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (func : word) (pad3 pad4 j1 j2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x53ae8, 0x53af8); (0x53b00, 0x53b08); (0x53c00, 0x53c08)]%Z m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' ATEXIT (atexit_cells (Z_to_bv 8 0) pad3 (Z_to_bv 64 1) pad4 (Z_to_bv 64 BUILTIN))
    /\ rw_cells ssegs m' BUILTIN (builtin_cells (Z_to_bv 64 CALL_THUNK) j1 func j2).

Lemma atexit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z)
    (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte)
    (pad3 pad4 : list byte) (f0 g0 : word) (j1 j2 : list byte),
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m LIBC (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc) ->      (* [comment removed for export] *)
  rw_cells ssegs m ATEXIT (atexit_cells (Z_to_bv 8 0) pad3 z64 pad4 z64) ->                       (* [comment removed for export] *)
  rw_cells ssegs m BUILTIN (builtin_cells f0 j1 g0 j2) ->
  mem_inv ssegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (alloc_ceiling <= lo)%Z ->
  evt ssegs (atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo a0 pad3 pad4 j1 j2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATEXIT_ENTRY) fc None m (seg_rom ssegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros until j2. intros ST LC ATX BLT MI LO LOLO.
  unfold libc_cells, atexit_cells, builtin_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x53ae8, 0x53af8); (0x53b00, 0x53b08); (0x53c00, 0x53c08)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  carve_frame 48%nat ST.
  (* [comment removed for export] *)
  steps_to 0x21154%Z. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
  (* [comment removed for export] *)
  steps_to 0x1837c%Z. lstep. if_false. lstep. lstep. if_false. lstep. lstep. lstep. lstep. lstep.
  change (sx32 z64) with z64. if_true.
  (* [comment removed for export] *)
  steps_to 0x213d8%Z. change (sx32 z64) with z64. astep. astep.
  steps_to 0x18404%Z. release_frame FR ST (bv_unsigned sp). astep.
  unfold atexit_post, atexit_cells, builtin_cells. finish.
Qed.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.AmoStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation ATEXIT_ENTRY := 0x18b04%Z (only parsing).
Notation ATEXIT := 0x542a0%Z (only parsing).           (* [comment removed for export] *)
Notation BUILTIN := 0x542b8%Z (only parsing).          (* [comment removed for export] *)
Notation LIBC := 0x544e8%Z (only parsing).
Notation CALL_THUNK := 0x18bc8%Z (only parsing).

Section WithCeil.
Context {CEILV : CEIL}.

Definition atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (func : word) (pad3 pad4 j1 j2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x542a8, 0x542b8); (0x542c0, 0x542c8); (0x543c0, 0x543c8)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' ATEXIT (atexit_cells (Z_to_bv 8 0) pad3 (Z_to_bv 64 1) pad4 (Z_to_bv 64 BUILTIN))
    /\ rw_cells usegs m' BUILTIN (builtin_cells (Z_to_bv 64 CALL_THUNK) j1 func j2).

Lemma atexit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z)
    (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte)
    (pad3 pad4 : list byte) (f0 g0 : word) (j1 j2 : list byte),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m LIBC (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc) ->      (* [comment removed for export] *)
  rw_cells usegs m ATEXIT (atexit_cells (Z_to_bv 8 0) pad3 z64 pad4 z64) ->                       (* [comment removed for export] *)
  rw_cells usegs m BUILTIN (builtin_cells f0 j1 g0 j2) ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (alloc_ceiling <= lo)%Z ->
  evt usegs (atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo a0 pad3 pad4 j1 j2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATEXIT_ENTRY) fc None m (seg_rom usegs)).
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
  intros until j2. intros ST LC ATX BLT MI LO LOLO.
  unfold libc_cells, atexit_cells, builtin_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x542a8, 0x542b8); (0x542c0, 0x542c8); (0x543c0, 0x543c8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  (* [comment removed for export] *)
  steps_to 0x21914%Z. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
  (* [comment removed for export] *)
  steps_to 0x18b3c%Z. lstep. if_false. lstep. lstep. if_false. lstep. lstep. lstep. lstep. lstep.
  change (sx32 z64) with z64. if_true.
  (* [comment removed for export] *)
  steps_to 0x21b98%Z. change (sx32 z64) with z64. astep. astep.
  steps_to 0x18bc4%Z. release_frame FR ST (bv_unsigned sp). astep.
  unfold atexit_post, atexit_cells, builtin_cells. finish.
Qed.

End WithCeil.
End TwB.
