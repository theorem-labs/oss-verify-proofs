(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Stdio.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Exec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Fmt PcapPrelim PcapTypes PcapPure Pcap Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module Exit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.AmoStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation EXIT := 0x1845c%Z (only parsing).
Notation STDIO_EXIT := 0x1ae7c%Z (only parsing).
Notation STDIO_EXIT_RET := 0x184c8%Z (only parsing).   (* [comment removed for export] *)
Notation EXIT_LOCK := 0x53d00%Z (only parsing).
Notation ATEXIT := 0x53ae0%Z (only parsing).           (* [comment removed for export] *)
Notation LIBC := 0x53d28%Z (only parsing).
Notation GOT_FINI := 0x22628%Z (only parsing).         (* [comment removed for export] *)
Notation FINI_ARRAY := 0x22558%Z (only parsing).
Notation FINALIZED := 0x23988%Z (only parsing).
Notation GOT_CXA := 0x225a8%Z (only parsing).          (* [comment removed for export] *)
Notation DSO_HANDLE := 0x23638%Z (only parsing).
(* [comment removed for export] *)
Notation BUILTIN := 0x53af8%Z (only parsing).
Notation EXIT_CB_FLAG := 0x33994%Z (only parsing).         (* [comment removed for export] *)
Notation CALL_THUNK := 0x18408%Z (only parsing).
Notation EXIT_CB_FN := 0x13f38%Z (only parsing).

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition exit_footprint : list (Z * Z) :=
  [(EXIT_LOCK, 0x53d04); (ATEXIT, 0x53af8); (FINALIZED, 0x23989); (alloc_ceiling, 2^64)]%Z.

Definition exit_agrees (m m' : word -> option byte) : Prop := munch exit_footprint m m'.

(* [comment removed for export] *)
Definition atexit_cells (fa : byte) (pad3 : list byte) (slot : word) (pad4 : list byte) (head : word) : list cell :=
  [C1 fa; CB 3 pad3; C4 z64; C4 slot; CB 4 pad4; C8 head].

(* [comment removed for export] *)
Definition builtin_cells (f0 : word) (j1 : list byte) (g0 : word) (j2 : list byte) : list cell :=
  [C8 z64; C8 f0; CB 248 j1; C8 g0; CB 248 j2].
(* [comment removed for export] *)
Definition bool8 (b : bool) : byte := if b then Z_to_bv 8 1 else Z_to_bv 8 0.
Definition atx_slot (reg : bool) : word := if reg then Z_to_bv 64 1 else z64.
Definition atx_head (reg : bool) : word := if reg then Z_to_bv 64 BUILTIN else z64.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExitProof.
  Context {St : Type} (stdio_exit_model : M St unit).
  (* [comment removed for export] *)
  Variable SX : St -> word -> (word -> option byte) -> Prop.
  (* [comment removed for export] *)
  Variable stdio_exit_frame : Z.
  Hypothesis stdio_exit_frame_nonneg : (0 <= stdio_exit_frame)%Z.

  (* [comment removed for export] *)
  Hypothesis SX_frame : forall s tp m m',
    SX s tp m -> munch exit_footprint m m' -> wmono ssegs m m' -> SX s tp m'.

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom ssegs).

  (* [comment removed for export] *)
  Definition stdio_exit_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St)
           (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte),
      stk ssegs m lo (bv_unsigned sp) ->
      SX s tp m ->
      rw_cells ssegs m LIBC (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc) ->   (* [comment removed for export] *)
      mem_inv ssegs m ->
      (lo <= bv_unsigned sp - stdio_exit_frame)%Z -> (alloc_ceiling <= lo)%Z ->
      (bv_unsigned sp <= 2^47)%Z ->      (* [comment removed for export] *)
      implM ssegs stdio_exit_model s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 STDIO_EXIT) fc None m (seg_rom ssegs)).

  Hypothesis stdio_exit_spec : stdio_exit_stmt.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition exit_prefix_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo code t : Z) (td0 td1 td2 td3 ra : word) (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte)
      (pad3 : list byte) (slot : word) (pad4 : list byte) (dso : word)
      (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR (Z_to_bv 64 STDIO_EXIT_RET) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
                   a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 STDIO_EXIT) fc None m' (seg_rom ssegs)
      /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (EXIT_LOCK, 0x53d04); (ATEXIT, 0x53af8); (FINALIZED, 0x23989)]%Z m m'
      /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp + -16)
      /\ rw_cells ssegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
      /\ rw_cells ssegs m' (bv_unsigned tp + -200) [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
      /\ rw_cells ssegs m' EXIT_LOCK [C4 (Z_to_bv 64 t)]
      /\ rw_cells ssegs m' LIBC (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc)
      /\ rw_cells ssegs m' ATEXIT (atexit_cells (Z_to_bv 8 1) pad3 slot pad4 z64)
      /\ rw_cells ssegs m' GOT_FINI [C8 (Z_to_bv 64 0x22560); C8 (Z_to_bv 64 FINI_ARRAY)]
      /\ rw_cells ssegs m' FINI_ARRAY [C8 (Z_to_bv 64 0x13a80)]
      /\ rw_cells ssegs m' FINALIZED [C1 (Z_to_bv 8 1)]
      /\ rw_cells ssegs m' GOT_CXA [C8 (Z_to_bv 64 0x18340); C8 z64]
      /\ rw_cells ssegs m' DSO_HANDLE [C8 dso]
      /\ exit_agrees m m'.

  Definition exit_prefix_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo code t : Z) (td0 td1 td2 td3 : word)
      (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte)
      (fa : byte) (pad3 : list byte) (slot : word) (pad4 : list byte) (dso : word),
    stk ssegs m lo (bv_unsigned sp) ->
    rw_cells ssegs m (bv_unsigned tp + -200) [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->   (* [comment removed for export] *)
    rw_cells ssegs m EXIT_LOCK [C4 z64] ->
    rw_cells ssegs m LIBC (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc) ->      (* [comment removed for export] *)
    rw_cells ssegs m ATEXIT (atexit_cells fa pad3 slot pad4 z64) ->                                 (* [comment removed for export] *)
    rw_cells ssegs m GOT_FINI [C8 (Z_to_bv 64 0x22560); C8 (Z_to_bv 64 FINI_ARRAY)] ->
    rw_cells ssegs m FINI_ARRAY [C8 (Z_to_bv 64 0x13a80)] ->                                          (* [comment removed for export] *)
    rw_cells ssegs m FINALIZED [C1 (Z_to_bv 8 0)] ->
    rw_cells ssegs m GOT_CXA [C8 (Z_to_bv 64 0x18340); C8 z64] ->
    rw_cells ssegs m DSO_HANDLE [C8 dso] ->
    mem_inv ssegs m ->
    a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 80)%Z -> (alloc_ceiling <= lo)%Z ->
    tls_block_ok (bv_unsigned tp - 200) ->
    evt ssegs (exit_prefix_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra
                 cdt thr sec tm1 auxv th ts ta tc ps loc pad3 slot pad4 dso m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT) fc None m (seg_rom ssegs)).
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo code t td0 td1 td2 td3 cdt thr sec tm1 auxv th ts ta tc ps loc fa pad3 slot pad4 dso : ltac2:(SecDiet.SzSec.tyM 'exit_prefix_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma exit_prefix_spec__body : ltac2:(SecDiet.SzSec.bodyP 'exit_prefix_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt. ceil_facts.
    intros ST TDa EXL LC ATX GF FA FIN GCX DSO MI -> Ht LO LOLO TB.
    unfold libc_cells, atexit_cells in *. destruct TB as (TBA & TB0 & TBC & TBI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (EXIT_LOCK, 0x53d04); (ATEXIT, 0x53af8); (FINALIZED, 0x23989)]%Z m) as MU.
    pose proof (wmono_refl ssegs m) as WM.
    carve_frame 16%nat ST.
    do 6 lstep.
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    lstep. lstep.
    (* [comment removed for export] *)
    amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    lstep. if_false. amo_step. lstep. if_false.
    lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
    lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
    steps_to 0x18278%Z.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. steps_to 0x21154%Z. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    steps_to 0x1833c%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    steps_to 0x213d8%Z. change (sx32 z64) with z64. astep. astep.
    (* [comment removed for export] *)
    astep. carve_frame 32%nat ST. steps_to 0x13a80%Z.
    carve_frame 16%nat ST. steps_to 0x13b0c%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. astep.
    steps_to 0x18458%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.
    (* [comment removed for export] *)
    astep.
    unfold exit_prefix_post, libc_cells, atexit_cells. sys_finish.
    intros a Ha. apply MU. unfold exit_footprint in Ha. cbn [outside] in Ha |- *. lia.
  Qed.
  End Sz1.
  Lemma exit_prefix_spec : ltac:(let t := eval cbv delta [exit_prefix_spec__stmt] in exit_prefix_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo code t td0 td1 td2 td3 cdt thr sec tm1 auxv th ts ta tc ps loc fa pad3 slot pad4 dso. ltac2:(SecDiet.SzSec.closeP 'exit_prefix_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_prefix_reg__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo code t : Z) (td0 td1 td2 td3 : word)
      (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte)
      (fa : byte) (pad3 : list byte) (pad4 : list byte) (dso : word) (j1 j2 : list byte),
    stk ssegs m lo (bv_unsigned sp) ->
    rw_cells ssegs m (bv_unsigned tp + -200) [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->   (* [comment removed for export] *)
    rw_cells ssegs m EXIT_LOCK [C4 z64] ->
    rw_cells ssegs m LIBC (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc) ->      (* [comment removed for export] *)
    rw_cells ssegs m ATEXIT (atexit_cells fa pad3 (Z_to_bv 64 1) pad4 (Z_to_bv 64 BUILTIN)) ->       (* [comment removed for export] *)
    rw_cells ssegs m BUILTIN (builtin_cells (Z_to_bv 64 CALL_THUNK) j1 (Z_to_bv 64 EXIT_CB_FN) j2) ->
    rw_cells ssegs m EXIT_CB_FLAG [C1 (Z_to_bv 8 0)] ->                                                   (* [comment removed for export] *)
    rw_cells ssegs m GOT_FINI [C8 (Z_to_bv 64 0x22560); C8 (Z_to_bv 64 FINI_ARRAY)] ->
    rw_cells ssegs m FINI_ARRAY [C8 (Z_to_bv 64 0x13a80)] ->                                          (* [comment removed for export] *)
    rw_cells ssegs m FINALIZED [C1 (Z_to_bv 8 0)] ->
    rw_cells ssegs m GOT_CXA [C8 (Z_to_bv 64 0x18340); C8 z64] ->
    rw_cells ssegs m DSO_HANDLE [C8 dso] ->
    mem_inv ssegs m ->
    a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 80)%Z -> (alloc_ceiling <= lo)%Z ->
    tls_block_ok (bv_unsigned tp - 200) ->
    evt ssegs (exit_prefix_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra
                 cdt thr sec tm1 auxv th ts ta tc ps loc pad3 (Z_to_bv 64 32) pad4 dso m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT) fc None m (seg_rom ssegs)).
  Lemma exit_prefix_reg : ltac:(let t := eval cbv delta [exit_prefix_reg__stmt] in exit_prefix_reg__stmt in exact t).
  Proof using Type. pin_using tt. ceil_facts.
    intros until j2.
    intros ST TDa EXL LC ATX BLT FLG GF FA FIN GCX DSO MI -> Ht LO LOLO TB.
    unfold libc_cells, atexit_cells, builtin_cells in *. destruct TB as (TBA & TB0 & TBC & TBI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (EXIT_LOCK, 0x53d04); (ATEXIT, 0x53af8); (FINALIZED, 0x23989)]%Z m) as MU.
    pose proof (wmono_refl ssegs m) as WM.
    carve_frame 16%nat ST.
    do 6 lstep.
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    lstep. lstep.
    (* [comment removed for export] *)
    amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    lstep. if_false. amo_step. lstep. if_false.
    lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
    lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
    steps_to 0x18278%Z.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. steps_to 0x21154%Z. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    steps_to 0x182a8%Z.
    lstep. if_false. lstep.
    change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
    lstep. lstep. lstep. lstep. if_false.
    (* [comment removed for export] *)
    steps_to 0x213d8%Z. change (sx32 z64) with z64. astep. astep.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep.
    cbv beta. change (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0))) with z64.
    astep. astep.
    (* [comment removed for export] *)
    steps_to 0x21154%Z. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    steps_to 0x18304%Z. change (sx32 z64) with z64.
    lstep. lstep. lstep. if_false. lstep. lstep. lstep. lstep. lstep. lstep.
    lstep. if_true.
    (* [comment removed for export] *)
    steps_to 0x1833c%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    steps_to 0x213d8%Z. change (sx32 z64) with z64. astep. astep.
    (* [comment removed for export] *)
    astep. carve_frame 32%nat ST. steps_to 0x13a80%Z.
    carve_frame 16%nat ST. steps_to 0x13b0c%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. astep.
    steps_to 0x18458%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.
    (* [comment removed for export] *)
    astep.
    unfold exit_prefix_post, libc_cells, atexit_cells. sys_finish.
    intros a Ha. apply MU. unfold exit_footprint in Ha. cbn [outside] in Ha |- *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition at_exit (code : Z) (s : St) (ms : machine_state) : Prop :=
    exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t : Z) (td0 td1 td2 td3 : word)
           (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte)
           (fa : byte) (pad3 : list byte) (reg : bool) (pad4 : list byte) (dso : word)
           (f0 g0 : word) (j1 j2 : list byte),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 EXIT) fc None m (seg_rom ssegs)
      /\ stk ssegs m lo (bv_unsigned sp)
      /\ rw_cells ssegs m (bv_unsigned tp + -200) [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
      /\ rw_cells ssegs m EXIT_LOCK [C4 z64]
      /\ rw_cells ssegs m LIBC (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc)
      (* [comment removed for export] *)
      /\ rw_cells ssegs m ATEXIT (atexit_cells fa pad3 (atx_slot reg) pad4 (atx_head reg))
      /\ rw_cells ssegs m BUILTIN (builtin_cells f0 j1 g0 j2)
      /\ (reg = true -> f0 = Z_to_bv 64 CALL_THUNK /\ g0 = Z_to_bv 64 EXIT_CB_FN)
      /\ rw_cells ssegs m EXIT_CB_FLAG [C1 (Z_to_bv 8 0)]
      /\ rw_cells ssegs m GOT_FINI [C8 (Z_to_bv 64 0x22560); C8 (Z_to_bv 64 FINI_ARRAY)]
      /\ rw_cells ssegs m FINI_ARRAY [C8 (Z_to_bv 64 0x13a80)]
      /\ rw_cells ssegs m FINALIZED [C1 (Z_to_bv 8 0)]
      /\ rw_cells ssegs m GOT_CXA [C8 (Z_to_bv 64 0x18340); C8 z64]
      /\ rw_cells ssegs m DSO_HANDLE [C8 dso]
      /\ SX s tp m
      /\ mem_inv ssegs m
      /\ a0 = Z_to_bv 64 code
      /\ (0 < t < 4194304)%Z /\ (lo <= bv_unsigned sp - 80 - stdio_exit_frame)%Z /\ (alloc_ceiling <= lo)%Z
      /\ tls_block_ok (bv_unsigned tp - 200)
      /\ (bv_unsigned sp <= 2^47)%Z.     (* [comment removed for export] *)

  Definition exit_spec__stmt : Prop := forall (code : Z) (s : St) (Q : Empty_set -> St -> machine_state -> Prop) ms,
    at_exit code s ms -> implM ssegs (exit_model stdio_exit_model code) s Q ms.
  Section Sz2.
  Variables code s Q ms : ltac2:(SecDiet.SzSec.tyM 'exit_spec__stmt "vvvv" @code).
  Lemma exit_spec__body : ltac2:(SecDiet.SzSec.bodyP 'exit_spec__stmt "vvvv").
  Proof using SX_frame stdio_exit_frame_nonneg stdio_exit_spec. pin_using (fun (SX_frame stdio_exit_frame_nonneg stdio_exit_spec : unit) => tt). ceil_facts.
    intros AE.
    destruct AE as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                    s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t &
                    td0 & td1 & td2 & td3 & cdt & thr & sec & tm1 & auxv & th & ts & ta & tc & ps & loc &
                    fa & pad3 & reg & pad4 & dso & f0 & g0 & j1 & j2 & -> & AE).
    destruct AE as (ST & TDa & EXL & LC & ATX & BLT & REG & FLG & GF & FA & FIN & GCX & DSO & HSX & MI & Ha0 & Ht & LO & LOLO & TB & SP47).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    unfold libc_cells in LC.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (EXIT_LOCK, 0x53d04); (ATEXIT, 0x53af8); (FINALIZED, 0x23989)]%Z m) as MU.
    pose proof (wmono_refl ssegs m) as WM.
    (* [comment removed for export] *)
    assert (PRE : exists slot', evt ssegs (exit_prefix_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra
                 cdt thr sec tm1 auxv th ts ta tc ps loc pad3 slot' pad4 dso m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT) fc None m (seg_rom ssegs))).
    { destruct reg; cbn [atx_slot atx_head] in ATX.
      - destruct (REG eq_refl) as [-> ->]. exists (Z_to_bv 64 32).
        eapply exit_prefix_reg; [exact ST | exact TDa | exact EXL | exact LC | exact ATX | exact BLT | exact FLG | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact MI
                               | exact Ha0 | exact Ht | lia | lia | exact TB ].
      - exists z64.
        eapply exit_prefix_spec; [exact ST | exact TDa | exact EXL | exact LC | exact ATX | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact MI
                               | exact Ha0 | exact Ht | lia | lia | exact TB ]. }
    destruct PRE as (slot' & PRE).
    unfold libc_cells, atexit_cells in LC, ATX.
    unfold exit_model.
    eapply (implM_bind ssegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F' fc' m',
                 ms' = MS (mkR (Z_to_bv 64 STDIO_EXIT_RET) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F' (Z_to_bv 64 STDIO_EXIT_RET) fc' None m' (seg_rom ssegs))).
    - (* [comment removed for export] *)
      unfold implM. iprefix.
      eapply evt_cut; [exact PRE|]. cbv beta. intros ms1 PO1. unfold exit_prefix_post in PO1. destruct_exs PO1.
      destruct PO1 as (-> & MU1 & WM1 & MI1 & ST1 & FR1 & TD1 & EXL1 & LC1 & ATX1 & GF1 & FA1 & FIN1 & GCX1 & DSO1 & AG1).
      clear MU WM MI ST TDa EXL LC ATX BLT FLG GF FA FIN GCX DSO REG. rename WM1 into WM. rename MI1 into MI.
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_stmt, implM in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 STDIO_EXIT_RET)) with (Z_to_bv 64 STDIO_EXIT_RET) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- SX _ _ _ =>
               eapply SX_frame; [exact HSX | | exact WM];
               match goal with AG : exit_agrees _ _ |- _ => exact AG end
           | |- _ => unname_sp; fastfirst (first [ hyp_by_addr | reflexivity | lia ])
           end.
    - (* [comment removed for export] *)
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H ].
  Qed.
  End Sz2.
  Lemma exit_spec : ltac:(let t := eval cbv delta [exit_spec__stmt] in exit_spec__stmt in exact t).
  Proof using SX_frame stdio_exit_frame_nonneg stdio_exit_spec. intros code s Q ms. ltac2:(SecDiet.SzSec.closeP 'exit_spec__body "vvvv"). Qed.
End ExitProof.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.AmoStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation EXIT := 0x18c1c%Z (only parsing).
Notation STDIO_EXIT := 0x1b63c%Z (only parsing).
Notation STDIO_EXIT_RET := 0x18c88%Z (only parsing).   (* [comment removed for export] *)
Notation EXIT_LOCK := 0x544c0%Z (only parsing).
Notation ATEXIT := 0x542a0%Z (only parsing).           (* [comment removed for export] *)
Notation LIBC := 0x544e8%Z (only parsing).
Notation GOT_FINI := 0x22de8%Z (only parsing).         (* [comment removed for export] *)
Notation FINI_ARRAY := 0x22d18%Z (only parsing).
Notation FINALIZED := 0x24148%Z (only parsing).
Notation GOT_CXA := 0x22d68%Z (only parsing).          (* [comment removed for export] *)
Notation DSO_HANDLE := 0x23df8%Z (only parsing).
(* [comment removed for export] *)
Notation BUILTIN := 0x542b8%Z (only parsing).
Notation EXIT_CB_FLAG := 0x34154%Z (only parsing).         (* [comment removed for export] *)
Notation CALL_THUNK := 0x18bc8%Z (only parsing).
Notation EXIT_CB_FN := 0x13fac%Z (only parsing).

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition exit_footprint : list (Z * Z) :=
  [(EXIT_LOCK, 0x544c4); (ATEXIT, 0x542b8); (FINALIZED, 0x24149); (alloc_ceiling, 2^64)]%Z.

Definition exit_agrees (m m' : word -> option byte) : Prop := munch exit_footprint m m'.

(* [comment removed for export] *)
Definition atexit_cells (fa : byte) (pad3 : list byte) (slot : word) (pad4 : list byte) (head : word) : list cell :=
  [C1 fa; CB 3 pad3; C4 z64; C4 slot; CB 4 pad4; C8 head].

(* [comment removed for export] *)
Definition builtin_cells (f0 : word) (j1 : list byte) (g0 : word) (j2 : list byte) : list cell :=
  [C8 z64; C8 f0; CB 248 j1; C8 g0; CB 248 j2].
(* [comment removed for export] *)
Definition bool8 (b : bool) : byte := if b then Z_to_bv 8 1 else Z_to_bv 8 0.
Definition atx_slot (reg : bool) : word := if reg then Z_to_bv 64 1 else z64.
Definition atx_head (reg : bool) : word := if reg then Z_to_bv 64 BUILTIN else z64.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExitProof.
  Context {St : Type} (stdio_exit_model : M St unit).
  (* [comment removed for export] *)
  Variable SX : St -> word -> (word -> option byte) -> Prop.
  (* [comment removed for export] *)
  Variable stdio_exit_frame : Z.
  Hypothesis stdio_exit_frame_nonneg : (0 <= stdio_exit_frame)%Z.

  (* [comment removed for export] *)
  Hypothesis SX_frame : forall s tp m m',
    SX s tp m -> munch exit_footprint m m' -> wmono usegs m m' -> SX s tp m'.

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom usegs).

  (* [comment removed for export] *)
  Definition stdio_exit_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St)
           (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte),
      stk usegs m lo (bv_unsigned sp) ->
      SX s tp m ->
      rw_cells usegs m LIBC (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc) ->   (* [comment removed for export] *)
      mem_inv usegs m ->
      (lo <= bv_unsigned sp - stdio_exit_frame)%Z -> (alloc_ceiling <= lo)%Z ->
      (bv_unsigned sp <= 2^47)%Z ->      (* [comment removed for export] *)
      implM usegs stdio_exit_model s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 STDIO_EXIT) fc None m (seg_rom usegs)).

  Hypothesis stdio_exit_spec : stdio_exit_stmt.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition exit_prefix_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo code t : Z) (td0 td1 td2 td3 ra : word) (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte)
      (pad3 : list byte) (slot : word) (pad4 : list byte) (dso : word)
      (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR (Z_to_bv 64 STDIO_EXIT_RET) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
                   a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 STDIO_EXIT) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (EXIT_LOCK, 0x544c4); (ATEXIT, 0x542b8); (FINALIZED, 0x24149)]%Z m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp + -16)
      /\ rw_cells usegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
      /\ rw_cells usegs m' (bv_unsigned tp + -200) [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
      /\ rw_cells usegs m' EXIT_LOCK [C4 (Z_to_bv 64 t)]
      /\ rw_cells usegs m' LIBC (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc)
      /\ rw_cells usegs m' ATEXIT (atexit_cells (Z_to_bv 8 1) pad3 slot pad4 z64)
      /\ rw_cells usegs m' GOT_FINI [C8 (Z_to_bv 64 0x22d20); C8 (Z_to_bv 64 FINI_ARRAY)]
      /\ rw_cells usegs m' FINI_ARRAY [C8 (Z_to_bv 64 0x13af4)]
      /\ rw_cells usegs m' FINALIZED [C1 (Z_to_bv 8 1)]
      /\ rw_cells usegs m' GOT_CXA [C8 (Z_to_bv 64 0x18b00); C8 z64]
      /\ rw_cells usegs m' DSO_HANDLE [C8 dso]
      /\ exit_agrees m m'.

  Definition exit_prefix_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo code t : Z) (td0 td1 td2 td3 : word)
      (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte)
      (fa : byte) (pad3 : list byte) (slot : word) (pad4 : list byte) (dso : word),
    stk usegs m lo (bv_unsigned sp) ->
    rw_cells usegs m (bv_unsigned tp + -200) [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->   (* [comment removed for export] *)
    rw_cells usegs m EXIT_LOCK [C4 z64] ->
    rw_cells usegs m LIBC (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc) ->      (* [comment removed for export] *)
    rw_cells usegs m ATEXIT (atexit_cells fa pad3 slot pad4 z64) ->                                 (* [comment removed for export] *)
    rw_cells usegs m GOT_FINI [C8 (Z_to_bv 64 0x22d20); C8 (Z_to_bv 64 FINI_ARRAY)] ->
    rw_cells usegs m FINI_ARRAY [C8 (Z_to_bv 64 0x13af4)] ->                                          (* [comment removed for export] *)
    rw_cells usegs m FINALIZED [C1 (Z_to_bv 8 0)] ->
    rw_cells usegs m GOT_CXA [C8 (Z_to_bv 64 0x18b00); C8 z64] ->
    rw_cells usegs m DSO_HANDLE [C8 dso] ->
    mem_inv usegs m ->
    a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 80)%Z -> (alloc_ceiling <= lo)%Z ->
    tls_block_ok_u (bv_unsigned tp - 200) ->
    evt usegs (exit_prefix_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra
                 cdt thr sec tm1 auxv th ts ta tc ps loc pad3 slot pad4 dso m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT) fc None m (seg_rom usegs)).
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo code t td0 td1 td2 td3 cdt thr sec tm1 auxv th ts ta tc ps loc fa pad3 slot pad4 dso : ltac2:(SecDiet.SzSec.tyM 'exit_prefix_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma exit_prefix_spec__body : ltac2:(SecDiet.SzSec.bodyP 'exit_prefix_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt. ceil_facts.
    intros ST TDa EXL LC ATX GF FA FIN GCX DSO MI -> Ht LO LOLO TB.
    unfold libc_cells, atexit_cells in *. destruct TB as (TBA & TB0 & TBC & TBI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (EXIT_LOCK, 0x544c4); (ATEXIT, 0x542b8); (FINALIZED, 0x24149)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    do 6 lstep.
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    lstep. lstep.
    (* [comment removed for export] *)
    amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    lstep. if_false. amo_step. lstep. if_false.
    lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
    lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
    steps_to 0x18a38%Z.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. steps_to 0x21914%Z. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    steps_to 0x18afc%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    steps_to 0x21b98%Z. change (sx32 z64) with z64. astep. astep.
    (* [comment removed for export] *)
    astep. carve_frame 32%nat ST. steps_to 0x13af4%Z.
    carve_frame 16%nat ST. steps_to 0x13b80%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. astep.
    steps_to 0x18c18%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.
    (* [comment removed for export] *)
    astep.
    unfold exit_prefix_post, libc_cells, atexit_cells. sys_finish.
    intros a Ha. apply MU. unfold exit_footprint in Ha. cbn [outside] in Ha |- *. lia.
  Qed.
  End Sz1.
  Lemma exit_prefix_spec : ltac:(let t := eval cbv delta [exit_prefix_spec__stmt] in exit_prefix_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo code t td0 td1 td2 td3 cdt thr sec tm1 auxv th ts ta tc ps loc fa pad3 slot pad4 dso. ltac2:(SecDiet.SzSec.closeP 'exit_prefix_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition exit_prefix_reg__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo code t : Z) (td0 td1 td2 td3 : word)
      (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte)
      (fa : byte) (pad3 : list byte) (pad4 : list byte) (dso : word) (j1 j2 : list byte),
    stk usegs m lo (bv_unsigned sp) ->
    rw_cells usegs m (bv_unsigned tp + -200) [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->   (* [comment removed for export] *)
    rw_cells usegs m EXIT_LOCK [C4 z64] ->
    rw_cells usegs m LIBC (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc) ->      (* [comment removed for export] *)
    rw_cells usegs m ATEXIT (atexit_cells fa pad3 (Z_to_bv 64 1) pad4 (Z_to_bv 64 BUILTIN)) ->       (* [comment removed for export] *)
    rw_cells usegs m BUILTIN (builtin_cells (Z_to_bv 64 CALL_THUNK) j1 (Z_to_bv 64 EXIT_CB_FN) j2) ->
    rw_cells usegs m EXIT_CB_FLAG [C1 (Z_to_bv 8 0)] ->                                                   (* [comment removed for export] *)
    rw_cells usegs m GOT_FINI [C8 (Z_to_bv 64 0x22d20); C8 (Z_to_bv 64 FINI_ARRAY)] ->
    rw_cells usegs m FINI_ARRAY [C8 (Z_to_bv 64 0x13af4)] ->                                          (* [comment removed for export] *)
    rw_cells usegs m FINALIZED [C1 (Z_to_bv 8 0)] ->
    rw_cells usegs m GOT_CXA [C8 (Z_to_bv 64 0x18b00); C8 z64] ->
    rw_cells usegs m DSO_HANDLE [C8 dso] ->
    mem_inv usegs m ->
    a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 80)%Z -> (alloc_ceiling <= lo)%Z ->
    tls_block_ok_u (bv_unsigned tp - 200) ->
    evt usegs (exit_prefix_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra
                 cdt thr sec tm1 auxv th ts ta tc ps loc pad3 (Z_to_bv 64 32) pad4 dso m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT) fc None m (seg_rom usegs)).
  Lemma exit_prefix_reg : ltac:(let t := eval cbv delta [exit_prefix_reg__stmt] in exit_prefix_reg__stmt in exact t).
  Proof using Type. pin_using tt. ceil_facts.
    intros until j2.
    intros ST TDa EXL LC ATX BLT FLG GF FA FIN GCX DSO MI -> Ht LO LOLO TB.
    unfold libc_cells, atexit_cells, builtin_cells in *. destruct TB as (TBA & TB0 & TBC & TBI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (EXIT_LOCK, 0x544c4); (ATEXIT, 0x542b8); (FINALIZED, 0x24149)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    do 6 lstep.
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    lstep. lstep.
    (* [comment removed for export] *)
    amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    lstep. if_false. amo_step. lstep. if_false.
    lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
    lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
    steps_to 0x18a38%Z.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. steps_to 0x21914%Z. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    steps_to 0x18a68%Z.
    lstep. if_false. lstep.
    change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
    lstep. lstep. lstep. lstep. if_false.
    (* [comment removed for export] *)
    steps_to 0x21b98%Z. change (sx32 z64) with z64. astep. astep.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep.
    cbv beta. change (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0))) with z64.
    astep. astep.
    (* [comment removed for export] *)
    steps_to 0x21914%Z. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
    steps_to 0x18ac4%Z. change (sx32 z64) with z64.
    lstep. lstep. lstep. if_false. lstep. lstep. lstep. lstep. lstep. lstep.
    lstep. if_true.
    (* [comment removed for export] *)
    steps_to 0x18afc%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    steps_to 0x21b98%Z. change (sx32 z64) with z64. astep. astep.
    (* [comment removed for export] *)
    astep. carve_frame 32%nat ST. steps_to 0x13af4%Z.
    carve_frame 16%nat ST. steps_to 0x13b80%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. astep.
    steps_to 0x18c18%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.
    (* [comment removed for export] *)
    astep.
    unfold exit_prefix_post, libc_cells, atexit_cells. sys_finish.
    intros a Ha. apply MU. unfold exit_footprint in Ha. cbn [outside] in Ha |- *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition at_exit (code : Z) (s : St) (ms : machine_state) : Prop :=
    exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t : Z) (td0 td1 td2 td3 : word)
           (cdt thr sec : byte) (tm1 auxv th ts ta tc ps : word) (loc : list byte)
           (fa : byte) (pad3 : list byte) (reg : bool) (pad4 : list byte) (dso : word)
           (f0 g0 : word) (j1 j2 : list byte),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 EXIT) fc None m (seg_rom usegs)
      /\ stk usegs m lo (bv_unsigned sp)
      /\ rw_cells usegs m (bv_unsigned tp + -200) [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
      /\ rw_cells usegs m EXIT_LOCK [C4 z64]
      /\ rw_cells usegs m LIBC (libc_cells cdt thr sec (Z_to_bv 8 0) tm1 auxv th ts ta tc ps loc)
      (* [comment removed for export] *)
      /\ rw_cells usegs m ATEXIT (atexit_cells fa pad3 (atx_slot reg) pad4 (atx_head reg))
      /\ rw_cells usegs m BUILTIN (builtin_cells f0 j1 g0 j2)
      /\ (reg = true -> f0 = Z_to_bv 64 CALL_THUNK /\ g0 = Z_to_bv 64 EXIT_CB_FN)
      /\ rw_cells usegs m EXIT_CB_FLAG [C1 (Z_to_bv 8 0)]
      /\ rw_cells usegs m GOT_FINI [C8 (Z_to_bv 64 0x22d20); C8 (Z_to_bv 64 FINI_ARRAY)]
      /\ rw_cells usegs m FINI_ARRAY [C8 (Z_to_bv 64 0x13af4)]
      /\ rw_cells usegs m FINALIZED [C1 (Z_to_bv 8 0)]
      /\ rw_cells usegs m GOT_CXA [C8 (Z_to_bv 64 0x18b00); C8 z64]
      /\ rw_cells usegs m DSO_HANDLE [C8 dso]
      /\ SX s tp m
      /\ mem_inv usegs m
      /\ a0 = Z_to_bv 64 code
      /\ (0 < t < 4194304)%Z /\ (lo <= bv_unsigned sp - 80 - stdio_exit_frame)%Z /\ (alloc_ceiling <= lo)%Z
      /\ tls_block_ok_u (bv_unsigned tp - 200)
      /\ (bv_unsigned sp <= 2^47)%Z.     (* [comment removed for export] *)

  Definition exit_spec__stmt : Prop := forall (code : Z) (s : St) (Q : Empty_set -> St -> machine_state -> Prop) ms,
    at_exit code s ms -> implM usegs (exit_model stdio_exit_model code) s Q ms.
  Section Sz2.
  Variables code s Q ms : ltac2:(SecDiet.SzSec.tyM 'exit_spec__stmt "vvvv" @code).
  Lemma exit_spec__body : ltac2:(SecDiet.SzSec.bodyP 'exit_spec__stmt "vvvv").
  Proof using SX_frame stdio_exit_frame_nonneg stdio_exit_spec. pin_using (fun (SX_frame stdio_exit_frame_nonneg stdio_exit_spec : unit) => tt). ceil_facts.
    intros AE.
    destruct AE as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                    s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t &
                    td0 & td1 & td2 & td3 & cdt & thr & sec & tm1 & auxv & th & ts & ta & tc & ps & loc &
                    fa & pad3 & reg & pad4 & dso & f0 & g0 & j1 & j2 & -> & AE).
    destruct AE as (ST & TDa & EXL & LC & ATX & BLT & REG & FLG & GF & FA & FIN & GCX & DSO & HSX & MI & Ha0 & Ht & LO & LOLO & TB & SP47).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    unfold libc_cells in LC.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (EXIT_LOCK, 0x544c4); (ATEXIT, 0x542b8); (FINALIZED, 0x24149)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    assert (PRE : exists slot', evt usegs (exit_prefix_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra
                 cdt thr sec tm1 auxv th ts ta tc ps loc pad3 slot' pad4 dso m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT) fc None m (seg_rom usegs))).
    { destruct reg; cbn [atx_slot atx_head] in ATX.
      - destruct (REG eq_refl) as [-> ->]. exists (Z_to_bv 64 32).
        eapply exit_prefix_reg; [exact ST | exact TDa | exact EXL | exact LC | exact ATX | exact BLT | exact FLG | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact MI
                               | exact Ha0 | exact Ht | lia | lia | exact TB ].
      - exists z64.
        eapply exit_prefix_spec; [exact ST | exact TDa | exact EXL | exact LC | exact ATX | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact MI
                               | exact Ha0 | exact Ht | lia | lia | exact TB ]. }
    destruct PRE as (slot' & PRE).
    unfold libc_cells, atexit_cells in LC, ATX.
    unfold exit_model.
    eapply (implM_bind usegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F' fc' m',
                 ms' = MS (mkR (Z_to_bv 64 STDIO_EXIT_RET) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F' (Z_to_bv 64 STDIO_EXIT_RET) fc' None m' (seg_rom usegs))).
    - (* [comment removed for export] *)
      unfold implM. iprefix.
      eapply evt_cut; [exact PRE|]. cbv beta. intros ms1 PO1. unfold exit_prefix_post in PO1. destruct_exs PO1.
      destruct PO1 as (-> & MU1 & WM1 & MI1 & ST1 & FR1 & TD1 & EXL1 & LC1 & ATX1 & GF1 & FA1 & FIN1 & GCX1 & DSO1 & AG1).
      clear MU WM MI ST TDa EXL LC ATX BLT FLG GF FA FIN GCX DSO REG. rename WM1 into WM. rename MI1 into MI.
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_stmt, implM in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 STDIO_EXIT_RET)) with (Z_to_bv 64 STDIO_EXIT_RET) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- SX _ _ _ =>
               eapply SX_frame; [exact HSX | | exact WM];
               match goal with AG : exit_agrees _ _ |- _ => exact AG end
           | |- _ => unname_sp; fastfirst (first [ hyp_by_addr | reflexivity | lia ])
           end.
    - (* [comment removed for export] *)
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H ].
  Qed.
  End Sz2.
  Lemma exit_spec : ltac:(let t := eval cbv delta [exit_spec__stmt] in exit_spec__stmt in exact t).
  Proof using SX_frame stdio_exit_frame_nonneg stdio_exit_spec. intros code s Q ms. ltac2:(SecDiet.SzSec.closeP 'exit_spec__body "vvvv"). Qed.
End ExitProof.

End WithCeil.
End TwB.
End Exit.

(* [comment removed for export] *)
Module F_stdio_cs.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_CLOSE : Z := 0x1a8a8.
Definition STDIO_SEEK : Z := 0x1a9ec.

Section CS.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition stdio_close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : St) (lo : Z) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\ exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp).

  Theorem stdio_close_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) (lo : Z),
      rw_cells ssegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
      a0 = Z_to_bv 64 Fp -> 3 <= fd < 2^31 ->
      stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x55000 <= lo -> mem_inv ssegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      implM ssegs (msys (NClose fd) dec_close_ok) st
        (stdio_close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_CLOSE) fc None m (seg_rom ssegs)).
  Proof using Type. pin_using tt.
    intros until lo. intros FC -> FD ST LO GLO MI Fp0 FPLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
    unfold file_cells in FC. unfold STDIO_CLOSE.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    apply implM_sys. carve_frame 16%nat ST.
    zs. zs. zs. rewrite (sx32_small fd) by lia. zs.
    replace (ret_pc (Z_to_bv 64 0x1a8b8)) with (Z_to_bv 64 0x1a8b8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. zs.
    step_ecall. split. { at_node_solve. }
    intros rsp [] Hdec. unfold dec_close_ok in Hdec.
    destruct (dec_close rsp) as [[e|v]|] eqn:E; try discriminate Hdec.
    unfold dec_close in E. apply dec_plain_Some in E as (-> & Hok & Hv). apply Z.eqb_eq in Hok. subst v.
    unfold eff0. sys_nret.
    step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
    step.
    replace (ret_pc (Z_to_bv 64 0x1a8c4)) with (Z_to_bv 64 0x1a8c4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. rewrite ?(sextw_small 0) by lia. zs. zs. zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold stdio_close_post. split; [reflexivity|]. sys_finish.
  Qed.

  (* [comment removed for export] *)
  Definition stdio_seek_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : St) (m : mem) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom ssegs).

  Theorem stdio_seek_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) (off whence : Z),
      rw_cells ssegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 off -> a2 = Z_to_bv 64 whence -> 3 <= fd < 2^31 -> 0 <= whence <= 2 ->
      mem_inv ssegs m -> 0 <= Fp ->
      implM ssegs (msys (NLseek fd off whence) dec_lseek_ok) st
        (stdio_seek_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_SEEK) fc None m (seg_rom ssegs)).
  Proof using Type. pin_using tt.
    intros until whence. intros FC -> -> -> FD WH MI Fp0.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
    unfold file_cells in FC. unfold STDIO_SEEK.
    apply implM_sys.
    zs. rewrite (sx32_small fd) by lia. zs. zs.
    step_ecall. split. { at_node_solve. }
    intros rsp v Hdec. unfold dec_lseek_ok in Hdec.
    destruct (dec_lseek rsp) as [[e|v']|] eqn:E; try discriminate Hdec. injection Hdec as <-.
    unfold dec_lseek in E. apply dec_plain_Some in E as (-> & _ & Hv).
    unfold eff0. sys_nret.
    step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
    step.
    apply evt_done. unfold stdio_seek_post. split; [reflexivity|]. sys_finish.
  Qed.
End CS.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan SecDiet.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_CLOSE : Z := 0x1b068.
Definition STDIO_SEEK : Z := 0x1b1ac.

Section CS.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition stdio_close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : St) (lo : Z) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\ exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp).

  Definition stdio_close_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) (lo : Z),
      rw_cells usegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
      a0 = Z_to_bv 64 Fp -> 3 <= fd < 2^31 ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x56000 <= lo -> mem_inv usegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      implM usegs (msys (NClose fd) dec_close_ok) st
        (stdio_close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_CLOSE) fc None m (seg_rom usegs)).
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail lo : ltac2:(SecDiet.SzSec.tyM 'stdio_close_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma stdio_close_spec__body : ltac2:(SecDiet.SzSec.bodyP 'stdio_close_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros FC -> FD ST LO GLO MI Fp0 FPLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
    unfold file_cells in FC. unfold STDIO_CLOSE.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    apply implM_sys. carve_frame 16%nat ST.
    zs. zs. zs. rewrite (sx32_small fd) by lia. zs.
    replace (ret_pc (Z_to_bv 64 0x1b078)) with (Z_to_bv 64 0x1b078 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. zs.
    step_ecall. split. { at_node_solve. }
    intros rsp [] Hdec. unfold dec_close_ok in Hdec.
    destruct (dec_close rsp) as [[e|v]|] eqn:E; try discriminate Hdec.
    unfold dec_close in E. apply dec_plain_Some in E as (-> & Hok & Hv). apply Z.eqb_eq in Hok. subst v.
    unfold eff0. sys_nret.
    step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
    step.
    replace (ret_pc (Z_to_bv 64 0x1b084)) with (Z_to_bv 64 0x1b084 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. rewrite ?(sextw_small 0) by lia. zs. zs. zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold stdio_close_post. split; [reflexivity|]. sys_finish.
  Qed.
  End Sz1.
  Theorem stdio_close_spec : ltac:(let t := eval cbv delta [stdio_close_spec__stmt] in stdio_close_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail lo. ltac2:(SecDiet.SzSec.closeP 'stdio_close_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition stdio_seek_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : St) (m : mem) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom usegs).

  Definition stdio_seek_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) (off whence : Z),
      rw_cells usegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 off -> a2 = Z_to_bv 64 whence -> 3 <= fd < 2^31 -> 0 <= whence <= 2 ->
      mem_inv usegs m -> 0 <= Fp ->
      implM usegs (msys (NLseek fd off whence) dec_lseek_ok) st
        (stdio_seek_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_SEEK) fc None m (seg_rom usegs)).
  Section Sz2.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail off whence : ltac2:(SecDiet.SzSec.tyM 'stdio_seek_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma stdio_seek_spec__body : ltac2:(SecDiet.SzSec.bodyP 'stdio_seek_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros FC -> -> -> FD WH MI Fp0.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
    unfold file_cells in FC. unfold STDIO_SEEK.
    apply implM_sys.
    zs. rewrite (sx32_small fd) by lia. zs. zs.
    step_ecall. split. { at_node_solve. }
    intros rsp v Hdec. unfold dec_lseek_ok in Hdec.
    destruct (dec_lseek rsp) as [[e|v']|] eqn:E; try discriminate Hdec. injection Hdec as <-.
    unfold dec_lseek in E. apply dec_plain_Some in E as (-> & _ & Hv).
    unfold eff0. sys_nret.
    step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
    step.
    apply evt_done. unfold stdio_seek_post. split; [reflexivity|]. sys_finish.
  Qed.
  End Sz2.
  Theorem stdio_seek_spec : ltac:(let t := eval cbv delta [stdio_seek_spec__stmt] in stdio_seek_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail off whence. ltac2:(SecDiet.SzSec.closeP 'stdio_seek_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CS.
End TwB.
End F_stdio_cs.

(* [comment removed for export] *)
Module F_unlink.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv ssegs _ |- _ => exact H end.

Definition UNLINK : Z := 0x2151c.
Definition REMOVE : Z := 0x1ba5c.
Definition CLOSEFD : Z := 0x21488.

(* [comment removed for export] *)
Definition sysfn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (rv : Z) (ev : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (bv_unsigned tp + -164) [C4 ev].

Section Walks.
  Context {St : Type}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (errv : word).
  Hypothesis LO : lo <= bv_unsigned sp - 32.
  Hypothesis GLO : 0x55000 <= lo.
  Hypothesis TPLO : bv_unsigned tp + -160 <= lo.
  Hypothesis TP200 : 200 <= bv_unsigned tp.

  (* [comment removed for export] *)
  Definition sysret_tail__stmt : Prop := forall (J : Z) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : word) (m0 m1 : mem) (jk : list byte),
    (J = 0x21538 \/ J = 0x1ba98 \/ J = 0x214c8) ->
    rw_cells ssegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
    rw_cells ssegs m1 (bv_unsigned tp + -164) [C4 errv] ->
    stk ssegs m1 lo (bv_unsigned sp + -16) -> mem_inv ssegs m1 ->
    munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m0 m1 -> wmono ssegs m0 m1 ->
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    evt ssegs (sysfn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
                 (match errno_of r with Some _ => -1 | None => 0 end)
                 (match errno_of r with Some e => Z_to_bv 64 e | None => errv end))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 J) fc None m1 (seg_rom ssegs)).
  Section Sz1.
  Variables J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r m0 m1 jk : ltac2:(SecDiet.SzSec.tyM 'sysret_tail__stmt "vvvvvvvvvvvvvvvvvvvv" @J).
  Lemma sysret_tail__body : ltac2:(SecDiet.SzSec.bodyP 'sysret_tail__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO TP200 TPLO. pin_using (fun (GLO LO TP200 TPLO : unit) => tt).
    intros HJ FR ERR ST MI MU WM HR.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    assert (STEP : forall J', (J' = 0x21538 \/ J' = 0x1ba98 \/ J' = 0x214c8) ->
      evt ssegs (sysfn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
                 (match errno_of r with Some _ => -1 | None => 0 end)
                 (match errno_of r with Some e => Z_to_bv 64 e | None => errv end))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 J') fc None m1 (seg_rom ssegs))).
    2:{ apply STEP. exact HJ. }
    intros J' [-> | [-> | ->]].
    all: zs; call_sp sysret_spec; [exact ST | exact ERR | mi | lia | lia | lia | ]; rename PC into ST'; rename POST into ERR'.
    all: unfold sysret_val, sysret_errno in *.
    all: destruct HR as (e & [[-> He] | ->]);
      [rewrite (errno_of_errno_ret e He) in * | rewrite (errno_of_lit 0) in * by lia].
    all: zs; zs; zs; release_frame FR ST' (bv_unsigned sp); zs.
    all: apply evt_done; unfold sysfn_post; repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|].
    all: split; [exact MU|]. all: split; [exact WM|].
    all: split; [mi|]. all: split; [assumption| assumption].
  Qed.
  End Sz1.
  Lemma sysret_tail : ltac:(let t := eval cbv delta [sysret_tail__stmt] in sysret_tail__stmt in exact t).
  Proof using GLO LO TP200 TPLO. intros J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r m0 m1 jk. ltac2:(SecDiet.SzSec.closeP 'sysret_tail__body "vvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition unlink_S1__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    stk ssegs m lo (bv_unsigned sp) -> mem_inv ssegs m ->
    evt ssegs (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-100)) a0 (Z_to_bv 64 0) a3 a4 a5 a6 (Z_to_bv 64 35)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x21534) fc None m1 (seg_rom ssegs)
        /\ rw_cells ssegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
        /\ stk ssegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 UNLINK) fc None m (seg_rom ssegs)).
  Section Sz2.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m : ltac2:(SecDiet.SzSec.tyM 'unlink_S1__stmt "vvvvvvvvvvvvvvvv" @t0).
  Lemma unlink_S1__body : ltac2:(SecDiet.SzSec.bodyP 'unlink_S1__stmt "vvvvvvvvvvvvvvvv").
  Proof using LO. pin_using (fun (LO : unit) => tt).
    intros ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold UNLINK. carve_frame 16%nat ST.
    do 6 zs.
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz2.
  Lemma unlink_S1 : ltac:(let t := eval cbv delta [unlink_S1__stmt] in unlink_S1__stmt in exact t).
  Proof using LO. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m. ltac2:(SecDiet.SzSec.closeP 'unlink_S1__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma remove_S1 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    evt ssegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-100)) a0 (Z_to_bv 64 0) a3 a4 a5 a6 (Z_to_bv 64 35)
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x1ba6c) fc None m (seg_rom ssegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REMOVE) fc None m (seg_rom ssegs)).
  Proof using Type. pin_using tt.
    intros. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold REMOVE. do 4 zs. apply evt_done. cbv delta [mkR]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition remove_S2__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (r : word) (m : mem),
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    stk ssegs m lo (bv_unsigned sp) -> mem_inv ssegs m ->
    evt ssegs (fun ms' =>
        (r = errno_ret EISDIR /\
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-100)) a1 (Z_to_bv 64 512) (Z_to_bv 64 (-21)) a4 a5 a6 (Z_to_bv 64 35)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1ba88) fc None m (seg_rom ssegs))
        \/ (r <> errno_ret EISDIR /\ exists (jk : list byte) (m1 : mem) (a2' : word),
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2' (Z_to_bv 64 (-21)) a4 a5 a6 (Z_to_bv 64 35)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1ba98) fc None m1 (seg_rom ssegs)
         /\ rw_cells ssegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
         /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
         /\ stk ssegs m1 lo (bv_unsigned sp + -16)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 (Z_to_bv 64 35) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ba70) fc None m (seg_rom ssegs)).
  Section Sz4.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m : ltac2:(SecDiet.SzSec.tyM 'remove_S2__stmt "vvvvvvvvvvvvvvv" @t0).
  Lemma remove_S2__body : ltac2:(SecDiet.SzSec.bodyP 'remove_S2__stmt "vvvvvvvvvvvvvvv").
  Proof using LO. pin_using (fun (LO : unit) => tt).
    intros HR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    destruct HR as (e & [[-> He] | ->]).
    - pose proof (errno_ret_unsigned e ltac:(lia)) as EU.
      zs. rewrite sextw_errno by lia. zs. zs. if_cases K; zify_cond K.
      all: unfold two_pow_64 in EU; rewrite ?EU, ?Z.mod_small in K by lia.
      + (* [comment removed for export] *)
        carve_frame 16%nat ST. zs. zs. zs. rewrite sextw_errno by lia.
        apply evt_done. right. split; [intros E; apply K; pose proof (f_equal bv_unsigned E) as E'; rewrite !errno_ret_unsigned in E' by (unfold EISDIR; lia); unfold two_pow_64, EISDIR in E'; lia|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
      + (* [comment removed for export] *)
        assert (E21 : e = 21) by lia. subst e.
        zs. zs. zs.
        apply evt_done. left. split; [reflexivity| cbv delta [mkR]; reflexivity].
    - zs. zs. zs. if_cases K; zify_cond K.
      2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. cbn. lia. }
      carve_frame 16%nat ST. zs. zs. zs.
      apply evt_done. right. split; [intros E; pose proof (f_equal bv_unsigned E) as E'; rewrite unsigned_lit, errno_ret_unsigned in E' by (unfold EISDIR; lia); unfold two_pow_64, EISDIR in E'; lia|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz4.
  Lemma remove_S2 : ltac:(let t := eval cbv delta [remove_S2__stmt] in remove_S2__stmt in exact t).
  Proof using LO. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m. ltac2:(SecDiet.SzSec.closeP 'remove_S2__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition remove_S3__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (r : word) (m : mem),
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    stk ssegs m lo (bv_unsigned sp) -> mem_inv ssegs m ->
    evt ssegs (fun ms' => exists (jk : list byte) (m1 : mem),
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 (Z_to_bv 64 35)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1ba98) fc None m1 (seg_rom ssegs)
         /\ rw_cells ssegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
         /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
         /\ stk ssegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 (Z_to_bv 64 35) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ba8c) fc None m (seg_rom ssegs)).
  Section Sz5.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m : ltac2:(SecDiet.SzSec.tyM 'remove_S3__stmt "vvvvvvvvvvvvvvv" @t0).
  Lemma remove_S3__body : ltac2:(SecDiet.SzSec.bodyP 'remove_S3__stmt "vvvvvvvvvvvvvvv").
  Proof using LO. pin_using (fun (LO : unit) => tt).
    intros HR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    carve_frame 16%nat ST. zs. zs. zs.
    destruct HR as (e & [[-> He] | ->]); [rewrite sextw_errno by lia|].
    all: apply evt_done; repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [mi| exact ST].
  Qed.
  End Sz5.
  Lemma remove_S3 : ltac:(let t := eval cbv delta [remove_S3__stmt] in remove_S3__stmt in exact t).
  Proof using LO. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m. ltac2:(SecDiet.SzSec.closeP 'remove_S3__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition close_S1__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fd : Z) (m : mem),
    0 <= fd < 2^31 ->
    stk ssegs m lo (bv_unsigned sp) -> mem_inv ssegs m ->
    evt ssegs (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR (Z_to_bv 64 0x214b4) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 57)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x21464) fc None m1 (seg_rom ssegs)
        /\ rw_cells ssegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
        /\ stk ssegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CLOSEFD) fc None m (seg_rom ssegs)).
  Section Sz6.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fd m : ltac2:(SecDiet.SzSec.tyM 'close_S1__stmt "vvvvvvvvvvvvvvvv" @t0).
  Lemma close_S1__body : ltac2:(SecDiet.SzSec.bodyP 'close_S1__stmt "vvvvvvvvvvvvvvvv").
  Proof using LO. pin_using (fun (LO : unit) => tt).
    intros FD ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold CLOSEFD. carve_frame 16%nat ST.
    zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0x21494)) with (Z_to_bv 64 0x21494 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 8 zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    do 7 zs.
    all: match goal with |- evt _ _ ?ms => idtac "C1:" ms end.
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz6.
  Lemma close_S1 : ltac:(let t := eval cbv delta [close_S1__stmt] in close_S1__stmt in exact t).
  Proof using LO. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fd m. ltac2:(SecDiet.SzSec.closeP 'close_S1__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma close_S2 : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
    evt ssegs (fun ms' => exists a1', ms' = MS (mkR (Z_to_bv 64 0x214b4) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2 a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x214c8) fc None mm (seg_rom ssegs))
      (MS (mkR (Z_to_bv 64 0x214b4) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x21468) fc None mm (seg_rom ssegs)).
  Proof using Type. pin_using tt.
    intros. pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    zs. replace (ret_pc (Z_to_bv 64 0x214b4)) with (Z_to_bv 64 0x214b4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 5 zs.
    all: match goal with |- evt _ _ ?ms => idtac "C2:" ms end.
    apply evt_done. eexists. cbv delta [mkR]. reflexivity.
  Qed.
End Walks.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv usegs _ |- _ => exact H end.

Definition UNLINK : Z := 0x21cdc.
Definition REMOVE : Z := 0x1c21c.
Definition CLOSEFD : Z := 0x21c48.

(* [comment removed for export] *)
Definition sysfn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (rv : Z) (ev : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (bv_unsigned tp + -164) [C4 ev].

Section Walks.
  Context {St : Type}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (errv : word).
  Hypothesis LO : lo <= bv_unsigned sp - 32.
  Hypothesis GLO : 0x56000 <= lo.
  Hypothesis TPLO : bv_unsigned tp + -160 <= lo.
  Hypothesis TP200 : 200 <= bv_unsigned tp.

  (* [comment removed for export] *)
  Definition sysret_tail__stmt : Prop := forall (J : Z) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : word) (m0 m1 : mem) (jk : list byte),
    (J = 0x21cf8 \/ J = 0x1c258 \/ J = 0x21c88) ->
    rw_cells usegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra] ->
    rw_cells usegs m1 (bv_unsigned tp + -164) [C4 errv] ->
    stk usegs m1 lo (bv_unsigned sp + -16) -> mem_inv usegs m1 ->
    munch [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m0 m1 -> wmono usegs m0 m1 ->
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    evt usegs (sysfn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
                 (match errno_of r with Some _ => -1 | None => 0 end)
                 (match errno_of r with Some e => Z_to_bv 64 e | None => errv end))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 J) fc None m1 (seg_rom usegs)).
  Section Sz1.
  Variables J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r m0 m1 jk : ltac2:(SecDiet.SzSec.tyM 'sysret_tail__stmt "vvvvvvvvvvvvvvvvvvvv" @J).
  Lemma sysret_tail__body : ltac2:(SecDiet.SzSec.bodyP 'sysret_tail__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO TP200 TPLO. pin_using (fun (GLO LO TP200 TPLO : unit) => tt).
 intros HJ FR ERR ST MI MU WM HR.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    assert (STEP : forall J', (J' = 0x21cf8 \/ J' = 0x1c258 \/ J' = 0x21c88) ->
      evt usegs (sysfn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
                 (match errno_of r with Some _ => -1 | None => 0 end)
                 (match errno_of r with Some e => Z_to_bv 64 e | None => errv end))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 J') fc None m1 (seg_rom usegs))).
    2:{ apply STEP. exact HJ. }
    intros J' [-> | [-> | ->]].
    all: zs; call_sp sysret_spec; [exact ST | exact ERR | mi | lia | lia | lia | ]; rename PC into ST'; rename POST into ERR'.
    all: unfold sysret_val, sysret_errno in *.
    all: destruct HR as (e & [[-> He] | ->]);
      [rewrite (errno_of_errno_ret e He) in * | rewrite (errno_of_lit 0) in * by lia].
    all: zs; zs; zs; release_frame FR ST' (bv_unsigned sp); zs.
    all: apply evt_done; unfold sysfn_post; repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|].
    all: split; [exact MU|]. all: split; [exact WM|].
    all: split; [mi|]. all: split; [assumption| assumption].
  Qed.
  End Sz1.
  Lemma sysret_tail : ltac:(let t := eval cbv delta [sysret_tail__stmt] in sysret_tail__stmt in exact t).
  Proof using GLO LO TP200 TPLO. intros J x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 r m0 m1 jk. ltac2:(SecDiet.SzSec.closeP 'sysret_tail__body "vvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition unlink_S1__stmt : Prop := forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-100)) a0 (Z_to_bv 64 0) a3 a4 a5 a6 (Z_to_bv 64 35)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x21cf4) fc None m1 (seg_rom usegs)
        /\ rw_cells usegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
        /\ stk usegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 UNLINK) fc None m (seg_rom usegs)).
  Section Sz2.
  Variables t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m : ltac2:(SecDiet.SzSec.tyM 'unlink_S1__stmt "vvvvvvvvvvvvvvvv" @t0).
  Lemma unlink_S1__body : ltac2:(SecDiet.SzSec.bodyP 'unlink_S1__stmt "vvvvvvvvvvvvvvvv").
  Proof using LO. pin_using (fun (LO : unit) => tt).
 intros ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold UNLINK. carve_frame 16%nat ST.
    do 6 zs.
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz2.
  Lemma unlink_S1 : ltac:(let t := eval cbv delta [unlink_S1__stmt] in unlink_S1__stmt in exact t).
  Proof using LO. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m. ltac2:(SecDiet.SzSec.closeP 'unlink_S1__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma remove_S1 : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-100)) a0 (Z_to_bv 64 0) a3 a4 a5 a6 (Z_to_bv 64 35)
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x1c22c) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REMOVE) fc None m (seg_rom usegs)).
  Proof using Type. pin_using tt.
    intros. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold REMOVE. do 4 zs. apply evt_done. cbv delta [mkR]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition remove_S2__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (r : word) (m : mem),
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m ->
    evt usegs (fun ms' =>
        (r = errno_ret EISDIR /\
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-100)) a1 (Z_to_bv 64 512) (Z_to_bv 64 (-21)) a4 a5 a6 (Z_to_bv 64 35)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1c248) fc None m (seg_rom usegs))
        \/ (r <> errno_ret EISDIR /\ exists (jk : list byte) (m1 : mem) (a2' : word),
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2' (Z_to_bv 64 (-21)) a4 a5 a6 (Z_to_bv 64 35)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1c258) fc None m1 (seg_rom usegs)
         /\ rw_cells usegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
         /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
         /\ stk usegs m1 lo (bv_unsigned sp + -16)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 (Z_to_bv 64 35) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1c230) fc None m (seg_rom usegs)).
  Section Sz4.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m : ltac2:(SecDiet.SzSec.tyM 'remove_S2__stmt "vvvvvvvvvvvvvvv" @t0).
  Lemma remove_S2__body : ltac2:(SecDiet.SzSec.bodyP 'remove_S2__stmt "vvvvvvvvvvvvvvv").
  Proof using LO. pin_using (fun (LO : unit) => tt).
 intros HR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct HR as (e & [[-> He] | ->]).
    - pose proof (errno_ret_unsigned e ltac:(lia)) as EU.
      zs. rewrite sextw_errno by lia. zs. zs. if_cases K; zify_cond K.
      all: unfold two_pow_64 in EU; rewrite ?EU, ?Z.mod_small in K by lia.
      + (* [comment removed for export] *)
        carve_frame 16%nat ST. zs. zs. zs. rewrite sextw_errno by lia.
        apply evt_done. right. split; [intros E; apply K; pose proof (f_equal bv_unsigned E) as E'; rewrite !errno_ret_unsigned in E' by (unfold EISDIR; lia); unfold two_pow_64, EISDIR in E'; lia|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
      + (* [comment removed for export] *)
        assert (E21 : e = 21) by lia. subst e.
        zs. zs. zs.
        apply evt_done. left. split; [reflexivity| cbv delta [mkR]; reflexivity].
    - zs. zs. zs. if_cases K; zify_cond K.
      2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. cbn. lia. }
      carve_frame 16%nat ST. zs. zs. zs.
      apply evt_done. right. split; [intros E; pose proof (f_equal bv_unsigned E) as E'; rewrite unsigned_lit, errno_ret_unsigned in E' by (unfold EISDIR; lia); unfold two_pow_64, EISDIR in E'; lia|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz4.
  Lemma remove_S2 : ltac:(let t := eval cbv delta [remove_S2__stmt] in remove_S2__stmt in exact t).
  Proof using LO. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m. ltac2:(SecDiet.SzSec.closeP 'remove_S2__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition remove_S3__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 : word) (r : word) (m : mem),
    (exists e, (r = errno_ret e /\ 1 <= e <= 4095) \/ r = Z_to_bv 64 0) ->
    stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (jk : list byte) (m1 : mem),
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 (Z_to_bv 64 35)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1c258) fc None m1 (seg_rom usegs)
         /\ rw_cells usegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
         /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
         /\ stk usegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 (Z_to_bv 64 35) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1c24c) fc None m (seg_rom usegs)).
  Section Sz5.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m : ltac2:(SecDiet.SzSec.tyM 'remove_S3__stmt "vvvvvvvvvvvvvvv" @t0).
  Lemma remove_S3__body : ltac2:(SecDiet.SzSec.bodyP 'remove_S3__stmt "vvvvvvvvvvvvvvv").
  Proof using LO. pin_using (fun (LO : unit) => tt).
 intros HR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST. zs. zs. zs.
    destruct HR as (e & [[-> He] | ->]); [rewrite sextw_errno by lia|].
    all: apply evt_done; repeat (lazymatch goal with |- ex _ => eexists end).
    all: split; [cbv delta [mkR]; reflexivity|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [mi| exact ST].
  Qed.
  End Sz5.
  Lemma remove_S3 : ltac:(let t := eval cbv delta [remove_S3__stmt] in remove_S3__stmt in exact t).
  Proof using LO. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 r m. ltac2:(SecDiet.SzSec.closeP 'remove_S3__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition close_S1__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fd : Z) (m : mem),
    0 <= fd < 2^31 ->
    stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR (Z_to_bv 64 0x21c74) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 57)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x21c24) fc None m1 (seg_rom usegs)
        /\ rw_cells usegs m1 (bv_unsigned sp + -16) [CB 8 jk; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
        /\ stk usegs m1 lo (bv_unsigned sp + -16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CLOSEFD) fc None m (seg_rom usegs)).
  Section Sz6.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fd m : ltac2:(SecDiet.SzSec.tyM 'close_S1__stmt "vvvvvvvvvvvvvvvv" @t0).
  Lemma close_S1__body : ltac2:(SecDiet.SzSec.bodyP 'close_S1__stmt "vvvvvvvvvvvvvvvv").
  Proof using LO. pin_using (fun (LO : unit) => tt).
 intros FD ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold CLOSEFD. carve_frame 16%nat ST.
    zs. zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0x21c54)) with (Z_to_bv 64 0x21c54 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 8 zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    do 7 zs.
    all: match goal with |- evt _ _ ?ms => idtac "C1:" ms end.
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz6.
  Lemma close_S1 : ltac:(let t := eval cbv delta [close_S1__stmt] in close_S1__stmt in exact t).
  Proof using LO. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fd m. ltac2:(SecDiet.SzSec.closeP 'close_S1__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma close_S2 : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
    evt usegs (fun ms' => exists a1', ms' = MS (mkR (Z_to_bv 64 0x21c74) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2 a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 0x21c88) fc None mm (seg_rom usegs))
      (MS (mkR (Z_to_bv 64 0x21c74) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x21c28) fc None mm (seg_rom usegs)).
  Proof using Type. pin_using tt.
    intros. pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    zs. replace (ret_pc (Z_to_bv 64 0x21c74)) with (Z_to_bv 64 0x21c74 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 5 zs.
    all: match goal with |- evt _ _ ?ms => idtac "C2:" ms end.
    apply evt_done. eexists. cbv delta [mkR]. reflexivity.
  Qed.
End Walks.
End TwB.
End F_unlink.

(* [comment removed for export] *)
Module MLeaf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Section Leaf.
  Context {nd : Type}.

  Fixpoint has_leaf {R} (t : itree nd R) (r : R) : Prop :=
    match t with
    | Ret r' => r' = r
    | Vis _ k => exists rsp, has_leaf (k rsp) r
    end.

  Lemma has_leaf_bind : forall {A B} (t : itree nd A) (f : A -> itree nd B) r,
    has_leaf (bind nd t f) r -> exists a, has_leaf t a /\ has_leaf (f a) r.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    induction t as [a|n k IH]; intros f r H; cbn in H.
    - exists a. split; [reflexivity| exact H].
    - destruct H as [rsp H]. destruct (IH rsp f r H) as (a & H1 & H2). exists a. split; [| exact H2]. cbn. exists rsp. exact H1.
  Qed.

  Variables (segs : list Segment) (at_node : nd -> machine_state -> Prop) (npeek : nd -> option (machine_state -> resp)).

  Lemma impl_has_leaf : forall {R} (t : itree nd R) Q ms,
    impl segs at_node npeek t Q ms -> impl segs at_node npeek t (fun r ms' => Q r ms' /\ has_leaf t r) ms.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    induction t as [r|n k IH]; intros Q ms H; cbn in *.
    - eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| reflexivity].
    - eapply evt_mono; [exact H|]. intros ms1 [[Hat Hk]|(f & Hf & Hk)].
      + left. split; [exact Hat|]. intros rsp. eapply impl_mono; [apply IH; apply Hk|].
        intros r ms' [H1 H2]. split; [exact H1|]. exists rsp. exact H2.
      + right. exists f. split; [exact Hf|]. eapply impl_mono; [apply IH; exact Hk|].
        intros r ms' [H1 H2]. split; [exact H1|]. exists (f ms1). exact H2.
  Qed.
End Leaf.

(* [comment removed for export] *)
Section MLeaf.
  Context {St : Type}.
  Definition mleaf {A} (c : @M St A) (s : St) (a : A) (s' : St) : Prop := has_leaf (c s) (Ok (a, s')).

  Lemma implM_leaf : forall segs {A} (c : @M St A) s Q ms,
    implM segs c s Q ms -> implM segs c s (fun a s' ms' => Q a s' ms' /\ mleaf c s a s') ms.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros segs A c s Q ms H. unfold implM in *. eapply impl_mono; [eapply impl_has_leaf; exact H|].
    intros [|[a s']] ms'; cbn; [tauto|]. intros [H1 H2]. split; [exact H1| exact H2].
  Qed.

  Lemma mleaf_ret : forall {A} (a b : A) s s', mleaf (mret a) s b s' -> b = a /\ s' = s.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros A a b s s' H. cbn in H. injection H as -> ->. auto. Qed.
  Lemma mleaf_unr : forall {A} (b : A) s s', mleaf (@munr St A) s b s' -> False.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros A b s s' H. cbn in H. discriminate H. Qed.
  Lemma mleaf_get : forall (b : St) s s', mleaf mget s b s' -> b = s /\ s' = s.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros b s s' H. cbn in H. injection H as -> ->. auto. Qed.
  Lemma mleaf_upd : forall f u s s', mleaf (mupd f) s u s' -> s' = f s.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros f u s s' H. cbn in H. injection H as _ <-. reflexivity. Qed.
  Lemma mleaf_sys : forall {A} n (dec : resp -> option A) s a s', mleaf (msys n dec) s a s' -> s' = s /\ exists rsp, dec rsp = Some a.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros A n dec s a s' H. cbn in H. destruct H as [rsp H].
    destruct (dec rsp) as [a'|] eqn:E; cbn in H; [|discriminate H]. injection H as -> ->. split; [reflexivity|]. exists rsp. exact E.
  Qed.
  Lemma mleaf_bind : forall {A B} (m : @M St A) (f : A -> @M St B) s b s'',
    mleaf (mbind m f) s b s'' -> exists a s', mleaf m s a s' /\ mleaf (f a) s' b s''.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros A B m f s b s'' H. unfold mleaf, mbind, ebind in H. apply has_leaf_bind in H as (r & H1 & H2).
    destruct r as [|[a s']]; [cbn in H2; discriminate H2|]. exists a, s'. split; [exact H1| exact H2].
  Qed.

  (* [comment removed for export] *)
  Lemma implM_ret_l : forall segs {A B} (a : A) (f : A -> @M St B) s Q ms,
    implM segs (f a) s Q ms -> implM segs (mbind (mret a) f) s Q ms.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. exact H. Qed.
  Lemma implM_get_l : forall segs {B} (f : St -> @M St B) s Q ms,
    implM segs (f s) s Q ms -> implM segs (mbind mget f) s Q ms.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. exact H. Qed.
  Lemma implM_upd_l : forall segs {B} g (f : unit -> @M St B) s Q ms,
    implM segs (f tt) (g s) Q ms -> implM segs (mbind (mupd g) f) s Q ms.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. exact H. Qed.
  Lemma implM_getret_l : forall segs {A B} (h : St -> A) (f : A -> @M St B) s Q ms,
    implM segs (f (h s)) s Q ms -> implM segs (mbind (mbind mget (fun s => mret (h s))) f) s Q ms.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. exact H. Qed.
End MLeaf.

(* [comment removed for export] *)
Section MOpsLeaf.
  Context {H hptr : Type}.
  #[local] Notation PS := (PState H hptr).
  Lemma mleaf_mobind : forall {A B} (m : M PS A) (f : A -> M PS B) s b s'',
    mleaf (mo_bind MOps m f) s b s'' -> exists a s', mleaf m s a s' /\ mleaf (f a) s' b s''.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. exact (mleaf_bind _ _ _ _ _ H0). Qed.
  Lemma mleaf_moret : forall {A} (a b : A) (s s' : PS), mleaf (mo_ret MOps a) s b s' -> b = a /\ s' = s.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. exact (mleaf_ret _ _ _ _ H0). Qed.
  Lemma mleaf_mounr : forall {A} (b : A) (s s' : PS), mleaf (mo_unr MOps (A:=A)) s b s' -> False.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros. exact (mleaf_unr _ _ _ H0). Qed.
End MOpsLeaf.

(* [comment removed for export] *)
End WithCeil.

Ltac mleaf_inv H :=
  lazymatch type of H with
  | mleaf (e_fenter _ _ ?b) ?s0 ?r0 ?s1 => change (mleaf b s0 r0 s1) in H; mleaf_inv H
  | mleaf (e_fret _ _ ?x) ?s0 ?r0 ?s1 => change (mleaf (mret x) s0 r0 s1) in H; mleaf_inv H
  | mleaf (mbind _ _) _ _ _ => let a := fresh "lv" in let s := fresh "ls" in let H1 := fresh "L" in
      apply mleaf_bind in H as (a & s & H1 & H)
  | mleaf (mo_bind MOps _ _) _ _ _ => let a := fresh "lv" in let s := fresh "ls" in let H1 := fresh "L" in
      apply mleaf_mobind in H as (a & s & H1 & H)
  | mleaf (mret _) _ _ _ => apply mleaf_ret in H as [? ?]
  | mleaf (mo_ret MOps _) _ _ _ => apply mleaf_moret in H as [? ?]
  | mleaf mget _ _ _ => apply mleaf_get in H as [? ?]
  | mleaf (mupd _) _ _ _ => apply mleaf_upd in H
  | mleaf (msys _ _) _ _ _ => apply mleaf_sys in H as [? [? ?]]
  | mleaf munr _ _ _ => destruct (mleaf_unr _ _ _ H)
  | mleaf (mo_unr MOps) _ _ _ => destruct (mleaf_mounr _ _ _ H)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Section ModelFacts.
  Context {H hptr : Type} (HO : HeapOps H hptr).
  #[local] Notation PS := (PState H hptr).
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.

  Lemma seal_TEMPLATE : seal_name TEMPLATE = Some TMPNAME.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma mkstemp_leaf : forall (s s' : PS) fn fd,
    mleaf (s_mkstemp (H:=H) (hptr:=hptr) TEMPLATE) s (fn, fd) s' -> fn = TMPNAME.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros s s' fn fd L. unfold s_mkstemp, mkstemp in L. rewrite seal_TEMPLATE in L.
    mleaf_inv L. destruct lv as [e|v].
    - mleaf_inv L. mleaf_inv L. congruence.
    - mleaf_inv L. congruence.
  Qed.

  (* [comment removed for export] *)
  Lemma fopen_leaf : forall (s s' : PS) name wr p,
    mleaf (s_fopen HO name wr) s (Some p) s' ->
    exists fd, files_lookup (ho_eqb HO) (lc_files (ps_libc s')) p = Some (fdopen_file fd wr).
  Proof using CEILV EQB. pin_using (fun (CEILV EQB : unit) => tt). ceil_facts.
    intros s s' name wr p L. unfold s_fopen, fopen in L.
    mleaf_inv L. destruct lv as [e|fd].
    - mleaf_inv L. mleaf_inv L. discriminate.
    - mleaf_inv L. destruct lv as [p'|].
      + mleaf_inv L. mleaf_inv L. unfold upd_lc in L3. mleaf_inv L3. mleaf_inv L. subst.
        lazymatch goal with E : Some _ = Some _ |- _ => injection E as -> end.
        exists fd. cbn [ps_libc set_libc lc_files set_files files_lookup].
        rewrite (proj2 (EQB p' p') eq_refl). reflexivity.
      + mleaf_inv L. mleaf_inv L. mleaf_inv L. discriminate.
  Qed.
End ModelFacts.

(* [comment removed for export] *)
End WithCeil.

Ltac crawl_with tac L :=
  repeat (first
   [ lazymatch type of L with
     (* [comment removed for export] *)
     | mleaf (e_fenter _ _ ?b) ?s0 ?r0 ?s1 => change (mleaf b s0 r0 s1) in L
     | mleaf (e_fret _ _ ?x) ?s0 ?r0 ?s1 => change (mleaf (mret x) s0 r0 s1) in L
     | mleaf (mbind _ _) _ _ _ => let a := fresh "lv" in let s := fresh "ls" in let H1 := fresh "HL" in
         apply mleaf_bind in L as (a & s & H1 & L); crawl_with tac H1; try (lazymatch type of H1 with mleaf _ _ _ _ => clear H1 end)
     | mleaf (mo_bind MOps _ _) _ _ _ => let a := fresh "lv" in let s := fresh "ls" in let H1 := fresh "HL" in
         apply mleaf_mobind in L as (a & s & H1 & L); crawl_with tac H1; try (lazymatch type of H1 with mleaf _ _ _ _ => clear H1 end)
     | mleaf (mret _) _ _ _ => let E1 := fresh "E" in let E2 := fresh "E" in apply mleaf_ret in L as [E1 E2];
         try (lazymatch type of E2 with ?x = _ => subst x end); try (lazymatch type of E1 with ?x = _ => subst x end)
     | mleaf (mo_ret MOps _) _ _ _ => let E1 := fresh "E" in let E2 := fresh "E" in apply mleaf_moret in L as [E1 E2];
         try (lazymatch type of E2 with ?x = _ => subst x end); try (lazymatch type of E1 with ?x = _ => subst x end)
     | mleaf munr _ _ _ => destruct (mleaf_unr _ _ _ L)
     | mleaf (mo_unr MOps) _ _ _ => destruct (mleaf_mounr _ _ _ L)
     | mleaf ((fun _ => _) _) _ _ _ => cbv beta in L
     | mleaf (if ?b then _ else _) _ _ _ => destruct b
     | mleaf (match ?x with _ => _ end) _ _ _ => destruct x
     | mleaf (let _ := _ in _) _ _ _ => cbv zeta in L
     | mleaf _ _ _ _ => tac L
     end ]).

Ltac notac H := fail.
Ltac inj_all := repeat (subst; match goal with H : (_, _) = (_, _) |- _ => injection H; clear H; intros end); subst.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Section Rfile.
  Context {H hptr : Type} (HO : HeapOps H hptr) (stk : stack_site -> Z).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Notation P := (prims HO fo_nop stk).

  Ltac rf_simp := cbn [fst snd pc_rfile set_errbuf set_bufdata set_buffer set_header set_priv set_ng set_break_loop] in *.
  Ltac rf_fin := inj_all; rf_simp;
    repeat (match goal with
            | |- context [pc_rfile (if ?c then _ else _)] => destruct c; rf_simp
            | H : context [pc_rfile (if ?c then _ else _)] |- _ => destruct c; rf_simp
            end); congruence.

  Lemma grow_buffer_rfile : forall (p : pcapT) n s r s', mleaf (grow_buffer MOps P p n) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros p n s r s' L. unfold grow_buffer in L. crawl_with notac L. all: rf_fin. Qed.

  Lemma read_block_rfile : forall d (p : pcapT) s r s', mleaf (read_block MOps P d p) s r s' ->
    match r with RB_Eof p' | RB_Err _ p' | RB_Ok _ p' => pc_rfile p' = pc_rfile p end.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros d p s r s' L. unfold read_block in L. crawl_with notac L. all: rf_fin. Qed.

  Lemma add_interface_rfile : forall (p : pcapT) off c s r s', mleaf (add_interface MOps P p off c) s r s' ->
    pc_rfile (snd (fst r)) = pc_rfile p.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros p off c s r s' L. unfold add_interface in L. crawl_with notac L. all: rf_fin. Qed.
  Ltac rf_heads H1 := first [ apply grow_buffer_rfile in H1 | apply read_block_rfile in H1 | apply add_interface_rfile in H1 ].

  Lemma ng_scan_blocks_rfile : forall fuel (p : pcapT) s r s', mleaf (ng_scan_blocks MOps P fuel p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    induction fuel as [|fuel IH]; intros p s r s' L; cbn [ng_scan_blocks] in L.
    - mleaf_inv L.
    - crawl_with ltac:(fun H1 => first [apply IH in H1 | rf_heads H1]) L. all: rf_fin.
  Qed.

  Lemma pcap_next_packet_rfile : forall (p : pcapT) s r s', mleaf (pcap_next_packet MOps P p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros p s r s' L. unfold pcap_next_packet in L. crawl_with rf_heads L. all: rf_fin. Qed.

  Lemma pcap_ng_next_packet_rfile : forall fuel (p : pcapT) s r s', mleaf (pcap_ng_next_packet MOps P fuel p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros fuel p s r s' L. unfold pcap_ng_next_packet in L.
    crawl_with ltac:(fun H1 => first [apply ng_scan_blocks_rfile in H1 | rf_heads H1]) L. all: rf_fin.
  Qed.

  Lemma next_packet_op_rfile : forall fuel (p : pcapT) s r s', mleaf (next_packet_op MOps P fuel p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros fuel p s r s' L. unfold next_packet_op in L.
    destruct (pc_priv p); [apply pcap_next_packet_rfile in L | apply pcap_ng_next_packet_rfile in L]; exact L.
  Qed.

  Lemma offline_read_rfile : forall fuel (p : pcapT) s r s', mleaf (pcapint_offline_read_1 MOps P fuel p) s r s' -> pc_rfile (snd r) = pc_rfile p.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros fuel p s r s' L. unfold pcapint_offline_read_1 in L.
    crawl_with ltac:(fun H1 => apply next_packet_op_rfile in H1) L. all: rf_fin.
  Qed.

  (* [comment removed for export] *)
  Lemma pcap_next_ex_rfile : forall fuel (p : pcapT) s st p' s',
    mleaf (Pcap.pcap_next_ex MOps P fuel p) s (st, p') s' -> pc_rfile p' = pc_rfile p.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros fuel p s st p' s' L. unfold Pcap.pcap_next_ex in L.
    crawl_with ltac:(fun H1 => apply offline_read_rfile in H1) L. all: rf_fin.
  Qed.

  Lemma pcap_stats_rfile : forall (p : pcapT) s sr p' s',
    mleaf (Pcap.pcap_stats (@MOps H hptr) p) s (sr, p') s' -> pc_rfile p' = pc_rfile p.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros p s sr p' s' L. unfold Pcap.pcap_stats in L. crawl_with notac L. all: rf_fin. Qed.
End Rfile.

End WithCeil.
End MLeaf.
