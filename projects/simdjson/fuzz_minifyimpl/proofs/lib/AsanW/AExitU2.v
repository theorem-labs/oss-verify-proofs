(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Driver AsanCtrl HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow ITreeA ExecF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AU_kit AU_iface AHarnessU_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import F_syscalls StdioFiles Stdio_kit MonadF AExit AAtexit_iface AIos_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition AEXITU2_PC : Z := 0x147adc.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AEXITU2_STACK : Z := 32768.

Section Params.
  Variable AI : AMallocIface.
  Variables MDPRE ICPT : mem -> Prop.
  Variable ICPTR : footprint -> Prop.
  Variables SLO SHI : Z.

  Definition aat_exitU2 (code : Z) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo t : Z) (cdt thr sec : byte) (tm1 dso guard : word) (tbl : list (Z * Z))
           (L : alayout) (LB : list ablock) (rstk : region),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 AEXITU2_PC) fc None m (seg_rom asegs)
      /\ MDPRE m /\ ICPT m /\ ICPTR RNG /\ ios_cells m
      /\ AHEAP AI L RNG (aps_m s) LB m /\ (forall b, In b LB -> exists q A n, b = HB q A n) /\ harness_invA m /\ aps_ok L s
      /\ stk asegs m lo (bv_unsigned sp)
      /\ rw_cells asegs m 0x6a4d40 [C4 (Z_to_bv 64 t)]                                   (* [comment removed for export] *)
      /\ rw_cells asegs m 0x6c5058 [C4 (Z_to_bv 64 0)]                                   (* [comment removed for export] *)
      /\ rw_cells asegs m 0x6c5078 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]       (* [comment removed for export] *)
      /\ ATEXIT tbl m
      /\ ((aps_cl s = None /\ (tbl = TBL_MAIN \/ tbl = TBL_REG))                  (* [comment removed for export] *)
          \/ (exists p V, aps_cl s = Some p /\ tbl = TBL_RUN ADTOR_THUNK AVEC /\ In (HB p V 8) LB
                          /\ rw_cells asegs m AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))]
                          /\ rw_cells asegs m V [C8 (Z_to_bv 64 AFALLBACK)]))
      /\ aincb 0 m                                                                     (* [comment removed for export] *)
      /\ rw_cells asegs m 0x16dbd4 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
      /\ rw_cells asegs m 0x202260 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
      /\ rw_cells asegs m 0x160c90 [C8 (Z_to_bv 64 0xb45a8); C8 (Z_to_bv 64 0x5a2b8)]  (* [comment removed for export] *)
      /\ rw_cells asegs m 0x16cd50 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
      /\ rw_cells asegs m 0x168e60 [C8 dso]                                             (* [comment removed for export] *)
      /\ rw_cells asegs m 0x6c55f0 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x16ba18 [C8 (Z_to_bv 64 RSTDIN)] /\ rw_cells asegs m RSTDIN stdin_cells
      /\ rw_cells asegs m 0x16bb08 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells asegs m 0x16b928 [C8 (Z_to_bv 64 RSTDERR)]
      /\ stdout_file m (aps_so s) /\ stderr_file m
      /\ rw_cells asegs m ssp_guard [C8 guard]
      /\ mem_inv asegs m /\ frm0 fc
      /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code
      /\ 0 < t < 4194304 /\ lo <= bv_unsigned sp - AEXITU2_STACK /\ ATOP + 4096 <= lo /\ SLO <= lo /\ bv_unsigned sp <= SHI /\ KHIGH <= lo
      /\ bv_unsigned sp mod 16 = 0
      /\ In [AFREE_PC] (al_U L)            (* [comment removed for export] *)
      /\ rclean m rstk /\ r_lo rstk <= lo /\ bv_unsigned sp - 64 <= r_hi rstk /\ ATOP <= r_rlo rstk
      /\ HUX L /\ rng RNG lo (al_top L - lo) /\ rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rrng RNG rstk
      /\ Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W /\ rng0 RNG
      /\ bv_unsigned sp < 2^47.

  (* [comment removed for export] *)
  Definition aexitU2_stmt : Prop :=
    forall code (s : APS) RNG ms (Q : Empty_set -> APS -> footprint -> machine_state -> Prop),
      aat_exitU2 code s RNG ms ->
      implMA RNG (client_exitA AAllocAsan ;;; exit_model (ioA AAllocAsan) code) s Q ms.
End Params.
End CANSEC1.
