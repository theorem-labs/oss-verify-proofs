(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import F_syscalls StdioFiles Stdio_kit AImg MonadF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ITreeA StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition so_act (so : stdout_st) : stdout_st := mkStdout true (so_buf so) (so_lbf_nl so) (so_first so).
Definition so_inact (so : stdout_st) : stdout_st := mkStdout false [] (so_lbf_nl so) (so_first so).

Section CANSEC1. Context {rc : runConstT}.
Definition FWRITE0_STUB : Z := 0x6c248.     (* [comment removed for export] *)
Definition FFLUSH_STUB : Z := 0x6c2a8.      (* [comment removed for export] *)
Definition WCRTOMB_STUB : Z := 0x6c28c.     (* [comment removed for export] *)
Definition ICPT_DEPTH : Z := 4096.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_OUT (sp : Z) : list (Z * Z) := [(sp - ICPT_DEPTH, sp); (RSTDOUT, RSTDOUT + 232)].
Definition W_ERR (sp : Z) : list (Z * Z) := [(sp - ICPT_DEPTH, sp); (RSTDERR, RSTDERR + 232)].

Section Stmts.
  (* [comment removed for export] *)
  Variable ICPT : mem -> Prop.
  (* [comment removed for export] *)
  Variable ICPTR : footprint -> Prop.
  (* [comment removed for export] *)
  Variables SLO SHI : Z.

  Definition icpt_post (W : list (Z * Z)) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : mem) (P : mem -> Prop) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ ICPT m' /\ P m'.

  (* [comment removed for export] *)
  Definition fwrite0_out_stmt : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (so_x : stdout_st),
      stk asegs m lo (bv_unsigned sp) -> stdout_file m so_x -> ssp_cells m guard -> ICPT m -> mem_inv asegs m ->
      a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 RSTDOUT -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG ->
      evtF asegs RNG (icpt_post [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                                (fun m' => stdout_file m' (so_act so_x)))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FWRITE0_STUB) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fwrite0_err_stmt : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk asegs m lo (bv_unsigned sp) -> stderr_file m -> ssp_cells m guard -> ICPT m -> mem_inv asegs m ->
      a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 RSTDERR -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG ->
      evtF asegs RNG (icpt_post [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                                (fun m' => stderr_file m'))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FWRITE0_STUB) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fflush_err_stmt : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk asegs m lo (bv_unsigned sp) -> stderr_file m -> ssp_cells m guard -> ICPT m -> mem_inv asegs m ->
      a0 = Z_to_bv 64 RSTDERR -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG ->
      evtF asegs RNG (icpt_post [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                                (fun m' => stderr_file m'))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FFLUSH_STUB) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition wcr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (P : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 4096, bv_unsigned sp); (P, P + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ ICPT m' /\ rw_cells asegs m' P [C1 (Z_to_bv 8 0)].

  Definition wcrtomb0_stmt : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (P : Z) (jb : list byte) (ST : Z),
      stk asegs m lo (bv_unsigned sp) -> rw_cells asegs m P [CB 1 jb] -> bv_unsigned sp <= P -> P + 4 <= bv_unsigned sp + 4096 ->
      ssp_cells m guard -> ICPT m -> mem_inv asegs m ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 ST -> (ST = 0x6a2eac \/ ST = 0x6a2eb4) -> tp = Z_to_bv 64 RTP ->
      SLO <= lo -> P + 8 <= SHI ->
      lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^47 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG P 1 -> rng_aimg RNG -> ICPTR RNG ->
      evtF asegs RNG (wcr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard P m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 WCRTOMB_STUB) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Section Out.
    Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
    Definition fflush_out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
        (lo : Z) (guard : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
      fun _ st' ms' => exists (so' : stdout_st),
        st' = set_so so' st /\ so_buf so' = []
        /\ icpt_post [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                     (fun m' => stdout_file m' (so_inact so')) ms'.

    Definition fflush_out_stmt : Prop :=
      forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (s : St) (so_x : stdout_st),
        stk asegs m lo (bv_unsigned sp) -> stdout_file m so_x ->
        so_buf so_x = so_buf (get_so s) -> (so_buf (get_so s) <> [] -> so_x = get_so s) ->
        so_first so_x = so_first (get_so s) -> so_lbf_nl so_x = so_lbf_nl (get_so s) ->          (* [comment removed for export] *)
        ssp_cells m guard -> ICPT m -> mem_inv asegs m ->
        a0 = Z_to_bv 64 RSTDOUT -> tp = Z_to_bv 64 RTP ->
        lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
        rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG -> rng0 RNG -> bv_unsigned sp < 2^47 ->
        implAM RNG (stdout_exit_flush get_so set_so) s
               (fflush_out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
               (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FFLUSH_STUB) fc None m (seg_rom asegs)).
  End Out.
End Stmts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ios_char_shared (m : mem) : Prop :=
  rw_cells asegs m 0x164880 [C8 (Z_to_bv 64 8)]                       (* [comment removed for export] *)
  /\ rw_cells asegs m 0x164bb8 [C8 (Z_to_bv 64 0x109afc)]             (* [comment removed for export] *)
  /\ rw_cells asegs m 0x6a3940 [C8 (Z_to_bv 64 0x165200)]             (* [comment removed for export] *)
  /\ rw_cells asegs m 0x165228 [C8 (Z_to_bv 64 0x131380)].            (* [comment removed for export] *)
Definition ios_cout (m : mem) : Prop :=
  rw_cells asegs m 0x6a3118 [C8 (Z_to_bv 64 0x164898)]
  /\ rw_cells asegs m 0x6a3128 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x6a3140 [C4 z64]
  /\ rw_cells asegs m 0x6a3148 [C8 (Z_to_bv 64 0x6a2ec8)]
  /\ rw_cells asegs m 0x6a31a8 [C8 z64]
  /\ rw_cells asegs m 0x6a2ec8 [C8 (Z_to_bv 64 0x164b88)]
  /\ rw_cells asegs m 0x6a2f08 [C8 (Z_to_bv 64 RSTDOUT); C8 (Z_to_bv 64 0x6a3940); C8 (Z_to_bv 64 0x6a2e94)].
Definition ios_clog (m : mem) : Prop :=
  rw_cells asegs m 0x6a3398 [C8 (Z_to_bv 64 0x164898)]
  /\ rw_cells asegs m 0x6a33a8 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x6a33c0 [C4 z64]
  /\ rw_cells asegs m 0x6a33c8 [C8 (Z_to_bv 64 0x6a2f28)]
  /\ rw_cells asegs m 0x6a3428 [C8 z64]
  /\ rw_cells asegs m 0x6a2f28 [C8 (Z_to_bv 64 0x164b88)]
  /\ rw_cells asegs m 0x6a2f68 [C8 (Z_to_bv 64 RSTDERR); C8 (Z_to_bv 64 0x6a3940); C8 (Z_to_bv 64 0x6a2e9c)].

(* [comment removed for export] *)
Definition ios_wide_shared (m : mem) : Prop :=
  rw_cells asegs m 0x1649a0 [C8 (Z_to_bv 64 8)]
  /\ rw_cells asegs m 0x164ce8 [C8 (Z_to_bv 64 0x10a260)]
  /\ rw_cells asegs m 0x6a3ad0 [C8 (Z_to_bv 64 0x164f50)]
  /\ rw_cells asegs m 0x164f78 [C8 (Z_to_bv 64 0x131b4c)]
  /\ rw_cells asegs m 0x6a3ae0 [C8 (Z_to_bv 64 0x34628)]
  /\ rw_cells asegs m 0x6a4db8 [C8 (Z_to_bv 64 0x6c50b0)].
Definition ios_wcout (m : mem) : Prop :=
  rw_cells asegs m 0x6a31b8 [C8 (Z_to_bv 64 0x1649b8)]
  /\ rw_cells asegs m 0x6a31c8 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x6a31e0 [C4 z64]
  /\ rw_cells asegs m 0x6a31e8 [C8 (Z_to_bv 64 0x6a2f88)]
  /\ rw_cells asegs m 0x6a3248 [C8 z64]
  /\ rw_cells asegs m 0x6a2f88 [C8 (Z_to_bv 64 0x164cb8)]
  /\ rw_cells asegs m 0x6a2fc8 [C8 (Z_to_bv 64 RSTDOUT); C8 (Z_to_bv 64 0x6a3ad0); C8 (Z_to_bv 64 0x6a2eac)].
Definition ios_wclog (m : mem) : Prop :=
  rw_cells asegs m 0x6a3438 [C8 (Z_to_bv 64 0x1649b8)]
  /\ rw_cells asegs m 0x6a3448 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x6a3460 [C4 z64]
  /\ rw_cells asegs m 0x6a3468 [C8 (Z_to_bv 64 0x6a2fe8)]
  /\ rw_cells asegs m 0x6a34c8 [C8 z64]
  /\ rw_cells asegs m 0x6a2fe8 [C8 (Z_to_bv 64 0x164cb8)]
  /\ rw_cells asegs m 0x6a3028 [C8 (Z_to_bv 64 RSTDERR); C8 (Z_to_bv 64 0x6a3ad0); C8 (Z_to_bv 64 0x6a2eb4)].
(* [comment removed for export] *)
Definition ios_cells (m : mem) : Prop :=
  ios_char_shared m /\ ios_cout m /\ ios_clog m /\ ios_wide_shared m /\ ios_wcout m /\ ios_wclog m.
End CANSEC1.
