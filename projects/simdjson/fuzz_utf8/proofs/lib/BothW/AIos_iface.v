(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import F_syscalls StdioFiles Stdio_kit BImg MonadF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ITreeA StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition so_act (so : stdout_st) : stdout_st := mkStdout true (so_buf so) (so_lbf_nl so) (so_first so).
Definition so_inact (so : stdout_st) : stdout_st := mkStdout false [] (so_lbf_nl so) (so_first so).

Section CANSEC1. Context {rc : runConstT}.
Definition FWRITE0_STUB : Z := 0x6b0f4.     (* [comment removed for export] *)
Definition FFLUSH_STUB : Z := 0x6b154.      (* [comment removed for export] *)
Definition WCRTOMB_STUB : Z := 0x6b138.     (* [comment removed for export] *)
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
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ ICPT m' /\ P m'.

  (* [comment removed for export] *)
  Definition fwrite0_out_stmt : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (so_x : stdout_st),
      stk bsegs m lo (bv_unsigned sp) -> stdout_file m so_x -> ssp_cells m guard -> ICPT m -> mem_inv bsegs m ->
      a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 RSTDOUT -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG ->
      evtF bsegs RNG (icpt_post [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                                (fun m' => stdout_file m' (so_act so_x)))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FWRITE0_STUB) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition fwrite0_err_stmt : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk bsegs m lo (bv_unsigned sp) -> stderr_file m -> ssp_cells m guard -> ICPT m -> mem_inv bsegs m ->
      a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 RSTDERR -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG ->
      evtF bsegs RNG (icpt_post [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                                (fun m' => stderr_file m'))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FWRITE0_STUB) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition fflush_err_stmt : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk bsegs m lo (bv_unsigned sp) -> stderr_file m -> ssp_cells m guard -> ICPT m -> mem_inv bsegs m ->
      a0 = Z_to_bv 64 RSTDERR -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG ->
      evtF bsegs RNG (icpt_post [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                                (fun m' => stderr_file m'))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FFLUSH_STUB) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition wcr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (P : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 4096, bv_unsigned sp); (P, P + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ ICPT m' /\ rw_cells bsegs m' P [C1 (Z_to_bv 8 0)].

  Definition wcrtomb0_stmt : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (P : Z) (jb : list byte) (ST : Z),
      stk bsegs m lo (bv_unsigned sp) -> rw_cells bsegs m P [CB 1 jb] -> bv_unsigned sp <= P -> P + 4 <= bv_unsigned sp + 4096 ->
      ssp_cells m guard -> ICPT m -> mem_inv bsegs m ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 ST -> (ST = 0x6adbcc \/ ST = 0x6adbd4) -> tp = Z_to_bv 64 RTP ->
      SLO <= lo -> P + 8 <= SHI ->
      lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^47 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG P 1 -> rng_aimg RNG -> ICPTR RNG ->
      evtF bsegs RNG (wcr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard P m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 WCRTOMB_STUB) fc None m (seg_rom bsegs)).

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
        stk bsegs m lo (bv_unsigned sp) -> stdout_file m so_x ->
        so_buf so_x = so_buf (get_so s) -> (so_buf (get_so s) <> [] -> so_x = get_so s) ->
        so_first so_x = so_first (get_so s) -> so_lbf_nl so_x = so_lbf_nl (get_so s) ->          (* [comment removed for export] *)
        ssp_cells m guard -> ICPT m -> mem_inv bsegs m ->
        a0 = Z_to_bv 64 RSTDOUT -> tp = Z_to_bv 64 RTP ->
        lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
        rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG -> rng0 RNG -> bv_unsigned sp < 2^47 ->
        implAM RNG (stdout_exit_flush get_so set_so) s
               (fflush_out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
               (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FFLUSH_STUB) fc None m (seg_rom bsegs)).
  End Out.
End Stmts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ios_char_shared (m : mem) : Prop :=
  rw_cells bsegs m 0x16f860 [C8 (Z_to_bv 64 8)]                       (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x16fb98 [C8 (Z_to_bv 64 0x114cc4)]             (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x6ae660 [C8 (Z_to_bv 64 0x1701e0)]             (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x170208 [C8 (Z_to_bv 64 0x13c608)].            (* [comment removed for export] *)
Definition ios_cout (m : mem) : Prop :=
  rw_cells bsegs m 0x6ade38 [C8 (Z_to_bv 64 0x16f878)]
  /\ rw_cells bsegs m 0x6ade48 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0x6ade60 [C4 z64]
  /\ rw_cells bsegs m 0x6ade68 [C8 (Z_to_bv 64 0x6adbe8)]
  /\ rw_cells bsegs m 0x6adec8 [C8 z64]
  /\ rw_cells bsegs m 0x6adbe8 [C8 (Z_to_bv 64 0x16fb68)]
  /\ rw_cells bsegs m 0x6adc28 [C8 (Z_to_bv 64 RSTDOUT); C8 (Z_to_bv 64 0x6ae660); C8 (Z_to_bv 64 0x6adbb4)].
Definition ios_clog (m : mem) : Prop :=
  rw_cells bsegs m 0x6ae0b8 [C8 (Z_to_bv 64 0x16f878)]
  /\ rw_cells bsegs m 0x6ae0c8 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0x6ae0e0 [C4 z64]
  /\ rw_cells bsegs m 0x6ae0e8 [C8 (Z_to_bv 64 0x6adc48)]
  /\ rw_cells bsegs m 0x6ae148 [C8 z64]
  /\ rw_cells bsegs m 0x6adc48 [C8 (Z_to_bv 64 0x16fb68)]
  /\ rw_cells bsegs m 0x6adc88 [C8 (Z_to_bv 64 RSTDERR); C8 (Z_to_bv 64 0x6ae660); C8 (Z_to_bv 64 0x6adbbc)].

(* [comment removed for export] *)
Definition ios_wide_shared (m : mem) : Prop :=
  rw_cells bsegs m 0x16f980 [C8 (Z_to_bv 64 8)]
  /\ rw_cells bsegs m 0x16fcc8 [C8 (Z_to_bv 64 0x115428)]
  /\ rw_cells bsegs m 0x6ae7f0 [C8 (Z_to_bv 64 0x16ff30)]
  /\ rw_cells bsegs m 0x16ff58 [C8 (Z_to_bv 64 0x13cdd4)]
  /\ rw_cells bsegs m 0x6ae800 [C8 (Z_to_bv 64 0x33188)]
  /\ rw_cells bsegs m 0x6afad8 [C8 (Z_to_bv 64 0x6cfdd0)].
Definition ios_wcout (m : mem) : Prop :=
  rw_cells bsegs m 0x6aded8 [C8 (Z_to_bv 64 0x16f998)]
  /\ rw_cells bsegs m 0x6adee8 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0x6adf00 [C4 z64]
  /\ rw_cells bsegs m 0x6adf08 [C8 (Z_to_bv 64 0x6adca8)]
  /\ rw_cells bsegs m 0x6adf68 [C8 z64]
  /\ rw_cells bsegs m 0x6adca8 [C8 (Z_to_bv 64 0x16fc98)]
  /\ rw_cells bsegs m 0x6adce8 [C8 (Z_to_bv 64 RSTDOUT); C8 (Z_to_bv 64 0x6ae7f0); C8 (Z_to_bv 64 0x6adbcc)].
Definition ios_wclog (m : mem) : Prop :=
  rw_cells bsegs m 0x6ae158 [C8 (Z_to_bv 64 0x16f998)]
  /\ rw_cells bsegs m 0x6ae168 [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 0x10); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0x6ae180 [C4 z64]
  /\ rw_cells bsegs m 0x6ae188 [C8 (Z_to_bv 64 0x6add08)]
  /\ rw_cells bsegs m 0x6ae1e8 [C8 z64]
  /\ rw_cells bsegs m 0x6add08 [C8 (Z_to_bv 64 0x16fc98)]
  /\ rw_cells bsegs m 0x6add48 [C8 (Z_to_bv 64 RSTDERR); C8 (Z_to_bv 64 0x6ae7f0); C8 (Z_to_bv 64 0x6adbd4)].
(* [comment removed for export] *)
Definition ios_cells (m : mem) : Prop :=
  ios_char_shared m /\ ios_cout m /\ ios_clog m /\ ios_wide_shared m /\ ios_wcout m /\ ios_wclog m.
End CANSEC1.
