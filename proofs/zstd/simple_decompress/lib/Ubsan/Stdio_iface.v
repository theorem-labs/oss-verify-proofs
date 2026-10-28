(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import F_memset F_memcpy F_printf_iface Stdio_kit StdioFiles.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition stderr_wfile0 (m : mem) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells usegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x688c8 0 2 mode 0xffffffff tail)
    /\ Z.land (bv_unsigned flags) 40 = 0
    /\ (wend = 0 \/ (wend = 0x688c8 /\ e = 0x688c8))
    /\ 0 <= e < 2^63.

Lemma stderr_wfile0_wfile : forall m, stderr_wfile0 m -> stderr_wfile m.
Proof. intros m (flags & mode & e & wend & tail & H & FL & _ & _). exists flags, mode, e, wend, tail. split; [exact H| exact FL]. Qed.
Lemma stderr_wfile0_file : forall m, stderr_wfile0 m -> stderr_file m.
Proof. intros m H. apply stderr_wfile_file, stderr_wfile0_wfile, H. Qed.

(* [comment removed for export] *)
Definition FWRITE_DEPTH : Z := 240.

Section Fwrite.
  Context {St : Type}.

  Definition fwrite_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ st' = st.

  (* [comment removed for export] *)
  Definition fwrite_diag_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
      towrite_stmt ->
      stderr_wfile0 m ->
      bytes_at usegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
      a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^47) -> (bv_unsigned a0 + zlength s <= 2^47) ->      (* [comment removed for export] *)
      (bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      ssp_cells m canary -> mem_inv usegs m ->
      implM usegs (stderr_fwrite s : M St unit) st
            (fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x30358) fc None m (seg_rom usegs)).
  (* [comment removed for export] *)
  Definition fwrite_1n_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z),
      towrite_stmt ->
      stderr_wfile0 m ->
      bytes_at usegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
      a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 (zlength s) -> a3 = Z_to_bv 64 RSTDERR ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^47) -> (bv_unsigned a0 + zlength s <= 2^47) ->      (* [comment removed for export] *)
      (bv_unsigned a0 + zlength s <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      ssp_cells m canary -> mem_inv usegs m ->
      implM usegs (stderr_fwrite s : M St unit) st
            (fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x30358) fc None m (seg_rom usegs)).
End Fwrite.

(* [comment removed for export] *)
Definition FPUTS_DEPTH : Z := 272.
Section Fputs.
  Context {St : Type}.
  Definition fputs_stderr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z) (slack : list byte),
      towrite_stmt ->
      stderr_wfile0 m ->
      bytes_at usegs m (bv_unsigned a0) (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256) s -> 0 < zlength s < 2^31 ->
      ((- (bv_unsigned a0 + zlength s + 1)) mod 8 <= zlength slack) ->
      a1 = Z_to_bv 64 RSTDERR ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPUTS_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned a0 + zlength s + 1 + zlength slack <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength s + 1 + zlength slack <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      ssp_cells m canary -> mem_inv usegs m ->
      implM usegs (stderr_fputs s : M St unit) st
            (fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x30304) fc None m (seg_rom usegs)).
End Fputs.
