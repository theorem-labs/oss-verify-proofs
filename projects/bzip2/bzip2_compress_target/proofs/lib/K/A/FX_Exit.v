(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac Arr Bytes ITree Nodes Decode SysStep ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Prelim Monad Stdio.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require FX_Layout.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Monad Stdio.
Export OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.FX_Layout.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

(* [comment removed for export] *)
Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
  exists (flags mode : word) (tail bufbytes : list byte),
    rw_cells bsegs m RSTDOUT
      (file_cells flags
         (if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
         (if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
         (if so_active so then RSTDOUT_BUF else 0)%Z
         (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
         RSTDOUT_BUF 1024 1 mode
         (if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
    /\ Z.land (bv_unsigned flags) 72 = 0%Z
    /\ rw_cells bsegs m RSTDOUT_BUF [CB 1024 bufbytes]
    /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
    /\ (zlength (so_buf so) <= 1024)%Z
    /\ (so_active so = false -> so_buf so = []).

(* [comment removed for export] *)
Definition stderr_file (m : word -> option byte) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells bsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x629be0 0 2 mode 0xffffffff tail).

(* [comment removed for export] *)
Notation RSTDIN := 0xd2458%Z (only parsing).
Definition stdin_file (m : word -> option byte) : Prop :=
  exists (j0 j1 j2 j3 j4 : list byte),
    rw_cells bsegs m RSTDIN [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 j1; C8 (Z_to_bv 64 0); CB 8 j2;
                             C8 (Z_to_bv 64 0); CB 76 j3; C4 (Z_to_bv 64 0xffffffff); CB 88 j4].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdioExitStatement.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0xd2630); (RSTDOUT_BUF, 0x62a428)]%Z m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ s' = set_so so' s
      /\ stdout_file m' so' /\ so_buf so' = []
      /\ stderr_file m'
      /\ ro_cells bsegs m' 0xcdad0 [C8 (Z_to_bv 64 0x629518)] /\ ro_cells bsegs m' 0x629518 [C8 guard].

  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk bsegs m lo (bv_unsigned sp) ->
      rw_cells bsegs m 0x629768 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
      rw_cells bsegs m 0x629bd0 [C8 (Z_to_bv 64 0)] ->                                            (* [comment removed for export] *)
      rw_cells bsegs m 0xd2540 [C8 (Z_to_bv 64 RSTDIN)] ->                            (* [comment removed for export] *)
      stdin_file m ->
      rw_cells bsegs m 0xd2630 [C8 (Z_to_bv 64 RSTDOUT)] ->                           (* [comment removed for export] *)
      rw_cells bsegs m 0xd2450 [C8 (Z_to_bv 64 RSTDERR)] ->                           (* [comment removed for export] *)
      stdout_file m (get_so s) -> stderr_file m ->
      ro_cells bsegs m 0xcdad0 [C8 (Z_to_bv 64 0x629518)] -> ro_cells bsegs m 0x629518 [C8 guard] ->   (* [comment removed for export] *)
      mem_inv bsegs m ->
      tp = Z_to_bv 64 0x6094d8 ->
      (lo <= bv_unsigned sp - 160)%Z -> (0x62b000 <= lo)%Z ->
      implM bsegs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xc221c) fc None m (seg_rom bsegs)).
End StdioExitStatement.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Export FX_Layout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

(* [comment removed for export] *)
Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
  exists (flags mode : word) (tail bufbytes : list byte),
    rw_cells asegs m RSTDOUT
      (file_cells flags
         (if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
         (if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
         (if so_active so then RSTDOUT_BUF else 0)%Z
         (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
         RSTDOUT_BUF 1024 1 mode
         (if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
    /\ Z.land (bv_unsigned flags) 72 = 0%Z
    /\ rw_cells asegs m RSTDOUT_BUF [CB 1024 bufbytes]
    /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
    /\ (zlength (so_buf so) <= 1024)%Z
    /\ (so_active so = false -> so_buf so = []).

(* [comment removed for export] *)
Definition stderr_file (m : word -> option byte) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells asegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x61c7e0 0 2 mode 0xffffffff tail).

(* [comment removed for export] *)
Notation RSTDIN := 0xc5018%Z (only parsing).
Definition stdin_file (m : word -> option byte) : Prop :=
  exists (j0 j1 j2 j3 j4 : list byte),
    rw_cells asegs m RSTDIN [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 j1; C8 (Z_to_bv 64 0); CB 8 j2;
                             C8 (Z_to_bv 64 0); CB 76 j3; C4 (Z_to_bv 64 0xffffffff); CB 88 j4].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdioExitStatement.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0xc51f0); (RSTDOUT_BUF, 0x61d028)]%Z m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ s' = set_so so' s
      /\ stdout_file m' so' /\ so_buf so' = []
      /\ stderr_file m'
      /\ ro_cells asegs m' 0xc06f0 [C8 (Z_to_bv 64 0x61c118)] /\ ro_cells asegs m' 0x61c118 [C8 guard].

  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk asegs m lo (bv_unsigned sp) ->
      rw_cells asegs m 0x61c368 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
      rw_cells asegs m 0x61c7d0 [C8 (Z_to_bv 64 0)] ->                                            (* [comment removed for export] *)
      rw_cells asegs m 0xc5100 [C8 (Z_to_bv 64 RSTDIN)] ->                            (* [comment removed for export] *)
      stdin_file m ->
      rw_cells asegs m 0xc51f0 [C8 (Z_to_bv 64 RSTDOUT)] ->                           (* [comment removed for export] *)
      rw_cells asegs m 0xc5010 [C8 (Z_to_bv 64 RSTDERR)] ->                           (* [comment removed for export] *)
      stdout_file m (get_so s) -> stderr_file m ->
      ro_cells asegs m 0xc06f0 [C8 (Z_to_bv 64 0x61c118)] -> ro_cells asegs m 0x61c118 [C8 guard] ->   (* [comment removed for export] *)
      mem_inv asegs m ->
      tp = Z_to_bv 64 0x5fc0d8 ->
      (lo <= bv_unsigned sp - 160)%Z -> (0x61e000 <= lo)%Z ->
      implM asegs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xb4e3c) fc None m (seg_rom asegs)).
End StdioExitStatement.
