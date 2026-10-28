(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Export FX_Layout.
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
    rw_cells bsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0xbfb558 0 2 mode 0xffffffff tail).

(* [comment removed for export] *)
Notation RSTDIN := 0x5e7258%Z (only parsing).
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
      /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x5e7430); (RSTDOUT_BUF, 0xbfbda0)]%Z m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ s' = set_so so' s
      /\ stdout_file m' so' /\ so_buf so' = []
      /\ stderr_file m'
      /\ ro_cells bsegs m' 0x5e2c40 [C8 (Z_to_bv 64 0xbfae90)] /\ ro_cells bsegs m' 0xbfae90 [C8 guard].

  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk bsegs m lo (bv_unsigned sp) ->
      rw_cells bsegs m 0xbfb0e0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
      rw_cells bsegs m 0xbfb548 [C8 (Z_to_bv 64 0)] ->                                            (* [comment removed for export] *)
      rw_cells bsegs m 0x5e7340 [C8 (Z_to_bv 64 RSTDIN)] ->                            (* [comment removed for export] *)
      stdin_file m ->
      rw_cells bsegs m 0x5e7430 [C8 (Z_to_bv 64 RSTDOUT)] ->                           (* [comment removed for export] *)
      rw_cells bsegs m 0x5e7250 [C8 (Z_to_bv 64 RSTDERR)] ->                           (* [comment removed for export] *)
      stdout_file m (get_so s) -> stderr_file m ->
      ro_cells bsegs m 0x5e2c40 [C8 (Z_to_bv 64 0xbfae90)] -> ro_cells bsegs m 0xbfae90 [C8 guard] ->   (* [comment removed for export] *)
      mem_inv bsegs m ->
      tp = Z_to_bv 64 0xbdae50 ->
      (lo <= bv_unsigned sp - 160)%Z -> (0xbfd000 <= lo)%Z ->
      implM bsegs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x55de04) fc None m (seg_rom bsegs)).
End StdioExitStatement.
