(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg S3Spec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import MState Mem Cells Step Frame Image.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface AllocLayout3 AllocTight AllocCover.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzIncs.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record FdImg := {
  fi_entry   : Z;      (* [comment removed for export] *)
  fi_crc     : Z;      (* [comment removed for export] *)
  fi_crcx    : list cell; (* [comment removed for export] *)
  fi_rnums   : Z;      (* [comment removed for export] *)
  fi_got     : Z;      (* [comment removed for export] *)
  fi_relro   : Z;      (* [comment removed for export] *)
  fi_stderrF : Z;      (* [comment removed for export] *)
  fi_stdinF  : Z;
  fi_stdoutF : Z;
  fi_template: Z;      (* [comment removed for export] *)
  fi_ofl     : Z;      (* [comment removed for export] *)
  fi_libc    : Z       (* [comment removed for export] *)
}.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fd_mem (segs : list Segment) (I : FdImg) (m : word -> option byte) : Prop :=
  rw_cells segs m (fi_got I) [C8 (Z_to_bv 64 (fi_relro I))]
  /\ rw_cells segs m (fi_got I + 16) [C8 (Z_to_bv 64 (fi_crc I)); C8 (Z_to_bv 64 (fi_rnums I));
                                      C8 (Z_to_bv 64 (fi_relro I + 16)); C8 (Z_to_bv 64 (fi_relro I + 8))]
  /\ rw_cells segs m (fi_relro I) [C8 (Z_to_bv 64 (fi_stderrF I)); C8 (Z_to_bv 64 (fi_stdinF I)); C8 (Z_to_bv 64 (fi_stdoutF I))]
  /\ rw_cells segs m (fi_crc I) (CB 1024 bz_crc_table_bytes :: fi_crcx I)
  /\ rw_cells segs m (fi_rnums I) [CB 2048 bz_rnums_table_bytes]
  /\ rw_cells segs m (fi_ofl I) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells segs m (fi_libc I + 1) [C1 (Z_to_bv 8 0)]
  (* [comment removed for export] *)
  /\ rw_cells segs m (fi_got I + 8) [C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition FD_STACK : Z := 65536.
(* [comment removed for export] *)
Definition FD_VM_NEED : nat := 13%nat.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition heap_pres_but (segs : list Segment) (L : alloc_layout) (LB : list ablock) (SP : Z) (E : Z -> Prop)
    (m m' : word -> option byte) : Prop :=
  forall a : Z, 0 <= a < 2 ^ 64 -> client_addr L LB SP a -> ~ E a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).
Definition ofl_range (I : FdImg) (a : Z) : Prop := fi_ofl I <= a < fi_ofl I + 16.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fds3 : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stmt.
  Variable segs : list Segment.
  Variable L : alloc_layout.
  Variable AI : AllocIface segs L.
  Variable AC : AllocCover segs L AI.
  Variable I : FdImg.
  (* [comment removed for export] *)
  Variable C : list byte -> list byte.

  (* [comment removed for export] *)
  Definition fd_post (o : fd_outcome)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list ablock) (m : word -> option byte) (MD : Model)
      (lo B : Z) (payload : list byte) (k : nat)
      (ms' : machine_state) (MD' : Model) : Prop :=
    exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv' : word) (m' : word -> option byte) (s' : ai_AS AI),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom segs)
      (* [comment removed for export] *)
      /\ ai_inv AI s' LB m' MD' /\ ac_c21 AC C21_idle s' LB /\ ac_vm AC k s' MD'
      (* [comment removed for export] *)
      /\ m_fds MD' = m_fds MD
      /\ m_fs MD' = fs_apply o (C payload) (m_fs MD)
      /\ mem_inv segs m'
      /\ stk segs m' lo (bv_unsigned sp)
      /\ rw_cells segs m' (errno_cell L) [C4 errv']
      /\ ai_aux AI m' B
      (* [comment removed for export] *)
      /\ heap_pres_but segs L LB (bv_unsigned sp) (ofl_range I) m m'
      (* [comment removed for export] *)
      /\ fd_mem segs I m'.

  (* [comment removed for export] *)
  Definition fd_spec : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
           (s : ai_AS AI) (LB : list ablock)
           (src len lo B : Z) (payload : list byte) (errv : word) (k : nat)
           (K : fd_outcome -> TSet),
      (* [comment removed for export] *)
      a0 = Z_to_bv 64 src -> a1 = Z_to_bv 64 len -> tp = Z_to_bv 64 (al_tp L) ->
      0 <= len < 2 ^ 26 ->
      (* [comment removed for export] *)
      ai_inv AI s LB m MD -> ac_c21 AC C21_idle s LB -> ac_vm AC (FD_VM_NEED + k)%nat s MD ->
      ai_aux AI m B -> bv_unsigned sp <= B ->
      (* [comment removed for export] *)
      m_fds MD = fds3 ->
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      bytes_at segs m src payload -> Z.of_nat (length payload) = len ->
      client_range L LB (bv_unsigned sp) src len -> src + len <= alloc_ceiling -> src mod 16 = 0 ->
      (* [comment removed for export] *)
      (len = 0 \/ exists b, In b LB /\ blk_addr b <= src /\ src + len <= blk_addr b + blk_size b) ->
      (* [comment removed for export] *)
      stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - FD_STACK ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 48 <= 2 ^ 47 ->
      (* [comment removed for export] *)
      rw_cells segs m (errno_cell L) [C4 errv] ->
      mem_inv segs m ->
      fd_mem segs I m ->
      (* [comment removed for export] *)
      (forall o ms' MD',
         fd_reachable (m_fs MD) o ->
         fd_post o ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB m MD lo B payload k ms' MD' ->
         realizes segs (mkCfg ms' MD') (K o)) ->
      realizes segs
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (fi_entry I)) fc None m (seg_rom segs)) MD)
        (t_fd_union (m_fs MD) K).
End Stmt.
End ACeilS1.


Arguments fd_spec {ACEIL__ segs L} AI AC I C.
Arguments fd_post {ACEIL__ segs L} AI AC I C.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition le8 (z : Z) : list byte := map (fun i => Z_to_bv 8 ((z / 2 ^ (8 * Z.of_nat i)) mod 256)) (seq 0 8).

(* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS2.
