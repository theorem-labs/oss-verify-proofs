(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg Spec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import MState Mem Cells Step Frame Image. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocTight AllocCover.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzIncs.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record HarnImg := {
  hi_entry   : Z;      (* [comment removed for export] *)
  hi_crc     : Z;      (* [comment removed for export] *)
  hi_crcx    : list cell; (* [comment removed for export] *)
  hi_rnums   : Z;      (* [comment removed for export] *)
  hi_got     : Z;      (* [comment removed for export] *)
  hi_relro   : Z;      (* [comment removed for export] *)
  hi_stderrF : Z;      (* [comment removed for export] *)
  hi_libc    : Z       (* [comment removed for export] *)
}.
Definition S0I : HarnImg :=
  {| hi_entry := 0x13a20; hi_crc := 0x33178; hi_crcx := [CB 56 incs_bytes]; hi_rnums := 0x335b0; hi_got := 0x320e8; hi_relro := 0x32098;
     hi_stderrF := 0x33db0; hi_libc := 0x64470 |}.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition harn_mem (segs : list Segment) (I : HarnImg) (m : word -> option byte) : Prop :=
  rw_cells segs m (hi_got I) [C8 (Z_to_bv 64 (hi_relro I))]
  /\ rw_cells segs m (hi_got I + 8) [C8 (Z_to_bv 64 0)]
  /\ rw_cells segs m (hi_got I + 16) [C8 (Z_to_bv 64 (hi_relro I + 8)); C8 (Z_to_bv 64 (hi_crc I)); C8 (Z_to_bv 64 (hi_rnums I))]
  /\ rw_cells segs m (hi_relro I) [C8 (Z_to_bv 64 (hi_stderrF I))]
  /\ rw_cells segs m (hi_crc I) (CB 1024 bz_crc_table_bytes :: hi_crcx I)
  /\ rw_cells segs m (hi_rnums I) [CB 2048 bz_rnums_table_bytes]
  /\ rw_cells segs m (hi_libc I + 1) [C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition HARN_STACK : Z := 65536.
(* [comment removed for export] *)
Definition HARN_VM_NEED : nat := 15%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stmt.
  Variable segs : list Segment.
  Variable L : alloc_layout.
  Variable AI : AllocIface segs L.
  Variable AC : AllocCover segs L AI.
  Variable I : HarnImg.

  (* [comment removed for export] *)
  Definition harn_post
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list ablock) (m : word -> option byte) (MD : Model)
      (lo B : Z) (k : nat)
      (ms' : machine_state) (MD' : Model) : Prop :=
    exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv' : word) (m' : word -> option byte) (s' : ai_AS AI),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom segs)
      (* [comment removed for export] *)
      /\ ai_inv AI s' LB m' MD' /\ ac_vm AC k s' MD'
      (* [comment removed for export] *)
      /\ vm_only MD MD'
      /\ mem_inv segs m'
      /\ stk segs m' lo (bv_unsigned sp)
      /\ rw_cells segs m' (errno_cell L) [C4 errv']
      /\ ai_aux AI m' B
      (* [comment removed for export] *)
      /\ heap_pres segs L LB (bv_unsigned sp) m m'
      (* [comment removed for export] *)
      /\ harn_mem segs I m'.

  (* [comment removed for export] *)
  Definition harn_spec : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
           (s : ai_AS AI) (LB : list ablock)
           (src len lo B : Z) (payload : list byte) (errv : word) (k : nat)
           (K : TSet),
      (* [comment removed for export] *)
      a0 = Z_to_bv 64 src -> a1 = Z_to_bv 64 len -> tp = Z_to_bv 64 (al_tp L) ->
      0 <= len < 2 ^ 26 ->
      (* [comment removed for export] *)
      ai_inv AI s LB m MD -> ac_vm AC (HARN_VM_NEED + k)%nat s MD ->
      ai_aux AI m B -> bv_unsigned sp <= B ->
      (* [comment removed for export] *)
      bytes_at segs m src payload -> Z.of_nat (length payload) = len ->
      client_range L LB (bv_unsigned sp) src len -> src + len <= alloc_ceiling -> src mod 16 = 0 ->
      (len = 0 \/ exists b, In b LB /\ blk_addr b <= src /\ src + len <= blk_addr b + blk_size b) ->
      (* [comment removed for export] *)
      stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - HARN_STACK ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 48 <= 2 ^ 47 ->
      (* [comment removed for export] *)
      rw_cells segs m (errno_cell L) [C4 errv] ->
      mem_inv segs m ->
      harn_mem segs I m ->
      (* [comment removed for export] *)
      (forall ms' MD',
         harn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB m MD lo B k ms' MD' ->
         realizes segs (mkCfg ms' MD') K) ->
      realizes segs
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (hi_entry I)) fc None m (seg_rom segs)) MD)
        K.
End Stmt.
End ACeilS1.


Arguments harn_spec {ACEIL__ segs L} AI AC I.
Arguments harn_post {ACEIL__ segs L} AI AC I.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition le8 (z : Z) : list byte := map (fun i => Z_to_bv 8 ((z / 2 ^ (8 * Z.of_nat i)) mod 256)) (seq 0 8).

Lemma harn_img_s0 :
  image_bytes s0segs (hi_crc S0I) 1024 = Some bz_crc_table_bytes
  /\ image_bytes s0segs (hi_rnums S0I) 2048 = Some bz_rnums_table_bytes
  /\ image_bytes s0segs (hi_got S0I) 40 = Some (le8 (hi_relro S0I) ++ le8 0 ++ le8 (hi_relro S0I + 8) ++ le8 (hi_crc S0I) ++ le8 (hi_rnums S0I))
  /\ image_bytes s0segs (hi_relro S0I) 8 = Some (le8 (hi_stderrF S0I)).
Proof. repeat match goal with |- _ /\ _ => split end; lazymatch goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS2.
