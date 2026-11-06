(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState ECH_C1_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition BUFNEW_STACK : Z := FR_BUF_MEM_new + CZALLOC_STACK.
Definition BUFFREE_STACK : Z := FR_BUF_MEM_free + CFREE_STACK.
Definition BIOACC_STACK : Z := FR_BIO_set_data.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bio_with_ptr (B : biorep) (p : Z) : biorep :=
  mkBIO (bio_method B) (bio_init B) (bio_shutdown B) (bio_flags B) (bio_retry B) (bio_numf B) p (bio_next B) (bio_prev B) (bio_refs B) (bio_nread B) (bio_nwrite B).
Definition bio_with_init (B : biorep) (i : Z) : biorep :=
  mkBIO (bio_method B) i (bio_shutdown B) (bio_flags B) (bio_retry B) (bio_numf B) (bio_ptr B) (bio_next B) (bio_prev B) (bio_refs B) (bio_nread B) (bio_nwrite B).
Definition bio_with_flags (B : biorep) (f : Z) : biorep :=
  mkBIO (bio_method B) (bio_init B) (bio_shutdown B) f (bio_retry B) (bio_numf B) (bio_ptr B) (bio_next B) (bio_prev B) (bio_refs B) (bio_nread B) (bio_nwrite B).
Definition bio_ok (B : biorep) : Prop :=
     0 <= bio_method B < 2^64 /\ 0 <= bio_init B < 2^32 /\ 0 <= bio_shutdown B < 2^32 /\ 0 <= bio_flags B < 2^31
  /\ 0 <= bio_retry B < 2^32 /\ 0 <= bio_numf B < 2^32 /\ 0 <= bio_ptr B < 2^64 /\ 0 <= bio_next B < 2^64
  /\ 0 <= bio_prev B < 2^64 /\ 0 <= bio_refs B < 2^32 /\ 0 <= bio_nread B < 2^64 /\ 0 <= bio_nwrite B < 2^64.

Section W.
  Variable H : hsr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bufnew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : PState),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ xpres LB (bv_unsigned sp) memflag_foot m m'
      /\ rblock_range A BUFMEM_SIZE /\ hs_RHEAP H s' ((p, A, BUFMEM_SIZE) :: LB) m'
      /\ rw_cells rsegs m' A (buf_cells (mkBUF 0 0 0 0))
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'.
  Definition bufnew_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (v lo B : Z) (errv : word),
      a0 = Z_to_bv 64 0 ->                 (* [comment removed for export] *)
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + BUFMEM_SIZE <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> lb_big LB <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BUFNEW_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (bufnew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BUF_MEM_new) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  Definition buffree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (p : bptr) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ xpres (hs_lb_remove H p LB) (bv_unsigned sp) [] m m'
      /\ hs_RHEAP H s' (hs_lb_remove H p LB) m' /\ IMPL_mem m' /\ GOT_mem m'.
  Definition buffree_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (p : bptr) (A len mx fl lo B : Z) (errv : word),
      a0 = Z_to_bv 64 A -> In (p, A, BUFMEM_SIZE) LB -> rw_cells rsegs m A (buf_cells (mkBUF len 0 mx fl)) ->
      0 <= len < 2^64 -> 0 <= mx < 2^64 -> 0 <= fl < 2^64 ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BUFFREE_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (buffree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BUF_MEM_free) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bioacc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv : word) (a : Z) (B' : biorep) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (a, a + BIO_SIZE)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' a (bio_cells B').
  (* [comment removed for export] *)
  Definition bioacc_stmt_at (entry : Z) (rv : Z -> biorep -> Z -> word) (upd : biorep -> Z -> biorep) (xmax : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a x lo : Z) (B : biorep),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 x -> 0 <= x < xmax -> rw_cells rsegs m a (bio_cells B) -> bio_ok B -> a + BIO_SIZE <= lo ->
      stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - BIOACC_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (bioacc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (rv a B x) a (upd B x) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).
  Definition biosetdata_stmt : Prop := bioacc_stmt_at P_BIO_set_data (fun a _ _ => Z_to_bv 64 a) bio_with_ptr (2^64).
  Definition biogetdata_stmt : Prop := bioacc_stmt_at P_BIO_get_data (fun _ B _ => Z_to_bv 64 (bio_ptr B)) (fun B _ => B) (2^64).
  Definition biosetinit_stmt : Prop := bioacc_stmt_at P_BIO_set_init (fun a _ _ => Z_to_bv 64 a) bio_with_init (2^31).
  Definition bioclearflags_stmt : Prop :=
    bioacc_stmt_at P_BIO_clear_flags (fun a _ _ => Z_to_bv 64 a) (fun B x => bio_with_flags B (Z.land (bio_flags B) (Z.lnot x))) (2^31).
  Definition biotestflags_stmt : Prop :=
    bioacc_stmt_at P_BIO_test_flags (fun _ B x => Z_to_bv 64 (Z.land (bio_flags B) x)) (fun B _ => B) (2^31).
  Definition biosetflags_stmt : Prop :=
    bioacc_stmt_at P_BIO_set_flags (fun a _ _ => Z_to_bv 64 a) (fun B x => bio_with_flags B (Z.lor (bio_flags B) x)) (2^31).
  (* [comment removed for export] *)
  Definition bionext_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a x lo : Z) (B : biorep),
      a0 = Z_to_bv 64 a -> 0 < a -> rw_cells rsegs m a (bio_cells B) -> bio_ok B -> a + BIO_SIZE <= lo ->
      stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - BIOACC_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (bioacc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (bio_next B)) a B lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_next) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition biofb64_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - BIOACC_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
                   ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A_b64_method) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (ret_pc ra) fc None m' (seg_rom rsegs)
                   /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_f_base64) fc None m (seg_rom rsegs)).

  Definition C6_stmts : Prop :=
    bufnew_stmt /\ buffree_stmt /\ biosetdata_stmt /\ biogetdata_stmt /\ biosetinit_stmt
    /\ bioclearflags_stmt /\ biotestflags_stmt /\ biosetflags_stmt /\ bionext_stmt /\ biofb64_stmt.
End W.
End HCW.
