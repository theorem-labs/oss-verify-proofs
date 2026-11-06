(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition CMALLOC_STACK : Z := FR_CRYPTO_malloc + RMALLOC_STACK.        (* [comment removed for export] *)
Definition CZALLOC_STACK : Z := FR_CRYPTO_zalloc + CMALLOC_STACK.         (* [comment removed for export] *)
Definition CFREE_STACK : Z := 16 + RFREE_STACK.
Definition CMEMDUP_STACK : Z := FR_CRYPTO_memdup + CMALLOC_STACK.
Definition CSTRNDUP_STACK : Z := FR_CRYPTO_strndup + CMALLOC_STACK.
Definition CARRAY_STACK : Z := FR_CRYPTO_array + CZALLOC_STACK.           (* [comment removed for export] *)
Definition CREALLOC_STACK : Z := FR_CRYPTO_realloc + RREALLOC_STACK.
Definition CREALLOC_ARRAY_STACK : Z := FR_CRYPTO_array + CREALLOC_STACK.

(* [comment removed for export] *)
Definition MEMFLAG (m : mem) (v : Z) : Prop :=
  exists fb : byte, rw_cells rsegs m A_mem_inited [C1 fb] /\ bv_unsigned fb = v /\ (v = 0 \/ v = 1).
Definition memflag_foot : list (Z * Z) := [(A_mem_inited, A_mem_inited + 1)].

(* [comment removed for export] *)
Fixpoint strnlen (bs : list byte) : nat :=
  match bs with [] => 0 | b :: bs' => if (bv_unsigned b =? 0)%Z then 0 else S (strnlen bs') end.
Lemma strnlen_le : forall bs, (strnlen bs <= length bs)%nat.
Proof. induction bs as [|b bs IH]; cbn; [lia|]. destruct (bv_unsigned b =? 0); cbn; lia. Qed.

Section W.
  Variable H : hsr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (n lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) junk (p : bptr) (s' : PState),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ xpres LB (bv_unsigned sp) memflag_foot m m'
      /\ rblock_range A n /\ hs_RHEAP H s' ((p, A, n) :: LB) m'
      /\ rw_cells rsegs m' A [CB (Z.to_nat n) junk]
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'.

  Definition cmalloc_stmt_at (entry stack : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (n v lo B : Z) (errv : word),
      a0 = Z_to_bv 64 n -> 1 <= n < 2^32 ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + n <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> lb_big LB + big1 n <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      hs_SR H (cmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)) mo).
  Definition cmalloc_stmt : Prop := cmalloc_stmt_at P_CRYPTO_malloc CMALLOC_STACK.
  (* [comment removed for export] *)
  Definition cmalloc_array_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (num size v lo B : Z) (errv : word),
      a0 = Z_to_bv 64 num -> a1 = Z_to_bv 64 size -> 0 <= num < 2^32 -> 0 <= size < 2^32 -> 1 <= num * size < 2^32 ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + num * size <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> lb_big LB + big1 (num * size) <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - CARRAY_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      hs_SR H (cmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (num * size) lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_malloc_array) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  Definition cmalloc0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).
  Definition cmalloc0_stmt_at (entry fr : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - fr -> mem_inv rsegs m -> IMPL_mem m -> GOT_mem m ->
      evt rsegs (cmalloc0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).
  Definition cmalloc0_stmt : Prop := cmalloc0_stmt_at P_CRYPTO_malloc FR_CRYPTO_malloc.
  Definition cmalloc_array0_stmt : Prop := cmalloc0_stmt_at P_CRYPTO_malloc_array (FR_CRYPTO_array + FR_CRYPTO_malloc).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition czalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (n lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : PState),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ xpres LB (bv_unsigned sp) memflag_foot m m'
      /\ rblock_range A n /\ hs_RHEAP H s' ((p, A, n) :: LB) m'
      /\ rw_cells rsegs m' A [CB (Z.to_nat n) (zeros (Z.to_nat n))]
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'.
  Definition czalloc_stmt_gen (entry stack : Z) (arr : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (num size v lo B : Z) (errv : word),
      a0 = Z_to_bv 64 num -> (if arr then a1 = Z_to_bv 64 size /\ 0 <= num < 2^32 /\ 0 <= size < 2^32 else size = 1) ->
      1 <= num * size < 2^32 ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + num * size <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> lb_big LB + big1 (num * size) <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      hs_SR H (czalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (num * size) lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)) mo).
  Definition czalloc_stmt : Prop := czalloc_stmt_gen P_CRYPTO_zalloc CZALLOC_STACK false.
  Definition ccalloc_stmt : Prop := czalloc_stmt_gen P_CRYPTO_calloc CARRAY_STACK true.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : PState),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv] /\ hs_rauxv_ok H m' B
      /\ xpres (hs_lb_remove H p LB) (bv_unsigned sp) [] m m'
      /\ hs_RHEAP H s' (hs_lb_remove H p LB) m'
      /\ IMPL_mem m' /\ GOT_mem m'.
  Definition cfree_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
      a0 = Z_to_bv 64 A -> hs_RHEAP H s LB m -> hs_KREL H s mo -> In (p, A, n) LB ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - CFREE_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      IMPL_mem m -> GOT_mem m ->
      hs_SR H (cfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs)) mo).

  Definition cfree_null_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ cfg_model c = mo
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ IMPL_mem m' /\ GOT_mem m'.
  Definition cfree_null_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z),
      m_halted mo = None -> m_vm_lazy mo = [] ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m -> IMPL_mem m -> GOT_mem m ->
      hs_SR H (cfree_null_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  Definition cfree_null_evt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m -> IMPL_mem m -> GOT_mem m ->
      evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom rsegs)
                   /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                   /\ IMPL_mem m' /\ GOT_mem m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cmemdup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (bs : list byte) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : PState),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ xpres LB (bv_unsigned sp) memflag_foot m m'
      /\ rblock_range A (zlength bs) /\ hs_RHEAP H s' ((p, A, zlength bs) :: LB) m'
      /\ rw_cells rsegs m' A [CB (length bs) bs]
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'.
  Definition cmemdup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (D v lo B : Z) (bs : list byte) (errv : word),
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength bs) -> 1 <= zlength bs < 0x7ffffffc ->
      bytes_at rsegs m D bs -> xclient_range LB (bv_unsigned sp) memflag_foot D (zlength bs) ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + zlength bs <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> lb_big LB + big1 (zlength bs) <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - CMEMDUP_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      hs_SR H (cmemdup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB bs lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_memdup) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cstrndup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (bs : list byte) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : PState),
      let k := strnlen bs in
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ xpres LB (bv_unsigned sp) memflag_foot m m'
      /\ rblock_range A (Z.of_nat k + 1) /\ hs_RHEAP H s' ((p, A, Z.of_nat k + 1) :: LB) m'
      /\ rw_cells rsegs m' A [CB k (firstn k bs); C1 (b8 0)]
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'.
  Definition cstrndup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (S v lo B : Z) (bs : list byte) (errv : word),
      a0 = Z_to_bv 64 S -> 0 < S < 2^64 -> a1 = Z_to_bv 64 (zlength bs) -> zlength bs < 2^31 ->
      bytes_at rsegs m S bs -> xclient_range LB (bv_unsigned sp) memflag_foot S (zlength bs) ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + (zlength bs + 1) <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> lb_big LB + big1 (zlength bs + 1) <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - CSTRNDUP_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      hs_SR H (cstrndup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB bs lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_strndup) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition crealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (p : bptr) (old n : Z) (obs : list byte) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A' : Z) junk (p' : bptr) (s' : PState),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ xpres (hs_lb_remove H p LB) (bv_unsigned sp) [] m m'
      /\ rblock_range A' n /\ hs_RHEAP H s' ((p', A', n) :: hs_lb_remove H p LB) m'
      /\ rw_cells rsegs m' A' [CB (Z.to_nat (Z.min old n)) (firstn (Z.to_nat (Z.min old n)) obs); CB (Z.to_nat (n - Z.min old n)) junk]
      /\ IMPL_mem m' /\ GOT_mem m'.
  Definition crealloc_stmt_gen (entry stack : Z) (arr : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (p : bptr)
           (A old num size lo B : Z) (obs : list byte) (errv : word),
      a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 num ->
      (if arr then a2 = Z_to_bv 64 size /\ 0 <= num < 2^32 /\ 0 <= size < 2^32 else size = 1) ->
      1 <= num * size < RMMAP_THRESHOLD ->
      hs_RHEAP H s LB m -> hs_KREL H s mo -> In (p, A, old) LB -> bytes_at rsegs m A obs -> zlength obs = old ->
      lb_bytes LB + num * size <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> lb_big LB + big1 (num * size) <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      IMPL_mem m -> GOT_mem m ->
      hs_SR H (crealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p old (num * size) obs lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)) mo).
  Definition crealloc_stmt : Prop := crealloc_stmt_gen P_CRYPTO_realloc CREALLOC_STACK false.
  Definition crealloc_array_stmt : Prop := crealloc_stmt_gen P_CRYPTO_realloc_array CREALLOC_ARRAY_STACK true.

  (* [comment removed for export] *)
  Definition C1_stmts : Prop :=
    cmalloc_stmt /\ cmalloc_array_stmt /\ cmalloc0_stmt /\ cmalloc_array0_stmt /\ czalloc_stmt /\ ccalloc_stmt
    /\ cfree_stmt /\ cfree_null_stmt /\ cmemdup_stmt /\ cstrndup_stmt /\ crealloc_stmt /\ crealloc_array_stmt.
End W.

End HCW.
