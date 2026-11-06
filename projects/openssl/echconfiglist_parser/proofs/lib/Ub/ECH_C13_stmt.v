(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState ECH_C1_stmt ECH_C5_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition EXTFREE_STACK : Z := FR_ossl_echext_free + CFREE_STACK.
Definition ENTRYFREE_STACK : Z := FR_ossl_echstore_entry_free + Z.max (SKPOPFREE_STACK EXTFREE_STACK) (Z.max CFREE_STACK FR_EVP_PKEY_free).
Definition STORENEW_STACK : Z := FR_OSSL_ECHSTORE_new + CZALLOC_STACK.
Definition STOREFREE_STACK : Z := FR_OSSL_ECHSTORE_free + Z.max (SKPOPFREE_STACK ENTRYFREE_STACK) CFREE_STACK.

Section W.
  Variable H : hsr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition storenew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : PState),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ xpres LB (bv_unsigned sp) memflag_foot m m'
      /\ rblock_range A STORE_SIZE /\ hs_RHEAP H s' ((p, A, STORE_SIZE) :: LB) m'
      /\ STOREobj ((p, A, STORE_SIZE) :: LB) m' A (store_empty p)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'.
  Definition storenew_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (v lo B : Z) (errv : word),
      a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 0 ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + STORE_SIZE <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> lb_big LB <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - STORENEW_STACK ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (storenew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OSSL_ECHSTORE_new) fc None m (seg_rom usegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition extfree_stmt : Prop := efree_stmt_at H extrep EXTobj blocks_EXT GOT_echfree P_ossl_echext_free EXTFREE_STACK.
  Definition entryfree_stmt : Prop := efree_stmt_at H entrep ENTRYobj blocks_ENTRY GOT_echfree P_ossl_echstore_entry_free ENTRYFREE_STACK.
  Definition storefree_stmt : Prop := efree_stmt_at H storerep STOREobj blocks_STORE GOT_echfree P_OSSL_ECHSTORE_free STOREFREE_STACK.
  (* [comment removed for export] *)
  Definition popfree_exts_stmt : Prop := skpopfree_stmt_gen H extrep EXTobj blocks_EXT GOT_echfree P_ossl_echext_free EXTFREE_STACK.
  Definition popfree_entries_stmt : Prop := skpopfree_stmt_gen H entrep ENTRYobj blocks_ENTRY GOT_echfree P_ossl_echstore_entry_free ENTRYFREE_STACK.
  (* [comment removed for export] *)
  Definition EXTobj_frame : Prop := EP_frame extrep EXTobj blocks_EXT.
  Definition ENTRYobj_frame : Prop := EP_frame entrep ENTRYobj blocks_ENTRY.

  (* [comment removed for export] *)
  Definition nullret_stmt_at (entry fr : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - fr -> lo <= bv_unsigned sp - 32 ->   (* [comment removed for export] *)
      mem_inv usegs m -> bv_unsigned ra mod 2 = 0 ->
      evt usegs (sknull_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom usegs)).
  Definition entryfree_null_stmt : Prop := nullret_stmt_at P_ossl_echstore_entry_free 0.
  Definition extfree_null_stmt : Prop := nullret_stmt_at P_ossl_echext_free 0.
  Definition pkeyfree_null_stmt : Prop := nullret_stmt_at P_EVP_PKEY_free FR_EVP_PKEY_free.

  (* [comment removed for export] *)
  Definition thunk_stmt_at (th : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (f e lo : Z),
      a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 e -> 0 <= f < 2^64 -> f mod 2 = 0 ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FR_sk_freefunc_thunk -> mem_inv usegs m ->
      evt usegs (fun ms' => exists t1' m',
                   ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 f) fc None m' (seg_rom usegs)
                   /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 th) fc None m (seg_rom usegs)).
  Definition thunk_ext_stmt : Prop := thunk_stmt_at P_sk_OSSL_ECHEXT_freefunc_thunk.
  Definition thunk_entry_stmt : Prop := thunk_stmt_at P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk.
  Definition thunk_xbuf_stmt : Prop := thunk_stmt_at P_sk_X509_BUFFER_freefunc_thunk.

  Definition C13_stmts : Prop :=
    storenew_stmt /\ extfree_stmt /\ entryfree_stmt /\ storefree_stmt /\ popfree_exts_stmt /\ popfree_entries_stmt
    /\ EXTobj_frame /\ ENTRYobj_frame /\ entryfree_null_stmt /\ pkeyfree_null_stmt
    /\ thunk_ext_stmt /\ thunk_entry_stmt /\ thunk_xbuf_stmt.
End W.
End HCW.
