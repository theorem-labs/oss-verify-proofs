(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition FR_sk_new_null : Z := 32.  Definition FR_sk_new : Z := 32.   Definition FR_sk_insert : Z := 112.   (* [comment removed for export] *)
Definition FR_sk_reserve : Z := 80.   Definition FR_sk_pop_free : Z := 112. Definition FR_sk_free : Z := 32.   (* [comment removed for export] *)
Definition SKNEW_STACK : Z := FR_sk_new + CZALLOC_STACK.
Definition SKRESERVE_STACK : Z := FR_sk_reserve + Z.max CARRAY_STACK CREALLOC_ARRAY_STACK.
Definition SKPUSH_STACK : Z := 16 + FR_sk_insert + SKRESERVE_STACK.
Definition SKFREE_STACK : Z := FR_sk_free + CFREE_STACK.

(* [comment removed for export] *)
Definition C1env (m : mem) (v : Z) : Prop := MEMFLAG m v /\ IMPL_mem m /\ GOT_mem m.
(* [comment removed for export] *)
Definition SK_shad (m : mem) (a : Z) (K : skrep) : Prop :=
  addressable m a SK_SIZE /\ (sk_cap K <> 0 -> addressable m (sk_data K) (8 * sk_cap K)).
(* [comment removed for export] *)
Definition PF_sknew_null : list (Z * list Z) := pf_shift R_sk_new_null_CRYPTO_zalloc PF_czalloc.
Definition PF_sknew : list (Z * list Z) := pf_shift R_sk_new_CRYPTO_zalloc PF_czalloc.
Definition PF_skreserve : list (Z * list Z) := pf_shift R_sk_reserve_CRYPTO_calloc PF_czalloc ++ pf_shift R_sk_reserve_CRYPTO_realloc_array PF_crealloc.
Definition PF_skpush : list (Z * list Z) := pf_shift R_sk_insert_sk_reserve PF_skreserve.      (* [comment removed for export] *)
Definition PF_skfree : list (Z * list Z) := pf_shift R_sk_free_CRYPTO_free PF_cfree ++ PF_cfree.  (* [comment removed for export] *)
Definition PF_skpopfree (PFe : list (Z * list Z)) : list (Z * list Z) :=
  pf_shift R_sk_pop_free_freefunc PFe ++ pf_shift R_sk_pop_free_freefunc_2 PFe ++ PF_skfree.

(* [comment removed for export] *)
Definition SK_below (a : Z) (K : skrep) (lo : Z) : Prop :=
  a + SK_SIZE <= lo /\ (sk_cap K = 0 \/ sk_data K + 8 * sk_cap K <= lo).

(* [comment removed for export] *)
Definition ASK_foot (a : Z) (K : skrep) : list (Z * Z) :=
  SK_foot a K ++ (if sk_cap K =? 0 then [] else [(sh (sk_data K), sh (sk_data K) + nsh (8 * sk_cap K))]).

(* [comment removed for export] *)
Definition SKPUSH_COST (K : skrep) : Z := 8 * sk_grow (sk_cap K) + 32.
(* [comment removed for export] *)
Definition SK_CAP_MAX : Z := 1024.     (* [comment removed for export] *)

Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition SK_ranges (a : Z) (K : skrep) : Prop :=
    ablock_range H a SK_SIZE /\ (sk_cap K <> 0 -> ablock_range H (sk_data K) (8 * sk_cap K)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition sknew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (c lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (id did : bptr) (s' : as_St H),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) memflag_foot m m'
      /\ 0 < A /\ as_RHEAP H s' ((id, A, SK_SIZE) :: LB) m'
      /\ SKobj ((id, A, SK_SIZE) :: LB) m' A (sk_fresh c id did) /\ SK_shad m' A (sk_fresh c id did)
      /\ C1env m' 1
      /\ as_AL H s' >= as_AL H s - as_Cm H SK_SIZE.
  Definition sknew_stmt_gen (entry stack : Z) (withcmp : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (c v lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      (if withcmp then a0 = Z_to_bv 64 c /\ 0 <= c < 2^64 else c = 0) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + SK_SIZE <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) (if withcmp then PF_sknew else PF_sknew_null) (bv_unsigned ra) CH -> as_Cm H SK_SIZE <= as_AL H s ->
      C1env m v ->
      as_SR H (sknew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB c lo B m mo) (mkCfg msF mo).
  Definition sknew_null_stmt : Prop := sknew_stmt_gen P_OPENSSL_sk_new_null (FR_sk_new_null + CZALLOC_STACK) false.
  Definition sknew_stmt : Prop := sknew_stmt_gen P_OPENSSL_sk_new SKNEW_STACK true.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition sk_with_thunk (K : skrep) (which : Z) (f : Z) : skrep :=
    mkSK (sk_elems K) (sk_data K) (sk_cap K) (sk_sorted K) (sk_comp K)
         (if which =? O_SK_CMPTH then f else sk_cmp_thunk K)
         (if which =? O_SK_FREETH then f else sk_free_thunk K)
         (if which =? O_SK_COPYTH then f else sk_copy_thunk K) (sk_id K) (sk_did K).
  Definition skset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0 : word) (LB : list block) (a : Z) (K' : skrep) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (a, a + SK_SIZE)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ SKobj LB m' a K'.
  Definition skset_stmt_at (entry which : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a f lo : Z) (K : skrep),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 f -> 0 <= f < 2^64 -> SKobj LB m a K -> SK_below a K lo -> SK_shad m a K -> SK_ranges a K -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m ->
      evt asegs (skset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 LB a (sk_with_thunk K which f) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition skset_thunks_stmt : Prop := skset_stmt_at P_OPENSSL_sk_set_thunks O_SK_FREETH.
  Definition skset_cmp_thunks_stmt : Prop := skset_stmt_at P_OPENSSL_sk_set_cmp_thunks O_SK_CMPTH.
  Definition skset_copy_thunks_stmt : Prop := skset_stmt_at P_OPENSSL_sk_set_copy_thunks O_SK_COPYTH.
  (* [comment removed for export] *)
  Definition sknull_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv : word) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp).
  (* [comment removed for export] *)
  Definition sknull_stmt_at (entry fr : Z) (rv : word) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - fr -> mem_inv asegs m -> ACONST m ->
      evt asegs (sknull_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rv lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition skset_thunks_null_stmt : Prop := sknull_stmt_at P_OPENSSL_sk_set_thunks 16 (Z_to_bv 64 0).
  Definition sk_free_null_stmt : Prop := sknull_stmt_at P_OPENSSL_sk_free FR_sk_free (Z_to_bv 64 0).
  Definition sk_pop_free_null_stmt : Prop := sknull_stmt_at P_OPENSSL_sk_pop_free FR_sk_pop_free (Z_to_bv 64 0).
  Definition sk_num_null_stmt : Prop := sknull_stmt_at P_OPENSSL_sk_num 16 (Z_to_bv 64 (-1)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition sknum_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a lo : Z) (K : skrep),
      a0 = Z_to_bv 64 a -> SKobj LB m a K -> SK_below a K lo -> SK_shad m a K -> SK_ranges a K -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m ->
      evt asegs (sknull_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (sk_num K)) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_num) fc None m (seg_rom asegs)).
  Definition skvalue_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a i p lo : Z) (K : skrep),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 i -> 0 <= i < sk_num K -> nth_error (sk_elems K) (Z.to_nat i) = Some p ->
      SKobj LB m a K -> SK_below a K lo -> SK_shad m a K -> SK_ranges a K -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m ->
      evt asegs (sknull_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 p) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_value) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition sk_push_nocmp (K : skrep) : Prop := sk_comp K = 0 \/ sk_num K = 0 \/ sk_sorted K = 0.
  Definition sk_after_push (K : skrep) (p : Z) (data' cap' : Z) (did' : bptr) : skrep :=
    mkSK (sk_elems K ++ [p]) data' cap'
         (if (sk_sorted K =? 1) && (1 <=? sk_num K) then 0 else sk_sorted K)
         (sk_comp K) (sk_cmp_thunk K) (sk_free_thunk K) (sk_copy_thunk K) (sk_id K) did'.
  (* [comment removed for export] *)
  Definition skpush_lb (K K' : skrep) (LB LB' : list block) : Prop :=
       (sk_num K + 1 <= sk_cap K /\ sk_cap K' = sk_cap K /\ sk_data K' = sk_data K /\ sk_did K' = sk_did K /\ LB' = LB)
    \/ (sk_cap K = 0 /\ sk_cap K' = 4 /\ LB' = (sk_did K', sk_data K', 32) :: LB)
    \/ (4 <= sk_cap K /\ sk_num K = sk_cap K /\ sk_cap K' = sk_grow (sk_cap K)
        /\ Permutation ((sk_did K, sk_data K, 8 * sk_cap K) :: LB') ((sk_did K', sk_data K', 8 * sk_cap K') :: LB)).
  Definition skpush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (a p : Z) (K : skrep) (v lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block) (K' : skrep) data' cap' did',
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sk_num K + 1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ K' = sk_after_push K p data' cap' did' /\ skpush_lb K K' LB LB'
      /\ as_RHEAP H s' LB' m' /\ SKobj LB' m' a K' /\ SK_shad m' a K'
      /\ xpres H LB' (bv_unsigned sp) (memflag_foot ++ ASK_foot a K') m m'          (* [comment removed for export] *)
      /\ (exists v', C1env m' v' /\ v <= v')
      /\ as_AL H s' >= as_AL H s - as_Cm H (SKPUSH_COST K) - as_Cf H (8 * sk_cap K).           (* [comment removed for export] *)
  Definition skpush_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (a p v lo B : Z) (K : skrep) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 p -> 0 < p < 2^64 -> SKobj LB m a K -> sk_push_nocmp K -> sk_cap K <= SK_CAP_MAX ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + SKPUSH_COST K <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->

      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - SKPUSH_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_skpush (bv_unsigned ra) CH -> as_Cm H (SKPUSH_COST K) + as_Cf H (8 * sk_cap K) <= as_AL H s ->
      SK_shad m a K ->
      C1env m v ->
      as_SR H (skpush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a p K v lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  Definition sk_after_reserve (K : skrep) (data' cap' : Z) (did' : bptr) : skrep :=
    mkSK (sk_elems K) data' cap' (sk_sorted K) (sk_comp K) (sk_cmp_thunk K) (sk_free_thunk K) (sk_copy_thunk K) (sk_id K) did'.
  Definition skreserve_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (a : Z) (K : skrep) (v lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block) (K' : skrep) data' cap' did',
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ K' = sk_after_reserve K data' cap' did' /\ skpush_lb K K' LB LB' /\ sk_num K' + 1 <= sk_cap K'
      /\ as_RHEAP H s' LB' m' /\ SKobj LB' m' a K' /\ SK_shad m' a K'
      /\ xpres H LB' (bv_unsigned sp) (memflag_foot ++ ASK_foot a K') m m'          (* [comment removed for export] *)
      /\ (exists v', C1env m' v' /\ v <= v')
      /\ as_AL H s' >= as_AL H s - as_Cm H (SKPUSH_COST K) - as_Cf H (8 * sk_cap K).
  Definition skreserve_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (a v lo B : Z) (K : skrep) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_sk_reserve) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> SKobj LB m a K -> sk_cap K <= SK_CAP_MAX ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + SKPUSH_COST K <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->

      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - SKRESERVE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_skreserve (bv_unsigned ra) CH -> as_Cm H (SKPUSH_COST K) + as_Cf H (8 * sk_cap K) <= as_AL H s ->
      SK_shad m a K ->
      C1env m v ->
      as_SR H (skreserve_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a K v lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition skfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (a : Z) (K : skrep) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (LB' : list block),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
      /\ Permutation (blocks_SK a K ++ LB') LB /\ as_RHEAP H s' LB' m'
      /\ xpres H LB' (bv_unsigned sp) [] m m'
      /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cf H (8 * sk_cap K) - as_Cf H SK_SIZE.
  Definition skfree_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (a lo B : Z) (K : skrep) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_OPENSSL_sk_free) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 a -> SKobj LB m a K ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - SKFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_skfree (bv_unsigned ra) CH -> as_Cf H (8 * sk_cap K) + as_Cf H SK_SIZE <= as_AL H s ->
      SK_shad m a K ->
      IMPL_mem m -> GOT_mem m ->
      as_SR H (skfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a K lo B errv m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition is_sk_freefunc_thunk (th : Z) : Prop :=
    th = P_sk_OSSL_ECHEXT_freefunc_thunk \/ th = P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk \/ th = P_sk_X509_BUFFER_freefunc_thunk.

  Section Elem.
    Context (X : Type) (EP : list block -> mem -> Z -> X -> Prop) (blocks_E : Z -> X -> list block).
    (* [comment removed for export] *)
    Context (G : mem -> Prop).

    (* [comment removed for export] *)
    Context (PFe : list (Z * list Z)) (ecost : X -> Z) (eshad : mem -> Z -> X -> Prop).

    Definition efree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
        (s : as_St H) (LB : list block) (p : Z) (x : X) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
      fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (LB' : list block),
        as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
        /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
        /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
        /\ Permutation (blocks_E p x ++ LB') LB /\ as_RHEAP H s' LB' m'
        /\ xpres H LB' (bv_unsigned sp) [] m m'
        /\ IMPL_mem m' /\ GOT_mem m' /\ G m'
        /\ as_AL H s' >= as_AL H s - ecost x.
    Definition efree_stmt_at (FN estack : Z) : Prop :=
      forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (p lo B : Z) (x : X) (errv : word)
             (CH : list (Z * Z)),
        as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 FN) fc None m (seg_rom asegs) ->
        a0 = Z_to_bv 64 p -> EP LB m p x -> eshad m p x ->
        List.NoDup (map blk_id (blocks_E p x)) ->     (* [comment removed for export] *)
        as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
        as_rauxv_ok H m B -> bv_unsigned sp <= B ->
        stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - estack ->
        rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
        bv_unsigned sp mod 16 = 0 -> ACONST m ->
        as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PFe (bv_unsigned ra) CH -> ecost x <= as_AL H s ->
        IMPL_mem m -> GOT_mem m -> G m ->
        bv_unsigned ra mod 2 = 0 ->
        as_SR H (efree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p x lo B errv m mo) (mkCfg msF mo).
    (* [comment removed for export] *)
    Definition EP_frame : Prop :=
      forall LB LB' m m' p x (SP : Z),
        EP LB m p x -> (forall b, In b (blocks_E p x) -> In b LB') ->
        xpres H LB' SP [] m m' -> (forall b, In b (blocks_E p x) -> blk_addr b + blk_size b <= SP) ->
        EP LB' m' p x.
    Definition G_frame : Prop := forall LB (SP : Z) m m', G m -> xpres H LB SP [] m m' -> aceil <= SP -> G m'.
    (* [comment removed for export] *)
    Definition eshad_frame : Prop :=
      forall (LB' : list block) m m' p x (SP : Z),
        eshad m p x -> (forall b, In b (blocks_E p x) -> In b LB') ->
        xpres H LB' SP [] m m' -> (forall b, In b (blocks_E p x) -> blk_addr b + blk_size b <= SP) ->
        eshad m' p x.
    Definition ecost_pos : Prop := forall x, 0 <= ecost x.
    Definition ecost_sum (xs : list X) : Z := fold_right (fun x acc => ecost x + acc) 0 xs.
    (* [comment removed for export] *)
    Definition EP_owned : Prop := forall LB m p x, EP LB m p x -> forall b, In b (blocks_E p x) -> In b LB.

    Definition skpopfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
        (s : as_St H) (LB : list block) (a : Z) (K : skrep) (xs : list X) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
      fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (LB' : list block),
        as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
        /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
        /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
        /\ Permutation (blocks_SK a K ++ concat (map (fun px => blocks_E (fst px) (snd px)) (combine (sk_elems K) xs)) ++ LB') LB
        /\ as_RHEAP H s' LB' m'
        /\ xpres H LB' (bv_unsigned sp) [] m m'
        /\ IMPL_mem m' /\ GOT_mem m' /\ G m'
        /\ as_AL H s' >= as_AL H s - ecost_sum xs - as_Cf H (8 * sk_cap K) - as_Cf H SK_SIZE.
    Definition SKPOPFREE_STACK (estack : Z) : Z := FR_sk_pop_free + 16 + Z.max estack CFREE_STACK.
    Definition skpopfree_stmt_gen (FN estack : Z) : Prop :=
      efree_stmt_at FN estack -> EP_frame -> EP_owned -> G_frame -> eshad_frame -> ecost_pos -> 0 <= FN < 2^64 -> FN mod 2 = 0 ->
      forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (a lo B : Z) (K : skrep) (xs : list X) (errv : word)
             (CH : list (Z * Z)),
        as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m (seg_rom asegs) ->
        a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 FN -> SKobj LB m a K -> SK_shad m a K -> is_sk_freefunc_thunk (sk_free_thunk K) ->
        length xs = length (sk_elems K) -> Forall2 (fun p x => EP LB m p x) (sk_elems K) xs -> Forall2 (fun p x => eshad m p x) (sk_elems K) xs ->
        List.NoDup (map blk_id (blocks_SK a K ++ concat (map (fun px => blocks_E (fst px) (snd px)) (combine (sk_elems K) xs)))) ->
        as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
        as_rauxv_ok H m B -> bv_unsigned sp <= B ->
        stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - SKPOPFREE_STACK estack ->
        rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
        bv_unsigned sp mod 16 = 0 -> ACONST m ->
        as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) (PF_skpopfree PFe) (bv_unsigned ra) CH ->
        ecost_sum xs + as_Cf H (8 * sk_cap K) + as_Cf H SK_SIZE <= as_AL H s ->
        IMPL_mem m -> GOT_mem m -> G m ->
        bv_unsigned ra mod 2 = 0 ->
        as_SR H (skpopfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a K xs lo B errv m mo) (mkCfg msF mo).
  End Elem.

  Definition C5_stmts : Prop :=
    sknew_null_stmt /\ sknew_stmt /\ skset_thunks_stmt /\ skset_cmp_thunks_stmt /\ skset_copy_thunks_stmt
    /\ skset_thunks_null_stmt /\ sk_free_null_stmt /\ sk_pop_free_null_stmt /\ sk_num_null_stmt
    /\ sknum_stmt /\ skvalue_stmt /\ skpush_stmt /\ skreserve_stmt /\ skfree_stmt.
End W.

End HCW.
