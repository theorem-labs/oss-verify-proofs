(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1 ECH_AStmt_C5.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
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

(* [comment removed for export] *)
Definition R_ossl_echext_free_CRYPTO_free : Z := 0x552658.
Definition R_ossl_echstore_entry_free_CRYPTO_free : Z := 0x552704.      (* [comment removed for export] *)
Definition R_ossl_echstore_entry_free_CRYPTO_free_2 : Z := 0x552730.    (* [comment removed for export] *)
Definition R_ossl_echstore_entry_free_EVP_PKEY_free : Z := 0x552750.
Definition R_ossl_echstore_entry_free_CRYPTO_free_3 : Z := 0x55277c.    (* [comment removed for export] *)
Definition R_ossl_echstore_entry_free_CRYPTO_free_4 : Z := 0x5527a8.    (* [comment removed for export] *)
Definition R_ossl_echstore_entry_free_sk_set_thunks : Z := 0x5527d0.
Definition R_ossl_echstore_entry_free_sk_pop_free : Z := 0x5527e0.
Definition R_OSSL_ECHSTORE_free_sk_set_thunks : Z := 0x5529b4.
Definition R_OSSL_ECHSTORE_free_sk_pop_free : Z := 0x5529c4.
Definition R_OSSL_ECHSTORE_free_CRYPTO_free : Z := 0x5529f4.           (* [comment removed for export] *)
Definition R_OSSL_ECHSTORE_new_CRYPTO_zalloc : Z := 0x5528a4.
Definition R_OSSL_ECHSTORE_new_CRYPTO_strdup : Z := 0x5528e8.           (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PF_extfree : list (Z * list Z) := pf_shift R_ossl_echext_free_CRYPTO_free PF_cfree ++ PF_cfree.
Definition PF_entryfree : list (Z * list Z) :=
  pf_shift R_ossl_echstore_entry_free_CRYPTO_free PF_cfree ++ pf_shift R_ossl_echstore_entry_free_CRYPTO_free_2 PF_cfree
  ++ pf_shift R_ossl_echstore_entry_free_CRYPTO_free_3 PF_cfree ++ pf_shift R_ossl_echstore_entry_free_CRYPTO_free_4 PF_cfree
  ++ pf_shift R_ossl_echstore_entry_free_sk_pop_free (PF_skpopfree PF_extfree) ++ PF_cfree.
Definition PF_storefree : list (Z * list Z) :=
  pf_shift R_OSSL_ECHSTORE_free_sk_pop_free (PF_skpopfree PF_entryfree) ++ pf_shift R_OSSL_ECHSTORE_free_CRYPTO_free PF_cfree ++ PF_cfree.
Definition PF_storenew : list (Z * list Z) := pf_shift R_OSSL_ECHSTORE_new_CRYPTO_zalloc PF_czalloc.

(* [comment removed for export] *)
Definition oshad (m : mem) (P : Z) (o : oblk) : Prop :=
  match o with
  | None => True
  | Some (id, n) => P + n <= AAPP_HI /\ addressable m P n /\ exists bs, rw_cells asegs m P [CB (Z.to_nat n) bs]
  end.
Definition EXT_shad (m : mem) (a : Z) (X : extrep) : Prop := a + EXT_SIZE <= AAPP_HI /\ addressable m a EXT_SIZE /\ oshad m (ex_val X) (ex_val_o X).
(* [comment removed for export] *)
Definition SKX_shad (m : mem) (P : Z) (K : skrep) : Prop :=
  SK_shad m P K /\ P + SK_SIZE <= AAPP_HI /\ (sk_cap K <> 0 -> sk_data K + 8 * sk_cap K <= AAPP_HI).
Definition EXTS_shad (m : mem) (P : Z) (xs : option (skrep * list extrep)) : Prop :=
  match xs with
  | None => True
  | Some (K, es) => SKX_shad m P K /\ Forall2 (fun p X => EXT_shad m p X) (sk_elems K) es
  end.
Definition ENTRY_shad (m : mem) (a : Z) (E : entrep) : Prop :=
  a + ENTRY_SIZE <= AAPP_HI /\ addressable m a ENTRY_SIZE
  /\ oshad m (en_pname E) (en_pname_o E) /\ oshad m (en_pub E) (en_pub_o E)
  /\ oshad m (en_suites E) (en_suites_o E) /\ oshad m (en_encoded E) (en_encoded_o E)
  /\ EXTS_shad m (en_exts E) (en_exts_o E).
Definition ENTRIES_shad (m : mem) (P : Z) (xs : option (skrep * list entrep)) : Prop :=
  match xs with
  | None => True
  | Some (K, es) => SKX_shad m P K /\ Forall2 (fun p E => ENTRY_shad m p E) (sk_elems K) es
  end.
Definition STORE_shad (m : mem) (a : Z) (S : storerep) : Prop :=
  a + STORE_SIZE <= AAPP_HI /\ addressable m a STORE_SIZE /\ ENTRIES_shad m (es_entries S) (es_entries_o S).

Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition ocost (o : oblk) : Z := match o with None => as_Cf H 0 | Some (_, n) => as_Cf H (Z.max n 0) end.
  Definition ext_cost (X : extrep) : Z := ocost (ex_val_o X) + as_Cf H EXT_SIZE.
  Definition exts_cost (xs : option (skrep * list extrep)) : Z :=
    match xs with
    | None => 0                                                          (* [comment removed for export] *)
    | Some (K, es) => ecost_sum extrep ext_cost es + as_Cf H (Z.max (8 * sk_cap K) 0) + as_Cf H SK_SIZE
    end.                                                    (* [comment removed for export] *)
  Definition entry_cost (E : entrep) : Z :=
    ocost (en_pname_o E) + ocost (en_pub_o E) + ocost (en_encoded_o E) + ocost (en_suites_o E) + exts_cost (en_exts_o E) + as_Cf H ENTRY_SIZE.
  Definition entries_cost (xs : option (skrep * list entrep)) : Z :=
    match xs with
    | None => 0
    | Some (K, es) => ecost_sum entrep entry_cost es + as_Cf H (Z.max (8 * sk_cap K) 0) + as_Cf H SK_SIZE
    end.
  Definition store_cost (S : storerep) : Z := entries_cost (es_entries_o S) + as_Cf H 0 + as_Cf H STORE_SIZE.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition storenew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) memflag_foot m m'
      /\ ablock_range H A STORE_SIZE /\ as_RHEAP H s' ((p, A, STORE_SIZE) :: LB) m'
      /\ STOREobj ((p, A, STORE_SIZE) :: LB) m' A (store_empty p) /\ STORE_shad m' A (store_empty p)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cm H STORE_SIZE.
  Definition storenew_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (v lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_OSSL_ECHSTORE_new) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 0 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + STORE_SIZE <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - STORENEW_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_storenew (bv_unsigned ra) CH ->
      as_Cm H STORE_SIZE <= as_AL H s ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      as_SR H (storenew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition extfree_stmt : Prop := efree_stmt_at H extrep EXTobj blocks_EXT GOT_echfree PF_extfree ext_cost EXT_shad P_ossl_echext_free EXTFREE_STACK.
  Definition entryfree_stmt : Prop := efree_stmt_at H entrep ENTRYobj blocks_ENTRY GOT_echfree PF_entryfree entry_cost ENTRY_shad P_ossl_echstore_entry_free ENTRYFREE_STACK.
  Definition storefree_stmt : Prop := efree_stmt_at H storerep STOREobj blocks_STORE GOT_echfree PF_storefree store_cost STORE_shad P_OSSL_ECHSTORE_free STOREFREE_STACK.
  (* [comment removed for export] *)
  Definition popfree_exts_stmt : Prop := skpopfree_stmt_gen H extrep EXTobj blocks_EXT GOT_echfree PF_extfree ext_cost EXT_shad P_ossl_echext_free EXTFREE_STACK.
  Definition popfree_entries_stmt : Prop := skpopfree_stmt_gen H entrep ENTRYobj blocks_ENTRY GOT_echfree PF_entryfree entry_cost ENTRY_shad P_ossl_echstore_entry_free ENTRYFREE_STACK.
  (* [comment removed for export] *)
  Definition EXTobj_frame : Prop := EP_frame H extrep EXTobj blocks_EXT.
  Definition ENTRYobj_frame : Prop := EP_frame H entrep ENTRYobj blocks_ENTRY.
  Definition EXT_shad_frame : Prop := eshad_frame H extrep blocks_EXT EXT_shad.
  Definition ENTRY_shad_frame : Prop := eshad_frame H entrep blocks_ENTRY ENTRY_shad.

  (* [comment removed for export] *)
  Definition entryfree_null_stmt : Prop := sknull_stmt_at P_ossl_echstore_entry_free FR_ossl_echstore_entry_free (Z_to_bv 64 0).
  Definition extfree_null_stmt : Prop := sknull_stmt_at P_ossl_echext_free FR_ossl_echext_free (Z_to_bv 64 0).
  Definition pkeyfree_null_stmt : Prop := sknull_stmt_at P_EVP_PKEY_free FR_EVP_PKEY_free (Z_to_bv 64 0).

  (* [comment removed for export] *)
  Definition thunk_stmt_at (th : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (f e lo : Z),
      a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 e -> 0 <= f < 2^64 -> f mod 2 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - FR_sk_freefunc_thunk -> mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists t1' m',
                   ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 f) fc None m' (seg_rom asegs)
                   /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 th) fc None m (seg_rom asegs)).
  Definition thunk_ext_stmt : Prop := thunk_stmt_at P_sk_OSSL_ECHEXT_freefunc_thunk.
  Definition thunk_entry_stmt : Prop := thunk_stmt_at P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk.
  Definition thunk_xbuf_stmt : Prop := thunk_stmt_at P_sk_X509_BUFFER_freefunc_thunk.

  Definition C13_stmts : Prop :=
    storenew_stmt /\ extfree_stmt /\ entryfree_stmt /\ storefree_stmt /\ popfree_exts_stmt /\ popfree_entries_stmt
    /\ EXTobj_frame /\ ENTRYobj_frame /\ EXT_shad_frame /\ ENTRY_shad_frame /\ entryfree_null_stmt /\ pkeyfree_null_stmt
    /\ thunk_ext_stmt /\ thunk_entry_stmt /\ thunk_xbuf_stmt.
End W.
End HCW.
