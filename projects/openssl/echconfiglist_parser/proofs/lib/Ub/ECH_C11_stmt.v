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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState ECH_C1_stmt ECH_C2_stmt ECH_C4_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition HPKE_KEM_IDS : list Z := [16; 17; 18; 32; 33].
Definition HPKE_KDF_IDS : list Z := [1; 2; 3].
Definition HPKE_AEAD_IDS : list Z := [1; 2; 3; 65535].
Definition HPKE_KEM_ROW : Z := 72.  Definition HPKE_KDF_ROW : Z := 24.  Definition HPKE_AEAD_ROW : Z := 40.
Definition ERR_LIB_PROV : Z := 57.
Definition PROV_R_INVALID_CURVE : Z := 176.  Definition PROV_R_INVALID_KDF : Z := 232.  Definition PROV_R_INVALID_AEAD : Z := 231.

(* [comment removed for export] *)
Fixpoint id_rows (m : mem) (a stride : Z) (ids : list Z) : Prop :=
  match ids with [] => True | x :: ids' => rw_cells usegs m a [C2 (wz x)] /\ id_rows m (a + stride) stride ids' end.
Definition HPKE_tabs (m : mem) : Prop :=
  id_rows m A_hpke_kem_tab HPKE_KEM_ROW HPKE_KEM_IDS /\ id_rows m A_hpke_kdf_tab HPKE_KDF_ROW HPKE_KDF_IDS
  /\ id_rows m A_hpke_aead_tab HPKE_AEAD_ROW HPKE_AEAD_IDS.
Fixpoint find_id (ids : list Z) (id : Z) : option nat :=
  match ids with [] => None | x :: ids' => if x =? id then Some 0%nat else option_map S (find_id ids' id) end.

(* [comment removed for export] *)
Record finder := mkF { f_entry : Z; f_tab : Z; f_stride : Z; f_ids : list Z; f_frame : Z; f_reason : Z; f_line : Z -> Z }.
Definition KEM_finder : finder := mkF P_ossl_HPKE_KEM_INFO_find_id A_hpke_kem_tab HPKE_KEM_ROW HPKE_KEM_IDS
                                      FR_ossl_HPKE_KEM_INFO_find_id PROV_R_INVALID_CURVE (fun id => if id =? 0 then 181 else 188).
Definition KDF_finder : finder := mkF P_ossl_HPKE_KDF_INFO_find_id A_hpke_kdf_tab HPKE_KDF_ROW HPKE_KDF_IDS
                                      FR_ossl_HPKE_KDF_INFO_find_id PROV_R_INVALID_KDF (fun _ => 210).
Definition AEAD_finder : finder := mkF P_ossl_HPKE_AEAD_INFO_find_id A_hpke_aead_tab HPKE_AEAD_ROW HPKE_AEAD_IDS
                                       FR_ossl_HPKE_AEAD_INFO_find_id PROV_R_INVALID_AEAD (fun _ => 232).

Section W.
  Variable H : hsr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hfind_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ HPKE_tabs m'.
  Definition hfind_found_stmt (f : finder) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (id lo : Z) (i : nat),
      a0 = Z_to_bv 64 id -> 0 <= id < 2^16 -> find_id (f_ids f) id = Some i -> HPKE_tabs m ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - f_frame f -> mem_inv usegs m -> bv_unsigned ra mod 2 = 0 ->
      evt usegs (hfind_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f_tab f + f_stride f * Z.of_nat i) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (f_entry f)) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition hfind_fail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (ph : errphase) (E : errst) (x : ctxinfo) (reason line lo B : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LBN : list block) (c : errchain)
                    (p1 p2 : bptr) (A1 n1 A2 n2 : Z),
      let E' := errst_raise E A1 p1 n1 line A2 p2 n2 ERR_LIB_PROV reason in
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ hs_MPRES H mo (cfg_model k) /\ c4_frame H sp tp s' (blocks_ERRST E' ++ LBN ++ LB) lo B m' k
      /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
      /\ errph_delta ph LBN c /\ raise_sizes A1 n1 A2 n2
      /\ ERRPH (LBN ++ LB) m' (ErrReady c) /\ CTXPH (LBN ++ LB) m' (CtxReady x)
      /\ ERRST (blocks_ERRST E') m' (blk_addr (ec_es c)) E'
      /\ HPKE_tabs m'
      /\ xpres LB (bv_unsigned sp) (ERR_X ++ memflag_foot ++ errph_foot ph) m m'.
  Definition hfind_fail_stmt (f : finder) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
           (ph : errphase) (E : errst) (x : ctxinfo) (id lo B : Z) (errv : word),
      a0 = Z_to_bv 64 id -> 0 <= id < 2^16 -> find_id (f_ids f) id = None -> HPKE_tabs m ->
      hs_RHEAP H s (blocks_ERRST E ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (blocks_ERRST E ++ LB) + raise_bytes ph <= hs_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + raise_cnt ph <= hs_LIVE_CNT_MAX H ->
      lb_big (blocks_ERRST E ++ LB) + errph_big ph <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - (f_frame f + RAISE_STACK ph) ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> relro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph lo -> CTXPH LB m (CtxReady x) -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (hfind_fail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB ph E x (f_reason f) (f_line f id) lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (f_entry f)) fc None m (seg_rom usegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition suite_word (kem kdf aead hi : Z) : Z := kem + kdf * 2^16 + aead * 2^32 + hi * 2^48.
  (* [comment removed for export] *)
  Definition suite_fail (kem kdf aead : Z) : option (Z * Z) :=
    match find_id HPKE_KEM_IDS kem with
    | None => Some (PROV_R_INVALID_CURVE, f_line KEM_finder kem)
    | Some _ => match find_id HPKE_KDF_IDS kdf with
                | None => Some (PROV_R_INVALID_KDF, 210)
                | Some _ => match find_id HPKE_AEAD_IDS aead with None => Some (PROV_R_INVALID_AEAD, 232) | Some _ => None end
                end
    end.
  Definition SUITECHECK_STACK (ph : errphase) : Z := FR_hpke_suite_check + FR_ossl_HPKE_KEM_INFO_find_id + RAISE_STACK ph.
  Definition SUITECHECK_OK_STACK : Z := FR_hpke_suite_check + FR_ossl_HPKE_KEM_INFO_find_id.

  Definition suiteok_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (kem kdf aead hi lo : Z),
      a0 = Z_to_bv 64 (suite_word kem kdf aead hi) -> 0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= hi < 2^16 ->
      suite_fail kem kdf aead = None -> HPKE_tabs m ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - SUITECHECK_OK_STACK -> mem_inv usegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt usegs (hfind_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom usegs)).
  Definition suitebad_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
           (ph : errphase) (E : errst) (x : ctxinfo) (kem kdf aead hi reason line lo B : Z) (errv : word),
      a0 = Z_to_bv 64 (suite_word kem kdf aead hi) -> 0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= hi < 2^16 ->
      suite_fail kem kdf aead = Some (reason, line) -> HPKE_tabs m ->
      hs_RHEAP H s (blocks_ERRST E ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (blocks_ERRST E ++ LB) + raise_bytes ph <= hs_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + raise_cnt ph <= hs_LIVE_CNT_MAX H ->
      lb_big (blocks_ERRST E ++ LB) + errph_big ph <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - SUITECHECK_STACK ph ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> relro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph lo -> CTXPH LB m (CtxReady x) -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (hfind_fail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB ph E x reason line lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom usegs)) mo).

  Definition C11_stmts : Prop :=
    hfind_found_stmt KEM_finder /\ hfind_fail_stmt KEM_finder /\ hfind_found_stmt KDF_finder /\ hfind_fail_stmt KDF_finder
    /\ hfind_found_stmt AEAD_finder /\ hfind_fail_stmt AEAD_finder /\ suiteok_stmt /\ suitebad_stmt.
End W.
End HCW.
