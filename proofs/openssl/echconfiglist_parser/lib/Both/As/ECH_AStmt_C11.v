(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1 ECH_AStmt_C2 ECH_AStmt_C4.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
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
  match ids with [] => True | x :: ids' => rw_cells asegs m a [C2 (wz x)] /\ id_rows m (a + stride) stride ids' end.
Definition HPKE_tabs (m : mem) : Prop :=
  id_rows m A_hpke_kem_tab HPKE_KEM_ROW HPKE_KEM_IDS /\ id_rows m A_hpke_kdf_tab HPKE_KDF_ROW HPKE_KDF_IDS
  /\ id_rows m A_hpke_aead_tab HPKE_AEAD_ROW HPKE_AEAD_IDS.
Fixpoint find_id (ids : list Z) (id : Z) : option nat :=
  match ids with [] => None | x :: ids' => if x =? id then Some 0%nat else option_map S (find_id ids' id) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record finder := mkF { f_entry : Z; f_tab : Z; f_stride : Z; f_ids : list Z; f_frame : Z; f_reason : Z; f_line : Z -> Z;
                       f_ra1 : Z; f_ra2 : Z; f_ra3 : Z }.
Definition KEM_finder : finder := mkF P_ossl_HPKE_KEM_INFO_find_id A_hpke_kem_tab HPKE_KEM_ROW HPKE_KEM_IDS
                                      FR_ossl_HPKE_KEM_INFO_find_id PROV_R_INVALID_CURVE (fun id => if id =? 0 then 181 else 188)
                                      0x3e5b9c 0x3e5bb8 0x3e5bcc.
Definition KDF_finder : finder := mkF P_ossl_HPKE_KDF_INFO_find_id A_hpke_kdf_tab HPKE_KDF_ROW HPKE_KDF_IDS
                                      FR_ossl_HPKE_KDF_INFO_find_id PROV_R_INVALID_KDF (fun _ => 210)
                                      0x3e5c64 0x3e5c80 0x3e5c94.
Definition AEAD_finder : finder := mkF P_ossl_HPKE_AEAD_INFO_find_id A_hpke_aead_tab HPKE_AEAD_ROW HPKE_AEAD_IDS
                                       FR_ossl_HPKE_AEAD_INFO_find_id PROV_R_INVALID_AEAD (fun _ => 232)
                                       0x3e5d28 0x3e5d44 0x3e5d58.
(* [comment removed for export] *)
Definition PF_hfind (f : finder) (ph : errphase) : list (Z * list Z) :=
  pf_shift (f_ra1 f) (PF_errnew ph) ++ pf_shift (f_ra2 f) PF_errdebug ++ pf_shift (f_ra3 f) PF_errseterr.
(* [comment removed for export] *)
Definition R_hsc_kem : Z := 0x5554a4.  Definition R_hsc_kdf : Z := 0x5554b8.  Definition R_hsc_aead : Z := 0x5554cc.
Definition PF_suitebad (ph : errphase) : list (Z * list Z) :=
  pf_shift R_hsc_kem (PF_hfind KEM_finder ph) ++ pf_shift R_hsc_kdf (PF_hfind KDF_finder ph) ++ pf_shift R_hsc_aead (PF_hfind AEAD_finder ph).

Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hfind_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ HPKE_tabs m'.
  Definition hfind_found_stmt (f : finder) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (id lo : Z) (i : nat),
      a0 = Z_to_bv 64 id -> 0 <= id < 2^16 -> find_id (f_ids f) id = Some i -> HPKE_tabs m -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - f_frame f -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (hfind_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f_tab f + f_stride f * Z.of_nat i) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (f_entry f)) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition hfind_fail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (ph : errphase) (E : errst) (x : ctxinfo) (reason line lo B : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LBN : list block) (c : errchain)
                    (p1 p2 : bptr) (A1 n1 A2 n2 : Z) (XS : list (Z * Z)),
      let E' := errst_raise E A1 p1 n1 line A2 p2 n2 ERR_LIB_PROV reason in
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_MPRES H mo (cfg_model k) /\ c4_frame H sp tp s' (blocks_ERRST E' ++ LBN ++ LB) lo B m' k
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv']
      /\ errph_delta ph LBN c /\ raise_sizes A1 n1 A2 n2
      /\ ERRPH (LBN ++ LB) m' (ErrReady c) /\ CTXPH (LBN ++ LB) m' (CtxReady x)
      /\ ERRXR m' c E' /\ lib_shad (chain_blocks c) m'
      /\ HPKE_tabs m'
      /\ Forall (fs_scratch H LF) XS /\ xpres H LB (bv_unsigned sp) (XS ++ ERR_XE ++ memflag_foot ++ errph_foot ph) m m'
      /\ as_RFS H LF m' /\ as_AL H s' >= as_AL H s - RAISE_COST H ph.
  Definition hfind_fail_stmt (f : finder) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
           (ph : errphase) (E : errst) (x : ctxinfo) (id lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 (f_entry f)) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 id -> 0 <= id < 2^16 -> find_id (f_ids f) id = None -> HPKE_tabs m ->
      as_RHEAP H s (blocks_ERRST E ++ LB) m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes (blocks_ERRST E ++ LB) + raise_bytes ph <= as_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + raise_cnt ph <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - (f_frame f + RAISE_STACK ph) -> errph_sh0 ph m lo sp ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> arelro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph aceil -> errph_shad m ph -> CTXPH LB m (CtxReady x) -> bv_unsigned ra mod 2 = 0 ->
      (* [comment removed for export] *)
      as_RFS H LF m -> (length LF + ERRPH_LF ph <= AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_hfind f ph) (bv_unsigned ra) CH -> errph_closed_ok H ph -> RAISE_COST H ph <= as_AL H s ->
      as_SR H (hfind_fail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF ph E x (f_reason f) (f_line f id) lo B m mo) (mkCfg msF mo).

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
  Definition SUITECHECK_STACK (ph : errphase) : Z := FR_OSSL_HPKE_suite_check + FR_hpke_suite_check + FR_ossl_HPKE_KEM_INFO_find_id + RAISE_STACK ph.   (* [comment removed for export] *)
  Definition SUITECHECK_OK_STACK : Z := FR_OSSL_HPKE_suite_check + FR_hpke_suite_check + FR_ossl_HPKE_KEM_INFO_find_id.

  Definition suiteok_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (kem kdf aead hi lo : Z),
      a0 = Z_to_bv 64 (suite_word kem kdf aead hi) -> 0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= hi < 2^16 ->
      suite_fail kem kdf aead = None -> HPKE_tabs m -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - SUITECHECK_OK_STACK -> mem_inv asegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt asegs (hfind_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom asegs)).
  Definition suitebad_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
           (ph : errphase) (E : errst) (x : ctxinfo) (kem kdf aead hi reason line lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 (suite_word kem kdf aead hi) -> 0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= hi < 2^16 ->
      suite_fail kem kdf aead = Some (reason, line) -> HPKE_tabs m ->
      as_RHEAP H s (blocks_ERRST E ++ LB) m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes (blocks_ERRST E ++ LB) + raise_bytes ph <= as_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + raise_cnt ph <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - SUITECHECK_STACK ph -> errph_sh0 ph m lo sp ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> arelro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph aceil -> errph_shad m ph -> CTXPH LB m (CtxReady x) -> bv_unsigned ra mod 2 = 0 ->
      as_RFS H LF m -> (length LF + ERRPH_LF ph <= AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_suitebad ph) (bv_unsigned ra) CH -> errph_closed_ok H ph -> RAISE_COST H ph <= as_AL H s ->
      as_SR H (hfind_fail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF ph E x reason line lo B m mo) (mkCfg msF mo).

  Definition C11_stmts : Prop :=
    hfind_found_stmt KEM_finder /\ hfind_fail_stmt KEM_finder /\ hfind_found_stmt KDF_finder /\ hfind_fail_stmt KDF_finder
    /\ hfind_found_stmt AEAD_finder /\ hfind_fail_stmt AEAD_finder /\ suiteok_stmt /\ suitebad_stmt.
End W.
End HCW.
