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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState ECH_C1_stmt ECH_C3_stmt ECH_C4_stmt ECH_C5_stmt ECH_C7_stmt ECH_C8_stmt ECH_C11_stmt ECH_C13_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record libmid := mkMID {
  mid_flag : Z;           (* [comment removed for export] *)
  mid_ctx : ctxphase;     (* [comment removed for export] *)
  mid_err : errphase;     (* [comment removed for export] *)
  mid_E : errst;          (* [comment removed for export] *)
  mid_vdso : bool }.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ERRPH_mid (LB : list block) (m : mem) (cph : ctxphase) (eph : errphase) : Prop :=
  match cph, eph with
  | CtxFresh, ErrFresh => ERR_fresh_core m
  | CtxFresh, ErrReady _ => False            (* [comment removed for export] *)
  | CtxReady _, _ => ERRPH LB m eph
  end.
Definition VDSO_X : list (Z * Z) := [(A_vdso_func, A_vdso_func + 8)].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition errst_fits (E : errst) : Prop :=
  Forall (fun s => lb_bytes (blocks_slot s) <= ERRDEBUG_BYTES /\ lb_big (blocks_slot s) = 0) (es_slots E).
Definition LIBMID (LB : list block) (m : mem) (M : libmid) : Prop :=
     IMPL_mem m /\ MEMFLAG m (mid_flag M)
  /\ CTXPH LB m (mid_ctx M) /\ ERRPH_mid LB m (mid_ctx M) (mid_err M) /\ ERRX m (mid_err M) (mid_E M)
  /\ rw_cells usegs m A_vdso_func [C8 (wz (if mid_vdso M then 0 else P_cgt_init))]
  /\ m (wa A_global_cleanup) = None
  /\ errst_fits (mid_E M)                                                   (* [comment removed for export] *)
  /\ GOT_mem m /\ GOT_echfree m /\ GOT_x509vpm m /\ METH_mem m /\ METH_b64 m /\ HPKE_tabs m /\ relro_lib m.
(* [comment removed for export] *)
Definition mid_errblocks (M : libmid) : list block := blocks_ERRST (mid_E M).
(* [comment removed for export] *)
Definition mid_step (M M' : libmid) : Prop :=
     mid_flag M' = 1
  /\ (forall b, mid_ctx M = CtxReady b -> mid_ctx M' = CtxReady b)
  /\ (forall c, mid_err M = ErrReady c -> mid_err M' = ErrReady c)
  /\ (mid_vdso M = true -> mid_vdso M' = true).
(* [comment removed for export] *)
Definition mid_newlib_ok (M M' : libmid) (LBN : list block) : Prop :=
  exists LA LE, Permutation LBN (LA ++ LE)
    /\ (match mid_ctx M, mid_ctx M' with CtxFresh, CtxReady b => ctxph_delta CtxFresh LA b | _, _ => LA = [] end)
    /\ (match mid_err M, mid_err M' with ErrFresh, ErrReady c => errph_delta ErrFresh LE c | _, _ => LE = [] end).
Definition mid_cnt (M : libmid) : Z := ctxph_cnt (mid_ctx M) + errph_cnt (mid_err M).
Definition mid_bytes (M : libmid) : Z := ctxph_bytes (mid_ctx M) + errph_bytes (mid_err M).
Definition mid_big (M : libmid) : Z := ctxph_big (mid_ctx M) + errph_big (mid_err M).
Definition mid_stack (M : libmid) : Z := Z.max (ctxph_stack (mid_ctx M)) (errph_stack (mid_err M)).

(* [comment removed for export] *)
Definition DECODE_CNT : Z := 720.
Definition DECODE_BYTES : Z := 2^17.
Definition DECODE_BIG : Z := 6.          (* [comment removed for export] *)
Definition ERRSTR_CNT : Z := 32.
Definition ERRSTR_BYTES : Z := 32 * 32.
Definition READCFG_STACK (M : libmid) : Z := FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 512 + Z.max (mid_stack M) RREALLOC_STACK.
   (* [comment removed for export] *)

Section W.
  Variable H : hsr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition readcfg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LIB LB : list block) (M : libmid) (st : Z) (S : storerep) (mb : Z) (R : membio) (ds : list byte)
      (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (rv : Z)
                    (M' : libmid) (S' : storerep) (R' : membio) (LBN NB : list block),
      let LB' := NB ++ LBN ++ LB in                                  (* [comment removed for export] *)
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ (rv = 0 \/ rv = 1)
      /\ hs_KREL H s' (cfg_model k) /\ hs_MPRES H mo (cfg_model k)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' (mid_errblocks M' ++ LB') m'
      /\ LIBMID (LBN ++ LIB) m' M' /\ mid_step M M' /\ mid_newlib_ok M M' LBN /\ mid_ctx M' = mid_ctx M
      /\ STOREobj LB' m' st S' /\ es_id S' = es_id S /\ Permutation (blocks_STORE st S') ((es_id S, st, STORE_SIZE) :: NB)
      /\ Z.of_nat (length NB) <= DECODE_CNT /\ lb_bytes NB <= DECODE_BYTES /\ lb_big NB <= DECODE_BIG
      /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES /\ lb_big (mid_errblocks M') = 0
      /\ List.NoDup (map blk_id (blocks_STORE st S'))
      /\ MEMBIO LB' m' mb R' /\ blocks_MEMBIO mb R' = blocks_MEMBIO mb R /\ bytes_at usegs m' (mb_buf R) ds
      /\ xpres LB (bv_unsigned sp) ([(st, st + STORE_SIZE)] ++ MEMBIO_foot mb R ++ ERR_X ++ VDSO_X ++ errph_foot (mid_err M)) m m'.   (* [comment removed for export] *)
  Definition readcfg_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LIB LB : list block)
           (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word),
      a0 = Z_to_bv 64 st -> a1 = Z_to_bv 64 mb ->
      STOREobj LB m st S -> es_entries S = 0 -> es_entries_o S = None -> st + STORE_SIZE <= lo ->
      MEMBIO LB m mb R -> mb_pos R = 0 -> mb_nread R = 0 -> MEMBIO_below mb R lo -> MEMBIO_sep mb R ->
      bytes_at usegs m (mb_buf R) ds -> zlength ds = mb_len R ->
      (1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD) ->   (* [comment removed for export] *)
      (1 <= mb_len R -> forall pD, In (pD, mb_buf R, mb_len R) LB -> pD <> es_id S) ->                        (* [comment removed for export] *)
      List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)) ->
      LIBMID LIB m M -> (forall b, In b LIB -> In b LB) -> mid_ctx M = CtxReady x -> mid_flag M = 1 ->
      (forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b') ->   (* [comment removed for export] *)
      hs_RHEAP H s (mid_errblocks M ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= hs_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= hs_LIVE_CNT_MAX H ->
      lb_big (mid_errblocks M ++ LB) + mid_big M + DECODE_BIG <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 -> bv_unsigned sp mod 16 = 0 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - READCFG_STACK M ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (readcfg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LB M st S mb R ds lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom usegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint suite_cells (rows : list (Z * Z * Z)) : list cell :=
    match rows with [] => [] | (kem, kdf, aead) :: rows' => C2 (wz kem) :: C2 (wz kdf) :: C2 (wz aead) :: suite_cells rows' end.
  Definition row_ok (r : Z * Z * Z) : Prop := 0 <= fst (fst r) < 2^16 /\ 0 <= snd (fst r) < 2^16 /\ 0 <= snd r < 2^16.
  Lemma suite_cells_size : forall rows, Z.of_nat (cells_size (suite_cells rows)) = 6 * zlength rows.
  Proof. unfold zlength. induction rows as [|[[k d] a] rows IH]; [reflexivity|]. cbn [suite_cells cells_size csize length]. rewrite Nat2Z.inj_succ. cbn [cells_size csize] in IH. lia. Qed.

  (* [comment removed for export] *)
  Definition FCC_CNT : Z := 5.                                     (* [comment removed for export] *)
  Definition FCC_BYTES : Z := VPM_SIZE + 16 + 264 + SK_SIZE + 32.
  Definition FCC_STACK (M : libmid) : Z := FR_ech_final_config_checks + 320 + Z.max (errph_stack (mid_err M)) RREALLOC_STACK.   (* [comment removed for export] *)
  Definition fcc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LIB LB : list block) (M : libmid) (ee : Z) (E : entrep) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (rv : Z) (M' : libmid) (LBN : list block),
      let LB' := LBN ++ LB in                                        (* [comment removed for export] *)
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ (rv = 0 \/ rv = 1)
      /\ hs_KREL H s' (cfg_model k) /\ hs_MPRES H mo (cfg_model k)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' (mid_errblocks M' ++ LB') m'
      /\ LIBMID (LBN ++ LIB) m' M' /\ mid_step M M' /\ mid_newlib_ok M M' LBN /\ mid_ctx M' = mid_ctx M /\ mid_vdso M' = mid_vdso M
      /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES /\ lb_big (mid_errblocks M') = 0
      /\ ENTRYobj LB' m' ee E
      /\ xpres LB (bv_unsigned sp) (ERR_X ++ errph_foot (mid_err M)) m m'.
  Definition fcc_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LIB LB : list block)
           (M : libmid) (x : ctxinfo) (ee lo B : Z) (E : entrep) (errv : word)
           (rows : list (Z * Z * Z)) (ps : bptr) (sn : Z) (pn : bptr) (ns : list byte),
      a0 = Z_to_bv 64 ee -> ENTRYobj LB m ee E -> 1 <= en_nsuites E < 2^31 ->
      en_suites_o E = Some (ps, sn) -> rw_cells usegs m (en_suites E) (suite_cells rows) -> zlength rows = en_nsuites E -> 6 * en_nsuites E <= sn ->
      Forall row_ok rows ->                                                                                     (* [comment removed for export] *)
      en_pname_o E = Some (pn, zlength ns + 1) -> bytes_at usegs m (en_pname E) (ns ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) ns -> 1 <= zlength ns <= 255 ->   (* [comment removed for export] *)
      Forall (fun b => blk_addr b + blk_size b <= lo) (blocks_ENTRY ee E) ->
      LIBMID LIB m M -> (forall b, In b LIB -> In b LB) -> mid_ctx M = CtxReady x -> mid_flag M = 1 ->
      (forall b b', In b LIB -> In b' (blocks_ENTRY ee E) -> blk_id b <> blk_id b') ->                     (* [comment removed for export] *)
      hs_RHEAP H s (mid_errblocks M ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (mid_errblocks M ++ LB) + errph_bytes (mid_err M) + FCC_BYTES + ERRSTR_BYTES <= hs_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks M ++ LB)) + errph_cnt (mid_err M) + FCC_CNT + ERRSTR_CNT <= hs_LIVE_CNT_MAX H ->
      lb_big (mid_errblocks M ++ LB) + errph_big (mid_err M) <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 -> bv_unsigned sp mod 16 = 0 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - FCC_STACK M ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (fcc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LB M ee E lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ech_final_config_checks) fc None m (seg_rom usegs)) mo).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition DECEXTS_STACK (M : libmid) : Z := FR_ech_decode_echconfig_exts + 192 + Z.max (errph_stack (mid_err M)) RREALLOC_STACK.   (* [comment removed for export] *)
  Definition DECEXTS_BYTES (rem : Z) : Z := 16 * rem + 256.     (* [comment removed for export] *)
  Definition decexts_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LIB LB : list block) (M : libmid) (ee pk base len cur rem : Z) (E : entrep) (bs : list byte) (lo B : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (rv : Z) (M' : libmid)
                    (xs : option (skrep * list extrep)) (exp : Z) (NB LBN : list block) (cur' rem' : Z),
      let LB' := NB ++ LBN ++ LB in                                  (* [comment removed for export] *)
      let E' := mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
                      (en_maxname E) (en_cfgid E) exp xs (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E) in
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ hs_KREL H s' (cfg_model k) /\ hs_MPRES H mo (cfg_model k)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' (mid_errblocks M' ++ LB') m'
      /\ LIBMID (LBN ++ LIB) m' M' /\ mid_step M M' /\ mid_newlib_ok M M' LBN /\ mid_ctx M' = mid_ctx M /\ mid_vdso M' = mid_vdso M
      /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES /\ lb_big (mid_errblocks M') = 0
      /\ ENTRYobj LB' m' ee E' /\ Permutation (blocks_EXTS exp xs) NB
      /\ ((rv = 1 /\ xs <> None /\ rem' = 0) \/ (rv = 0 /\ xs = None /\ exp = 0 /\ NB = []))
      /\ 5 * Z.of_nat (length NB) <= 2 * (rem - rem') + 10 /\ lb_bytes NB <= rem + SK_SIZE + 8 * (rem + 4) /\ lb_big NB <= rem / 600   (* [comment removed for export] *)
      /\ rw_cells usegs m' pk (pk_cells cur' base rem') /\ bytes_at usegs m' base bs /\ pk_in base len cur' rem' /\ cur + rem = cur' + rem'   (* [comment removed for export] *)
      /\ xpres LB (bv_unsigned sp) ((pk, pk + 24) :: (ee, ee + ENTRY_SIZE) :: ERR_X ++ errph_foot (mid_err M)) m m'.
  Definition decexts_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LIB LB : list block)
           (M : libmid) (x : ctxinfo) (ee pk base len cur rem lo B : Z) (E : entrep) (bs : list byte) (pbin : bptr) (errv : word),
      a0 = Z_to_bv 64 ee -> a1 = Z_to_bv 64 pk ->
      ENTRYobj LB m ee E -> en_exts E = 0 -> en_exts_o E = None -> Forall (fun b => blk_addr b + blk_size b <= lo) (blocks_ENTRY ee E) ->
      rw_cells usegs m pk (pk_cells cur base rem) -> pk_in base len cur rem -> 1 <= rem -> rem <= 1499 ->     (* [comment removed for export] *)
      bv_unsigned sp <= pk -> pk + 24 <= B ->                                   (* [comment removed for export] *)
      In (pbin, base, len) LB -> en_id E <> pbin -> bytes_at usegs m base bs -> zlength bs <= len -> cur + rem <= base + zlength bs ->   (* [comment removed for export] *)
      LIBMID LIB m M -> (forall b, In b LIB -> In b LB) -> mid_ctx M = CtxReady x -> mid_flag M = 1 ->
      (forall b b', In b LIB -> In b' (blocks_ENTRY ee E) -> blk_id b <> blk_id b') ->                     (* [comment removed for export] *)
      (forall b, In b LIB -> blk_id b <> pbin) ->                                                            (* [comment removed for export] *)
      hs_RHEAP H s (mid_errblocks M ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (mid_errblocks M ++ LB) + errph_bytes (mid_err M) + DECEXTS_BYTES rem + ERRDEBUG_BYTES <= hs_LIVE_MAX H ->     (* [comment removed for export] *)
      Z.of_nat (length (mid_errblocks M ++ LB)) + errph_cnt (mid_err M) + (2 * rem) / 5 + 8 <= hs_LIVE_CNT_MAX H ->       (* [comment removed for export] *)
      lb_big (mid_errblocks M ++ LB) + errph_big (mid_err M) + 2 <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 -> bv_unsigned sp mod 16 = 0 ->
      pk mod 8 = 0 ->   (* [comment removed for export] *)
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - DECEXTS_STACK M ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (decexts_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LB M ee pk base len cur rem E bs lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ech_decode_echconfig_exts) fc None m (seg_rom usegs)) mo).

  Definition C14_stmts : Prop := readcfg_stmt /\ fcc_stmt /\ decexts_stmt.
End W.
End HCW.
