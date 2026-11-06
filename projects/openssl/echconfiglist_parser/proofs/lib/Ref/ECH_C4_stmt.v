(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState
     ECH_C0_stmt ECH_C1_stmt ECH_C2_stmt ECH_LibFrame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ERRINIT_CNT : Z := 1600.
Definition ERRINIT_BYTES : Z := 2^16.
Definition ERRINIT_BIG : Z := 2.
Definition ERRINIT_STACK : Z := 1024 + RREALLOC_STACK.
Definition EGS_STACK : Z := FR_ossl_err_get_state_int + CINITCRYPTO_STACK.      (* [comment removed for export] *)
Definition errph_cnt (ph : errphase) : Z := match ph with ErrFresh => ERRINIT_CNT | ErrReady _ => 0 end.
Definition errph_bytes (ph : errphase) : Z := match ph with ErrFresh => ERRINIT_BYTES | ErrReady _ => 0 end.
Definition errph_big (ph : errphase) : Z := match ph with ErrFresh => ERRINIT_BIG | ErrReady _ => 0 end.
Definition errph_stack (ph : errphase) : Z := match ph with ErrFresh => FR_ossl_err_get_state_int + ERRINIT_STACK | ErrReady _ => EGS_STACK end.
Definition ERRNEW_STACK (ph : errphase) : Z := FR_ERR_new + Z.max (errph_stack ph) CFREE_STACK.
Definition ERRDEBUG_STACK : Z := FR_ERR_set_debug + Z.max EGS_STACK CMALLOC_STACK.
Definition ERRSETERR_STACK : Z := FR_ERR_set_error + FR_ERR_vset_error + EGS_STACK.
Definition ERRCLEAR_STACK (ph : errphase) : Z := FR_ERR_clear_error + Z.max (errph_stack ph) CFREE_STACK.
(* [comment removed for export] *)
Definition ERRDEBUG_BYTES : Z := 64.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ERRX (m : mem) (ph : errphase) (E : errst) : Prop :=
  match ph with ErrFresh => E = errst_zero | ErrReady c => ERRST (blocks_ERRST E) m (blk_addr (ec_es c)) E end.
(* [comment removed for export] *)
Definition errph_delta (ph : errphase) (LBN : list block) (c : errchain) : Prop :=
  match ph with
  | ErrReady c0 => c = c0 /\ LBN = []
  | ErrFresh => Z.of_nat (length LBN) <= ERRINIT_CNT /\ lb_bytes LBN <= ERRINIT_BYTES /\ lb_big LBN <= 1
                /\ Forall (fun b => In b LBN) (chain_blocks c)
  end.
(* [comment removed for export] *)
Definition errph_below (ph : errphase) (lo : Z) : Prop :=
  match ph with ErrFresh => True | ErrReady c => chain_below c lo end.
(* [comment removed for export] *)
Definition errph_foot (ph : errphase) : list (Z * Z) :=
  match ph with ErrFresh => [] | ErrReady c => [(blk_addr (ec_es c), blk_addr (ec_es c) + ERRST_SIZE)] end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition err_next (t : Z) : Z := (t + 1) mod 16.
Definition slot_upd (ss : list errslot) (i : nat) (x : errslot) : list errslot := firstn i ss ++ x :: skipn (S i) ss.
Definition slot_at (E : errst) (i : Z) : errslot := nth (Z.to_nat i) (es_slots E) (slot_clear 0).
(* [comment removed for export] *)
Definition errst_new (E : errst) : errst :=
  let t := err_next (es_top E) in
  mkERRST (slot_upd (es_slots E) (Z.to_nat t) (slot_clear (2^32 - 1))) t
          (if t =? es_bottom E then err_next (es_bottom E) else es_bottom E).
(* [comment removed for export] *)
Definition errst_debug (E : errst) (f : Z) (fo : oblk) (line : Z) (g : Z) (go : oblk) : errst :=
  let s := slot_at E (es_top E) in
  mkERRST (slot_upd (es_slots E) (Z.to_nat (es_top E)) (mkSLOT (sl_flags s) (sl_buffer s) f fo line g go)) (es_top E) (es_bottom E).
(* [comment removed for export] *)
Definition ERR_PACK (lib reason : Z) : Z := Z.lor (Z.shiftl (Z.land lib 255) 23) (Z.land reason 8388607).
Definition errst_seterr (E : errst) (lib reason : Z) : errst :=
  let s := slot_at E (es_top E) in
  mkERRST (slot_upd (es_slots E) (Z.to_nat (es_top E)) (mkSLOT (sl_flags s) (ERR_PACK lib reason) (sl_file s) (sl_file_o s) (sl_line s) (sl_func s) (sl_func_o s)))
          (es_top E) (es_bottom E).
Definition slot_empty (s : errslot) : Prop := sl_file_o s = None /\ sl_func_o s = None.

(* [comment removed for export] *)
Definition CSTR (m : mem) (A : Z) (str slack : list byte) : Prop :=
  bytes_at rsegs m A (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str
  /\ (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack).
(* [comment removed for export] *)
Definition ROSTR (A : Z) (str slack : list byte) : Prop :=
  IMG_LO <= A /\ A + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= IMG_HI       (* [comment removed for export] *)
  /\ forall m, mem_inv rsegs m -> CSTR m A str slack.

Section W.
  Variable H : hsr.

  (* [comment removed for export] *)
  Definition c4_frame (sp tp : word) (s' : PState) (LB' : list block) (lo B : Z) (m' : mem) (c : config) : Prop :=
       hs_KREL H s' (cfg_model c) /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ hs_rauxv_ok H m' B /\ hs_RHEAP H s' LB' m' /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ relro_lib m'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition egs_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (ph : errphase) (E : errst) (x : ctxinfo) (save lo B : Z) (errv : word) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LBN : list block) (c : errchain),
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (blk_addr (ec_es c))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_MPRES H mo (cfg_model k) /\ c4_frame sp tp s' (blocks_ERRST E ++ LBN ++ LB) lo B m' k
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ (save <> 0 -> errv' = errv)
      /\ errph_delta ph LBN c /\ ERRPH (LBN ++ LB) m' (ErrReady c) /\ CTXPH (LBN ++ LB) m' (CtxReady x)
      /\ ERRST (blocks_ERRST E) m' (blk_addr (ec_es c)) E
      /\ xpres LB (bv_unsigned sp) ERR_X m m'.
  (* [comment removed for export] *)
  Definition egs_stmt_for (ph : errphase) (E : errst) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
           (x : ctxinfo) (save lo B : Z) (errv : word),
      a0 = Z_to_bv 64 save -> 0 <= save < 2^32 -> (ph = ErrFresh -> save = 0 \/ save = 1) ->
      hs_RHEAP H s (blocks_ERRST E ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (blocks_ERRST E ++ LB) + errph_bytes ph <= hs_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + errph_cnt ph <= hs_LIVE_CNT_MAX H ->
      lb_big (blocks_ERRST E ++ LB) + errph_big ph <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - errph_stack ph ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> relro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph lo -> CTXPH LB m (CtxReady x) -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (egs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB ph E x save lo B errv m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ossl_err_get_state_int) fc None m (seg_rom rsegs)) mo).
  Definition egs_stmt : Prop := forall ph E, egs_stmt_for ph E.
  Definition egs_fresh_stmt : Prop := egs_stmt_for ErrFresh errst_zero.

  (* [comment removed for export] *)
  Definition egsr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (c : errchain) (exl : ctxinfo) (lo : Z) (errv : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (blk_addr (ec_es c))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (RERRNO, RERRNO + 4)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
      /\ CTX_statics m' exl /\ ERR_statics m' c /\ ERR_chain LB m' c.
  Definition egs_ready_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (c : errchain) (exl : ctxinfo) (save lo : Z) (errv : word),
      a0 = Z_to_bv 64 save -> 0 <= save < 2^32 -> tp = Z_to_bv 64 RATP -> rw_cells rsegs m (errno_addr tp) [C4 errv] ->
      CTX_statics m exl -> ERR_statics m c -> ERR_chain LB m c -> chain_below c lo ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - EGS_STACK -> mem_inv rsegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt rsegs (egsr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB c exl lo errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ossl_err_get_state_int) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition errnew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (ph : errphase) (E : errst) (x : ctxinfo) (lo B : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LBN : list block) (c : errchain),
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_MPRES H mo (cfg_model k) /\ c4_frame sp tp s' (blocks_ERRST (errst_new E) ++ LBN ++ LB) lo B m' k
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
      /\ errph_delta ph LBN c /\ ERRPH (LBN ++ LB) m' (ErrReady c) /\ CTXPH (LBN ++ LB) m' (CtxReady x)
      /\ ERRST (blocks_ERRST (errst_new E)) m' (blk_addr (ec_es c)) (errst_new E)
      /\ xpres LB (bv_unsigned sp) (ERR_X ++ errph_foot ph) m m'.
  Definition errnew_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
           (ph : errphase) (E : errst) (x : ctxinfo) (lo B : Z) (errv : word),
      hs_RHEAP H s (blocks_ERRST E ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (blocks_ERRST E ++ LB) + errph_bytes ph <= hs_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + errph_cnt ph <= hs_LIVE_CNT_MAX H ->
      lb_big (blocks_ERRST E ++ LB) + errph_big ph <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - ERRNEW_STACK ph ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> relro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph lo -> CTXPH LB m (CtxReady x) -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (errnew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB ph E x lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition errdebug_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (c : errchain) (E : errst) (x : ctxinfo) (line : Z) (fs gs : list byte) (lo B : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (A1 A2 : Z) (p1 p2 : bptr),
      let E' := errst_debug E A1 (Some (p1, Z.of_nat (length fs) + 1)) line A2 (Some (p2, Z.of_nat (length gs) + 1)) in
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_MPRES H mo (cfg_model k) /\ c4_frame sp tp s' (blocks_ERRST E' ++ LB) lo B m' k
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rblock_range A1 (Z.of_nat (length fs) + 1) /\ rblock_range A2 (Z.of_nat (length gs) + 1)
      /\ ERRPH LB m' (ErrReady c) /\ CTXPH LB m' (CtxReady x)
      /\ ERRST (blocks_ERRST E') m' (blk_addr (ec_es c)) E'
      /\ xpres LB (bv_unsigned sp) (memflag_foot ++ errph_foot (ErrReady c)) m m'.
  Definition errdebug_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
           (c : errchain) (E : errst) (x : ctxinfo) (file line func : Z) (fs fsl gs gsl : list byte) (lo B : Z) (errv : word),
      a0 = Z_to_bv 64 file -> a1 = Z_to_bv 64 line -> a2 = Z_to_bv 64 func -> 0 <= line < 2^31 ->
      ROSTR file fs fsl -> fs <> [] -> Z.of_nat (length fs) < 24 -> 0 < file ->
      ROSTR func gs gsl -> gs <> [] -> Z.of_nat (length gs) < 32 -> 0 < func ->
      slot_empty (slot_at E (es_top E)) ->
      hs_RHEAP H s (blocks_ERRST E ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (blocks_ERRST E ++ LB) + ERRDEBUG_BYTES <= hs_LIVE_MAX H -> Z.of_nat (length (blocks_ERRST E ++ LB)) + 2 <= hs_LIVE_CNT_MAX H ->
      lb_big (blocks_ERRST E ++ LB) <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - ERRDEBUG_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> relro_lib m ->
      ERRPH LB m (ErrReady c) -> ERRST (blocks_ERRST E) m (blk_addr (ec_es c)) E -> chain_below c lo -> CTXPH LB m (CtxReady x) ->
      bv_unsigned ra mod 2 = 0 ->
      hs_SR H (errdebug_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB c E x line fs gs lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_set_debug) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition errseterr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (c : errchain) (E : errst) (exl : ctxinfo) (lib reason lo : Z) (errv : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (RERRNO, RERRNO + 4); (blk_addr (ec_es c), blk_addr (ec_es c) + ERRST_SIZE)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
      /\ CTX_statics m' exl /\ ERR_statics m' c /\ ERR_chain LB m' c
      /\ ERRST LB m' (blk_addr (ec_es c)) (errst_seterr E lib reason).
  Definition errseterr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (c : errchain) (E : errst) (exl : ctxinfo) (lib reason lo : Z) (errv : word),
      a0 = Z_to_bv 64 lib -> a1 = Z_to_bv 64 reason -> a2 = Z_to_bv 64 0 -> 0 < lib < 256 -> lib <> 2 -> 0 < reason < 2^23 ->
      tp = Z_to_bv 64 RATP -> rw_cells rsegs m (errno_addr tp) [C4 errv] ->
      CTX_statics m exl -> ERR_statics m c -> ERR_chain LB m c -> chain_below c lo -> chain_sep c -> ERRST LB m (blk_addr (ec_es c)) E ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - ERRSETERR_STACK -> mem_inv rsegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt rsegs (errseterr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB c E exl lib reason lo errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ERR_set_error) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition errclear_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (ph : errphase) (E : errst) (x : ctxinfo) (lo B : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LBN : list block) (c : errchain),
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_MPRES H mo (cfg_model k) /\ c4_frame sp tp s' (LBN ++ LB) lo B m' k          (* [comment removed for export] *)
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
      /\ errph_delta ph LBN c /\ ERRPH (LBN ++ LB) m' (ErrReady c) /\ CTXPH (LBN ++ LB) m' (CtxReady x)
      /\ ERRST [] m' (blk_addr (ec_es c)) errst_cleared
      /\ xpres LB (bv_unsigned sp) (ERR_X ++ errph_foot ph) m m'.
  Definition errclear_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
           (ph : errphase) (E : errst) (x : ctxinfo) (lo B : Z) (errv : word),
      hs_RHEAP H s (blocks_ERRST E ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (blocks_ERRST E ++ LB) + errph_bytes ph <= hs_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + errph_cnt ph <= hs_LIVE_CNT_MAX H ->
      lb_big (blocks_ERRST E ++ LB) + errph_big ph <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - ERRCLEAR_STACK ph ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> relro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph lo -> CTXPH LB m (CtxReady x) -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (errclear_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB ph E x lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ERR_clear_error) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition errst_raise (E : errst) (A1 : Z) (p1 : bptr) (n1 : Z) (line : Z) (A2 : Z) (p2 : bptr) (n2 : Z) (lib reason : Z) : errst :=
    errst_seterr (errst_debug (errst_new E) A1 (Some (p1, n1)) line A2 (Some (p2, n2))) lib reason.
  Definition RAISE_STACK (ph : errphase) : Z := Z.max (ERRNEW_STACK ph) (Z.max ERRDEBUG_STACK ERRSETERR_STACK).
  Definition raise_cnt (ph : errphase) : Z := errph_cnt ph + 2.
  Definition raise_bytes (ph : errphase) : Z := errph_bytes ph + ERRDEBUG_BYTES.
  (* [comment removed for export] *)
  Definition raise_sizes (A1 n1 A2 n2 : Z) : Prop :=
    rblock_range A1 n1 /\ rblock_range A2 n2 /\ 0 < n1 /\ 0 < n2 /\ n1 + n2 <= ERRDEBUG_BYTES.

  Definition C4_stmts : Prop := egs_ready_stmt /\ egs_stmt /\ errnew_stmt /\ errdebug_stmt /\ errseterr_stmt /\ errclear_stmt.
End W.
End HCW.
