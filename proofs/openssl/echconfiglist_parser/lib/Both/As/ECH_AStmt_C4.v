(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C0 ECH_AStmt_C1 ECH_AStmt_C2 ECH_APF_C4.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ERRINIT_CNT : Z := 1600.
Definition ERRINIT_BYTES : Z := 2^16.
Definition ERRINIT_STACK : Z := 1024 + AREALLOC_STACK.
Definition EGS_STACK : Z := FR_ossl_err_get_state_int + CINITCRYPTO_STACK.      (* [comment removed for export] *)
Definition errph_cnt (ph : errphase) : Z := match ph with ErrFresh => ERRINIT_CNT | ErrReady _ => 0 end.
Definition errph_bytes (ph : errphase) : Z := match ph with ErrFresh => ERRINIT_BYTES | ErrReady _ => 0 end.
Definition errph_stack (ph : errphase) : Z := match ph with ErrFresh => FR_ossl_err_get_state_int + ERRINIT_STACK | ErrReady _ => EGS_STACK end.
Definition ERRNEW_STACK (ph : errphase) : Z := FR_ERR_new + Z.max (errph_stack ph) CFREE_STACK.
Definition ERRDEBUG_STACK : Z := FR_ERR_set_debug + Z.max EGS_STACK CMALLOC_STACK.
Definition ERRSETERR_STACK : Z := FR_ERR_set_error + 32 + Z.max AFS_STACK (FR_ERR_vset_error + EGS_STACK).   (* [comment removed for export] *)
Definition ERRCLEAR_STACK (ph : errphase) : Z := FR_ERR_clear_error + Z.max (errph_stack ph) (96 + CFREE_STACK).
(* [comment removed for export] *)
Definition ERRDEBUG_BYTES : Z := 64.
(* [comment removed for export] *)
Definition ARERRNO : Z := ATP - 164.
(* [comment removed for export] *)
Definition ERRNO_X : list (Z * Z) := [(ARERRNO, ARERRNO + 4)].
Definition ERR_XE : list (Z * Z) := ERRNO_X ++ ERR_X.
(* [comment removed for export] *)
Definition ERRPH_LF (ph : errphase) : nat := match ph with ErrFresh => 4%nat | ErrReady _ => 2%nat end.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition oszb (o : oblk) : Z := match o with None => 0 | Some (_, n) => n end.
Definition slot_bytes (sl : errslot) : Z := oszb (sl_file_o sl) + oszb (sl_func_o sl).
Definition estrs_ok (E : errst) : Prop := Forall (fun sl => 0 <= oszb (sl_file_o sl) <= 24 /\ 0 <= oszb (sl_func_o sl) <= 32) (es_slots E).
Definition estr_bytes (E : errst) : Z := fold_right (fun sl acc => slot_bytes sl + acc) 0 (es_slots E).
(* [comment removed for export] *)
Definition estrs_cells (m : mem) (E : errst) : Prop :=
  Forall (fun b => exists bs, rw_cells asegs m (blk_addr b) [CB (Z.to_nat (blk_size b)) bs]) (blocks_ERRST E).
Definition ERRXR (m : mem) (c : errchain) (E : errst) : Prop :=
  ERRST (blocks_ERRST E) m (blk_addr (ec_es c)) E /\ estrs_ok E /\ lib_shad (blocks_ERRST E) m /\ estrs_cells m E.
Definition ERRX (m : mem) (ph : errphase) (E : errst) : Prop :=
  match ph with ErrFresh => E = errst_zero | ErrReady c => ERRXR m c E end.
(* [comment removed for export] *)
Definition chain_sep (c : errchain) : Prop :=
  let es := blk_addr (ec_es c) in
     (blk_addr (ec_mkey c) + 72 <= es \/ es + ERRST_SIZE <= blk_addr (ec_mkey c))
  /\ (blk_addr (ec_sa c) + 32 <= es \/ es + ERRST_SIZE <= blk_addr (ec_sa c))
  /\ (blk_addr (ec_nodes c) + 128 <= es \/ es + ERRST_SIZE <= blk_addr (ec_nodes c)).
(* [comment removed for export] *)
Definition errph_shad (m : mem) (ph : errphase) : Prop :=
  match ph with ErrFresh => True | ErrReady c => lib_shad (chain_blocks c) m end.
(* [comment removed for export] *)
Definition errph_delta (ph : errphase) (LBN : list block) (c : errchain) : Prop :=
  match ph with
  | ErrReady c0 => c = c0 /\ LBN = []
  | ErrFresh => Z.of_nat (length LBN) <= ERRINIT_CNT /\ lb_bytes LBN <= ERRINIT_BYTES
                /\ Forall (fun b => In b LBN) (chain_blocks c)       (* [comment removed for export] *)
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

Definition CSTR (m : mem) (A : Z) (str slack : list byte) : Prop :=
  bytes_at asegs m A (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str
  /\ (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack).
(* [comment removed for export] *)
Definition ROSTR (A : Z) (str slack : list byte) : Prop :=
  IMG_LO <= A /\ A + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= IMG_HI       (* [comment removed for export] *)
  /\ forall m, mem_inv asegs m -> CSTR m A str slack.
(* [comment removed for export] *)
Definition AROSTR (A : Z) (str slack : list byte) : Prop :=
  ROSTR A str slack /\ (forall m, ACONST m -> accessible m A (Z.of_nat (length str) + 1))
  /\ AIMG_LO + 0x1000 <= A /\ A + Z.of_nat (length str) + 1 + Z.of_nat (length slack) + 64 <= AIMG_TOP.
Lemma AROSTR_intro : forall A str slack rz, ROSTR A str slack -> In (A, Z.of_nat (length str) + 1, rz) aglobals ->
  AIMG_LO + 0x1000 <= A -> A + Z.of_nat (length str) + 1 + Z.of_nat (length slack) + 64 <= AIMG_TOP -> AROSTR A str slack.
Proof.
  intros A str slack rz R IN LO HI. split; [exact R|]. split; [| split; [exact LO| exact HI]].
  intros m AC. pose proof (ACONST_global_addressable m _ _ _ AC IN ltac:(lia)) as AD.
  eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI, AIMG_TOP in *; lia].
Qed.
(* [comment removed for export] *)
Lemma AROSTR_intro_hull : forall A str slack H0 hsz rz, ROSTR A str slack -> In (H0, hsz, rz) aglobals ->
  H0 <= A -> A + Z.of_nat (length str) + 1 <= H0 + hsz -> H0 + hsz <= AIMG_TOP ->
  AIMG_LO + 0x1000 <= A -> A + Z.of_nat (length str) + 1 + Z.of_nat (length slack) + 64 <= AIMG_TOP -> AROSTR A str slack.
Proof.
  intros A str slack H0 hsz rz R IN B1 B2 B3 LO HI. split; [exact R|]. split; [| split; [exact LO| exact HI]].
  intros m AC. pose proof (ACONST_global_addressable m _ _ _ AC IN ltac:(lia)) as AD.
  eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI, AIMG_TOP in *; lia].
Qed.


(* [comment removed for export] *)
Definition errst_raise (E : errst) (A1 : Z) (p1 : bptr) (n1 : Z) (line : Z) (A2 : Z) (p2 : bptr) (n2 : Z) (lib reason : Z) : errst :=
  errst_seterr (errst_debug (errst_new E) A1 (Some (p1, n1)) line A2 (Some (p2, n2))) lib reason.
Definition RAISE_STACK (ph : errphase) : Z := Z.max (ERRNEW_STACK ph) (Z.max ERRDEBUG_STACK (ERRSETERR_STACK + 16)).   (* [comment removed for export] *)
Definition raise_cnt (ph : errphase) : Z := errph_cnt ph + 2.
Definition raise_bytes (ph : errphase) : Z := errph_bytes ph + ERRDEBUG_BYTES.
(* [comment removed for export] *)
Definition raise_sizes (A1 n1 A2 n2 : Z) : Prop :=
  0 < A1 /\ 1 <= n1 <= 24 /\ 0 < A2 /\ 1 <= n2 <= 32.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PF_egs (ph : errphase) : list (Z * list Z) := match ph with ErrFresh => PF_EGS_FRESH | ErrReady _ => [] end.
Definition PF_errnew (ph : errphase) : list (Z * list Z) := pf_shift R_ERR_new_egs (PF_egs ph) ++ PF_ERRNEW_READY.
Definition PF_errdebug : list (Z * list Z) := PF_ERRDEBUG.      (* [comment removed for export] *)
Definition PF_errseterr : list (Z * list Z) := [].
Definition PF_errclear (ph : errphase) : list (Z * list Z) := pf_shift R_ERR_clear_error_egs (PF_egs ph) ++ PF_ERRCLEAR_READY.

Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition ERRINIT_COST : Z := as_Cm H ERRINIT_BYTES + as_Cf H ERRINIT_BYTES.
  Definition errph_cost (ph : errphase) : Z := match ph with ErrFresh => ERRINIT_COST | ErrReady _ => 0 end.
  (* [comment removed for export] *)
  Definition errph_closed_ok (ph : errphase) : Prop :=
    match ph with ErrFresh => Forall (fun r : Z * list Z => trace_ok (as_TR H) (fst r) (snd r)) PFC_ERRINIT | ErrReady _ => True end.
  Definition RAISE_COST (ph : errphase) : Z := as_Cm H (raise_bytes ph) + as_Cf H (errph_bytes ph + ERRDEBUG_BYTES).

  (* [comment removed for export] *)
  Definition chain_apl (c : errchain) : Prop := Forall (fun b => ablock_range H (blk_addr b) (blk_size b)) (chain_blocks c).
  (* [comment removed for export] *)
  Definition errph_sh0 (ph : errphase) (m : mem) (lo : Z) (sp : word) : Prop :=
    match ph with ErrFresh => stack0 m lo (bv_unsigned sp) | ErrReady _ => True end.
  (* [comment removed for export] *)
  Lemma errph_sh0_xpres : forall ph LB X m m' lo (sp : word),
    errph_sh0 ph m lo sp -> xpres H LB (bv_unsigned sp) X m m' -> Forall stack0_ok X -> errph_sh0 ph m' lo sp.
  Proof. intros ph LB X m m' lo sp S XP FX. destruct ph; [| exact I]. cbn in *. eapply (stack0_xpres H); [exact XP| exact S| exact FX]. Qed.
  Lemma errph_sh0_munch : forall ph W m m' lo (sp : word),
    errph_sh0 ph m lo sp -> munch W m m' -> wmono asegs m m' -> Forall stack0_ok W -> errph_sh0 ph m' lo sp.
  Proof. intros ph W m m' lo sp S MU WM FW. destruct ph; [| exact I]. cbn in *. eapply stack0_transport; [exact S| exact MU| exact WM| exact FW]. Qed.
  Lemma errph_sh0_sub : forall ph m lo (sp sp' : word),
    errph_sh0 ph m lo sp -> lo <= bv_unsigned sp' <= bv_unsigned sp -> bv_unsigned sp' mod 8 = 0 -> errph_sh0 ph m lo sp'.
  Proof. intros ph m lo sp sp' S R A8. destruct ph; [| exact I]. cbn in *. eapply stack0_sub; [exact S| lia| lia| exact A8]. Qed.

  (* [comment removed for export] *)
  Definition c4_frame (sp tp : word) (s' : as_St H) (LB' : list block) (lo B : Z) (m' : mem) (c : config) : Prop :=
       as_AKREL H s' c /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ as_rauxv_ok H m' B /\ as_RHEAP H s' LB' m' /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ arelro_lib m'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition egs_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (ph : errphase) (E : errst) (x : ctxinfo) (save lo B : Z) (errv : word) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LBN : list block) (c : errchain) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (blk_addr (ec_es c))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_MPRES H mo (cfg_model k) /\ c4_frame sp tp s' (blocks_ERRST E ++ LBN ++ LB) lo B m' k
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ (save <> 0 -> errv' = errv)
      /\ errph_delta ph LBN c /\ ERRPH (LBN ++ LB) m' (ErrReady c) /\ CTXPH (LBN ++ LB) m' (CtxReady x)
      /\ ERRXR m' c E /\ lib_shad (chain_blocks c) m'
      /\ Forall (fs_scratch H LF) XS /\ xpres H LB (bv_unsigned sp) (XS ++ ERR_XE) m m'
      /\ as_RFS H LF m' /\ as_AL H s' >= as_AL H s - errph_cost ph.
  Definition egs_stmt_for (ph : errphase) (E : errst) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
           (x : ctxinfo) (save lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_ossl_err_get_state_int) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 save -> 0 <= save < 2^32 -> (ph = ErrFresh -> save = 0 \/ save = 1) ->
      as_RHEAP H s (blocks_ERRST E ++ LB) m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes (blocks_ERRST E ++ LB) + errph_bytes ph <= as_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + errph_cnt ph <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - errph_stack ph -> errph_sh0 ph m lo sp ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> arelro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph aceil -> errph_shad m ph -> CTXPH LB m (CtxReady x) ->
      as_RFS H LF m -> (length LF + ERRPH_LF ph <= AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_egs ph) (bv_unsigned ra) CH -> errph_closed_ok ph -> errph_cost ph <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (egs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF ph E x save lo B errv m mo) (mkCfg msF mo).
  Definition egs_stmt : Prop := forall ph E, egs_stmt_for ph E.
  Definition egs_fresh_stmt : Prop := egs_stmt_for ErrFresh errst_zero.

  (* [comment removed for export] *)
  Definition egsr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (LF : list fframe) (c : errchain) (exl : ctxinfo) (lo : Z) (errv : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (XS : list (Z * Z)),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (blk_addr (ec_es c))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ Forall (fs_scratch H LF) XS
      /\ munch ((lo, bv_unsigned sp) :: XS ++ [(ARERRNO, ARERRNO + 4)]) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv]
      /\ CTX_statics m' exl /\ ERR_statics m' c /\ ERR_chain LB m' c /\ lib_shad (chain_blocks c) m'
      /\ as_RFS H LF m' /\ ACONST m' /\ arelro_lib m'.
  Definition egs_ready_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (LF : list fframe) (c : errchain) (exl : ctxinfo) (save lo : Z) (errv : word),
      a0 = Z_to_bv 64 save -> 0 <= save < 2^32 -> tp = Z_to_bv 64 ATP -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
      CTX_statics m exl -> ERR_statics m c -> ERR_chain LB m c -> chain_below c aceil -> chain_apl c -> lib_shad (chain_blocks c) m ->
      ACONST m -> arelro_lib m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> athr_cells m -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - EGS_STACK -> mem_inv asegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt asegs (egsr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF c exl lo errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ossl_err_get_state_int) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ERRNEW_COST (ph : errphase) (E : errst) : Z := errph_cost ph + as_Cf H (slot_bytes (slot_at E (err_next (es_top E)))).
  Definition errnew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (ph : errphase) (E : errst) (x : ctxinfo) (lo B : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LBN : list block) (c : errchain) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_MPRES H mo (cfg_model k) /\ c4_frame sp tp s' (blocks_ERRST (errst_new E) ++ LBN ++ LB) lo B m' k
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv']
      /\ errph_delta ph LBN c /\ ERRPH (LBN ++ LB) m' (ErrReady c) /\ CTXPH (LBN ++ LB) m' (CtxReady x)
      /\ ERRXR m' c (errst_new E) /\ lib_shad (chain_blocks c) m'
      /\ Forall (fs_scratch H LF) XS /\ xpres H LB (bv_unsigned sp) (XS ++ ERR_XE ++ errph_foot ph) m m'
      /\ as_RFS H LF m' /\ as_AL H s' >= as_AL H s - ERRNEW_COST ph E.
  Definition errnew_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
           (ph : errphase) (E : errst) (x : ctxinfo) (lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs) ->
      as_RHEAP H s (blocks_ERRST E ++ LB) m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes (blocks_ERRST E ++ LB) + errph_bytes ph <= as_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + errph_cnt ph <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ERRNEW_STACK ph -> errph_sh0 ph m lo sp ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> arelro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph aceil -> errph_shad m ph -> CTXPH LB m (CtxReady x) ->
      as_RFS H LF m -> (length LF + ERRPH_LF ph <= AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_errnew ph) (bv_unsigned ra) CH -> errph_closed_ok ph -> ERRNEW_COST ph E <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (errnew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF ph E x lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ERRDEBUG_COST (n1 n2 : Z) : Z := as_Cm H (n1 + n2) + as_Cf H 0.
  Definition errdebug_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (c : errchain) (E : errst) (x : ctxinfo) (line : Z) (fs gs : list byte) (lo B : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (A1 A2 : Z) (p1 p2 : bptr) (XS : list (Z * Z)),
      let n1 := Z.of_nat (length fs) + 1 in let n2 := Z.of_nat (length gs) + 1 in
      let E' := errst_debug E A1 (Some (p1, n1)) line A2 (Some (p2, n2)) in
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_MPRES H mo (cfg_model k) /\ c4_frame sp tp s' (blocks_ERRST E' ++ LB) lo B m' k
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ ablock_range H A1 n1 /\ ablock_range H A2 n2
      /\ ERRPH LB m' (ErrReady c) /\ CTXPH LB m' (CtxReady x)
      /\ ERRXR m' c E' /\ lib_shad (chain_blocks c) m'
      /\ Forall (fs_scratch H LF) XS /\ xpres H LB (bv_unsigned sp) (XS ++ ERRNO_X ++ memflag_foot ++ errph_foot (ErrReady c)) m m'
      /\ as_RFS H LF m' /\ as_AL H s' >= as_AL H s - ERRDEBUG_COST n1 n2.
  Definition errdebug_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
           (c : errchain) (E : errst) (x : ctxinfo) (file line func : Z) (fs fsl gs gsl : list byte) (lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_ERR_set_debug) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 file -> a1 = Z_to_bv 64 line -> a2 = Z_to_bv 64 func -> 0 <= line < 2^31 ->
      AROSTR file fs fsl -> fs <> [] -> Z.of_nat (length fs) < 24 -> 0 < file ->
      AROSTR func gs gsl -> gs <> [] -> Z.of_nat (length gs) < 32 -> 0 < func ->
      slot_empty (slot_at E (es_top E)) ->
      as_RHEAP H s (blocks_ERRST E ++ LB) m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes (blocks_ERRST E ++ LB) + ERRDEBUG_BYTES <= as_LIVE_MAX H -> Z.of_nat (length (blocks_ERRST E ++ LB)) + 2 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ERRDEBUG_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> arelro_lib m ->
      ERRPH LB m (ErrReady c) -> ERRXR m c E -> chain_below c aceil -> lib_shad (chain_blocks c) m -> CTXPH LB m (CtxReady x) ->
      as_RFS H LF m -> (length LF + 1 <= AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) PF_errdebug (bv_unsigned ra) CH ->
      ERRDEBUG_COST (Z.of_nat (length fs) + 1) (Z.of_nat (length gs) + 1) <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (errdebug_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF c E x line fs gs lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition errseterr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (c : errchain) (E : errst) (exl : ctxinfo) (lib reason lo : Z) (errv : word) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (XS : list (Z * Z)),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ Forall (fs_scratch H LF) XS
      /\ munch ((lo, bv_unsigned sp) :: XS ++ [(ARERRNO, ARERRNO + 4); (blk_addr (ec_es c), blk_addr (ec_es c) + ERRST_SIZE)]) m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv]
      /\ CTX_statics m' exl /\ ERR_statics m' c /\ ERR_chain LB m' c /\ lib_shad (chain_blocks c) m'
      /\ ERRST (blocks_ERRST E) m' (blk_addr (ec_es c)) (errst_seterr E lib reason)
      /\ as_RHEAP H s LB m' /\ as_RFS H LF m' /\ ACONST m' /\ arelro_lib m'.
  Definition errseterr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : as_St H) (LB : list block) (LF : list fframe) (c : errchain) (E : errst) (exl : ctxinfo)
           (lib reason lo : Z) (errv : word),
      a0 = Z_to_bv 64 lib -> a1 = Z_to_bv 64 reason -> a2 = Z_to_bv 64 0 -> 0 < lib < 256 -> lib <> 2 -> 0 < reason < 2^23 ->
      tp = Z_to_bv 64 ATP -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
      CTX_statics m exl -> ERR_statics m c -> ERR_chain LB m c -> chain_below c aceil -> chain_sep c -> lib_shad (chain_blocks c) m ->
      ERRST (blocks_ERRST E) m (blk_addr (ec_es c)) E ->
      as_RHEAP H s LB m -> ACONST m -> arelro_lib m -> as_RFS H LF m -> (length LF + 2 <= AFS_MAXLIVE)%nat -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ERRSETERR_STACK -> mem_inv asegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt asegs (errseterr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF c E exl lib reason lo errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ERR_set_error) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ERRCLEAR_COST (ph : errphase) (E : errst) : Z := errph_cost ph + as_Cf H (estr_bytes E).
  Definition errclear_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (ph : errphase) (E : errst) (x : ctxinfo) (lo B : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LBN : list block) (c : errchain) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_MPRES H mo (cfg_model k) /\ c4_frame sp tp s' (LBN ++ LB) lo B m' k          (* [comment removed for export] *)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv']
      /\ errph_delta ph LBN c /\ ERRPH (LBN ++ LB) m' (ErrReady c) /\ CTXPH (LBN ++ LB) m' (CtxReady x)
      /\ ERRXR m' c errst_cleared /\ lib_shad (chain_blocks c) m'
      /\ Forall (fs_scratch H LF) XS /\ xpres H LB (bv_unsigned sp) (XS ++ ERR_XE ++ errph_foot ph) m m'
      /\ as_RFS H LF m' /\ as_AL H s' >= as_AL H s - ERRCLEAR_COST ph E.
  Definition errclear_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
           (ph : errphase) (E : errst) (x : ctxinfo) (lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_ERR_clear_error) fc None m (seg_rom asegs) ->
      as_RHEAP H s (blocks_ERRST E ++ LB) m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes (blocks_ERRST E ++ LB) + errph_bytes ph <= as_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + errph_cnt ph <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ERRCLEAR_STACK ph -> errph_sh0 ph m lo sp ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> arelro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph aceil -> errph_shad m ph -> CTXPH LB m (CtxReady x) ->
      as_RFS H LF m -> (length LF + ERRPH_LF ph <= AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_errclear ph) (bv_unsigned ra) CH -> errph_closed_ok ph -> ERRCLEAR_COST ph E <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (errclear_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF ph E x lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  Definition araise_stmt : Prop :=
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
           (ph : errphase) (E : errst) (x : ctxinfo) (lo B : Z) (errv : word) (CH : list (Z * Z))
           (ra1 ra2 ra3 file line func lib reason : Z) (fs fsl gs gsl : list byte) (Q : config -> Prop),
      (* [comment removed for export] *)
      as_VIS H s msF = MS (mkR (Z_to_bv 64 ra1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs) ->
      as_RHEAP H s (blocks_ERRST E ++ LB) m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes (blocks_ERRST E ++ LB) + raise_bytes ph <= as_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + raise_cnt ph <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - RAISE_STACK ph -> errph_sh0 ph m lo sp ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> arelro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph aceil -> errph_shad m ph -> CTXPH LB m (CtxReady x) ->
      (* [comment removed for export] *)
      as_RFS H LF m -> (length LF + ERRPH_LF ph <= AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_errnew ph) ra1 CH -> pf_ok (as_TR H) PF_errdebug ra2 CH -> pf_ok (as_TR H) PF_errseterr ra3 CH -> errph_closed_ok ph ->
      RAISE_COST ph <= as_AL H s ->
      (* [comment removed for export] *)
      AROSTR file fs fsl -> fs <> [] -> Z.of_nat (length fs) < 24 -> 0 < file ->
      AROSTR func gs gsl -> gs <> [] -> Z.of_nat (length gs) < 32 -> 0 < func ->
      0 <= line < 2^31 -> 0 < lib < 256 -> lib <> 2 -> 0 < reason < 2^23 ->
      0 <= ra1 < 2^64 -> ra1 mod 2 = 0 -> 0 <= ra2 < 2^64 -> ra2 mod 2 = 0 -> 0 <= ra3 < 2^64 -> ra3 mod 2 = 0 ->
      (* [comment removed for export] *)
      (forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), mem_inv asegs m1 ->
         evt asegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                      ms' = MS (mkR (Z_to_bv 64 ra2) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 file) (Z_to_bv 64 line) (Z_to_bv 64 func) c3 c4 c5 c6 c7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 P_ERR_set_debug) fc None m1 (seg_rom asegs))
           (MS (mkR (Z_to_bv 64 ra1) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
               F (ret_pc (Z_to_bv 64 ra1)) fc None m1 (seg_rom asegs))) ->
      (* [comment removed for export] *)
      (forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), mem_inv asegs m1 ->
         evt asegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                      ms' = MS (mkR (Z_to_bv 64 ra3) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 lib) (Z_to_bv 64 reason) (Z_to_bv 64 0) c3 c4 c5 c6 c7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 P_ERR_set_error) fc None m1 (seg_rom asegs))
           (MS (mkR (Z_to_bv 64 ra2) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
               F (ret_pc (Z_to_bv 64 ra2)) fc None m1 (seg_rom asegs))) ->
      (* [comment removed for export] *)
      (forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (msF' : machine_state) (m' : mem) (mo' : Model) (s' : as_St H) (errv' : word)
              (LBN : list block) (c : errchain) (p1 p2 : bptr) (A1 A2 : Z),
         let n1 := Z.of_nat (length fs) + 1 in let n2 := Z.of_nat (length gs) + 1 in
         let E' := errst_raise E A1 p1 n1 line A2 p2 n2 lib reason in
         as_VIS H s' msF' = MS (mkR (Z_to_bv 64 ra3) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                               F (ret_pc (Z_to_bv 64 ra3)) fc None m' (seg_rom asegs) ->
         as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' -> mem_inv asegs m' -> ACONST m' -> stk asegs m' lo (bv_unsigned sp) ->
         as_rauxv_ok H m' B -> as_RHEAP H s' (blocks_ERRST E' ++ LBN ++ LB) m' ->
         MEMFLAG m' 1 -> IMPL_mem m' -> GOT_mem m' -> arelro_lib m' ->
         rw_cells asegs m' (errno_addr tp) [C4 errv'] -> errph_delta ph LBN c -> raise_sizes A1 n1 A2 n2 ->
         ERRPH (LBN ++ LB) m' (ErrReady c) -> CTXPH (LBN ++ LB) m' (CtxReady x) ->
         ERRXR m' c E' -> lib_shad (chain_blocks c) m' ->
         forall XS : list (Z * Z), Forall (fs_scratch H LF) XS ->
         xpres H LB (bv_unsigned sp) (XS ++ ERR_XE ++ memflag_foot ++ errph_foot ph) m m' ->
         as_RFS H LF m' -> as_AL H s' >= as_AL H s - RAISE_COST ph ->
         as_SR H Q (mkCfg msF' mo')) ->
      as_SR H Q (mkCfg msF mo).

  Definition C4_stmts : Prop := egs_ready_stmt /\ egs_stmt /\ errnew_stmt /\ errdebug_stmt /\ errseterr_stmt /\ errclear_stmt.
End W.
End HCW.
