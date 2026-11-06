(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_LibState
     ECH_C0_stmt ECH_C1_stmt ECH_C2_stmt ECH_LibFrame ECH_C4_stmt ECH_C4_rep ECH_C4_frame ECH_C4_frame2 ECH_C4_egs ECH_C4_seterr ECH_C4_new ECH_C4_debug.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma errst_new_top : forall E, es_top (errst_new E) = err_next (es_top E).
Proof. reflexivity. Qed.
Lemma errst_new_slots_len : forall E, length (es_slots E) = 16%nat -> 0 <= es_top E < 16 -> length (es_slots (errst_new E)) = 16%nat.
Proof. intros E L T. unfold errst_new. cbn [es_slots]. rewrite slot_upd_length; [exact L|]. pose proof (err_next_range _ T). lia. Qed.
Lemma errst_new_empty : forall E, length (es_slots E) = 16%nat -> 0 <= es_top E < 16 -> slot_empty (slot_at (errst_new E) (es_top (errst_new E))).
Proof.
  intros E L T. pose proof (err_next_range _ T) as T'. rewrite errst_new_top.
  change (errst_new E) with (es_with_slot (mkERRST (es_slots E) (err_next (es_top E)) (if err_next (es_top E) =? es_bottom E then err_next (es_bottom E) else es_bottom E))
                                          (err_next (es_top E)) (slot_clear (2 ^ 32 - 1))).
  rewrite slot_at_upd; [split; reflexivity| exact L| exact T'].
Qed.
Lemma blocks_new_perm : forall E, length (es_slots E) = 16%nat -> 0 <= es_top E < 16 ->
  Permutation (blocks_ERRST E) (blocks_slot (slot_at E (err_next (es_top E))) ++ blocks_ERRST (errst_new E)).
Proof.
  intros E L T. pose proof (err_next_range _ T) as T'.
  exact (blocks_slots_clear_perm (es_slots E) (Z.to_nat (err_next (es_top E))) (2 ^ 32 - 1) (slot_clear 0) ltac:(lia)).
Qed.
Lemma blocks_seterr : forall E lib reason, length (es_slots E) = 16%nat -> 0 <= es_top E < 16 -> blocks_ERRST (errst_seterr E lib reason) = blocks_ERRST E.
Proof.
  intros E lib reason L T. unfold errst_seterr. cbv zeta. rewrite !blocks_ERRST_slots. cbn [es_slots].
  apply (blocks_slots_upd_same _ _ _ (slot_clear 0)); [lia| reflexivity].
Qed.

Section HC.
  Context {HCEIL : HeapCeil}.
Lemma ERR_chain_LB_mono : forall LIB LIB' m c, ERR_chain LIB m c -> (forall b, In b LIB -> In b LIB') -> ERR_chain LIB' m c.
Proof. intros LIB LIB' m c (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR) SUB. unfold ERR_chain. repeat match goal with |- _ /\ _ => split end; auto. Qed.
(* [comment removed for export] *)
Lemma ERR_chain_reLB : forall LIB LIB' m m' c, ERR_chain LIB' m' c -> ERR_chain LIB m c -> ERR_chain LIB m' c.
Proof.
  intros LIB LIB' m m' c (_ & _ & K2 & _ & _ & K3 & _ & _ & K4 & _) (I2 & Z2 & _ & I3 & Z3 & _ & I4 & Z4 & _ & I5 & Z5 & I6 & Z6 & RR).
  unfold ERR_chain. repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
Lemma ERROWN_LB_mono : forall LB LB' E, ERROWN LB E -> (forall b, In b LB -> In b LB') -> ERROWN LB' E.
Proof.
  intros LB LB' E OW SUB. unfold ERROWN in *. eapply Forall_impl; [| exact OW]. cbn beta. intros sl [O1 O2].
  split; (eapply ofield_LB_mono; [eassumption| exact SUB]).
Qed.
(* [comment removed for export] *)
Lemma ERROWN_seterr : forall LB E lib reason, length (es_slots E) = 16%nat -> 0 <= es_top E < 16 -> ERROWN LB E -> ERROWN LB (errst_seterr E lib reason).
Proof.
  intros LB E lib reason L T OW. unfold ERROWN, errst_seterr in *. cbv zeta. cbn [es_slots].
  pose proof (slot_at_own _ E (es_top E) OW L T) as [O1 O2].
  apply own_slot_upd; [exact OW|]. cbn [sl_file sl_file_o sl_func sl_func_o]. split; assumption.
Qed.
End HC.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis EGS : egs_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.

  Lemma raise_spec :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
           (ph : errphase) (E : errst) (x : ctxinfo) (lo B : Z) (errv : word)
           (ra1 ra2 ra3 file line func lib reason : Z) (fs fsl gs gsl : list byte) (Q : config -> Prop),
      (* [comment removed for export] *)
      hs_RHEAP H s (blocks_ERRST E ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (blocks_ERRST E ++ LB) + raise_bytes ph <= hs_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + raise_cnt ph <= hs_LIVE_CNT_MAX H ->
      lb_big (blocks_ERRST E ++ LB) + errph_big ph <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - RAISE_STACK ph ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> relro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph lo -> CTXPH LB m (CtxReady x) ->
      (* [comment removed for export] *)
      ROSTR file fs fsl -> fs <> [] -> Z.of_nat (length fs) < 24 -> 0 < file ->
      ROSTR func gs gsl -> gs <> [] -> Z.of_nat (length gs) < 32 -> 0 < func ->
      0 <= line < 2^31 -> 0 < lib < 256 -> lib <> 2 -> 0 < reason < 2^23 ->
      0 <= ra1 < 2^64 -> ra1 mod 2 = 0 -> 0 <= ra2 < 2^64 -> ra2 mod 2 = 0 -> 0 <= ra3 < 2^64 -> ra3 mod 2 = 0 ->
      (* [comment removed for export] *)
      (forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), mem_inv rsegs m1 ->
         evt rsegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                      ms' = MS (mkR (Z_to_bv 64 ra2) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 file) (Z_to_bv 64 line) (Z_to_bv 64 func) c3 c4 c5 c6 c7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 P_ERR_set_debug) fc None m1 (seg_rom rsegs))
           (MS (mkR (Z_to_bv 64 ra1) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
               F (ret_pc (Z_to_bv 64 ra1)) fc None m1 (seg_rom rsegs))) ->
      (* [comment removed for export] *)
      (forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), mem_inv rsegs m1 ->
         evt rsegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                      ms' = MS (mkR (Z_to_bv 64 ra3) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 lib) (Z_to_bv 64 reason) (Z_to_bv 64 0) c3 c4 c5 c6 c7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 P_ERR_set_error) fc None m1 (seg_rom rsegs))
           (MS (mkR (Z_to_bv 64 ra2) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
               F (ret_pc (Z_to_bv 64 ra2)) fc None m1 (seg_rom rsegs))) ->
      (* [comment removed for export] *)
      (forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : mem) (mo' : Model) (s' : PState) (errv' : word)
              (LBN : list block) (c : errchain) (p1 p2 : bptr) (A1 A2 : Z),
         let n1 := Z.of_nat (length fs) + 1 in let n2 := Z.of_nat (length gs) + 1 in
         let E' := errst_raise E A1 p1 n1 line A2 p2 n2 lib reason in
         hs_KREL H s' mo' -> hs_MPRES H mo mo' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
         hs_rauxv_ok H m' B -> hs_RHEAP H s' (blocks_ERRST E' ++ LBN ++ LB) m' ->
         MEMFLAG m' 1 -> IMPL_mem m' -> GOT_mem m' -> relro_lib m' ->
         rw_cells rsegs m' (errno_addr tp) [C4 errv'] -> errph_delta ph LBN c -> raise_sizes A1 n1 A2 n2 ->
         ERRPH (LBN ++ LB) m' (ErrReady c) -> CTXPH (LBN ++ LB) m' (CtxReady x) ->
         ERRST (blocks_ERRST E') m' (blk_addr (ec_es c)) E' ->
         xpres LB (bv_unsigned sp) (ERR_X ++ memflag_foot ++ errph_foot ph) m m' ->
         hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 ra3) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                              F (ret_pc (Z_to_bv 64 ra3)) fc None m' (seg_rom rsegs)) mo')) ->
      hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 ra1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom rsegs)) mo).
  Proof.
    intros until Q.
    intros HP KREL BY CN BG AUX SPB SPA ST CEIL LO ERR MI TP MF IM GM RL EP EX EB CP
           RSF FSN FSL FPOS RSG GSN GSL GPOS LNR LIBR LIB2 REAS R1 R1E R2 R2E R3 R3E G1 G2 K.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (STKS : ERRNEW_STACK ph <= RAISE_STACK ph /\ ERRDEBUG_STACK <= RAISE_STACK ph /\ ERRSETERR_STACK <= RAISE_STACK ph) by (unfold RAISE_STACK; lia).
    assert (LOSP : lo <= bv_unsigned sp).
    { destruct STKS as (_ & K2 & _). unfold ERRDEBUG_STACK, FR_ERR_set_debug, CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK in K2. lia. }
    (* [comment removed for export] *)
    eapply (sr_seq H HH).
    { eapply (errnew_spec H HX EGS) with (lo := lo) (B := B) (LB := LB) (s := s) (ph := ph) (E := E) (x := x) (errv := errv); try eassumption; try lia.
      - unfold raise_bytes, ERRDEBUG_BYTES in BY. lia.
      - unfold raise_cnt in CN. lia.
      - rewrite unsigned_lit by lia. exact R1E. }
    intros [ms1 mo1] PO. unfold errnew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & errv1 & s1' & LBN & c &
                    -> & MP1 & (KREL1 & MI1 & ST1 & AUX1 & HP1 & MF1 & IM1 & GM1 & RL1) & ERR1 & DL & EP1 & CP1 & EST1 & XP1).
    (* [comment removed for export] *)
    assert (SHE : length (es_slots E) = 16%nat /\ 0 <= es_top E < 16).
    { destruct ph as [|c0]; cbn [ERRX] in EX; [subst E; split; [reflexivity| cbn; lia]| destruct EX as (K1 & K2 & _); tauto]. }
    destruct SHE as [SLE TRE]. pose proof (errst_new_slots_len E SLE TRE) as SL1.
    set (E1 := errst_new E) in *.
    assert (SUB1 : forall b, In b (LBN ++ LB) -> In b (blocks_ERRST E1 ++ LBN ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    pose proof EP1 as [ES1 EC1]. pose proof CP1 as [CS1 CB1].
    pose proof (chain_below_of_RHEAP H HH _ _ _ _ _ _ _ HP1 SUB1 EC1 CEIL) as CBL.
    (* [comment removed for export] *)
    pose proof (blocks_new_perm E SLE TRE) as PMN. fold E1 in PMN.
    assert (NNEG : 0 <= lb_bytes (blocks_slot (slot_at E (err_next (es_top E))))).
    { apply lb_bytes_nonneg. apply Forall_forall. intros b Hb.
      assert (IB : In b (blocks_ERRST E ++ LB)).
      { apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PMN| apply in_or_app; left; exact Hb]. }
      pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP IB) as RB. unfold rblock_range in RB. lia. }
    pose proof (lb_bytes_perm _ _ PMN) as PB. rewrite lb_bytes_app in PB.
    pose proof (lb_big_perm _ _ PMN) as PG. rewrite lb_big_app in PG.
    pose proof (Permutation_length PMN) as PL. rewrite length_app in PL.
    pose proof (lb_big_nonneg (blocks_slot (slot_at E (err_next (es_top E))))) as NNG.
    assert (DLB : lb_bytes LBN <= errph_bytes ph /\ Z.of_nat (length LBN) <= errph_cnt ph /\ lb_big LBN <= errph_big ph).
    { destruct ph as [|c0]; cbn [errph_delta errph_bytes errph_cnt errph_big] in *; [unfold ERRINIT_BIG; lia| destruct DL as [_ ->]; cbn; lia]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL1| apply (G1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 MI1)|].
    intros ms2 (v0 & v1 & v2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & ->).
    eapply (sr_seq H HH).
    { eapply (errdebug_spec H HX) with (lo := lo) (B := B) (LB := LBN ++ LB) (s := s1') (c := c) (E := E1) (x := x) (fs := fs) (fsl := fsl) (gs := gs) (gsl := gsl) (errv := errv1);
        try eassumption; try reflexivity; try lia.
      - apply errst_new_empty; assumption.
      - rewrite !lb_bytes_app in *. unfold raise_bytes in BY. lia.
      - rewrite !length_app in *. unfold raise_cnt in CN. lia.
      - rewrite !lb_big_app in *. lia.
      - rewrite unsigned_lit by lia. exact R2E. }
    intros [ms3 mo3] PO. unfold errdebug_post in PO. cbn [cfg_ms cfg_model] in PO. cbv zeta in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & errv3 & s3' & A1 & A2 & p1 & p2 &
                    -> & MP3 & (KREL3 & MI3 & ST3 & AUX3 & HP3 & MF3 & IM3 & GM3 & RL3) & ERR3 & RB1 & RB2 & EP3 & CP3 & EST3 & XP3).
    set (n1 := Z.of_nat (length fs) + 1) in *. set (n2 := Z.of_nat (length gs) + 1) in *.
    set (E2 := errst_debug E1 A1 (Some (p1, n1)) line A2 (Some (p2, n2))) in *.
    pose proof EST3 as (SL2 & TR2 & _).
    assert (SUB3 : forall b, In b (LBN ++ LB) -> In b (blocks_ERRST E2 ++ LBN ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    pose proof EP3 as [ES3 EC3]. pose proof CP3 as [CS3 CB3].
    pose proof (chain_below_of_RHEAP H HH _ _ _ _ _ _ _ HP3 SUB3 EC3 CEIL) as CBL3.
    pose proof (chain_sep_of_RHEAP H HH _ _ _ _ _ _ HP3 SUB3 EC3) as CSEP3.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL3| apply (G2 w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 m3 MI3)|].
    intros ms4 (y0 & y1 & y2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & ->).
    set (LBq := blocks_ERRST E2 ++ LBN ++ LB) in *.
    apply ERRST_split in EST3. destruct EST3 as [EM3 OW3].
    eapply (sr_evt_krel H HH); [exact KREL3|
      eapply errseterr_spec with (lo := lo) (LB := LBq) (c := c) (E := E2) (exl := x) (lib := lib) (reason := reason) (errv := errv3);
        try eassumption; try reflexivity; try lia; try (rewrite unsigned_lit by lia; exact R3E)|].
    { eapply ERR_chain_LB_mono; [exact EC3| exact SUB3]. }
    { apply ERRST_split. split; [exact EM3|]. eapply ERROWN_LB_mono; [exact OW3|]. intros b Hb. apply in_or_app. left. exact Hb. }
    intros ms5 PO. unfold errseterr_post in PO.
    destruct PO as (z0 & z1 & z2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & z3 & z4 & z5 & z6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & ERR5 & CS5 & ES5 & EC5 & EST5).
    (* [comment removed for export] *)
    set (bk1 := (p1, A1, n1)) in *.
    assert (IB1 : In bk1 LBq).
    { unfold LBq. apply in_or_app. left. unfold E2, errst_debug. cbv zeta. rewrite blocks_ERRST_slots. cbn [es_slots].
      rewrite blocks_slots_upd. apply in_or_app. right. apply in_or_app. left. cbn. left. reflexivity. }
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP3) as ND3. fold LBq in ND3.
    assert (NB1 : ~ In bk1 (LBN ++ LB)).
    { intros K1. eapply (nodup_map_app_excl blk_id (blocks_ERRST E2) (LBN ++ LB) bk1); [exact ND3| | exact K1].
      unfold E2, errst_debug. cbv zeta. rewrite blocks_ERRST_slots. cbn [es_slots].
      rewrite blocks_slots_upd. apply in_or_app. right. apply in_or_app. left. cbn. left. reflexivity. }
    assert (CW3 : C4W (LBN ++ LB) m3 (ErrReady c) x) by (unfold C4W; cbn [ERRPH CTXPH]; tauto).
    assert (FW5 : Forall (heapw4 c lo (bv_unsigned sp) bk1) [(lo, bv_unsigned sp); (RERRNO, RERRNO + 4); (blk_addr (ec_es c), blk_addr (ec_es c) + ERRST_SIZE)]).
    { unfold heapw4, heapw. constructor; [left; left; cbn; lia|]. constructor; [right; cbn; lia|]. constructor; [left; right; left; cbn; lia| constructor]. }
    destruct (heapw4_world H HH _ _ _ _ m5 _ _ lo (bv_unsigned sp) B _ _ HP3 SUB3 IB1 NB1 CW3 AUX3 CEIL ltac:(lia) SPB MU5 WM5 FW5) as (HP5 & CW5 & AUX5).
    destruct CW5 as (MF5 & IM5 & GM5 & RL5 & EP5 & CP5).
    pose proof (blocks_seterr E2 lib reason SL2 TR2) as BSE.
    (* [comment removed for export] *)
    eapply (K z0 z1 z2 f0 f1 f2 f3 f4 f5 f6 f7 z3 z4 z5 z6 m5 mo3 s3' errv3 LBN c p1 p2 A1 A2); cbv zeta; fold n1 n2;
      change (errst_raise E A1 p1 n1 line A2 p2 n2 lib reason) with (errst_seterr E2 lib reason); try assumption.
    all: lazymatch goal with
         | |- hs_MPRES _ _ _ => eapply (mpres_trans H HH); [exact MP1| exact MP3]
         | |- hs_RHEAP _ _ _ _ => rewrite BSE; exact HP5
         | |- rw_cells _ _ (errno_addr _) _ => subst tp; rewrite ?errno_RATP; exact ERR5
         | |- raise_sizes _ _ _ _ => unfold raise_sizes; split; [exact RB1|]; split; [exact RB2|]; unfold n1, n2, ERRDEBUG_BYTES; lia
         | |- ERRST _ _ _ _ => rewrite BSE; apply ERRST_split in EST5; destruct EST5 as [EM5 _]; apply ERRST_split; split; [exact EM5|];
                               apply ERROWN_seterr; assumption
         | _ => idtac
         end.
    (* [comment removed for export] *)
    { set (X := ERR_X ++ memflag_foot ++ errph_foot ph).
      assert (NCL : forall a, blk_addr (ec_es c) <= a < blk_addr (ec_es c) + ERRST_SIZE -> ~ xclient LB (bv_unsigned sp) X a).
      { intros a Hr HC. eapply (es_not_client H HH _ _ _ _ _ _ _ _ (bv_unsigned sp) (ERR_X ++ memflag_foot) a HP3 EC3 DL ltac:(lia) Hr).
        destruct HC as [HC HXn]. split; [exact HC|]. intros KK. apply HXn. unfold X. rewrite <- app_assoc in KK. exact KK. }
      eapply xpres_trans.
      { eapply xpres_weaken; [exact XP1| lia| auto|]. intros a Ka. unfold X. apply rin_ivs_app in Ka. apply rin_ivs_app. destruct Ka as [Ka|Ka]; [left; exact Ka| right; apply rin_ivs_app; right; exact Ka]. }
      eapply xpres_trans.
      { eapply (xpres_drop_nonclient _ _ X (errph_foot (ErrReady c))).
        - eapply xpres_weaken; [exact XP3| lia| intros b Hb; apply in_or_app; right; exact Hb|].
          intros a Ka. apply rin_ivs_app in Ka. apply rin_ivs_app. destruct Ka as [Ka|Ka]; [left; unfold X; apply rin_ivs_app; right; apply rin_ivs_app; left; exact Ka| right; exact Ka].
        - intros a Ka. cbn in Ka. destruct Ka as [Ka|[]]. apply NCL. exact Ka. }
      eapply xpres_of_munch_gen; [exact MU5| exact WM5|]. intros a Ha HC. unfold RERRNO. cbn.
      assert (RBL : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)).
      { intros b Hb. eapply (HH_RHEAP_block_range H HH); [exact HP3| apply SUB3; apply in_or_app; right; exact Hb]. }
      split; [| split; [| split; [| exact I]]].
      + destruct HC as [[KK|[[KK _]|(b & Hb & Hr)]] _]; [lia| lia|]. pose proof (RBL b Hb) as RB. unfold rblock_range in RB. lia.
      + destruct HC as [[KK|[[_ KK]|(b & Hb & Hr)]] _]; [lia| unfold ralloc_static, RERRNO in KK; lia|]. pose proof (RBL b Hb) as RB. unfold rblock_range in RB. lia.
      + intros Hr. exact (NCL a Hr HC). }
  Qed.
End W.
