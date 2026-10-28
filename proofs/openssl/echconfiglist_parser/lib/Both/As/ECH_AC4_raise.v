(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsWalk AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AKit ECH_AsKit ECH_AKitS ECH_AStmt_C0 ECH_AStmt_C1 ECH_AStmt_C2 ECH_APF_C4 ECH_AStmt_C4 ECH_AC4_rep ECH_AC4_frame ECH_AC4_egs
  ECH_AC4_seterr ECH_AC4_new ECH_AC4_debug ECH_AC4_debugW.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
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
Lemma estrs_ok_seterr : forall E lib reason, length (es_slots E) = 16%nat -> 0 <= es_top E < 16 -> estrs_ok E -> estrs_ok (errst_seterr E lib reason).
Proof.
  intros E lib reason L T OK. unfold estrs_ok, errst_seterr in *. cbv zeta. cbn [es_slots].
  pose proof (slot_at_own _ E (es_top E) OK L T) as [O1 O2].
  apply own_slot_upd; [exact OK|]. cbn [sl_file_o sl_func_o]. split; assumption.
Qed.
Lemma lb_bytes_permR : forall L L', Permutation L L' -> lb_bytes L = lb_bytes L'.
Proof. induction 1; unfold lb_bytes in *; cbn [fold_right] in *; lia. Qed.
Lemma lb_bytes_appR : forall L1 L2, lb_bytes (L1 ++ L2) = lb_bytes L1 + lb_bytes L2.
Proof. induction L1 as [|b L1 IH]; intros L2; unfold lb_bytes in *; cbn [fold_right app]; [lia| rewrite IH; lia]. Qed.
Lemma lb_bytes_nonnegR : forall L, Forall (fun b => 0 <= blk_size b) L -> 0 <= lb_bytes L.
Proof. induction L as [|b L IH]; intros FA; unfold lb_bytes in *; cbn [fold_right]; [lia|]. pose proof (Forall_inv FA). pose proof (IH (Forall_inv_tail FA)). cbn in *. lia. Qed.
Lemma disjoint_from_app : forall W1 W2 A n, disjoint_from W1 A n -> disjoint_from W2 A n -> disjoint_from (W1 ++ W2) A n.
Proof. induction W1 as [|[l h] W1 IH]; intros W2 A n D1 D2; cbn in *; [exact D2|]. destruct D1 as [K D1]. split; [exact K| exact (IH _ _ _ D1 D2)]. Qed.

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
Lemma ERROWN_seterr : forall LB E lib reason, length (es_slots E) = 16%nat -> 0 <= es_top E < 16 -> ERROWN LB E -> ERROWN LB (errst_seterr E lib reason).
Proof.
  intros LB E lib reason L T OW. unfold ERROWN, errst_seterr in *. cbv zeta. cbn [es_slots].
  pose proof (slot_at_own _ E (es_top E) OW L T) as [O1 O2].
  apply own_slot_upd; [exact OW|]. cbn [sl_file sl_file_o sl_func sl_func_o]. split; assumption.
Qed.
End HC.

Lemma rin_ivs_inR : forall (X : list (Z * Z)) iv a, In iv X -> fst iv <= a < snd iv -> rin_ivs X a.
Proof.
  induction X as [|[u v] X IH]; intros iv a Hin Ha; [destruct Hin|]. cbn. destruct Hin as [<-|Hin]; [left; cbn in Ha; lia| right; eapply IH; [exact Hin| exact Ha]].
Qed.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis EGS : egs_stmt H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Let PERM : rheap_perm H := HHx_rheap_perm H HHx.

  Lemma xpres_dropY : forall LB SP X Y m m',
    xpres H LB SP (X ++ Y) m m' -> (forall q, rin_ivs Y q -> ~ xclient H LB SP X q) -> xpres H LB SP X m m'.
  Proof.
    intros LB SP X Y m m' XP HY q Hq HXq. apply XP; [exact Hq|]. destruct HXq as [HC HX]. split; [exact HC|].
    intros Kq. apply rin_ivs_app in Kq. destruct Kq as [Kq|Kq]; [exact (HX Kq)| exact (HY _ Kq (conj HC HX))].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dj_low_se : forall LF m0 XS lo hi es A n,
    as_RFS H LF m0 -> Forall (fs_scratch H LF) XS -> aceil <= lo -> AIMG_TOP <= es -> A + n <= AIMG_TOP ->
    (A + n <= ARERRNO \/ ARERRNO + 4 <= A) ->
    disjoint_from ((lo, hi) :: XS ++ [(ARERRNO, ARERRNO + 4); (es, es + ERRST_SIZE)]) A n.
  Proof.
    intros LF m0 XS lo hi es A n R FXS CE ES HA HE. acb. cbn [disjoint_from app]. split; [unfold AIMG_TOP in *; lia|].
    apply disjoint_from_app.
    - clear - FXS R HA HH. induction XS as [|[wl wh] XS IH]; [exact I|]. cbn. pose proof (fs_scratch_range H HH _ _ _ R (Forall_inv FXS)) as K. cbn in K.
      split; [lia| exact (IH (Forall_inv_tail FXS))].
    - cbn. split; [lia|]. split; [lia| exact I].
  Qed.
  (* [comment removed for export] *)
  Lemma dj_blk_se : forall s L m0 LBx LF m1 XS lo hi es b k,
    as_RHEAP H s L m0 -> (forall b, In b LBx -> In b L) -> In es L -> blk_size es = ERRST_SIZE -> In b LBx -> blk_size b <> ERRST_SIZE ->
    as_RFS H LF m1 -> Forall (fs_scratch H LF) XS -> aceil <= lo -> 0 <= k <= blk_size b ->
    disjoint_from ((lo, hi) :: XS ++ [(ARERRNO, ARERRNO + 4); (blk_addr es, blk_addr es + ERRST_SIZE)]) (blk_addr b) k.
  Proof.
    intros s L m0 LBx LF m1 XS lo hi es b k HP SUB IES ZES Hb NE R FXS CE Hk. acb.
    pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as BR. pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    cbn [disjoint_from app]. split; [lia|]. apply disjoint_from_app.
    - clear - FXS R BR Hk HH. induction XS as [|[wl wh] XS IH]; [exact I|]. cbn.
      pose proof (scr_ok_obj H HH _ _ _ _ _ R (or_introl (Forall_inv FXS)) BR ltac:(lia)) as [K _]. cbn in K.
      split; [lia| exact (IH (Forall_inv_tail FXS))].
    - cbn. split; [unfold ARERRNO, ATP, AIMG_TOP in *; lia|]. split; [| exact I].
      pose proof (ablocks_apart_by_size H HH _ _ _ _ _ HP (SUB _ Hb) IES ltac:(rewrite ZES; exact NE)) as D. rewrite ZES in D. unfold ERRST_SIZE in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma magree_strings_se : forall s L m0 Lx LF m1 XS lo hi es m m',
    as_RHEAP H s L m0 -> (forall b, In b Lx -> In b L) -> In es L -> blk_size es = ERRST_SIZE -> (forall b, In b Lx -> 0 <= blk_size b <= 32) ->
    as_RFS H LF m1 -> Forall (fs_scratch H LF) XS -> aceil <= lo ->
    munch ((lo, hi) :: XS ++ [(ARERRNO, ARERRNO + 4); (blk_addr es, blk_addr es + ERRST_SIZE)]) m m' -> wmono asegs m m' ->
    magree (lib_addr Lx) m m'.
  Proof.
    intros s L m0 Lx LF m1 XS lo hi es m m' HP SUB IES ZES SMALL R FXS CE MU WM. acb.
    pose proof (ah_blocks H HH _ _ _ _ HP IES) as EB. rewrite ZES in EB. pose proof EB as (E1 & E2 & E3 & E4 & E5 & E6 & E7). unfold ERRST_SIZE in *.
    eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha. clear MU WM.
    assert (TAIL : outside [(ARERRNO, ARERRNO + 4); (blk_addr es, blk_addr es + 904)] a).
    { cbn. unfold ARERRNO, ATP. destruct Ha as [HX|[(b & Hb & Hr)|(b & Hb & Hr)]].
      - pose proof (LIBX_below _ HX). split; [| split; [unfold AIMG_TOP in *; lia| exact I]].
        revert HX. unfold LIBX, LIBX0, LIBXW. cbn [rin_ivs fst snd app]. lia.
      - pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
        pose proof (ablocks_apart_by_size H HH _ _ _ _ _ HP (SUB _ Hb) IES ltac:(rewrite ZES; pose proof (SMALL _ Hb); lia)) as D. rewrite ZES in D.
        split; [unfold AIMG_TOP in *; lia|]. split; [lia| exact I].
      - pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
        pose proof (sh_aapp_range _ _ B7 B3) as (S1 & S2 & S3).
        assert (S0 : ASHADOW_BASE <= sh (blk_addr b)) by (unfold sh; Z.div_mod_to_equations; lia). rewrite ASHADOW_BASE_val in S0.
        pose proof (aapp_not_shadowland _ _ E7). unfold ALOWSH_LO, AHI_LO in *. split; [lia|]. split; [lia| exact I]. }
    cbn [outside app]. split.
    - destruct Ha as [HX|[(b & Hb & Hr)|(b & Hb & Hr)]].
      + pose proof (LIBX_below _ HX). unfold AIMG_TOP in *. lia.
      + pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & _ & _ & B5 & _). lia.
      + pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & B3 & _ & _ & _ & B7).
        pose proof (sh_aapp_range _ _ B7 B3) as (_ & S2 & _). assert (SC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; lia). lia.
    - revert TAIL. induction XS as [|iv XS IH]; intros TAIL; [exact TAIL|]. destruct iv as [wl wh]. cbn. split; [| exact (IH (Forall_inv_tail FXS) TAIL)].
      pose proof (Forall_inv FXS) as SC.
      destruct Ha as [HX|[(b & Hb & Hr)|(b & Hb & Hr)]].
      + exact (scr_ok_libx H HH _ _ _ _ R (or_introl SC) HX).
      + pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as BR. pose proof BR as (_ & _ & B3 & _).
        pose proof (scr_ok_obj H HH _ _ _ _ _ R (or_introl SC) BR B3) as [D _]. cbn [fst snd] in D. lia.
      + pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as BR. pose proof BR as (_ & _ & B3 & _).
        pose proof (scr_ok_obj H HH _ _ _ _ _ R (or_introl SC) BR B3) as [_ D]. cbn [fst snd] in D. lia.
  Qed.

  Lemma araise_spec : araise_stmt H.
  Proof.
    unfold araise_stmt. intros until Q.
    intros VIS HP KREL BY CN AUX SPB SPA ST CEIL LO SH0 ERR MI TP AC MF IM GM RL EP EX EB ESH CP RFS LFN CHN CHS PF1 PF2 PF3 ECL AL
           RSF FSN FSL FPOS RSG GSN GSL GPOS LNR LIBR LIB2 REAS R1 R1E R2 R2E R3 R3E G1 G2 K.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range s0) as S0R. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (STKS : ERRNEW_STACK ph <= RAISE_STACK ph /\ ERRDEBUG_STACK <= RAISE_STACK ph /\ ERRSETERR_STACK + 16 <= RAISE_STACK ph) by (unfold RAISE_STACK; lia).
    assert (LOSP : lo + 96 + 8240 <= bv_unsigned sp).
    { destruct STKS as (_ & K2 & _). unfold ERRDEBUG_STACK, FR_ERR_set_debug, CMALLOC_STACK, FR_CRYPTO_malloc, AMALLOC_STACK, EGS_STACK in K2. lia. }
    set (SB := blocks_ERRST E) in *.
    (* [comment removed for export] *)
    assert (SHE : length (es_slots E) = 16%nat /\ 0 <= es_top E < 16 /\ estrs_ok E).
    { destruct ph as [|c0]; cbn [ERRX] in EX.
      - subst E. split; [reflexivity|]. split; [cbn; lia|]. unfold estrs_ok, errst_zero. cbn [es_slots].
        apply Forall_forall. intros sl Hsl. apply repeat_spec in Hsl. subst sl. cbn. lia.
      - destruct EX as ((K1 & K2 & _) & K3 & _). split; [exact K1|]. split; [exact K2| exact K3]. }
    destruct SHE as (SLE & TRE & ESZ). pose proof (errst_new_slots_len E SLE TRE) as SL1.
    pose proof (err_next_range _ TRE) as TRE'.
    pose proof (slot_at_own _ E (err_next (es_top E)) ESZ SLE TRE') as [SZf SZg].
    (* [comment removed for export] *)
    pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & CMS & CFS).
    assert (CFZ : as_Cf H 0 = 0) by (pose proof (CFS 0 0 ltac:(lia) ltac:(lia)) as K0; change (0 + 0) with 0 in K0; pose proof (CF0 0 ltac:(lia)); lia).
    assert (KEYC : ERRNEW_COST H ph E + as_Cm H ERRDEBUG_BYTES <= RAISE_COST H ph).
    { unfold ERRNEW_COST, RAISE_COST, raise_bytes, slot_bytes. set (sb := oszb (sl_file_o (slot_at E (err_next (es_top E)))) + oszb (sl_func_o (slot_at E (err_next (es_top E))))).
      assert (SBR : 0 <= sb <= ERRDEBUG_BYTES) by (unfold sb, ERRDEBUG_BYTES; lia).
      destruct ph as [|c0]; cbn [errph_cost errph_bytes].
      - unfold ERRINIT_COST. pose proof (CMS ERRINIT_BYTES ERRDEBUG_BYTES ltac:(unfold ERRINIT_BYTES; lia) ltac:(unfold ERRDEBUG_BYTES; lia)).
        pose proof (CFS ERRINIT_BYTES sb ltac:(unfold ERRINIT_BYTES; lia) ltac:(lia)).
        pose proof (CFM (ERRINIT_BYTES + sb) (ERRINIT_BYTES + ERRDEBUG_BYTES) ltac:(unfold ERRINIT_BYTES; lia)). lia.
      - change (0 + ERRDEBUG_BYTES) with ERRDEBUG_BYTES. pose proof (CFM sb ERRDEBUG_BYTES ltac:(lia)). lia. }
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (aerrnew_spec H HHx EGS) with (ph := ph) (E := E) (lo := lo) (B := B) (LB := LB) (s := s) (x := x) (errv := errv) (LF := LF) (CH := CH);
        [ exact VIS| exact HP| exact KREL
        | fold SB; unfold raise_bytes, ERRDEBUG_BYTES in BY; lia| fold SB; unfold raise_cnt in CN; lia
        | exact AUX| exact SPB| exact SPA| exact ST| exact CEIL| lia| exact SH0
        | exact ERR| exact MI| exact TP| exact AC| exact MF| exact IM| exact GM| exact RL| exact EP| exact EX| exact EB| exact ESH| exact CP
        | exact RFS| exact LFN| exact CHN| exact CHS| rewrite unsigned_lit by lia; exact PF1| exact ECL
        | pose proof (CM0 ERRDEBUG_BYTES ltac:(unfold ERRDEBUG_BYTES; lia)); lia
        | rewrite unsigned_lit by lia; exact R1E ]. }
    intros [ms1 mo1] PO. unfold errnew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & errv1 & s1' & LBN & c & XS1 &
                    VIS1 & MP1 & (KREL1 & MI1 & AC1 & ST1 & AUX1 & HP1 & MF1 & IM1 & GM1 & RL1) & ERR1 & DL & EP1 & CP1 & EXR1 & LS1 & FXS1 & XP1 & RFS1 & AL1).
    set (E1 := errst_new E) in *.
    assert (SUB1 : forall b, In b (LBN ++ LB) -> In b (blocks_ERRST E1 ++ LBN ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    pose proof EP1 as [ES1 EC1]. pose proof CP1 as [CS1 CB1]. pose proof EC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    set (es := blk_addr (ec_es c)) in *.
    pose proof (ah_blocks H HH _ _ _ _ HP1 (SUB1 _ I5)) as BR5. rewrite Z5 in BR5. fold es in BR5. unfold ERRST_SIZE in BR5.
    pose proof BR5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). pose proof (aapp_bounds _ _ Q7 ltac:(lia)) as (_ & _ & T5 & _). unfold AAPP_HI in T5.
    assert (CBL : chain_below c aceil).
    { pose proof EC1 as (I2 & Z2 & _ & I3 & Z3 & _ & I4 & Z4 & _ & _ & _ & I6 & Z6 & _). unfold chain_below.
      pose proof (ah_blocks H HH _ _ _ _ HP1 (SUB1 _ I2)) as (_ & _ & _ & _ & K2 & _). pose proof (ah_blocks H HH _ _ _ _ HP1 (SUB1 _ I3)) as (_ & _ & _ & _ & K3 & _).
      pose proof (ah_blocks H HH _ _ _ _ HP1 (SUB1 _ I4)) as (_ & _ & _ & _ & K4 & _).
      pose proof (ah_blocks H HH _ _ _ _ HP1 (SUB1 _ I2)) as (P2 & _). pose proof (ah_blocks H HH _ _ _ _ HP1 (SUB1 _ I3)) as (P3 & _).
      pose proof (ah_blocks H HH _ _ _ _ HP1 (SUB1 _ I4)) as (P4 & _).
      rewrite Z2 in K2. rewrite Z3 in K3. rewrite Z4 in K4. fold es. unfold ERRST_SIZE. lia. }
    (* [comment removed for export] *)
    pose proof (blocks_new_perm E SLE TRE) as PMN. fold E1 in PMN. fold SB in PMN.
    assert (NNEG : 0 <= lb_bytes (blocks_slot (slot_at E (err_next (es_top E))))).
    { apply lb_bytes_nonnegR. apply Forall_forall. intros b Hb.
      assert (IB : In b (SB ++ LB)) by (apply in_or_app; left; eapply Permutation_in; [apply Permutation_sym; exact PMN| apply in_or_app; left; exact Hb]).
      pose proof (ah_blocks H HH _ _ _ _ HP IB) as (_ & _ & K3 & _). exact K3. }
    pose proof (lb_bytes_permR _ _ PMN) as PB. rewrite lb_bytes_appR in PB.
    pose proof (Permutation_length PMN) as PL. rewrite length_app in PL.
    assert (DLB : lb_bytes LBN <= errph_bytes ph /\ Z.of_nat (length LBN) <= errph_cnt ph).
    { destruct ph as [|c0]; cbn [errph_delta errph_bytes errph_cnt] in *; [lia| destruct DL as [_ ->]; cbn; lia]. }
    (* [comment removed for export] *)
    assert (CHN1 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (ah_chain_ext H HH); [exact CHN|]. intros fp' ra' a Hin Ha. pose proof (ah_chain_range H HH _ _ _ _ _ CHN Hin) as (W1 & _). specialize (CHS _ _ Hin).
      apply XP1; [lia| split; [left; lia|]]. apply (rin_ivs_off _ a). apply Forall_app. split.
      - eapply Forall_impl; [| exact FXS1]. intros iv SC. pose proof (fs_scratch_range H HH _ _ _ RFS SC). lia.
      - apply Forall_app. split.
        + unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key,
            A_master_once_ret, A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf,
            A_keys, A_next_key, A_key_lock, A_tsd_main.
          cbn [app]. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
        + destruct ph as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. apply Forall_cons; [cbn [fst snd]| apply Forall_nil].
          cbn [errph_delta] in DL. destruct DL as [-> _]. fold es. unfold ERRST_SIZE. lia. }
    assert (CHS1 : forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') by exact CHS.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| apply (G1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 MI1)|].
    intros msF2 mo2 KREL2 MP2 (v0 & v1 & v2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & VIS2).
    set (n1 := Z.of_nat (length fs) + 1) in *. set (n2 := Z.of_nat (length gs) + 1) in *.
    eapply (ah_seq H HH).
    { eapply (aerrdebug_spec H HHx) with (lo := lo) (B := B) (LB := LBN ++ LB) (s := s1') (c := c) (E := E1) (x := x) (fs := fs) (fsl := fsl) (gs := gs) (gsl := gsl)
                                        (errv := errv1) (LF := LF) (CH := CH) (file := file) (line := line) (func := func);
        [ exact VIS2| reflexivity| reflexivity| reflexivity| exact LNR| exact RSF| exact FSN| exact FSL| exact FPOS| exact RSG| exact GSN| exact GSL| exact GPOS
        | apply errst_new_empty; assumption
        | exact HP1| exact KREL2
        | rewrite !lb_bytes_appR in *; unfold raise_bytes in BY; lia
        | rewrite !length_app in *; unfold raise_cnt in CN; lia
        | exact AUX1| exact SPB| exact SPA| exact ST1| exact CEIL| lia
        | exact ERR1| exact MI1| exact TP| exact AC1| exact MF1| exact IM1| exact GM1| exact RL1| exact EP1| exact EXR1| exact CBL| exact LS1| exact CP1
        | exact RFS1| destruct ph; cbn [ERRPH_LF] in LFN; lia| exact CHN1| exact CHS1
        | rewrite unsigned_lit by lia; exact PF2
        | fold n1 n2; unfold ERRDEBUG_COST; pose proof (CMM (n1 + n2) ERRDEBUG_BYTES ltac:(unfold n1, n2, ERRDEBUG_BYTES; lia)); lia
        | rewrite unsigned_lit by lia; exact R2E ]. }
    intros [ms3 mo3] PO. unfold errdebug_post in PO. cbn [cfg_ms cfg_model] in PO. cbv zeta in PO. fold n1 n2 in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & errv3 & s3' & A1 & A2 & p1 & p2 & XS3 &
                    VIS3 & MP3 & (KREL3 & MI3 & AC3 & ST3 & AUX3 & HP3 & MF3 & IM3 & GM3 & RL3) & ERR3 & RB1 & RB2 & EP3 & CP3 & EXR3 & LS3 & FXS3 & XP3 & RFS3 & AL3).
    set (E2 := errst_debug E1 A1 (Some (p1, n1)) line A2 (Some (p2, n2))) in *.
    destruct EXR3 as (EST3 & ESZ3 & ESH3 & ESC3). pose proof EST3 as (SL2 & TR2 & _).
    assert (SUB3 : forall b, In b (LBN ++ LB) -> In b (blocks_ERRST E2 ++ LBN ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    pose proof EP3 as [ES3 EC3]. pose proof CP3 as [CS3 CB3].
    pose proof (chain_sep_of_RHEAP H HH _ _ _ _ m3 _ HP3 SUB3 EC3) as CSEP3.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| apply (G2 w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 m3 MI3)|].
    intros msF4 mo4 KREL4 MP4 (y0 & y1 & y2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & VIS4).
    set (LBq := blocks_ERRST E2 ++ LBN ++ LB) in *.
    apply ERRST_split in EST3. destruct EST3 as [EM3 OW3].
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4
      | eapply (aerrseterr_spec H HHx) with (lo := lo) (LB := LBq) (c := c) (E := E2) (exl := x) (lib := lib) (reason := reason) (errv := errv3) (LF := LF) (s := s3');
        [ reflexivity| reflexivity| reflexivity| exact LIBR| exact LIB2| exact REAS| exact TP| exact ERR3| exact CS3| exact ES3
        | eapply ERR_chain_LB_mono; [exact EC3| exact SUB3]
        | exact CBL| exact CSEP3| exact LS3
        | apply ERRST_split; split; [exact EM3| exact OW3]
        | exact HP3| exact AC3| exact RL3| exact RFS3| destruct ph; cbn [ERRPH_LF] in LFN; lia| exact SPA| exact ST3| exact CEIL| lia| exact MI3
        | rewrite unsigned_lit by lia; exact R3E ]|].
    intros msF5 mo5 KREL5 MP5 PO. unfold errseterr_post in PO.
    destruct PO as (z0 & z1 & z2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & z3 & z4 & z5 & z6 & m5 & XS5 & VIS5 & FXS5 & MU5 & WM5 & MI5 & ST5 & ERR5 & CS5 & ES5 & EC5 & LS5 & EST5 & HP5 & RFS5 & AC5 & RL5).
    cbn [app] in MU5.
    (* [comment removed for export] *)
    pose proof (ah_nodup H HH _ _ _ HP3) as ND3.
    assert (I5q : In (ec_es c) LBq) by (apply SUB3; exact I5).
    assert (ESZ4 := estrs_ok_seterr E2 lib reason SL2 TR2 ESZ3). pose proof (blocks_seterr E2 lib reason SL2 TR2) as BSE.
    assert (DJL : forall A n, A + n <= AIMG_TOP -> (A + n <= ARERRNO \/ ARERRNO + 4 <= A) ->
              disjoint_from ((lo, bv_unsigned sp) :: XS5 ++ [(ARERRNO, ARERRNO + 4); (es, es + ERRST_SIZE)]) A n).
    { intros A n K1 K2. eapply dj_low_se; [exact RFS3| exact FXS5| exact CEIL| exact Q4| exact K1| exact K2]. }
    assert (MF5 : MEMFLAG m5 1).
    { destruct MF3 as (fb & MFa & MFb). exists fb. split; [| exact MFb]. eapply rw_cells_transport; [exact MFa| exact MU5| exact WM5|].
      apply DJL; unfold A_mem_inited, AIMG_TOP, ARERRNO, ATP; cbn; lia. }
    assert (IM5 : IMPL_mem m5).
    { destruct IM3 as (IMa & IMb & IMc). unfold IMPL_mem.
      split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU5| exact WM5|]; apply DJL; unfold A_malloc_impl, A_realloc_impl, A_free_impl, AIMG_TOP, ARERRNO, ATP; cbn; lia). }
    assert (GM5 : GOT_mem m5).
    { unfold GOT_mem in *. eapply rw_cells_transport; [exact GM3| exact MU5| exact WM5|]. apply DJL; unfold A_got_CRYPTO_malloc, AIMG_TOP, ARERRNO, ATP; cbn; lia. }
    assert (AUX5 : as_rauxv_ok H m5 B).
    { eapply (ah_rauxv_frame H HH) with (LB := LBq); [exact AUX3| exact MU5| exact WM5|].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_app. split; [eapply (fs_scratch_write_ok_Forall H); exact FXS5|].
      apply Forall_cons; [right; left; unfold aimg_client_w, ARERRNO, ATLS_PRIV_LO, ATP; cbn [fst snd]; lia|].
      apply Forall_cons; [| apply Forall_nil]. right; right; left. exists (ec_es c). split; [exact I5q| rewrite Z5; cbn [fst snd]; fold es; lia]. }
    assert (CB5 : CTX_blocks (LBN ++ LB) m5 x).
    { destruct CB3 as [EXL OTH]. split; [| exact OTH]. pose proof EXL as (XI & XZ & _ & _).
      eapply EXLOCK_munch; [exact EXL| exact MU5| exact WM5|].
      eapply (dj_blk_se s3' LBq m3 (LBN ++ LB)); [exact HP3| exact SUB3| exact I5q| exact Z5| exact XI| rewrite XZ; unfold MUTEX_SIZE, ERRST_SIZE; lia
                                                | exact RFS3| exact FXS5| exact CEIL| rewrite XZ; unfold MUTEX_SIZE; lia]. }
    assert (AGS : magree (lib_addr (blocks_ERRST E2)) m3 m5).
    { eapply (magree_strings_se s3' LBq m3); [exact HP3| intros b Hb; unfold LBq; apply in_or_app; left; exact Hb| exact I5q| exact Z5
        | intros b Hb; exact (estrs_pos _ _ ESZ3 Hb)| exact RFS3| exact FXS5| exact CEIL| exact MU5| exact WM5]. }
    destruct (estrs_agree (blocks_ERRST E2) m3 m5 E2 (fun b Hb => Hb) (fun b Hb => proj1 (estrs_pos _ _ ESZ3 Hb)) AGS ESH3 ESC3) as [ESH5 ESC5].
    (* [comment removed for export] *)
    set (XS := XS1 ++ XS3 ++ XS5). set (X := XS ++ ERR_XE ++ memflag_foot ++ errph_foot ph).
    assert (FXS : Forall (fs_scratch H LF) XS) by (unfold XS; apply Forall_app; split; [exact FXS1| apply Forall_app; split; [exact FXS3| exact FXS5]]).
    assert (NCL : forall a, es <= a < es + 904 -> ~ xclient H LB (bv_unsigned sp) X a).
    { intros a Hr [HC HXn].
      destruct HC as [Ka|[Ka|[(b & Hb & Hrb)|[(b & Hb & Hrb)|[Ka|[Ka|Ka]]]]]].
      - lia.
      - unfold aimg_client, AIMG_TOP in *. lia.
      - assert (NN : ~ (blk_id b <> blk_id (ec_es c))).
        { intros NE. pose proof (ah_disj H HH _ _ _ _ _ HP3 (SUB3 _ (in_or_app _ _ _ (or_intror Hb))) I5q NE) as DJ.
          rewrite Z5 in DJ. fold es in DJ. unfold ERRST_SIZE in DJ. lia. }
        apply NN. intros EQid.
        pose proof (nodup_id_inj _ _ _ ND3 (SUB3 _ (in_or_app _ _ _ (or_intror Hb))) I5q EQid) as EQB. subst b.
        destruct ph as [|cq]; cbn [errph_delta errph_foot] in *.
        + destruct DL as (_ & _ & FA). pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail FA)))) as IN5.
          pose proof (ah_nodup H HH _ _ _ HP1) as ND1.
          assert (NDx : List.NoDup (map blk_id (LBN ++ LB))) by (rewrite map_app in ND1; eapply NoDup_app_remove_l; exact ND1).
          eapply (nodup_map_app_excl blk_id LBN LB (ec_es c)); [exact NDx| exact IN5| exact Hb].
        + destruct DL as [-> _]. apply HXn. unfold X. apply rin_ivs_app. right. apply rin_ivs_app. right. apply rin_ivs_app. right. cbn. left. fold es. unfold ERRST_SIZE. lia.
      - pose proof (ah_blocks H HH _ _ _ _ HP3 (SUB3 _ (in_or_app _ _ _ (or_intror Hb)))) as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
        pose proof (aapp_bounds _ _ W7 W3) as (_ & _ & T1 & _).
        pose proof (aapp_disjoint_sh es 904 (blk_addr b) (blk_size b) Q7 ltac:(lia) ltac:(lia) W3). lia.
      - pose proof (RFS_fsb H HH _ _ RFS3) as (F1 & F2 & F3 & F4). unfold AFS_SIZE in *. lia.
      - pose proof (RFS_fsb H HH _ _ RFS3) as (F1 & F2 & F3 & F4). unfold AIMG_TOP in F1.
        pose proof (aapp_bounds _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (U1 & U2 & U3 & U4 & _).
        pose proof (aapp_disjoint_sh es 904 (as_FSB H) AFS_SIZE Q7 ltac:(lia) ltac:(lia) ltac:(unfold AFS_SIZE; lia)) as D.
        clear - D Ka Hr F3. unfold sh, nsh, AFS_SIZE in *. Z.div_mod_to_equations. lia.
      - clear - Ka Hr Q7 ACEILB. unfold aapp, aapp_lo, aapp_hi, AHI_LO, ALOWSH_LO, AIMG_TOP, sh in *. rewrite ASHADOW_BASE_val in Ka. lia. }
    (* [comment removed for export] *)
    assert (XPALL : xpres H LB (bv_unsigned sp) X m m5).
    { eapply xpres_trans.
      { eapply xpres_weaken; [exact XP1| lia| auto|]. intros a Ka. unfold X, XS.
        apply rin_ivs_app in Ka. destruct Ka as [Ka|Ka]; [apply rin_ivs_app; left; apply rin_ivs_app; left; exact Ka|].
        apply rin_ivs_app in Ka. destruct Ka as [Ka|Ka]; [apply rin_ivs_app; right; apply rin_ivs_app; left; exact Ka|].
        apply rin_ivs_app; right; apply rin_ivs_app; right; apply rin_ivs_app; right; exact Ka. }
      eapply xpres_trans.
      { eapply (xpres_dropY LB (bv_unsigned sp) X [(es, es + ERRST_SIZE)]).
        - eapply xpres_weaken; [exact XP3| lia| intros b Hb; apply in_or_app; right; exact Hb|].
          intros a Ka. apply rin_ivs_app in Ka. destruct Ka as [Ka|Ka]; [apply rin_ivs_app; left; unfold X, XS; apply rin_ivs_app; left; apply rin_ivs_app; right; apply rin_ivs_app; left; exact Ka|].
          apply rin_ivs_app in Ka. destruct Ka as [Ka|Ka]; [apply rin_ivs_app; left; unfold X; apply rin_ivs_app; right; apply rin_ivs_app; left; unfold ERR_XE; apply rin_ivs_app; left; exact Ka|].
          apply rin_ivs_app in Ka. destruct Ka as [Ka|Ka]; [apply rin_ivs_app; left; unfold X; apply rin_ivs_app; right; apply rin_ivs_app; right; apply rin_ivs_app; left; exact Ka|].
          apply rin_ivs_app; right; exact Ka.
        - intros a Ka. cbn in Ka. destruct Ka as [Ka|[]]. apply NCL. fold es in Ka. unfold ERRST_SIZE in Ka. lia. }
      eapply (xpres_dropY LB (bv_unsigned sp) X [(es, es + ERRST_SIZE)]); [| intros a Ka; cbn in Ka; destruct Ka as [Ka|[]]; apply NCL; unfold ERRST_SIZE in Ka; lia].
      eapply (xpres_weaken H LBq LB); [| apply Z.le_refl| intros b Hb; apply SUB3; apply in_or_app; right; exact Hb| intros ax Kx; exact Kx].
      eapply (xpres_of_munch H s3' LBq); [exact HH| exact HP3| exact MU5| exact WM5|].
      apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_app. split.
      - apply Forall_forall. intros iv Hiv. right. intros a Ha. apply rin_ivs_app. left. unfold X, XS. apply rin_ivs_app. left. apply rin_ivs_app. right. apply rin_ivs_app. right.
        eapply rin_ivs_inR; [exact Hiv| exact Ha].
      - apply Forall_cons; [right; intros a Ha; apply rin_ivs_app; left; unfold X; apply rin_ivs_app; right; apply rin_ivs_app; left; unfold ERR_XE, ERRNO_X; apply rin_ivs_app; left; cbn; cbn in Ha; left; lia|].
        apply Forall_cons; [right; intros a Ha; apply rin_ivs_app; right; cbn; cbn in Ha; left; fold es; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    assert (RSZ : raise_sizes A1 n1 A2 n2).
    { unfold raise_sizes. pose proof RB1 as (Y1 & _ & Y3 & _). pose proof RB2 as (Y1' & _ & Y3' & _).
      assert (1 <= n1 /\ 1 <= n2) by (unfold n1, n2; lia). unfold n1, n2 in *. lia. }
    eapply (K z0 z1 z2 f0 f1 f2 f3 f4 f5 f6 f7 z3 z4 z5 z6 msF5 m5 mo5 s3' errv3 LBN c p1 p2 A1 A2).
    all: cbv zeta; fold n1 n2; try change (errst_raise E A1 p1 n1 line A2 p2 n2 lib reason) with (errst_seterr E2 lib reason).
    all: lazymatch goal with
         | |- as_VIS _ _ _ = _ => exact VIS5
         | |- as_AKREL _ _ _ => exact KREL5
         | |- as_MPRES _ _ _ => eapply (ah_mpres_trans H HH); [exact MP1|]; eapply (ah_mpres_trans H HH); [exact MP2|]; eapply (ah_mpres_trans H HH); [exact MP3|];
                                eapply (ah_mpres_trans H HH); [exact MP4| exact MP5]
         | |- mem_inv _ _ => exact MI5
         | |- ACONST _ => exact AC5
         | |- stk _ _ _ _ => exact ST5
         | |- as_rauxv_ok _ _ _ => exact AUX5
         | |- as_RHEAP _ _ _ _ => rewrite BSE; exact HP5
         | |- MEMFLAG _ _ => exact MF5
         | |- IMPL_mem _ => exact IM5
         | |- GOT_mem _ => exact GM5
         | |- arelro_lib _ => exact RL5
         | |- rw_cells _ _ (errno_addr _) _ => exact ERR5
         | |- errph_delta _ _ _ => exact DL
         | |- raise_sizes _ _ _ _ => exact RSZ
         | |- ERRPH _ _ _ => split; [exact ES5| eapply ERR_chain_reLB; [exact EC5| exact EC3]]
         | |- CTXPH _ _ _ => split; [exact CS5| exact CB5]
         | |- ERRXR _ _ _ => split; [rewrite BSE; exact EST5|]; split; [exact ESZ4|]; split; [rewrite BSE; exact ESH5| unfold estrs_cells; rewrite BSE; exact ESC5]
         | |- lib_shad _ _ => exact LS5
         | |- Forall _ _ => exact FXS
         | |- xpres _ _ _ _ _ _ => exact XPALL
         | |- as_RFS _ _ _ => exact RFS5
         | |- _ >= _ => unfold ERRDEBUG_COST in AL3; pose proof (CMM (n1 + n2) ERRDEBUG_BYTES ltac:(unfold n1, n2, ERRDEBUG_BYTES; lia)); lia
         end.
  Qed.
End W.
