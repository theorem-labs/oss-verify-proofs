(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsWalk AsAtomics AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AKit ECH_AsKit ECH_AKitS ECH_AStmt_C0 ECH_AStmt_C1 ECH_AC1_free ECH_AC1_freeopt ECH_AStmt_C2 ECH_APF_C4 ECH_AStmt_C4 ECH_AC4_rep ECH_AC4_frame ECH_AC4_egs
  ECH_AC4_new ECH_AC4_clear.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pref_bytes (ss : list errslot) (i : nat) : Z := fold_right (fun sl acc => slot_bytes sl + acc) 0 (firstn i ss).
Lemma fold_bytes_app : forall l1 l2, fold_right (fun sl acc => slot_bytes sl + acc) 0 (l1 ++ l2) =
  fold_right (fun sl acc => slot_bytes sl + acc) 0 l1 + fold_right (fun sl acc => slot_bytes sl + acc) 0 l2.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn; [lia| rewrite IH; lia]. Qed.
Lemma pref_bytes_S : forall ss i d, (i < length ss)%nat -> pref_bytes ss (S i) = pref_bytes ss i + slot_bytes (nth i ss d).
Proof.
  unfold pref_bytes. induction ss as [|x ss IH]; intros i d Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn [firstn nth fold_right]; [rewrite firstn_O; cbn; lia|]. rewrite (IH i d) by lia. lia.
Qed.
Lemma pref_bytes_all : forall E, length (es_slots E) = 16%nat -> pref_bytes (es_slots E) 16 = estr_bytes E.
Proof. intros E SL. unfold pref_bytes, estr_bytes. rewrite firstn_all2 by lia. reflexivity. Qed.
Lemma pref_bytes_0 : forall ss, pref_bytes ss 0 = 0. Proof. reflexivity. Qed.
Lemma fold_bytes_nonneg : forall l, Forall (fun sl => 0 <= oszb (sl_file_o sl) <= 24 /\ 0 <= oszb (sl_func_o sl) <= 32) l ->
  0 <= fold_right (fun sl acc => slot_bytes sl + acc) 0 l.
Proof.
  induction l as [|x l IH]; intros FA; cbn; [lia|]. pose proof (Forall_inv FA) as K1. cbn in K1. pose proof (IH (Forall_inv_tail FA)) as K2.
  unfold slot_bytes in *. lia.
Qed.
Lemma pref_bytes_le : forall E i, estrs_ok E -> (i <= length (es_slots E))%nat -> 0 <= pref_bytes (es_slots E) i <= estr_bytes E.
Proof.
  intros E i OK Hi. unfold pref_bytes, estr_bytes. rewrite <- (firstn_skipn i (es_slots E)) at 3. rewrite fold_bytes_app.
  unfold estrs_ok in OK. rewrite <- (firstn_skipn i (es_slots E)) in OK. apply Forall_app in OK. destruct OK as [O1 O2].
  pose proof (fold_bytes_nonneg _ O1). pose proof (fold_bytes_nonneg _ O2). lia.
Qed.

Lemma blocks_ERRST_cleared : blocks_ERRST errst_cleared = []. Proof. reflexivity. Qed.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis EGS : egs_stmt H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Let PERM : rheap_perm H := HHx_rheap_perm H HHx.

  Section Loop.
    Variables (sp gp s11 : word) (F : bvmap 5 word) (fc : bv 32) (ra : word).
    Variables (f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word).                 (* [comment removed for export] *)
    Variables (E : errst) (c : errchain) (x : ctxinfo) (LBx LB0 : list block) (LF : list fframe) (SP lo B ALB : Z) (X : list (Z * Z)) (errv : word)
              (CH : list (Z * Z)).
    Variables (m_in : mem) (mo_in : Model).
    Let es := blk_addr (ec_es c).
    Let spx := bv_unsigned sp + -48.
    Hypothesis SL : length (es_slots E) = 16%nat.
    Hypothesis OWN : ERROWN (blocks_ERRST E) E.
    Hypothesis ESZ : estrs_ok E.
    Hypothesis SUB0 : forall b, In b LB0 -> In b LBx.
    Hypothesis NCL : forall a, es <= a < es + 904 -> ~ xclient H LB0 SP X a.
    Hypothesis CEIL : aceil <= lo.
    Hypothesis LOB : lo <= bv_unsigned sp - (144 + 8208).
    Hypothesis SPB : bv_unsigned sp <= B.
    Hypothesis SPS : bv_unsigned sp <= SP.
    Hypothesis SPA : bv_unsigned sp mod 16 = 0.
    Hypothesis CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -48 + 16 <= fp'.
    Hypothesis PF : forall site, site = AEC_RA1 \/ site = AEC_RA2 -> pf_ok (as_TR H) PF_cfree site ((spx, AEC_RAL) :: (bv_unsigned sp, bv_unsigned ra) :: CH).
    Hypothesis CFT : as_Cf H (estr_bytes E) <= ALB.

    Definition aec_inv (i : Z) : config -> Prop :=
      fun k => exists ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m (s : as_St H),
        as_VIS H s (cfg_ms k) = MS (mkR ra0 (Z_to_bv 64 spx) gp (Z_to_bv 64 ATP) t0 t1 t2 sp (Z_to_bv 64 es) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 i)
                                      (Z_to_bv 64 SHBv) (Z_to_bv 64 16) f5 f6 f7 f8 f9 f10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 (if i <? 16 then AEC_LOOP else AEC_EXIT)) fc None m (seg_rom asegs)
        /\ as_AKREL H s k /\ as_MPRES H mo_in (cfg_model k) /\ mem_inv asegs m /\ ACONST m /\ stk asegs m lo spx
        /\ rw_cells asegs m ARERRNO [C4 errv] /\ as_rauxv_ok H m B
        /\ as_RHEAP H s (blocks_slots (skipn (Z.to_nat i) (es_slots E)) ++ LBx) m /\ AC4W LBx m (ErrReady c) x
        /\ ERRSTm m es (clr E i) /\ rw_cells asegs m spx (aec_frame f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra)
        /\ lib_shad (chain_blocks c) m /\ as_RFS H LF m /\ as_chain H m (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)
        /\ strw E (blocks_slots (skipn (Z.to_nat i) (es_slots E)) ++ LBx) m
        /\ xpres H LB0 SP X m_in m
        /\ as_AL H s >= ALB - as_Cf H (pref_bytes (es_slots E) (Z.to_nat i)).

    Lemma aec_inner_chain : forall m j (w9 w8 w7 w6 w5 w4 w3 w2 w1 : word),
      as_chain H m (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH) ->
      rw_cells asegs m (spx + -96) (aecl_frame j w9 w8 w7 w6 w5 w4 w3 w2 w1 sp) ->
      as_chain H m spx ((spx, AEC_RAL) :: (bv_unsigned sp, bv_unsigned ra) :: CH).
    Proof.
      intros m j w9 w8 w7 w6 w5 w4 w3 w2 w1 CHN FRc. acb. pose proof (aword_range sp) as SPR.
      eapply (ah_chain_cons H HH); [exact CHN| lia| unfold AEC_RAL; lia| unfold spx; clear - SPA; Z.div_mod_to_equations; lia| unfold spx; lia| unfold spx; lia|].
      unfold aecl_frame in FRc.
      change ([CB 8 j; C8 w9; C8 w8; C8 w7; C8 w6; C8 w5; C8 w4; C8 w3; C8 w2; C8 w1; C8 sp; C8 (Z_to_bv 64 AEC_RAL)])
        with ([CB 8 j; C8 w9; C8 w8; C8 w7; C8 w6; C8 w5; C8 w4; C8 w3; C8 w2; C8 w1] ++ [C8 sp; C8 (Z_to_bv 64 AEC_RAL)]) in FRc.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FRc. destruct FRc as [_ FRc]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FRc.
      replace (spx - 16) with (spx + -96 + 80) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FRc || (revert FRc; rewrite !Z_to_bv_bv_unsigned; intros FRc; exact FRc).
    Qed.

    Lemma aec_trip : forall i, 0 <= i < 16 -> forall k, aec_inv i k -> as_SR H (aec_inv (i + 1)) k.
    Proof.
      intros i Hi [ms mo] (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & s &
                           VIS & KREL & MP & MI & AC & ST & ERR & AUX & HP & CW & EM & FR & LS & RFS & CHN & SW & XP & AL).
      cbn [cfg_ms cfg_model] in *. replace (i <? 16) with true in VIS by (symmetry; apply Z.ltb_lt; lia).
      acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      pose proof (pref_bytes_le E (Z.to_nat i) ESZ ltac:(rewrite SL; lia)) as PB0. pose proof (pref_bytes_le E (Z.to_nat (i + 1)) ESZ ltac:(rewrite SL; lia)) as PB1.
      pose proof (pref_bytes_S (es_slots E) (Z.to_nat i) (slot_clear 0) ltac:(rewrite SL; lia)) as PBS. fold (slot_at E i) in PBS.
      replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in PBS by lia. unfold slot_bytes in PBS.
      set (ss := es_slots E) in *. set (SBi := blocks_slots (skipn (Z.to_nat i) ss)) in *.
      assert (SUBx : forall b, In b LBx -> In b (SBi ++ LBx)) by (intros b Hb; apply in_or_app; right; exact Hb).
      pose proof CW as (MF0 & IM0 & GM0 & RL0 & [ES EC] & CP0). pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
      pose proof (ah_blocks H HH _ _ _ _ HP (SUBx _ I5)) as BR5. rewrite Z5 in BR5. fold es in BR5. unfold ERRST_SIZE in BR5.
      pose proof BR5 as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof (aapp_bounds _ _ B7 ltac:(lia)) as (_ & _ & T5 & _). unfold AAPP_HI in T5.
      assert (SLc : length (es_slots (clr E i)) = 16%nat) by (unfold clr; cbn [es_slots]; rewrite clr_slots_length; exact SL).
      set (sl := slot_at E i) in *.
      pose proof (slot_at_own _ E i OWN SL Hi) as [OF OG]. fold sl in OF, OG. fold sl in PBS.
      pose proof (slot_at_own _ E i ESZ SL Hi) as [SZf SZg]. fold sl in SZf, SZg.
      pose proof (estrs_pos E) as POSE.
      assert (SPL : SBi = (blocks_of (sl_file sl) (sl_file_o sl) ++ blocks_of (sl_func sl) (sl_func_o sl)) ++ blocks_slots (skipn (S (Z.to_nat i)) ss)).
      { unfold SBi. rewrite (skipn_cons_nth ss (Z.to_nat i) (slot_clear 0)) by lia. unfold sl, slot_at. fold ss. reflexivity. }
      assert (SBS : forall b, In b SBi -> In b (blocks_ERRST E)).
      { intros b Hb. unfold SBi, blocks_slots in Hb. rewrite blocks_ERRST_slots. fold ss. unfold blocks_slots. rewrite <- (firstn_skipn (Z.to_nat i) ss).
        rewrite map_app, concat_app. apply in_or_app. right. exact Hb. }
      assert (ACC0 : accessible m es 904).
      { pose proof (proj1 (Forall_forall _ _) LS _ ltac:(unfold chain_blocks; cbn; do 3 right; left; reflexivity)) as AD. cbv beta in AD. fold es in AD. rewrite Z5 in AD.
        unfold ERRST_SIZE in AD. eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]. }
      pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & CMS & CFS).
      (* [comment removed for export] *)
      assert (SPXR : 0 <= spx < 2^64) by (unfold spx; lia).
      assert (SPXL : lo + 144 + 8208 <= spx + 96) by (unfold spx; lia).
      assert (CHSe : forall fp' ra', In (fp', ra') ((spx, AEC_RAL) :: (bv_unsigned sp, bv_unsigned ra) :: CH) -> spx + -96 + 16 <= fp').
      { intros fp' ra' [E0|Hin]; [injection E0 as <- <-; lia| specialize (CHS1 _ _ Hin); unfold spx in *; lia]. }
      eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply aec_segA0 with (es := es) (i := i) (E := clr E i) (lo := lo);
        [exact EM| exact Hi| lia| lia| exact B2| exact B7| exact ACC0| exact MI
        | rewrite (unsigned_lit spx) by lia; exact ST| exact CEIL| rewrite (unsigned_lit spx) by lia; lia| lia| exact AC]|].
      intros msF0 mo0 KREL0 MP0 (j0 & a0_0 & m0 & VIS0 & MU0 & WM0 & MI0 & ST0 & FRc0 & EM0 & ACCa).
      rewrite (unsigned_lit spx) in MU0, ST0, FRc0 by lia.
      assert (XP0 : xpres H (SBi ++ LBx) spx [] m m0).
      { eapply (xpres_of_munch H s (SBi ++ LBx)); [exact HH| exact HP| exact MU0| exact WM0|]. apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      destruct (afree_world H _ _ _ m0 _ _ _ _ _ _ CW XP0 SUBx FR ltac:(lia) EM ltac:(fold es; lia) ltac:(fold es; unfold ERRST_SIZE; lia) LS) as (CW0 & FR0 & _ & LS0).
      assert (HP0 : as_RHEAP H s (SBi ++ LBx) m0).
      { eapply (ah_RHEAP_frame H HH); [exact HP| exact MU0| exact WM0|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      assert (AUX0 : as_rauxv_ok H m0 B).
      { eapply (ah_rauxv_frame H HH) with (LB := SBi ++ LBx); [exact AUX| exact MU0| exact WM0|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      assert (ERR0 : rw_cells asegs m0 ARERRNO [C4 errv]).
      { eapply rw_cells_transport; [exact ERR| exact MU0| exact WM0|]. cbn. unfold ARERRNO, ATP, AIMG_TOP in *. lia. }
      assert (AC0 : ACONST m0) by (eapply ACONST_stack_frame; [exact AC| exact MU0| exact WM0| lia]).
      assert (RFS0 : as_RFS H LF m0) by (eapply (RFS_stack H HH); [exact RFS| exact MU0| exact WM0| lia]).
      assert (CHN0 : as_chain H m0 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
      { eapply (achain_below H HH m m0); [exact CHN| exact CHS1| exact MU0|]. apply Forall_cons; [left; cbn; unfold spx in *; lia| apply Forall_nil]. }
      pose proof (strw_xpres H E _ _ _ _ _ (fun b Hb => POSE b ESZ Hb) SW XP0 (fun b Hb => Hb)) as SW0.
      eapply (ahh_evt_then H HH); [exact KREL0| exact VIS0| eapply aec_segA with (es := es) (i := i) (E := clr E i); [exact EM0| exact Hi| lia| lia| exact B2| exact B7| exact ACCa| exact MI0]|].
      intros msF1 mo1 KREL1 MP1 (u0_1 & u1_1 & u2_1 & a3_1 & a4_1 & a5_1 & a6_1 & a7_1 & m1 & VIS1 & MU1 & WM1 & MI1 & EM1 & ACC1).
      rewrite (slot_at_clr E i SL Hi) in EM1, VIS1. fold sl in EM1, VIS1.
      destruct (aes_world H HH _ _ _ _ m1 _ _ _ _ _ _ _ _ HP0 SUBx CW0 AUX0 ERR0 ST0 FR0 AC0 LS0 CEIL ltac:(lia) ltac:(lia) MU1 WM1)
        as (HP1 & CW1 & AUX1 & ERR1 & ST1 & FR1 & AC1 & LS1).
      assert (FRc1 : rw_cells asegs m1 (spx + -96) (aecl_frame j0 f9 f8 f7 f6 f5 (Z_to_bv 64 16) (Z_to_bv 64 SHBv) (Z_to_bv 64 i) (Z_to_bv 64 es) sp)).
      { eapply rw_cells_transport; [exact FRc0| exact MU1| exact WM1|]. cbn. lia. }
      assert (SW1 : strw E (SBi ++ LBx) m1).
      { eapply (strw_es H HHx E _ _ m0 m1 (ec_es c)); [exact HP0| exact (SUBx _ I5)| exact Z5| reflexivity| intros b Hb; exact (POSE b ESZ Hb)| exact SW0| exact MU1| exact WM1]. }
      assert (CHN1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
      { eapply (achain_below H HH m0 m1); [exact CHN0| exact CHS1| exact MU1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      assert (RFS1 : as_RFS H LF m1).
      { eapply (ah_RFS_frame H HH); [exact RFS0| exact MU1| exact WM1|]. pose proof (RFS_fsb H HH _ _ RFS0) as (F1 & F2 & F3 & F4).
        apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia| apply Forall_nil]. }
      assert (FSf : forall b, In b (blocks_of (sl_file sl) (sl_file_o sl)) -> In b SBi) by (intros b Hb; rewrite SPL; apply in_or_app; left; apply in_or_app; left; exact Hb).
      assert (FSg : forall b, In b (blocks_of (sl_func sl) (sl_func_o sl)) -> In b SBi) by (intros b Hb; rewrite SPL; apply in_or_app; left; apply in_or_app; right; exact Hb).
      pose proof CW1 as (MF1 & IM1 & GM1 & _).
      assert (CFF : as_Cf H (oszb (sl_file_o sl)) <= as_AL H s).
      { pose proof (CFS (pref_bytes ss (Z.to_nat i)) (oszb (sl_file_o sl)) ltac:(lia) ltac:(lia)) as K1.
        pose proof (CFM (pref_bytes ss (Z.to_nat i) + oszb (sl_file_o sl)) (estr_bytes E) ltac:(lia)) as K2. lia. }
      pose proof (aec_inner_chain m1 j0 _ _ _ _ _ _ _ _ _ CHN1 FRc1) as CHNe1.
      (* [comment removed for export] *)
      eapply (ah_seq H HH).
      { eapply (acfree_opt_spec H HH) with (P := sl_file sl) (o := sl_file_o sl) (LB := SBi ++ LBx) (lo := lo) (B := B) (s := s) (errv := errv)
                                            (CH := (spx, AEC_RAL) :: (bv_unsigned sp, bv_unsigned ra) :: CH);
          [ exact VIS1| reflexivity
          | destruct (sl_file_o sl) as [[idf nf]|] eqn:EO; cbn [ofield] in OF;
            [ destruct OF as (_ & _ & OF);
              assert (INF : In (idf, sl_file sl, nf) (SBi ++ LBx)) by (apply in_or_app; left; apply FSf; try rewrite EO; cbn; left; reflexivity);
              split; [exact INF| apply (SW1 (idf, sl_file sl, nf)); [apply SBS; apply FSf; try rewrite EO; cbn; left; reflexivity| exact INF]]
            | exact OF ]
          | exact HP1| exact KREL1| exact AUX1
          | rewrite (unsigned_lit spx), (unsigned_lit (spx + -96)) by lia; lia
          | rewrite (unsigned_lit spx), (unsigned_lit (spx + -96)) by lia; exact ST1| exact CEIL
          | rewrite (unsigned_lit spx), (unsigned_lit (spx + -96)) by lia; unfold CFREE_STACK, AFREE_STACK; lia
          | rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR1| exact MI1| reflexivity
          | rewrite (unsigned_lit spx), (unsigned_lit (spx + -96)) by lia; unfold spx; clear - SPA; Z.div_mod_to_equations; lia
          | exact AC1| rewrite (unsigned_lit spx) by lia; exact CHNe1
          | rewrite (unsigned_lit spx), (unsigned_lit (spx + -96)) by lia; exact CHSe
          | rewrite (unsigned_lit AEC_RA1) by (unfold AEC_RA1; lia); apply PF; left; reflexivity
          | exact CFF
          | exact IM1| exact GM1 ]. }
      intros [ms2 mo2] PO. unfold acfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & s2' & L2 &
                      VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & PM2 & SUB2 & XP2 & HP2 & IM2 & GM2 & AL2).
      rewrite (unsigned_lit spx), (unsigned_lit (spx + -96)) in ST2, XP2 by lia.
      rewrite (unsigned_lit ATP) in ERR2 by (unfold ATP; lia).
      assert (OZ : forall o, oszb' o = oszb o) by (intros [[i' n']|]; reflexivity). rewrite OZ in AL2.
      (* [comment removed for export] *)
      pose proof (ah_nodup H HH _ _ _ HP) as ND.
      assert (KEEP : forall Fr L', Permutation (Fr ++ L') (SBi ++ LBx) -> (forall b, In b Fr -> In b SBi) -> forall b, In b LBx -> In b L').
      { intros Fr L' PMx FS b Hb. eapply perm_keep; [exact PMx| apply SUBx; exact Hb|]. intros K.
        eapply (nodup_map_app_excl blk_id SBi LBx b); [exact ND| apply FS; exact K| exact Hb]. }
      pose proof (KEEP _ _ PM2 FSf) as SUBK2.
      destruct (afree_world H _ _ _ m2 _ _ _ _ _ _ CW1 XP2 SUBK2 FR1 ltac:(lia) EM1 ltac:(fold es; lia) ltac:(fold es; unfold ERRST_SIZE; lia) LS1) as (CW2 & FR2 & EM2 & LS2).
      destruct (afree_world H _ _ _ m2 _ _ _ _ _ _ CW1 XP2 SUBK2 FRc1 ltac:(lia) EM1 ltac:(fold es; lia) ltac:(fold es; unfold ERRST_SIZE; lia) LS1) as (_ & FRc2 & _ & _).
      fold es in EM2.
      pose proof (strw_xpres H E _ _ _ _ _ (fun b Hb => POSE b ESZ Hb) SW1 XP2 SUB2) as SW2.
      assert (ACC2 : accessible m2 es 904).
      { pose proof (proj1 (Forall_forall _ _) LS2 _ ltac:(unfold chain_blocks; cbn; do 3 right; left; reflexivity)) as AD. cbv beta in AD. fold es in AD. rewrite Z5 in AD.
        unfold ERRST_SIZE in AD. eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]. }
      assert (CHN2 : as_chain H m2 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
      { eapply (ah_chain_ext H HH); [exact CHN1|]. intros fp' ra' a Hin Ha. apply XP2; [| split; [left; specialize (CHS1 _ _ Hin); unfold spx in *; lia| intros []]].
        pose proof (ah_chain_range H HH _ _ _ _ _ CHN1 Hin) as (Q1 & _). lia. }
      assert (RFS2 : as_RFS H LF m2) by (eapply (RFS_via_xpres H HH); [exact RFS1| exact XP2| apply Forall_nil]).
      pose proof CW2 as (MF2 & IM2' & GM2' & _).
      (* [comment removed for export] *)
      eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2
        | eapply aec_segB with (es := es) (i := i) (E := es_with_slot (clr E i) i (slot_wipe sl)); [exact EM2| exact Hi| lia| lia| exact B7| exact ACC2| exact MI2]|].
      intros msF3 mo3 KREL3 MP3 (u0_3 & u1_3 & u2_3 & a3_3 & a4_3 & a5_3 & a6_3 & a7_3 & m3 & VIS3 & MU3 & WM3 & MI3 & EM3 & ACC3).
      rewrite (slot_at_upd (clr E i) i _ SLc Hi) in EM3, VIS3. rewrite (es_with_slot_twice (clr E i) i _ _ SLc Hi) in EM3. cbn [slot_wipe sl_func] in EM3, VIS3.
      destruct (aes_world H HH _ _ _ _ m3 _ _ _ _ _ _ _ _ HP2 SUBK2 CW2 AUX2 ERR2 ST2 FR2 AC2 LS2 CEIL ltac:(lia) ltac:(lia) MU3 WM3)
        as (HP3 & CW3 & AUX3 & ERR3 & ST3 & FR3 & AC3 & LS3).
      assert (FRc3 : rw_cells asegs m3 (spx + -96) (aecl_frame j0 f9 f8 f7 f6 f5 (Z_to_bv 64 16) (Z_to_bv 64 SHBv) (Z_to_bv 64 i) (Z_to_bv 64 es) sp)).
      { eapply rw_cells_transport; [exact FRc2| exact MU3| exact WM3|]. cbn. lia. }
      assert (SW3 : strw E L2 m3).
      { eapply (strw_es H HHx E _ _ m2 m3 (ec_es c)); [exact HP2| exact (SUBK2 _ I5)| exact Z5| reflexivity| intros b Hb; exact (POSE b ESZ Hb)| exact SW2| exact MU3| exact WM3]. }
      assert (CHN3 : as_chain H m3 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
      { eapply (achain_below H HH m2 m3); [exact CHN2| exact CHS1| exact MU3|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      assert (RFS3 : as_RFS H LF m3).
      { eapply (ah_RFS_frame H HH); [exact RFS2| exact MU3| exact WM3|]. pose proof (RFS_fsb H HH _ _ RFS2) as (F1 & F2 & F3 & F4).
        apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia| apply Forall_nil]. }
      pose proof CW3 as (MF3 & IM3 & GM3 & _).
      assert (CFG : as_Cf H (oszb (sl_func_o sl)) <= as_AL H s2').
      { pose proof (CFS (pref_bytes ss (Z.to_nat i)) (oszb (sl_file_o sl)) ltac:(lia) ltac:(lia)) as K1.
        pose proof (CFS (pref_bytes ss (Z.to_nat i) + oszb (sl_file_o sl)) (oszb (sl_func_o sl)) ltac:(lia) ltac:(lia)) as K2.
        pose proof (CFM (pref_bytes ss (Z.to_nat i) + oszb (sl_file_o sl) + oszb (sl_func_o sl)) (estr_bytes E) ltac:(lia)) as K3. lia. }
      pose proof (aec_inner_chain m3 j0 _ _ _ _ _ _ _ _ _ CHN3 FRc3) as CHNe3.
      (* [comment removed for export] *)
      eapply (ah_seq H HH).
      { eapply (acfree_opt_spec H HH) with (P := sl_func sl) (o := sl_func_o sl) (LB := L2) (lo := lo) (B := B) (s := s2') (errv := errv)
                                            (CH := (spx, AEC_RAL) :: (bv_unsigned sp, bv_unsigned ra) :: CH);
          [ exact VIS3| reflexivity
          | destruct (sl_func_o sl) as [[idg ng]|] eqn:EG; cbn [ofield] in OG;
            [ destruct OG as (_ & _ & OG);
              assert (ING : In (idg, sl_func sl, ng) L2);
              [ eapply perm_keep; [exact PM2| apply in_or_app; left; apply FSg; try rewrite EG; cbn; left; reflexivity|]; intros K;
                assert (NDS : List.NoDup (map blk_id SBi)) by (rewrite map_app in ND; eapply NoDup_app_remove_r; exact ND);
                rewrite SPL in NDS;
                eapply (nodup_mid_excl blk_id [] _ _ _ _ NDS K); try rewrite EG; cbn; left; reflexivity
              | split; [exact ING| apply (SW3 (idg, sl_func sl, ng)); [apply SBS; apply FSg; try rewrite EG; cbn; left; reflexivity| exact ING]] ]
            | exact OG ]
          | exact HP3| exact KREL3| exact AUX3
          | rewrite (unsigned_lit spx), (unsigned_lit (spx + -96)) by lia; lia
          | rewrite (unsigned_lit spx), (unsigned_lit (spx + -96)) by lia; exact ST3| exact CEIL
          | rewrite (unsigned_lit spx), (unsigned_lit (spx + -96)) by lia; unfold CFREE_STACK, AFREE_STACK; lia
          | rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR3| exact MI3| reflexivity
          | rewrite (unsigned_lit spx), (unsigned_lit (spx + -96)) by lia; unfold spx; clear - SPA; Z.div_mod_to_equations; lia
          | exact AC3| rewrite (unsigned_lit spx) by lia; exact CHNe3
          | rewrite (unsigned_lit spx), (unsigned_lit (spx + -96)) by lia; exact CHSe
          | rewrite (unsigned_lit AEC_RA2) by (unfold AEC_RA2; lia); apply PF; right; reflexivity
          | exact CFG
          | exact IM3| exact GM3 ]. }
      intros [ms4 mo4] PO. unfold acfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & s4' & L4 &
                      VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & PM4 & SUB4 & XP4 & HP4 & IM4 & GM4 & AL4).
      rewrite (unsigned_lit spx), (unsigned_lit (spx + -96)) in ST4, XP4 by lia.
      rewrite (unsigned_lit ATP) in ERR4 by (unfold ATP; lia). rewrite OZ in AL4.
      assert (SUBK4 : forall b, In b LBx -> In b L4).
      { intros b Hb. eapply perm_keep; [exact PM4| apply SUBK2; exact Hb|]. intros K.
        eapply (nodup_map_app_excl blk_id SBi LBx b); [exact ND| apply FSg; exact K| exact Hb]. }
      destruct (afree_world H _ _ _ m4 _ _ _ _ _ _ CW3 XP4 SUBK4 FR3 ltac:(lia) EM3 ltac:(fold es; lia) ltac:(fold es; unfold ERRST_SIZE; lia) LS3) as (CW4 & FR4 & EM4 & LS4).
      destruct (afree_world H _ _ _ m4 _ _ _ _ _ _ CW3 XP4 SUBK4 FRc3 ltac:(lia) EM3 ltac:(fold es; lia) ltac:(fold es; unfold ERRST_SIZE; lia) LS3) as (_ & FRc4 & _ & _).
      fold es in EM4.
      pose proof (strw_xpres H E _ _ _ _ _ (fun b Hb => POSE b ESZ Hb) SW3 XP4 SUB4) as SW4.
      assert (ACC4 : accessible m4 es 904).
      { pose proof (proj1 (Forall_forall _ _) LS4 _ ltac:(unfold chain_blocks; cbn; do 3 right; left; reflexivity)) as AD. cbv beta in AD. fold es in AD. rewrite Z5 in AD.
        unfold ERRST_SIZE in AD. eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]. }
      assert (CHN4 : as_chain H m4 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
      { eapply (ah_chain_ext H HH); [exact CHN3|]. intros fp' ra' a Hin Ha. apply XP4; [| split; [left; specialize (CHS1 _ _ Hin); unfold spx in *; lia| intros []]].
        pose proof (ah_chain_range H HH _ _ _ _ _ CHN3 Hin) as (Q1 & _). lia. }
      assert (RFS4 : as_RFS H LF m4) by (eapply (RFS_via_xpres H HH); [exact RFS3| exact XP4| apply Forall_nil]).
      (* [comment removed for export] *)
      eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4
        | eapply aec_segC with (es := es) (i := i) (lo := lo) (E := es_with_slot (clr E i) i (slot_file0 (slot_wipe sl)));
          [exact EM4| exact Hi| lia| lia| exact B7| exact ACC4| exact MI4
          | rewrite (unsigned_lit spx) by lia; exact ST4| exact CEIL| rewrite (unsigned_lit spx) by lia; lia| lia
          | rewrite (unsigned_lit spx) by lia; exact FRc4]|].
      intros msF5 mo5 KREL5 MP5 (t0_5 & t1_5 & t2_5 & a0_5 & a1_5 & a2_5 & a3_5 & a4_5 & a5_5 & a6_5 & a7_5 & t3_5 & t4_5 & t5_5 & t6_5 & m5 & VIS5 & MU5 & WM5 & MI5 & ST5 & EM5 & ACC5).
      rewrite (unsigned_lit spx) in ST5 by lia.
      rewrite (slot_at_upd (clr E i) i _ SLc Hi) in EM5. rewrite (es_with_slot_twice (clr E i) i _ _ SLc Hi) in EM5.
      unfold slot_func0, slot_file0, slot_wipe in EM5. cbn [sl_flags sl_buffer sl_file sl_file_o sl_line sl_func sl_func_o] in EM5.
      change (mkSLOT 0 0 0 None (2 ^ 32 - 1) 0 None) with (slot_clear (2 ^ 32 - 1)) in EM5. rewrite (clr_step E i SL Hi) in EM5.
      destruct (aes_world H HH _ _ _ _ m5 _ _ _ _ _ _ _ _ HP4 SUBK4 CW4 AUX4 ERR4 ST4 FR4 AC4 LS4 CEIL ltac:(lia) ltac:(lia) MU5 WM5)
        as (HP5 & CW5 & AUX5 & ERR5 & _ & FR5 & AC5 & LS5).
      assert (SW5 : strw E L4 m5).
      { eapply (strw_es H HHx E _ _ m4 m5 (ec_es c)); [exact HP4| exact (SUBK4 _ I5)| exact Z5| reflexivity| intros b Hb; exact (POSE b ESZ Hb)| exact SW4| exact MU5| exact WM5]. }
      assert (CHN5 : as_chain H m5 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
      { eapply (achain_below H HH m4 m5); [exact CHN4| exact CHS1| exact MU5|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      assert (RFS5 : as_RFS H LF m5).
      { eapply (ah_RFS_frame H HH); [exact RFS4| exact MU5| exact WM5|]. pose proof (RFS_fsb H HH _ _ RFS4) as (F1 & F2 & F3 & F4).
        apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia| apply Forall_nil]. }
      (* [comment removed for export] *)
      assert (PMF : Permutation L4 (blocks_slots (skipn (Z.to_nat (i + 1)) ss) ++ LBx)).
      { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        set (bf := blocks_of (sl_file sl) (sl_file_o sl)) in *. set (bg := blocks_of (sl_func sl) (sl_func_o sl)) in *.
        set (SBn := blocks_slots (skipn (S (Z.to_nat i)) ss)) in *.
        apply (Permutation_app_inv_l (bf ++ bg)). rewrite <- (app_assoc bf bg L4).
        eapply Permutation_trans; [apply Permutation_app_head; exact PM4|].
        eapply Permutation_trans; [exact PM2|]. rewrite SPL. rewrite <- (app_assoc (bf ++ bg) SBn LBx). apply Permutation_refl. }
      assert (SWF : strw E (blocks_slots (skipn (Z.to_nat (i + 1)) ss) ++ LBx) m5).
      { intros b Hb HbL. apply (SW5 b Hb). eapply Permutation_in; [apply Permutation_sym; exact PMF| exact HbL]. }
      (* [comment removed for export] *)
      assert (XES : forall ma mb, munch [(es, es + 904)] ma mb -> wmono asegs ma mb -> xpres H LB0 SP X ma mb).
      { intros ma mb MUx WMx. eapply xpres_of_munch_gen; [exact MUx| exact WMx|]. intros a Ha HC. cbn. split; [| exact I]. intros Hr. exact (NCL a Hr HC). }
      assert (XFR : forall L' S ma mb, xpres H L' S [] ma mb -> S <= spx -> (forall b, In b LBx -> In b L') -> xpres H LB0 SP X ma mb).
      { intros L' S ma mb XPx HS SUBx'. eapply xpres_weaken; [exact XPx| unfold spx in *; lia| intros b Hb; apply SUBx'; apply SUB0; exact Hb| intros a []]. }
      apply (ah_done H HH). unfold aec_inv. cbn [cfg_ms cfg_model].
      exists (Z_to_bv 64 AEC_RAL), t0_5, t1_5, t2_5, a0_5, a1_5, a2_5, a3_5, a4_5, a5_5, a6_5, a7_5, t3_5, t4_5, t5_5, t6_5, m5, s4'.
      split; [exact VIS5|]. split; [exact KREL5|].
      split. { eapply (ah_mpres_trans H HH); [exact MP|]. eapply (ah_mpres_trans H HH); [exact MP0|]. eapply (ah_mpres_trans H HH); [exact MP1|].
               eapply (ah_mpres_trans H HH); [exact MP2|]. eapply (ah_mpres_trans H HH); [exact MP3|].
               eapply (ah_mpres_trans H HH); [exact MP4| exact MP5]. }
      split; [exact MI5|]. split; [exact AC5|]. split; [exact ST5|]. split; [exact ERR5|]. split; [exact AUX5|].
      split; [eapply PERM; [exact HP5| exact PMF]|]. split; [exact CW5|]. split; [exact EM5|]. split; [exact FR5|].
      split; [exact LS5|]. split; [exact RFS5|]. split; [exact CHN5|]. split; [exact SWF|].
      split.
      { eapply xpres_trans; [exact XP|]. eapply xpres_trans; [apply (XFR _ _ _ _ XP0 ltac:(lia) SUBx)|].
        eapply xpres_trans; [apply (XES _ _ MU1 WM1)|]. eapply xpres_trans; [apply (XFR _ _ _ _ XP2 ltac:(lia) SUBK2)|].
        eapply xpres_trans; [apply (XES _ _ MU3 WM3)|]. eapply xpres_trans; [apply (XFR _ _ _ _ XP4 ltac:(lia) SUBK4)|]. apply (XES _ _ MU5 WM5). }
      fold ss. rewrite PBS. pose proof (CFS (pref_bytes ss (Z.to_nat i) + oszb (sl_file_o sl)) (oszb (sl_func_o sl)) ltac:(lia) ltac:(lia)).
      pose proof (CFS (pref_bytes ss (Z.to_nat i)) (oszb (sl_file_o sl)) ltac:(lia) ltac:(lia)).
      rewrite Z.add_assoc. lia.
    Qed.

    Lemma aec_loop : forall n i, i = 16 - Z.of_nat n -> 0 <= i -> forall k, aec_inv i k -> as_SR H (aec_inv 16) k.
    Proof.
      induction n as [|n IH]; intros i Ei Hi k INV.
      - replace i with 16 in INV by lia. apply (ah_done H HH). exact INV.
      - eapply (ah_seq H HH); [apply (aec_trip i ltac:(lia) k INV)|]. intros k' INV'. apply (IH (i + 1)); [lia| lia| exact INV'].
    Qed.
  End Loop.

  Lemma aerrclear_spec : errclear_stmt H.
  Proof.
    unfold errclear_stmt. intros until CH. intros VIS HP KREL BY CN AUX SPB SPA ST CEIL LO SH0 ERR MI TP AC MF IM GM RL EP EX EB ESH CP RFS LFN CHN CHS PF ECL AL RAE.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (STK1 : 48 + errph_stack ph <= bv_unsigned sp - lo /\ 144 + 8208 <= bv_unsigned sp - lo).
    { unfold ERRCLEAR_STACK, FR_ERR_clear_error, CFREE_STACK, AFREE_STACK in LO. destruct ph; cbn [errph_stack] in *;
        unfold ERRINIT_STACK, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, AFS_STACK, AREALLOC_STACK in *; lia. }
    set (SB := blocks_ERRST E) in *.
    assert (SUBx : forall b, In b LB -> In b (SB ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    subst tp. unfold ATP in ERR. rewrite (unsigned_lit 12459152) in ERR by lia. change (12459152 + -164) with 12458988 in ERR.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply aec_seg0 with (lo := lo); [exact AC| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (MU1' : munch ((bv_unsigned sp + -48, bv_unsigned sp) :: [] ++ []) m m1) by exact MU1.
    assert (CW0 : AC4W LB m ph x) by (split; [exact MF| split; [exact IM| split; [exact GM| split; [exact RL| split; [exact EP| exact CP]]]]]).
    assert (CW1 : AC4W LB m1 ph x).
    { eapply (AC4W_foot H HH) with (XS := []) (LIT := []); [exact RFS| apply Forall_nil| apply Forall_nil| | exact HP| exact SUBx| exact MU1'| exact WM1| exact CW0]. lia. }
    assert (HP1 : as_RHEAP H s (SB ++ LB) m1).
    { eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : as_rauxv_ok H m1 B).
    { eapply (ah_rauxv_frame H HH) with (LB := LB); [exact AUX| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (ERR1 : rw_cells asegs m1 12458988 [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold AIMG_TOP in *. lia. }
    assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame; [exact AC| exact MU1| exact WM1| lia]).
    assert (RFS1 : as_RFS H LF m1) by (eapply (RFS_stack H HH); [exact RFS| exact MU1| exact WM1| lia]).
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (CHN1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SPA| lia| lia|].
      pose proof FR1 as FR2. unfold aec_frame in FR2.
      change ([C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        with ([C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -48 + 32) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -48 + 16 <= fp').
    { intros fp' ra' [E0|Hin]; [injection E0 as <- <-; lia| specialize (CHS _ _ Hin); lia]. }
    clear CH0.
    destruct CW1 as (MF1 & IM1 & GM1 & RL1 & EP1 & CP1).
    assert (AGL : magree (lib_addr (SB ++ LB)) m m1).
    { eapply (lib_magree_scratch H HH) with (W := [] ++ []); [exact RFS| | exact MU1| exact WM1| lia| apply Forall_nil].
      apply Forall_forall. intros b Hb. eapply (ah_blocks H HH); [exact HP| exact Hb]. }
    assert (EX1 : ERRX m1 ph E).
    { destruct ph as [|c0]; [exact EX|]. cbn [ERRX ERRPH] in EX, EP |- *. destruct EP as [_ EC0].
      pose proof EC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _). pose proof EX as (_ & ESZ & _).
      eapply ERRXR_agree; [exact EX| apply SUBx; exact I5| exact Z5| intros b Hb; apply in_or_app; left; exact Hb
                          | intros b Hb; pose proof (estrs_pos _ _ ESZ Hb); lia| exact AGL]. }
    assert (ESH1 : errph_shad m1 ph).
    { destruct ph as [|c0]; [exact I|]. cbn [errph_shad ERRPH] in ESH, EP |- *. destruct EP as [_ EC0].
      eapply lib_shad_frame; [exact ESH|]. eapply magree_mono; [exact AGL|]. intros a Ha. eapply lib_addr_mono; [| exact Ha].
      intros b Hb. apply SUBx. eapply chain_blocks_in; [exact EC0| exact Hb]. }
    pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & CMS & CFS).
    assert (ESZ : estrs_ok E).
    { destruct ph as [|c0]; cbn [ERRX] in EX; [| exact (proj1 (proj2 EX))]. subst E. unfold estrs_ok, errst_zero. cbn [es_slots].
      apply Forall_forall. intros sl Hsl. apply repeat_spec in Hsl. subst sl. cbn. lia. }
    pose proof (fold_bytes_nonneg _ ESZ) as EBN. change (fold_right _ 0 (es_slots E)) with (estr_bytes E) in EBN.
    pose proof (CF0 (estr_bytes E) EBN) as CFT0. unfold ERRCLEAR_COST in AL.
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (EGS ph E) with (save := 0) (lo := lo) (B := B) (LB := LB) (s := s) (x := x) (errv := errv) (LF := LF) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [ exact VIS1| reflexivity| lia| intros _; left; reflexivity| exact HP1| exact KREL1| exact BY| exact CN| exact AUX1
        | rewrite (unsigned_lit (bv_unsigned sp + -48)) by lia; lia
        | rewrite (unsigned_lit (bv_unsigned sp + -48)) by lia; clear - SPA; Z.div_mod_to_equations; lia
        | rewrite (unsigned_lit (bv_unsigned sp + -48)) by lia; exact ST1
        | exact CEIL
        | rewrite (unsigned_lit (bv_unsigned sp + -48)) by lia; lia
        | eapply errph_sh0_sub; [eapply errph_sh0_munch; [exact SH0| exact MU1| exact WM1| apply Forall_cons; [apply stack0_ok_app; unfold AHI_LO; lia| cbn [app]; apply Forall_nil]]
                               | rewrite (unsigned_lit (bv_unsigned sp + -48)) by lia; lia| rewrite (unsigned_lit (bv_unsigned sp + -48)) by lia; clear - SPA; Z.div_mod_to_equations; lia]
        | rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR1
        | exact MI1| reflexivity| exact AC1| exact MF1| exact IM1| exact GM1| exact RL1| exact EP1| exact EX1| exact EB| exact ESH1| exact CP1
        | exact RFS1| exact LFN| exact CHN1| rewrite (unsigned_lit (bv_unsigned sp + -48)) by lia; exact CHS1
        | rewrite (unsigned_lit AEC_RA0) by (unfold AEC_RA0; lia); eapply pf_ok_call; [exact PF|]; unfold PF_errclear, R_ERR_clear_error_egs, AEC_RA0; apply incl_appl; apply incl_refl
        | exact ECL
        | lia
        | rewrite (unsigned_lit AEC_RA0) by (unfold AEC_RA0; lia); reflexivity ]. }
    intros [ms2 mo2] PO. unfold egs_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & LBN & c & XS &
                    VIS2 & MP2 & (KREL2 & MI2 & AC2 & ST2 & AUX2 & HP2 & MF2 & IM2 & GM2 & RL2) & ERR2 & _ & DL & EP2 & CP2 & EST2 & LS2 & FXS & XP2 & RFS2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia. rewrite (unsigned_lit ATP) in ERR2 by (unfold ATP; lia).
    (* [comment removed for export] *)
    assert (FXE : forall A n, aceil <= A -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) (XS ++ ERR_XE)).
    { intros A n HA. apply Forall_app. split.
      - eapply Forall_impl; [| exact FXS]. intros iv SC. pose proof (fs_scratch_range H HH _ _ _ RFS SC). lia.
      - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key,
          A_master_once_ret, A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf,
          A_keys, A_next_key, A_key_lock, A_tsd_main.
        cbn [app]. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -48) (aec_frame s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply xpres_rw_cells'; [exact XP2| exact FR1| left; lia|]. apply FXE. lia. }
    set (es := blk_addr (ec_es c)) in *.
    pose proof EP2 as [ES2 EC2]. pose proof EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    assert (SUB2 : forall b, In b (LBN ++ LB) -> In b (SB ++ LBN ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    pose proof (ah_blocks H HH _ _ _ _ HP2 (SUB2 _ I5)) as BR5. rewrite Z5 in BR5. fold es in BR5. unfold ERRST_SIZE in BR5.
    pose proof BR5 as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof (aapp_bounds _ _ B7 ltac:(lia)) as (_ & _ & T5 & _). unfold AAPP_HI in T5.
    destruct EST2 as (EST & ESZ2 & ESHs & ESC). apply ERRST_split in EST. destruct EST as [EM2 OWN]. fold es in EM2. pose proof EM2 as (SL & _).
    pose proof (ah_nodup H HH _ _ _ HP2) as ND2.
    assert (CHN2 : as_chain H m2 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_ext H HH); [exact CHN1|]. intros fp' ra' a Hin Ha. apply XP2; [| split; [left; specialize (CHS1 _ _ Hin); lia|]].
      - pose proof (ah_chain_range H HH _ _ _ _ _ CHN1 Hin) as (Q1 & _). lia.
      - pose proof (ah_chain_range H HH _ _ _ _ _ CHN1 Hin) as (Q1 & _). specialize (CHS1 _ _ Hin).
        apply (rin_ivs_off _ a). apply FXE. lia. }
    assert (SW2 : strw E (SB ++ LBN ++ LB) m2).
    { intros b Hb HbL. split; [exact (proj1 (Forall_forall _ _) ESC _ Hb)| exact (proj1 (Forall_forall _ _) ESHs _ Hb)]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply aec_seg1 with (es := es); lia|].
    intros msF3 mo3 KREL3 MP3 (a0' & VIS3).
    (* [comment removed for export] *)
    set (X := XS ++ ERR_XE ++ errph_foot ph).
    assert (NCL : forall a, es <= a < es + 904 -> ~ xclient H LB (bv_unsigned sp) X a).
    { intros a Hr [HC HXn].
      destruct HC as [K|[K|[(b & Hb & Hrb)|[(b & Hb & Hrb)|[K|[K|K]]]]]].
      - lia.
      - unfold aimg_client, AIMG_TOP in *. lia.
      - assert (NN : ~ (blk_id b <> blk_id (ec_es c))).
        { intros NE. pose proof (ah_disj H HH _ _ _ _ _ HP2 (SUB2 _ (in_or_app _ _ _ (or_intror Hb))) (SUB2 _ I5) NE) as DJ.
          rewrite Z5 in DJ. fold es in DJ. unfold ERRST_SIZE in DJ. lia. }
        apply NN. intros EQid.
        pose proof (nodup_id_inj _ _ _ ND2 (SUB2 _ (in_or_app _ _ _ (or_intror Hb))) (SUB2 _ I5) EQid) as EQB. subst b.
        destruct ph as [|cq]; cbn [errph_delta errph_foot] in *.
        + destruct DL as (_ & _ & FA). pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail FA)))) as IN5.
          assert (NDx : List.NoDup (map blk_id (LBN ++ LB))) by (rewrite map_app in ND2; eapply NoDup_app_remove_l; exact ND2).
          eapply (nodup_map_app_excl blk_id LBN LB (ec_es c)); [exact NDx| exact IN5| exact Hb].
        + destruct DL as [-> _]. apply HXn. unfold X. apply rin_ivs_app. right. apply rin_ivs_app. right. cbn. left. fold es. unfold ERRST_SIZE. lia.
      - pose proof (ah_blocks H HH _ _ _ _ HP2 (SUB2 _ (in_or_app _ _ _ (or_intror Hb)))) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
        pose proof (aapp_bounds _ _ Q7 Q3) as (_ & _ & T1 & _).
        pose proof (aapp_disjoint_sh es 904 (blk_addr b) (blk_size b) B7 ltac:(lia) ltac:(lia) Q3). lia.
      - pose proof (RFS_fsb H HH _ _ RFS2) as (F1 & F2 & F3 & F4). unfold AFS_SIZE in *. lia.
      - pose proof (RFS_fsb H HH _ _ RFS2) as (F1 & F2 & F3 & F4). unfold AIMG_TOP in F1.
        pose proof (aapp_bounds _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (U1 & U2 & U3 & U4 & _).
        pose proof (aapp_disjoint_sh es 904 (as_FSB H) AFS_SIZE B7 ltac:(lia) ltac:(lia) ltac:(unfold AFS_SIZE; lia)) as D.
        clear - D K Hr F3. unfold sh, nsh, AFS_SIZE in *. Z.div_mod_to_equations. lia.
      - clear - K Hr B7 ACEILB. unfold aapp, aapp_lo, aapp_hi, AHI_LO, ALOWSH_LO, AIMG_TOP, sh in *. rewrite ASHADOW_BASE_val in K. lia. }
    (* [comment removed for export] *)
    assert (CW2 : AC4W (LBN ++ LB) m2 (ErrReady c) x) by (split; [exact MF2| split; [exact IM2| split; [exact GM2| split; [exact RL2| split; [exact EP2| exact CP2]]]]]).
    assert (PFC : forall site, site = AEC_RA1 \/ site = AEC_RA2 -> pf_ok (as_TR H) PF_cfree site ((bv_unsigned sp + -48, AEC_RAL) :: (bv_unsigned sp, bv_unsigned ra) :: CH)).
    { assert (PFE : pf_ok (as_TR H) [(APC0_FREE, [AEC_RA1]); (APC0_FREE, [AEC_RA2])] AEC_RAL ((bv_unsigned sp, bv_unsigned ra) :: CH)).
      { eapply pf_ok_call; [exact PF|]. unfold PF_errclear, PF_ERRCLEAR_READY, pf_shift, AEC_RA1, AEC_RA2, AEC_RAL; cbn.
        intros pp [<-|[<-|[]]]; apply in_or_app; right; cbn; [left| right; left]; reflexivity. }
      intros site [-> | ->]; (eapply pf_ok_call; [exact PFE|]); unfold PF_cfree, pf_shift; cbn;
        intros pp [<-|[]]; cbn; [left| right; left]; reflexivity. }
    assert (CFT : as_Cf H (estr_bytes E) <= as_AL H s - errph_cost H ph) by lia.
    eapply (ah_seq H HH).
    { eapply (aec_loop sp gp s11 F fc ra s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra E c x (LBN ++ LB) LB LF (bv_unsigned sp) lo B (as_AL H s - errph_cost H ph) X errv2 CH m2 mo2
                SL OWN ESZ ltac:(intros b Hb; apply in_or_app; right; exact Hb) NCL CEIL ltac:(lia) SPB ltac:(lia) SPA CHS1 PFC CFT 16%nat 0 ltac:(lia) ltac:(lia)).
      unfold aec_inv. cbn [cfg_ms cfg_model]. fold es.
      exists (Z_to_bv 64 AEC_RA0), u0, u1, u2, a0', b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s2'.
      split; [exact VIS3|]. split; [exact KREL3|]. split; [exact MP3|]. split; [exact MI2|]. split; [exact AC2|]. split; [exact ST2|].
      split; [exact ERR2|]. split; [exact AUX2|]. split; [exact HP2|]. split; [exact CW2|].
      split; [destruct E; exact EM2|]. split; [exact FR2|]. split; [exact LS2|]. split; [exact RFS2|]. split; [exact CHN2|]. split; [exact SW2|].
      split; [apply xpres_refl|]. rewrite pref_bytes_0. pose proof (CF0 0 ltac:(lia)). pose proof (CFS 0 0 ltac:(lia) ltac:(lia)) as K00. change (0 + 0) with 0 in K00. lia. }
    intros [ms4 mo4] INV. unfold aec_inv in INV. cbn [cfg_ms cfg_model] in INV. fold es in INV.
    destruct INV as (ra4 & w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & s4' &
                     VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & HP4 & CW4 & EM4 & FR4 & LS4 & RFS4 & CHN4 & SW4 & XP4 & AL4).
    change (16 <? 16) with false in VIS4. cbv iota in VIS4.
    assert (ESK : skipn (Z.to_nat 16) (es_slots E) = []) by (apply skipn_all2; lia).
    rewrite ESK in HP4, SW4. cbn [blocks_slots map concat app] in HP4, SW4.
    assert (ACC4 : accessible m4 es 904).
    { pose proof (proj1 (Forall_forall _ _) LS4 _ ltac:(unfold chain_blocks; cbn; do 3 right; left; reflexivity)) as AD. cbv beta in AD. fold es in AD. rewrite Z5 in AD.
      unfold ERRST_SIZE in AD. eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4
      | eapply aec_segD with (es := es) (lo := lo) (E := clr E 16); [exact EM4| lia| exact B2| lia| exact B7| exact ACC4| lia| exact MI4| exact ST4| exact FR4| exact RAE]|].
    intros msF5 mo5 KREL5 MP5 (a0_5 & a1_5 & m5 & VIS5 & MU5 & WM5 & MI5 & ST5 & EM5).
    assert (SUB4 : forall b, In b (LBN ++ LB) -> In b (LBN ++ LB)) by (intros b Hb; exact Hb).
    destruct (aes_world H HH _ _ _ _ m5 _ _ _ _ _ _ _ _ HP4 SUB4 CW4 AUX4 ERR4 ST4 FR4 AC4 LS4 CEIL ltac:(lia) ltac:(lia) MU5 WM5)
      as (HP5 & CW5 & AUX5 & ERR5 & _ & _ & AC5 & LS5).
    destruct CW5 as (MF5 & IM5 & GM5 & RL5 & EP5 & CP5).
    assert (RFS5 : as_RFS H LF m5).
    { eapply (ah_RFS_frame H HH); [exact RFS4| exact MU5| exact WM5|]. pose proof (RFS_fsb H HH _ _ RFS2) as (F1 & F2 & F3 & F4).
      apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia| apply Forall_nil]. }
    apply (ah_done H HH). unfold errclear_post. cbn [cfg_ms cfg_model].
    exists w0, w1, w2, a0_5, a1_5, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m5, errv2, s4', LBN, c, XS.
    split; [exact VIS5|].
    split. { eapply (ah_mpres_trans H HH); [exact MP1|]. eapply (ah_mpres_trans H HH); [exact MP2|].
             eapply (ah_mpres_trans H HH); [exact MP4| exact MP5]. }
    split. { unfold c4_frame. cbn [cfg_model]. split; [exact KREL5|]. split; [exact MI5|]. split; [exact AC5|]. split; [exact ST5|]. split; [exact AUX5|].
             split; [exact HP5|]. split; [exact MF5|]. split; [exact IM5|]. split; [exact GM5| exact RL5]. }
    split; [rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR5|]. split; [exact DL|]. split; [exact EP5|]. split; [exact CP5|].
    split.
    { split; [| split; [| split]].
      - apply ERRST_split. split.
        + unfold clr in EM5. cbn [es_slots] in EM5. replace (Z.to_nat 16) with (length (es_slots E)) in EM5 by lia.
          rewrite clr_slots_all, SL in EM5. exact EM5.
        + unfold ERROWN, errst_cleared. cbn [es_slots]. apply Forall_forall. intros s0' Hs. apply repeat_spec in Hs. subst s0'. cbn. split; reflexivity.
      - unfold estrs_ok, errst_cleared. cbn [es_slots]. apply Forall_forall. intros sl Hsl. apply repeat_spec in Hsl. subst sl. cbn. lia.
      - unfold lib_shad. rewrite blocks_ERRST_cleared. apply Forall_nil.
      - unfold estrs_cells. rewrite blocks_ERRST_cleared. apply Forall_nil. }
    split; [exact LS5|]. split; [exact FXS|].
    split.
    { eapply xpres_trans.
      { eapply (xpres_weaken H (SB ++ LB) LB); [| apply Z.le_refl| exact SUBx| intros ax K; exact K].
        eapply (xpres_of_munch H s (SB ++ LB)); [exact HH| exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| auto| intros a Ka; unfold X; apply rin_ivs_app in Ka; apply rin_ivs_app; destruct Ka as [Ka|Ka]; [left; exact Ka| right; apply rin_ivs_app; left; exact Ka]]|].
      eapply xpres_trans; [exact XP4|].
      eapply xpres_of_munch_gen; [exact MU5| exact WM5|]. intros a Ha HC. cbn. split; [| exact I]. intros Hr. exact (NCL a Hr HC). }
    split; [exact RFS5|].
    change (Z.to_nat 16) with 16%nat in AL4. rewrite (pref_bytes_all E SL) in AL4. unfold ERRCLEAR_COST. lia.
  Qed.
End W.
