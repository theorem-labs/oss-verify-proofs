(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I3_base Fz_I3_kit Fz_W3_iface Fz_T_ekit Fz_M_free.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_sa Fz_I3_fxi Fz_W2_exd Fz_W5_defs Fz_W5_env Fz_W5_gsi Fz_W5_gsi0 Fz_W5_vset Fz_W5_new Fz_W5_debug Fz_W5_clear Fz_W5_clear2 Fz_W5_clearl.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition cboxed (P : Prop) : Prop := P.
Ltac cbox H := lazymatch type of H with ?P => change P with (cboxed P) in H end.
Ltac cunbox H := unfold cboxed in H.

Section Clr. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (LBall LB LBL : list block) (L : @clist bptr) (f : nat) (pe : bptr) (E top bot lo B : Z) (strs : list block).
  Hypothesis CF : crypto_free_stmt.

  (* [comment removed for export] *)
  Definition clrT : bptr -> Prop := fun q => q = pe \/ In q (map blk_id strs).
  Definition clrS : bptr -> Prop := fun q => In q (map blk_id strs).

  (* [comment removed for export] *)
  Definition clr_pre : Prop :=
       cstate s LBall LB L m sp tp lo B /\ lo <= bv_unsigned sp - (64 + ERRN_STACK) /\ libenv m LBL E /\ incl_blocks LBL LBall
    /\ (forall b, In b LBL -> ~ In (blk_id b) (map blk_id strs)) /\ In (pe, E, 904) LBall
    /\ Forall (fun b => cown LBall L (blk_id b) (blk_addr b) (blk_size b) (blk_size b) /\ blk_id b <> pe) strs
    /\ (length strs <= f)%nat.

  (* [comment removed for export] *)
  Definition clr_lists (f1 : nat) (LB1 : list block) (L1 : @clist bptr) (strs1 : list block) : Prop :=
       Forall (fun b => cown LB1 L1 (blk_id b) (blk_addr b) (blk_size b) (blk_size b)) strs1
    /\ (forall b, In b strs1 -> In b strs) /\ (length strs1 <= length strs)%nat
    /\ (forall b, In b LB1 <-> In b LBall /\ (In b strs -> In b strs1))
    /\ (forall q nm, In (q, nm) L1 <-> In (q, nm) L /\ (In q (map blk_id strs) -> In q (map blk_id strs1)))
    /\ (f - (length strs - length strs1) <= f1)%nat /\ (length strs1 <= f1)%nat /\ cgrow L L1 0 0 0
    /\ In (pe, E, 904) LB1 /\ incl_blocks LBL LB1.

  Definition clr_frame (jk : list byte) : list cell := [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition clr_head (i : Z) (f1 : nat) (L1 : @clist bptr) (s1' : PState) (ms1 : machine_state) : Prop :=
    exists (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jk : list byte) (m1 : mem) (LB1 : list block)
           (fl mk buf fs ls fn : list word) (ks : list (Z * bool)) (strs1 : list block),
         ms1 = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 i) (Z_to_bv 64 16) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CLR_HEAD) fc None m1 (seg_rom usegs)
      /\ cstate s1' LB1 LB L1 m1 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B
      /\ cframe clrT [] (bv_unsigned sp) s LBall L m s1' LB1 L1 m1
      /\ libenv m1 LBL E
      /\ rw_cells usegs m1 (bv_unsigned sp + -48) (clr_frame jk)
      /\ es_rep m1 E top bot fl mk buf fs ls fn
      /\ slots_ok fs fn ks strs1 /\ (forall ik, In ik ks -> i <= fst ik)
      /\ clr_lists f1 LB1 L1 strs1.

  (* [comment removed for export] *)
  Definition clr_mid (i : Z) (f1 : nat) (L1 : @clist bptr) (s1' : PState) (ms1 : machine_state) : Prop :=
    exists (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (jk : list byte) (m1 : mem) (LB1 : list block)
           (fl mk buf fs ls fn : list word) (ks : list (Z * bool)) (strs1 : list block),
         ms1 = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (i + 1)) (Z_to_bv 64 16) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if i =? 15 then U.Fz_I3_eciter.FZ_ECL_DONE else CLR_HEAD)) fc None m1 (seg_rom usegs)
      /\ cstate s1' LB1 LB L1 m1 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B
      /\ cframe clrT [] (bv_unsigned sp) s LBall L m s1' LB1 L1 m1
      /\ libenv m1 LBL E
      /\ rw_cells usegs m1 (bv_unsigned sp + -48) (clr_frame jk)
      /\ es_rep m1 E top bot fl mk buf fs ls (upd fn (Z.to_nat i) (Z_to_bv 64 0))
      /\ slots_ok fs (upd fn (Z.to_nat i) (Z_to_bv 64 0)) ks strs1 /\ (forall ik, In ik ks -> i + 1 <= fst ik)
      /\ clr_lists f1 LB1 L1 strs1.

  Definition clr_post : nat -> @clist bptr -> PState -> machine_state -> Prop :=
    cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B clrT [] (length strs) 0 0 0
       (fun _ LBall' L' m' => (forall b, In b LBall' <-> (In b LBall /\ ~ In b strs)) /\ (forall q nm, In (q, nm) L' <-> (In (q, nm) L /\ ~ In q (map blk_id strs)))
            /\ libenv m' LBL E /\ errst_at_rest E [] m').

  (* [comment removed for export] *)
  Lemma clr_npe : clr_pre -> ~ In pe (map blk_id strs).
  Proof.
    intros (_ & _ & _ & _ & _ & _ & OWNS & _) Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb).
    exact (proj2 (proj1 (List.Forall_forall _ _) OWNS b Hb) Eb).
  Qed.

  (* [comment removed for export] *)
  Lemma clr_libenv_keep : forall (P : Z -> Prop) m1 m2 LB1,
    clr_pre -> libenv m1 LBL E -> incl_blocks LBL LB1 -> agree_on P m1 m2 ->
    (forall a, 0x2c0000 <= a < 0x353000 -> ~ ralloc_static a -> a <> LX_FLAGS -> P a) ->
    (forall b a, In b LBL -> In b LB1 -> ~ In (blk_id b) (map blk_id strs) -> blk_addr b <= a < blk_addr b + blk_size b -> P a) ->
    libenv m2 LBL E.
  Proof.
    intros P m1 m2 LB1 (_ & _ & _ & _ & LBLX & _) ENV1 INCL1 AG HS HB.
    eapply libenv_agree; [exact ENV1|]. eapply agree_on_mono; [exact AG|]. intros a [Hs|(b & Hb & Hr)].
    - destruct (libenv_fp_where LBL a (or_introl Hs)) as [(X1 & X2 & X3)|(b & Hb & Hr)]; [exact (HS a X1 X2 X3)|].
      exact (HB b a Hb (INCL1 _ Hb) (LBLX _ Hb) Hr).
    - exact (HB b a Hb (INCL1 _ Hb) (LBLX _ Hb) Hr).
  Qed.

  (* [comment removed for export] *)
  Lemma clr_libenv_seg : forall W m1 m2 s1' LB1 L1 sp1,
    clr_pre -> libenv m1 LBL E -> incl_blocks LBL LB1 -> In (pe, E, 904) LB1 -> cstate s1' LB1 LB L1 m1 sp1 tp lo B ->
    munch W m1 m2 -> wmono usegs m1 m2 ->
    (forall a, (a < lo \/ bv_unsigned sp <= a) -> (a < E \/ E + 904 <= a) -> outside W a) ->
    libenv m2 LBL E.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros W m1 m2 s1' LB1 L1 sp1 PRE ENV1 INCL1 INE1 CST1 MU WM HW. pose proof PRE as (_ & SLO & _).
    pose proof (cstate_B _ _ _ _ _ _ _ _ _ CST1) as (_ & LO1 & GLO1). unfold GLOBALS_TOP in GLO1.
    eapply (clr_libenv_keep _ m1 m2 LB1 PRE ENV1 INCL1 (agree_on_of_munch _ _ _ MU WM)).
    - intros a X1 X2 X3. cbv beta. apply HW; [left; lia|].
      pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 INE1) as (_ & _ & _ & ECL & EIMG). clear - X1 ECL EIMG LO1 GLO1. lia.
    - intros b a Hb Hb1 NI Hr. cbv beta. destruct b as [[q A] n]. cbn [blk_addr blk_size blk_id fst snd] in Hr, NI.
      pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 Hb1) as (_ & _ & _ & BCL & _).
      assert (NE : q <> pe). { intros ->. pose proof PRE as (_ & _ & _ & _ & _ & _ & OWNS & _).
        destruct (cown_block_eq LB1 pe A n E 904 (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST1)) Hb1 INE1) as [_ Hn].
        pose proof PRE as (_ & _ & ENV & _). destruct (libenv_cells _ _ _ ENV) as (od & pad & tw & ne & k & MK & SA & NODES & pm & psa & pn & pk & LK & ELBL & _).
        rewrite ELBL in Hb. cbn [In] in Hb. clear - Hb Hn. destruct Hb as [Hb|[Hb|[Hb|[Hb|[]]]]]; apply (f_equal snd) in Hb; cbn [snd] in Hb; lia. }
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST1 Hb1 INE1 NE) as D.
      apply HW; [left; clear - Hr BCL LO1; lia| clear - Hr D; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma clr_stack_seg : forall m1 m2 s1' LB1 L1 sp1 jk,
    In (pe, E, 904) LB1 -> cstate s1' LB1 LB L1 m1 sp1 tp lo B -> munch [(E, E + 904)] m1 m2 -> wmono usegs m1 m2 ->
    rw_cells usegs m1 (bv_unsigned sp + -48) (clr_frame jk) -> lo <= bv_unsigned sp + -48 ->
    rw_cells usegs m2 (bv_unsigned sp + -48) (clr_frame jk) /\ (stk usegs m1 lo (bv_unsigned sp + -48) -> stk usegs m2 lo (bv_unsigned sp + -48)).
  Proof.
    intros m1 m2 s1' LB1 L1 sp1 jk INE1 CST1 MU WM FRC SLO1.
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 INE1) as (_ & _ & _ & ECL & _). pose proof (cstate_B _ _ _ _ _ _ _ _ _ CST1) as (_ & LO1 & _).
    split.
    - eapply rw_cells_transport; [exact FRC| exact MU| exact WM|]. cbn [disjoint_from cells_size clr_frame csize Nat.add]. clear - ECL LO1 SLO1. lia.
    - intros ST. eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn [disjoint_from]. clear - ECL LO1 SLO1. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma clr_free :
    forall (SITE : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s0x s1x s2x s3x s4x s5x s6x : word)
           (m1 : mem) (s1' : PState) (LB1 : list block) (L1 : @clist bptr) (f1 : nat)
           (fs fn : list word) (ks : list (Z * bool)) (strs1 : list block) (ik : Z * bool) (w : word),
    clr_pre -> 0 <= SITE < 2 ^ 64 -> SITE mod 2 = 0 ->
    slots_ok fs fn ks strs1 -> length fs = 16%nat -> length fn = 16%nat -> 0 <= fst ik < 16 -> slot_word fs fn ik = Some w ->
    clr_lists f1 LB1 L1 strs1 ->
    cstate s1' LB1 LB L1 m1 (Z_to_bv 64 (bv_unsigned sp + -112)) tp lo B ->
    cframe clrT [] (bv_unsigned sp) s LBall L m s1' LB1 L1 m1 ->
    libenv m1 LBL E ->
    climpl f1 L1 s1'
      (MS (mkR (Z_to_bv 64 SITE) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 s0x s1x w a1 a2 a3 a4 a5 a6 a7
               s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_CRYPTO_FREE) fc None m1 (seg_rom usegs))
      (fun f2 L2 s2' ms2 => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem) (LB2 : list block)
                                   (ks2 : list (Z * bool)) (strs2 : list block),
            ms2 = MS (mkR (Z_to_bv 64 SITE) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' s0x s1x a0' a1' a2' a3' a4' a5' a6' a7'
                          s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 SITE) fc None m2 (seg_rom usegs)
          /\ cstate s2' LB2 LB L2 m2 (Z_to_bv 64 (bv_unsigned sp + -112)) tp lo B
          /\ cframe clrT [] (bv_unsigned sp) s LBall L m s2' LB2 L2 m2
          /\ cfr clrS [] (bv_unsigned sp - 112) LB1 m1 m2
          /\ libenv m2 LBL E
          /\ slots_ok (fst (zero_slot fs fn ik)) (snd (zero_slot fs fn ik)) ks2 strs2
          /\ (forall ik', In ik' ks2 <-> In ik' ks /\ ik' <> ik)
          /\ clr_lists f2 LB2 L2 strs2).
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros until w. intros PRE SR SEV SOK L16 L16' RI SW LISTS1 CST1 FR1 ENV1. pose proof CF as CF'. unfold crypto_free_stmt in CF'.
    pose proof PRE as (CST & SLO & ENV & INCL & LBLX & INE & OWNS & Hf).
    pose proof LISTS1 as (OWN1 & SUB1 & LEN1 & HLB1 & HL1 & FU1 & FU2 & GR1 & INE1 & INCL1).
    pose proof CST1 as (HP1 & _ & (errv1 & _ & SPB1 & ST1 & LO1 & _ & MI1 & _) & LXS1 & _ & _ & GLO1).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ERRN_STACK, GLOBALS_TOP, ceil_window in *.
    assert (USP1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    rewrite USP1 in SPB1, ST1.
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 INE1) as (E0 & _ & _ & ECL & EIMG).
    destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [NDB1 NDL1].
    pose proof SOK as (NDK & LENK & RNG & SL & NUL & NDS).
    pose proof (clr_npe PRE) as NPE.
    destruct ik as [i isf]. cbn [fst snd] in RI.
    destruct (slot_dec (i, isf) ks) as [IN|NI].
    - (* [comment removed for export] *)
      destruct (slot_owned fs fn ks strs1 (i, isf) SOK IN) as (j & bj & Hk & Hs & SWb & Ab & Sb).
      rewrite SWb in SW. injection SW as <-.
      pose proof (proj1 (List.Forall_forall _ _) OWN1 bj (nth_error_In _ _ Hs)) as OWNb. cbv beta in OWNb.
      assert (INbs : In bj strs) by (exact (SUB1 _ (nth_error_In _ _ Hs))).
      assert (INB1 : In bj LB1) by (rewrite <- (blk_eta bj); exact (proj1 OWNb)).
      assert (LEN1p : (1 <= length strs1)%nat) by (pose proof (nth_error_lt _ _ _ Hs); lia).
      eapply climpl_seq.
      { eapply (CF' (Z_to_bv 64 SITE) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 s0x s1x _ a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6
                   F fc m1 s1' LB1 LB L1 f1 (blk_id bj) (blk_addr bj) (blk_size bj) (blk_size bj) lo B);
          [clear - FU2 LEN1p; lia| exact OWNb| exact CST1| rewrite USP1; unfold CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity]. }
      intros f2 L2 st2 ms2 (v & m2 & LB2 & RET & FU & GR & CST2 & FRM & -> & idx & HN & ->).
      destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
      replace (ret_pc (Z_to_bv 64 SITE)) with (Z_to_bv 64 SITE) by (symmetry; apply ret_pc_even; [exact SR| exact SEV]). rewrite USP1 in FRM.
      replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) in FRM by lia.
      pose proof FRM as (CFR & KP & _).
      apply climpl_done. do 15 eexists. exists m2, (lb_remove (blk_id bj) LB1), (rm_nth j ks), (rm_nth j strs1).
      split; [reflexivity|]. split; [exact CST2|].
      split. { eapply cframe_call; [exact FR1| exact FRM| clear - RSP; lia| intros a X; exact X|]. intros q _ NT E1. apply NT. right. rewrite <- E1. apply in_map. exact INbs. }
      split. { eapply agree_on_mono; [exact CFR|]. intros a [X|[(b0 & Hb0 & NT0 & Hr0)|X]]; [left; exact X| | right; right; exact X].
               right; left. exists b0. split; [exact Hb0|]. split; [| exact Hr0]. intros E1. apply NT0. unfold clrS. rewrite <- E1. apply in_map. exact INbs. }
      split. { eapply (clr_libenv_keep _ m1 m2 LB1 PRE ENV1 INCL1 CFR).
               - intros a X1 X2 X3. right; right. split; [exact X1|]. split; [exact X2|]. split; [exact X3| cbn; tauto].
               - intros b a Hb Hb1 NIb Hr. right; left. exists b. split; [exact Hb1|]. split; [| exact Hr]. intros E1. apply NIb. rewrite <- E1. apply in_map. exact INbs. }
      split; [exact (slot_free fs fn ks strs1 j (i, isf) bj SOK L16 L16' Hk Hs)|].
      split. { intros ik'. apply (rm_nth_In_iff j ks (i, isf) ik'); [| exact Hk]. apply (proj1 (NoDup_ListNoDup ks)). exact NDK. }
      (* [comment removed for export] *)
      split; [exact (clr_own_step LB1 strs1 L1 j bj idx NDS Hs HN OWN1)|].
      split; [intros b Hb; exact (SUB1 _ (rm_nth_In j strs1 bj b Hs Hb))|].
      split; [rewrite (rm_nth_length j strs1 bj Hs); clear - LEN1 LEN1p; lia|].
      split; [exact (clr_LB_step LBall LB1 strs strs1 j bj NDB1 NDS Hs SUB1 INB1 HLB1)|].
      split; [exact (clr_L_step L L1 strs strs1 j bj idx NDL1 NDS Hs SUB1 HN HL1)|].
      split; [rewrite (rm_nth_length j strs1 bj Hs); clear - FU FU1 FU2 LEN1 LEN1p; lia|].
      split; [rewrite (rm_nth_length j strs1 bj Hs); clear - FU FU1 FU2 LEN1 LEN1p; lia|].
      split. { pose proof (w_bounds (blk_size bj) ltac:(clear - Sb; lia)) as WB.
               eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR)| clear - WB; lia| clear - WB; lia| clear - WB; lia]. }
      split. { apply (proj2 (lb_remove_In _ _ _)). split; [exact INE1|]. cbn [blk_id fst]. intros E1. exact (proj2 (proj1 (List.Forall_forall _ _) OWNS bj INbs) (eq_sym E1)). }
      intros b Hb. apply (proj2 (lb_remove_In _ _ _)). split; [exact (INCL1 _ Hb)|]. intros E1. apply (LBLX _ Hb). rewrite E1. apply in_map. exact INbs.
    - (* [comment removed for export] *)
      pose proof (slot_unowned_zero fs fn ks strs1 i isf SOK L16 L16' RI NI) as W0. rewrite W0 in SW. injection SW as <-.
      eapply climpl_evt.
      { eapply (crypto_free_null (Z_to_bv 64 SITE) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 s0x s1x _ a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo);
          [reflexivity| exact LXS1| rewrite USP1; exact ST1| exact GLO1| rewrite USP1; clear - SLO; lia| exact MI1]. }
      intros ms2 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU & WM & MI2 & ST2).
      rewrite USP1 in MU, ST2.
      replace (ret_pc (Z_to_bv 64 SITE)) with (Z_to_bv 64 SITE) by (symmetry; apply ret_pc_even; [exact SR| exact SEV]).
      assert (FRX : cframe clrS [] (bv_unsigned sp - 112) s1' LB1 L1 m1 s1' LB1 L1 m2).
      { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP1| clear - SLO LO1; lia|].
        apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO1; lia| apply Forall_nil]. }
      apply climpl_done. do 15 eexists. exists m2, LB1, ks, strs1.
      split; [reflexivity|].
      split. { eapply (cstate_seg _ _ _ _ _ m1 m2 _ _ tp lo B (bv_unsigned sp - 112));
                 [exact CST1| exact MU| exact WM| exact MI2| | clear - SLO LO1; lia| clear - SPB1; lia| | rewrite USP1; exact ST2| rewrite USP1; exact SPB1].
               - apply Forall_cons; [apply cwin_stack; clear - SLO LO1; lia| apply Forall_nil].
               - cbn [disjoint_from]. unfold LX_FLAGS. clear - GLO1 SLO; lia. }
      split. { eapply cframe_seg; [exact FR1| exact MU| exact WM| exact HP1| clear - SLO LO1; lia|].
               apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO1; lia| apply Forall_nil]. }
      split; [exact (proj1 FRX)|].
      split. { eapply (clr_libenv_seg _ m1 m2 s1' LB1 L1 _ PRE ENV1 INCL1 INE1 CST1 MU WM). intros a H1 H2. cbn [outside]. clear - H1 H2 SLO. lia. }
      split. { unfold zero_slot. cbn [fst snd]. unfold slot_word in W0. cbn [fst snd] in W0.
               destruct isf; cbn [fst snd]; rewrite (upd_same _ _ _ W0); exact SOK. }
      split. { intros ik'. split; [intros H; split; [exact H| intros ->; exact (NI H)]| intros [H _]; exact H]. }
      exact LISTS1.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma clr_step : forall i f1 L1 s1' ms1, clr_pre -> 0 <= i < 16 -> clr_head i f1 L1 s1' ms1 -> climpl f1 L1 s1' ms1 (clr_mid i).
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros i f1 L1 s1' ms1 PRE Hi (rax & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & jk & m1 & LB1 & fl & mk & buf & fs & ls & fn & ks & strs1
                                    & -> & CST1 & FR1 & ENV1 & FRC1 & ES1 & SOK1 & KS1 & LISTS1).
    pose proof PRE as (CST & SLO & ENV & INCL & LBLX & INE & OWNS & Hf). pose proof (clr_npe PRE) as NPE.
    pose proof LISTS1 as (OWN1 & SUB1 & LEN1 & HLB1 & HL1 & FU1 & FU2 & GR1 & INE1 & INCL1).
    pose proof CST1 as (HP1 & _ & (errv1 & _ & SPB1 & ST1 & LO1 & _ & MI1 & _) & LXS1 & _ & _ & GLO1).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ERRN_STACK, GLOBALS_TOP, ceil_window in *.
    assert (USP1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    assert (USP2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    assert (H112 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) + -64 = bv_unsigned sp + -112) by (rewrite USP1; lia).
    rewrite USP1 in SPB1, ST1.
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 INE1) as (E0 & E16 & _ & ECL & EIMG).
    assert (E8 : E mod 8 = 0) by (clear - E16; Z.div_mod_to_equations; lia). cbox EIMG.
    pose proof SOK1 as (NDK & LENK & RNG & SL & NUL & NDS).
    pose proof ES1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L7 & _ & _ & _ & L9 & _).
    destruct (nth_error fs (Z.to_nat i)) as [w|] eqn:FSI; [| exfalso; apply nth_error_None in FSI; clear - FSI L7 Hi; lia].
    destruct (nth_error fn (Z.to_nat i)) as [w'|] eqn:FNI; [| exfalso; apply nth_error_None in FNI; clear - FNI L9 Hi; lia].
    (* [comment removed for export] *)
    cprefix. eapply evt_cut.
    { eapply (clr_sA_walk rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo E i top bot w fl mk buf fs ls fn);
        [exact Hi| exact FSI| exact ES1| exact E0| exact E8| exact EIMG| rewrite USP1; exact ST1| exact GLO1| clear - ECL LO1; lia| rewrite USP1; clear - SLO; lia| exact MI1]. }
    intros msA (t0a & t1a & t2a & a1a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & mA & -> & MUA & WMA & MIA & STA & HFA & ESA). chere.
    rewrite H112. rewrite H112 in STA, HFA. rewrite USP1 in MUA.
    assert (FRCA : rw_cells usegs mA (bv_unsigned sp + -48) (clr_frame jk)).
    { eapply rw_cells_transport; [exact FRC1| exact MUA| exact WMA|]. cbn [disjoint_from cells_size clr_frame csize Nat.add]. clear - ECL LO1 SLO. lia. }
    assert (CSTA : cstate s1' LB1 LB L1 mA (Z_to_bv 64 (bv_unsigned sp + -112)) tp lo B).
    { eapply (cstate_seg _ _ _ _ _ m1 mA _ _ tp lo B (bv_unsigned sp + -48)); [exact CST1| exact MUA| exact WMA| exact MIA| | clear - SLO LO1; lia| exact SPB1| | rewrite USP2; exact STA| rewrite USP2; clear - SPB1; lia].
      - apply Forall_cons; [apply cwin_stack; clear - SLO LO1; lia|].
        apply Forall_cons; [apply (cwin_block _ _ _ (pe, E, 904)); [exact INE1| cbn; lia| cbn; lia]| apply Forall_nil].
      - cbn [disjoint_from]. unfold LX_FLAGS. cunbox EIMG. clear - EIMG E0 GLO1 SLO LO1; lia. }
    assert (FRA : cframe clrT [] (bv_unsigned sp) s LBall L m s1' LB1 L1 mA).
    { eapply cframe_seg; [exact FR1| exact MUA| exact WMA| exact HP1| clear - SLO LO1; lia|].
      apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO1; lia|].
      apply Forall_cons; [| apply Forall_nil]. apply (cseg_ok_block _ _ _ _ _ (pe, E, 904)); [exact INE1| | cbn; lia| cbn; lia].
      intros b0 _ NT. cbn [blk_id fst]. intros E1. apply NT. left. exact E1. }
    assert (ENVA : libenv mA LBL E).
    { eapply (clr_libenv_seg _ m1 mA s1' LB1 L1 _ PRE ENV1 INCL1 INE1 CST1 MUA WMA). intros a H1 H2. cbn [outside]. clear - H1 H2 SLO; lia. }
    (* [comment removed for export] *)
    eapply climpl_seq.
    { eapply (clr_free SITE_clr_f1 t0a t1a t2a a1a (Z_to_bv 64 112) a3a a4a a5a a6a a7a t3a t4a t5a t6a
                 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 E) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (E + 576 + i * 8)) (Z_to_bv 64 (E + i * 4)) (Z_to_bv 64 (E + i * 4 + 512)) s6
                 mA s1' LB1 L1 f1 fs fn ks strs1 (i, false) w);
        [exact PRE| unfold SITE_clr_f1; lia| reflexivity| exact SOK1| exact L7| exact L9| cbn [fst]; exact Hi| unfold slot_word; cbn [fst snd]; exact FSI
        | exact LISTS1| exact CSTA| exact FRA| exact ENVA]. }
    intros f2 L2 s2' ms2 (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & LB2 & ks2 & strs2
                          & -> & CST2 & FR2 & CFR2 & ENV2 & SOK2 & HK2 & LISTS2).
    unfold zero_slot in SOK2. cbn [fst snd] in SOK2.
    pose proof LISTS2 as (OWN2 & SUB2 & LEN2 & HLB2 & HL2 & FU1' & FU2' & GR2 & INE2 & INCL2).
    pose proof CST2 as (HP2 & _ & (errv2 & _ & SPB2 & ST2 & LO2 & _ & MI2 & _) & LXS2 & _ & _ & GLO2).
    rewrite USP2 in SPB2, ST2.
    assert (ES2 : es_rep m2 E top bot (upd fl (Z.to_nat i) (Z_to_bv 64 0)) (upd mk (Z.to_nat i) (Z_to_bv 64 0)) (upd buf (Z.to_nat i) (Z_to_bv 64 0)) fs
                        (upd ls (Z.to_nat i) (Z_to_bv 64 (-1))) fn).
    { eapply (es_rep_agree _ mA m2); [exact CFR2| exact ESA|]. intros a Ha. right; left. exists (pe, E, 904). split; [exact INE1|]. split; [exact NPE| cbn; lia]. }
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FRCA ltac:(clear - RSP; lia)) as FRC2.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 HFA ltac:(clear - RSP; lia)) as HF2.
    (* [comment removed for export] *)
    rewrite <- H112. cprefix. eapply evt_cut.
    { eapply (clr_sB_walk (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0b t1b t2b sp a0b a1b a2b a3b a4b a5b a6b a7b s4 s5 s6 s7 s8 s9 s10 s11 t3b t4b t5b t6b F fc m2 lo E i top bot w'
                 (upd fl (Z.to_nat i) (Z_to_bv 64 0)) (upd mk (Z.to_nat i) (Z_to_bv 64 0)) (upd buf (Z.to_nat i) (Z_to_bv 64 0)) fs (upd ls (Z.to_nat i) (Z_to_bv 64 (-1))) fn);
        [exact Hi| exact FNI| exact ES2| exact E0| exact E8| exact EIMG| rewrite H112; exact ST2| exact GLO1| clear - ECL LO1; lia| rewrite USP1; clear - SLO; lia
        | rewrite H112; exact HF2| exact MI2]. }
    intros msB (t0c & t1c & t2c & a1c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & mB & -> & MUB & WMB & MIB & STB & HFB & ESB). chere.
    rewrite H112. rewrite H112 in STB, HFB.
    destruct (clr_stack_seg m2 mB s2' LB2 L2 _ jk INE2 CST2 MUB WMB FRC2 ltac:(clear - SLO LO1; lia)) as [FRCB _].
    assert (CSTB : cstate s2' LB2 LB L2 mB (Z_to_bv 64 (bv_unsigned sp + -112)) tp lo B).
    { eapply (cstate_seg _ _ _ _ _ m2 mB _ _ tp lo B lo); [exact CST2| exact MUB| exact WMB| exact MIB| | lia| clear - SPB2 SLO LO1; lia| | rewrite USP2; exact STB| rewrite USP2; exact SPB2].
      - apply Forall_cons; [apply (cwin_block _ _ _ (pe, E, 904)); [exact INE2| cbn; lia| cbn; lia]| apply Forall_nil].
      - cbn [disjoint_from]. unfold LX_FLAGS. cunbox EIMG. clear - EIMG E0; lia. }
    assert (FRB : cframe clrT [] (bv_unsigned sp) s LBall L m s2' LB2 L2 mB).
    { eapply cframe_seg; [exact FR2| exact MUB| exact WMB| exact HP2| clear - SLO LO1; lia|].
      apply Forall_cons; [| apply Forall_nil]. apply (cseg_ok_block _ _ _ _ _ (pe, E, 904)); [exact INE2| | cbn; lia| cbn; lia].
      intros b0 _ NT. cbn [blk_id fst]. intros E1. apply NT. left. exact E1. }
    assert (ENVB : libenv mB LBL E).
    { eapply (clr_libenv_seg _ m2 mB s2' LB2 L2 _ PRE ENV2 INCL2 INE2 CST2 MUB WMB). intros a H1 H2. cbn [outside]. clear - H1 H2; lia. }
    (* [comment removed for export] *)
    eapply climpl_seq.
    { eapply (clr_free SITE_clr_f2 t0c t1c t2c a1c (Z_to_bv 64 114) a3c a4c a5c a6c a7c t3c t4c t5c t6c
                 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (E + 768 + i * 8)) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (E + 576 + i * 8)) (Z_to_bv 64 (E + i * 4)) (Z_to_bv 64 (E + i * 4 + 512)) s6
                 mB s2' LB2 L2 f2 (upd fs (Z.to_nat i) (Z_to_bv 64 0)) fn ks2 strs2 (i, true) w');
        [exact PRE| unfold SITE_clr_f2; lia| reflexivity| exact SOK2| rewrite upd_length; exact L7| exact L9| cbn [fst]; exact Hi| unfold slot_word; cbn [fst snd]; exact FNI
        | exact LISTS2| exact CSTB| exact FRB| exact ENVB]. }
    intros f3 L3 s3' ms3 (t0d & t1d & t2d & a0d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m3 & LB3 & ks3 & strs3
                          & -> & CST3 & FR3 & CFR3 & ENV3 & SOK3 & HK3 & LISTS3).
    unfold zero_slot in SOK3. cbn [fst snd] in SOK3.
    pose proof LISTS3 as (_ & _ & _ & _ & _ & _ & _ & _ & INE3 & INCL3).
    pose proof CST3 as (HP3 & _ & (errv3 & _ & SPB3 & ST3 & LO3 & _ & MI3 & _) & LXS3 & _ & _ & GLO3).
    rewrite USP2 in SPB3, ST3.
    assert (ES3 : es_rep m3 E top bot (upd fl (Z.to_nat i) (Z_to_bv 64 0)) (upd mk (Z.to_nat i) (Z_to_bv 64 0)) (upd buf (Z.to_nat i) (Z_to_bv 64 0))
                        (upd fs (Z.to_nat i) (Z_to_bv 64 0)) (upd ls (Z.to_nat i) (Z_to_bv 64 (-1))) fn).
    { eapply (es_rep_agree _ mB m3); [exact CFR3| exact ESB|]. intros a Ha. right; left. exists (pe, E, 904). split; [exact INE2|]. split; [exact NPE| cbn; lia]. }
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FRCB ltac:(clear - RSP; lia)) as FRC3.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 HFB ltac:(clear - RSP; lia)) as HF3.
    rewrite <- H112. cprefix. eapply evt_cut.
    { eapply (clr_sC_walk (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0d t1d t2d sp a0d a1d a2d a3d a4d a5d a6d a7d s4 s5 s6 s7 s8 s9 s10 s11 t3d t4d t5d t6d F fc m3 lo E i top bot
                 (upd fl (Z.to_nat i) (Z_to_bv 64 0)) (upd mk (Z.to_nat i) (Z_to_bv 64 0)) (upd buf (Z.to_nat i) (Z_to_bv 64 0)) (upd fs (Z.to_nat i) (Z_to_bv 64 0))
                 (upd ls (Z.to_nat i) (Z_to_bv 64 (-1))) fn);
        [exact Hi| exact ES3| exact E0| exact E8| exact EIMG| rewrite H112; exact ST3| exact GLO1| clear - ECL LO1; lia| rewrite USP1; clear - SLO; lia
        | rewrite H112; exact HF3| exact MI3]. }
    intros msC (t0e & t1e & t2e & a0e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & mC & -> & MUC & WMC & MIC & STC & ESC). chere.
    rewrite USP1 in STC.
    destruct (clr_stack_seg m3 mC s3' LB3 L3 _ jk INE3 CST3 MUC WMC FRC3 ltac:(clear - SLO LO1; lia)) as [FRCC _].
    assert (CSTC : cstate s3' LB3 LB L3 mC (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
    { eapply (cstate_seg _ _ _ _ _ m3 mC _ _ tp lo B lo); [exact CST3| exact MUC| exact WMC| exact MIC| | lia| clear - SPB3 SLO LO1; lia| | rewrite USP1; exact STC| rewrite USP1; exact SPB1].
      - apply Forall_cons; [apply (cwin_block _ _ _ (pe, E, 904)); [exact INE3| cbn; lia| cbn; lia]| apply Forall_nil].
      - cbn [disjoint_from]. unfold LX_FLAGS. cunbox EIMG. clear - EIMG E0; lia. }
    assert (FRC : cframe clrT [] (bv_unsigned sp) s LBall L m s3' LB3 L3 mC).
    { eapply cframe_seg; [exact FR3| exact MUC| exact WMC| exact HP3| clear - SLO LO1; lia|].
      apply Forall_cons; [| apply Forall_nil]. apply (cseg_ok_block _ _ _ _ _ (pe, E, 904)); [exact INE3| | cbn; lia| cbn; lia].
      intros b0 _ NT. cbn [blk_id fst]. intros E1. apply NT. left. exact E1. }
    assert (ENVC : libenv mC LBL E).
    { eapply (clr_libenv_seg _ m3 mC s3' LB3 L3 _ PRE ENV3 INCL3 INE3 CST3 MUC WMC). intros a H1 H2. cbn [outside]. clear - H1 H2; lia. }
    apply climpl_done. unfold clr_mid.
    do 16 eexists. exists jk, mC, LB3.
    exists (upd fl (Z.to_nat i) (Z_to_bv 64 0)), (upd mk (Z.to_nat i) (Z_to_bv 64 0)), (upd buf (Z.to_nat i) (Z_to_bv 64 0)), (upd fs (Z.to_nat i) (Z_to_bv 64 0)),
           (upd ls (Z.to_nat i) (Z_to_bv 64 (-1))), fn, ks3, strs3.
    split; [reflexivity|]. split; [exact CSTC|]. split; [exact FRC|]. split; [exact ENVC|]. split; [exact FRCC|]. split; [exact ESC|]. split; [exact SOK3|].
    split; [| exact LISTS3].
    intros [i' f'] Hin. cbn [fst]. destruct (proj1 (HK3 _) Hin) as [Hin2 NE2]. destruct (proj1 (HK2 _) Hin2) as [Hin1 NE1].
    pose proof (KS1 _ Hin1) as LE. cbn [fst] in LE.
    destruct (Z.eq_dec i' i) as [->|NE]; [| clear - LE NE; lia]. exfalso. destruct f'; [exact (NE2 eq_refl)| exact (NE1 eq_refl)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma clr_loop : forall k : nat, (k <= 15)%nat -> clr_pre -> forall f1 L1 s1' ms1, clr_head (15 - Z.of_nat k) f1 L1 s1' ms1 -> climpl f1 L1 s1' ms1 clr_post.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    induction k as [|k IH]; intros Hk PRE f1 L1 s1' ms1 HEAD.
    - (* [comment removed for export] *)
      change (15 - Z.of_nat 0) with 15 in HEAD.
      eapply climpl_seq; [exact (clr_step 15 f1 L1 s1' ms1 PRE ltac:(lia) HEAD)|].
      clear f1 L1 s1' ms1 HEAD. intros f2 L2 s2' ms2 (rax & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & jk & m2 & LB2 & fl & mk & buf & fs & ls & fn & ks & strs2
                                            & -> & CST2 & FR2 & ENV2 & FRC2 & ES2 & SOK2 & KS2 & LISTS2).
      pose proof PRE as (CST & SLO & ENV & INCL & LBLX & INE & OWNS & Hf). pose proof (clr_npe PRE) as NPE.
      pose proof LISTS2 as (OWN2 & SUB2 & LEN2 & HLB2 & HL2 & FU1 & FU2 & GR2 & INE2 & INCL2).
      pose proof CST2 as (HP2 & _ & (errv2 & _ & SPB2 & ST2 & LO2 & _ & MI2 & _) & LXS2 & _ & _ & GLO2).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ERRN_STACK, GLOBALS_TOP, ceil_window in *.
      assert (USP1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
      pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST2 INE2) as (E0 & E16 & _ & ECL & EIMG).
      assert (E8 : E mod 8 = 0) by (clear - E16; Z.div_mod_to_equations; lia). cbox EIMG.
      pose proof (cstate_B _ _ _ _ _ _ _ _ _ CST2) as (_ & LO1 & _).
      (* [comment removed for export] *)
      pose proof SOK2 as (NDK & LENK & RNG & SL & NUL & NDS).
      assert (KS0 : ks = []). { destruct ks as [|ik ks']; [reflexivity|]. exfalso. pose proof (RNG ik (or_introl eq_refl)) as R1. pose proof (KS2 ik (or_introl eq_refl)) as R2. clear - R1 R2. lia. }
      assert (STRS0 : strs2 = []) by (destruct strs2; [reflexivity| subst ks; discriminate LENK]).
      subst ks strs2. cbn [length Nat.sub] in FU1.
      change (if 15 =? 15 then U.Fz_I3_eciter.FZ_ECL_DONE else CLR_HEAD) with U.Fz_I3_eciter.FZ_ECL_DONE. try change (15 + 1) with 16. unfold U.Fz_I3_eciter.FZ_ECL_DONE.
      cprefix. eapply evt_cut.
      { eapply (clr_sC_last_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax jk F fc m2 lo E top bot
                   fl mk buf fs ls fn);
          [exact ES2| exact E0| exact E8| exact EIMG| rewrite <- USP1; exact ST2| exact GLO2| clear - SLO; lia| clear - ECL LO1; lia| exact FRC2| exact MI2]. }
      intros msC (t0e & t1e & t2e & a0e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m3 & -> & MUC & WMC & MIC & STC & ESC). chere.
      apply climpl_done. exists a0e, m3, LB2.
      split; [unfold cret; do 14 eexists; reflexivity|].
      split; [clear - FU1; lia|]. split; [exact GR2|].
      split. { cunbox EIMG. eapply (cstate_seg _ _ _ _ _ m2 m3 _ sp tp lo B (bv_unsigned sp));
                 [exact CST2| exact MUC| exact WMC| exact MIC| | clear - SLO LO1; lia| exact (proj1 (cstate_B _ _ _ _ _ _ _ _ _ CST))| | exact STC| exact (proj1 (cstate_B _ _ _ _ _ _ _ _ _ CST))].
               - apply Forall_cons; [apply (cwin_block _ _ _ (pe, E, 904)); [exact INE2| cbn; lia| cbn; lia]|].
                 apply Forall_cons; [apply cwin_stack; clear - SLO LO1; lia| apply Forall_nil].
               - cbn [disjoint_from]. unfold LX_FLAGS. clear - EIMG E0 SLO GLO2; lia. }
      split. { eapply cframe_seg; [exact FR2| exact MUC| exact WMC| exact HP2| clear - SLO LO1; lia|].
               apply Forall_cons. { apply (cseg_ok_block _ _ _ _ _ (pe, E, 904)); [exact INE2| | cbn; lia| cbn; lia]. intros b0 _ NT. cbn [blk_id fst]. intros E1. apply NT. left. exact E1. }
               apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO1; lia| apply Forall_nil]. }
      split. { intros b. rewrite (HLB2 b). cbn [In]. tauto. }
      split. { intros q nm. rewrite (HL2 q nm). cbn [map In]. tauto. }
      split. { eapply (clr_libenv_seg _ m2 m3 s2' LB2 L2 _ PRE ENV2 INCL2 INE2 CST2 MUC WMC). intros a H1 H2. cbn [outside]. clear - H1 H2 SLO; lia. }
      apply errst_live_rest. exists fl, mk, buf, fs, ls, (upd fn 15%nat (Z_to_bv 64 0)), []. split; [exact ESC| exact SOK2].
    - (* [comment removed for export] *)
      set (i := 15 - Z.of_nat (S k)) in *. assert (Hi : 0 <= i < 15) by (subst i; clear - Hk; lia).
      eapply climpl_seq; [exact (clr_step i f1 L1 s1' ms1 PRE ltac:(clear - Hi; lia) HEAD)|].
      clear f1 L1 s1' ms1 HEAD. intros f2 L2 s2' ms2 (rax & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & jk & m2 & LB2 & fl & mk & buf & fs & ls & fn & ks & strs2
                                            & -> & CST2 & FR2 & ENV2 & FRC2 & ES2 & SOK2 & KS2 & LISTS2).
      apply (IH ltac:(clear - Hk; lia) PRE). replace (15 - Z.of_nat k) with (i + 1) by (subst i; clear - Hk; lia).
      rewrite (proj2 (Z.eqb_neq i 15) ltac:(clear - Hi; lia)).
      unfold clr_head. exists rax, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, jk, m2, LB2.
      exists fl, mk, buf, fs, ls, (upd fn (Z.to_nat i) (Z_to_bv 64 0)), ks, strs2.
      split; [reflexivity|]. split; [exact CST2|]. split; [exact FR2|]. split; [exact ENV2|].
      split; [exact FRC2|]. split; [exact ES2|]. split; [exact SOK2|]. split; [exact KS2| exact LISTS2].
  Qed.
End Clr.

(* [comment removed for export] *)
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem err_clear_steady_proof : crypto_free_stmt -> err_clear_steady_stmt libenv errst_at_rest errst_live.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CF. unfold err_clear_steady_stmt. intros until strs. intros Hf CST SLO ENV INCL LBLX OWN LIVE OWNS.
  assert (PRE : clr_pre sp tp m s LBall LB LBL L f pe E lo B strs) by (exact (conj CST (conj SLO (conj ENV (conj INCL (conj LBLX (conj (proj1 OWN) (conj OWNS Hf)))))))).
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  pose proof (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST)) as ND.
  destruct (libenv_cells _ _ _ ENV) as (od & pad & tw & ne & k & MK & SA & NODES & pm & psa & pn & pk & LK & ELBL & STOP & ONCE & OD & OC & KC & HK & TS & SLOT & HMK & P3 & HSA & HDR & HNO & NE & LEAF).
  destruct LIVE as (fl & mk & buf & fs & ls & fn & ks & ES & SOK).
  destruct OWN as [INE INL].
  assert (INM : In (pm, MK, 72) LBall) by (apply INCL; rewrite ELBL; cbn; tauto).
  assert (INS : In (psa, SA, 32) LBall) by (apply INCL; rewrite ELBL; cbn; tauto).
  assert (INN : In (pn, NODES, 128) LBall) by (apply INCL; rewrite ELBL; cbn; tauto).
  assert (INK : In (pk, LK, 40) LBall) by (apply INCL; rewrite ELBL; cbn; tauto).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INE) as (E0 & E16 & _ & ECL & EIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INM) as (_ & M16 & _ & MCL & MIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INS) as (_ & S16 & _ & SCL & SIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INN) as (_ & N16 & _ & NCL & NIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INK) as (_ & _ & _ & KCL & KIMG).
  assert (E8 : E mod 8 = 0) by (clear - E16; Z.div_mod_to_equations; lia).
  assert (M8 : MK mod 8 = 0) by (clear - M16; Z.div_mod_to_equations; lia). assert (S8 : SA mod 8 = 0) by (clear - S16; Z.div_mod_to_equations; lia). assert (N8 : NODES mod 8 = 0) by (clear - N16; Z.div_mod_to_equations; lia).
  cbox EIMG. cbox MIMG. cbox SIMG. cbox NIMG. cbox KIMG.
  assert (TPV : bv_unsigned tp = RATP) by (rewrite TP; apply unsigned_lit; unfold RATP; lia).
  unfold ERRN_STACK, GLOBALS_TOP, ceil_window in *.
  rewrite <- TPV in TS.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  (* [comment removed for export] *)
  cprefix. eapply evt_cut.
  { pose proof clr_s0_walk as X. unfold CLR_STACK, CF_STACK, RFREE_STACK, FZ_ERRCLR in X. unfold wz, FZ_ERR_CLEAR.
    eapply (X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo TSD_MAIN k MK SA NODES E top bot od pad tw ne fl mk buf fs ls fn);
      first [reflexivity | eassumption | cunbox MIMG; cunbox SIMG; cunbox NIMG; unfold TSD_MAIN, IC_S, RMallocRep.RATP in *; clear - TPV HK MCL SCL NCL ECL LO GLO SLO RSP HMK HSA HNO E0; lia]. }
  intros ms1 (rax & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & jk & m1 & -> & MU0 & WM0 & MI1 & ST1 & FR1 & ES1).
  chere.
  lazymatch goal with |- climpl ?f0 ?L0 ?st0 ?ms0 _ =>
    change (climpl f0 L0 st0 ms0 (clr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LBall LB LBL L f pe E lo B strs)) end.
  apply (clr_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LBall LB LBL L f pe E top bot lo B strs CF 15%nat (le_n 15%nat) PRE).
  change (15 - Z.of_nat 15) with 0. unfold clr_head.
  exists rax, t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', jk, m1, LBall. exists fl, mk, buf, fs, ls, fn, ks, strs.
  split; [reflexivity|].
  split. { eapply (cstate_seg _ _ _ _ _ m m1 _ _ tp lo B (bv_unsigned sp));
             [exact CST| exact MU0| exact WM0| exact MI1| | clear - SLO LO; lia| exact SPB| | rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; clear - SPB; lia].
           - apply Forall_cons; [apply cwin_stack; clear - SLO LO; lia| apply Forall_nil].
           - cbn [disjoint_from]. unfold LX_FLAGS. clear - SLO GLO; lia. }
  split. { eapply cframe_seg; [apply cframe_refl| exact MU0| exact WM0| exact HP| clear - SLO LO; lia|].
           apply Forall_cons; [apply cseg_ok_stack; clear - SLO LO; lia| apply Forall_nil]. }
  split. { eapply libenv_agree; [exact ENV|]. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU0 WM0)|].
           intros a [Hs|(b & Hb & Hr)]; cbv beta; cbn [outside].
           - clear - Hs SLO GLO. unfold libenv_static, IC_S, TH_ONCE, TH_KEY, TSD_MAIN, DC_S, DC_GLOBAL_LOCK, DC_IP12, RMallocRep.RATP in *. lia.
           - rewrite ELBL in Hb. cunbox MIMG. cunbox SIMG. cunbox NIMG. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; cbn [blk_addr blk_size fst snd] in Hr; clear - Hr MCL SCL NCL KCL LO SLO; lia. }
  split; [exact FR1|]. split; [exact ES1|]. split; [exact SOK|]. split; [intros ik Hik; exact (proj1 (proj1 (proj2 (proj2 SOK)) ik Hik))|].
  (* [comment removed for export] *)
  split; [eapply List.Forall_impl; [| exact OWNS]; intros b [Hb _]; exact Hb|].
  split; [intros b Hb; exact Hb|]. split; [lia|].
  split; [intros b; split; [intros H; split; [exact H| intros H'; exact H']| intros [H _]; exact H]|].
  split; [intros q nm; split; [intros H; split; [exact H| intros H'; exact H']| intros [H _]; exact H]|].
  split; [clear - Hf; lia|]. split; [exact Hf|]. split; [apply cgrow_refl|]. split; [exact INE| exact INCL].
Qed.

End WithCeiling0.
