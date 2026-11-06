(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA W_expandA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnAKitAF BnCallAF AFrameComp PlaceRecpA RecpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require W_freeA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_RECP_CTX_FREE : Z := 0x2b1af4.
Notation BN_FREE := W_freeA.BN_FREE.
Notation BN_FREE_STACK := W_freeA.BN_FREE_STACK.
Notation lb_remove_opt := W_freeA.lb_remove_opt.
Definition RECP_FREE_STACK : Z := 32 + BN_FREE_STACK.

Definition tfree_opt {X : Type} (o : option bptr) (k : btree bptr X) : btree bptr X :=
  match o with Some p => TFree p k | None => k end.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition bnfree_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (o : option bptr) (lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom bgasegs)
    /\ mem_inv bgasegs m' /\ stk bgasegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (lb_remove_opt o OW ++ LB) (bv_unsigned sp)) m m'
    /\ rt_credit RT Σ' = rt_credit RT Σ
    /\ AHEAP Σ' (lb_remove_opt o OW) LB m'.

Lemma BN_free_frame_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (o : option bptr) (D n a lo : Z) (tw dw nw : word) (bs : block) (ras : list Z)
    (k : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  (forall p, o = Some p -> In (p, D, n) OW /\ blk_id bs <> p) -> (o = None -> D = 0) ->
  stk bgasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bgasegs m -> tp = wz TP_A -> BnRepDefs.crypto_statics m ->
  rw_cells bgasegs m a [C8 (wz D); C4 tw; C4 dw; C4 nw; C4 (wz 0)] ->
  In bs (OW ++ LB) -> blk_addr bs <= a -> a + 24 <= blk_addr bs + blk_size bs -> a mod 8 = 0 ->
  a0 = wz a ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_FREE (bv_unsigned ra :: ras) ->
  (forall Σ' ms', bnfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB o lo m Σ' ms' -> implA k Σ' Q ms') ->
  implA (tfree_opt o k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_FREE) fc None m (seg_rom bgasegs)).
Proof.
  intros until Q. intros HEAP HO HN ST CEIL LO SPT SP16 MI -> CS BN INS RS1 RS2 AL -> UW CTX K.
  pose proof LO as LO'. unfold W_freeA.BN_FREE_STACK, W_freeA.BN_FREE_D0_STACK, CRYPTO_FREE_STACK, RT_STACK in LO'.
  pose proof (AH_nodup _ _ _ _ HEAP) as NDL.
  unfold W_freeA.BN_FREE, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bs HEAP INS) as (S0 & _ & _ & SC & SI).
  pose proof (AH_acc_in _ _ _ _ bs a 24 HEAP INS RS1 RS2) as ACC.
  pose proof (AH_offsh _ _ _ _ bs HEAP INS) as OFA. unfold SHLO, SHHI in OFA.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof BN as BN0.
  apply (flag_cell_split bgasegs m a _ _ _ _ 0 ltac:(clear; lia)) in BN.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 48, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  assert (EA0 : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - S0 SC RS1 RS2 C1 C2 C3; lia).
  apply implA_from_evt.
  carve_frame 48%nat ST.
  do 7 step.
  step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EA0 in KA; clear - KA S0 RS1; lia|]. clear KA.
  do 4 step. do 3 step. shl_with ACC AL. chk0.
  step. rewrite (zxb_small 0) by (clear; lia). step. step. if_false.
  do 2 step. step.

  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (jfr := j) in *; clearbody jfr end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (AH_frame Σ OW LB m m1 _ HEAP MU WM). constructor; [left; cbn [fst snd]; unfold BnHeapA.ACEIL, USTACK_TOP in *; clear - CEIL LO' SPT; lia | constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (bv_unsigned sp) HEAP MU). constructor; [cbn [fst snd]; unfold BnHeapA.ACEIL in *; clear - CEIL LO'; lia | constructor]. }
  assert (CS1 : BnRepDefs.crypto_statics m1).
  { eapply BnRepA.crypto_statics_agree; [exact AG1 | | exact CS]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -48) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m1 _ (bv_unsigned sp) 48 [CB 8 jfr; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  set (OWd := lb_remove_opt o OW).
  assert (INCd : forall b0, In b0 OWd -> In b0 OW).
  { subst OWd. destruct o as [pd0|]; cbn [W_freeA.lb_remove_opt]; [intros bk Hbk; eapply lb_remove_incl; exact Hbk | auto]. }
  assert (INSd : In bs (OWd ++ LB)).
  { subst OWd. destruct o as [pd0|]; cbn [W_freeA.lb_remove_opt]; [| exact INS].
    apply in_app_or in INS. apply in_or_app. destruct INS as [INS|INS]; [left | right; exact INS].
    apply lb_remove_In. split; [exact INS | exact (proj2 (HO pd0 eq_refl))]. }

  assert (CONT : forall (Σ1 : rts RT) (m2 : mem) (FT : bvmap 5 word) (fcT : bv 32)
                        (q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
      AHEAP Σ1 OWd LB m2 -> agree_on (aclient_addr (OWd ++ LB) (bv_unsigned sp + -48)) m1 m2 ->
      rt_credit RT Σ1 = rt_credit RT Σ ->
      stk bgasegs m2 lo (bv_unsigned sp + -48) -> mem_inv bgasegs m2 ->
      implA k Σ1 Q
        (MS (mkR (Z_to_bv 64 2245208) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 a) q10 q11 q12 q13 q14 q15 q16 q17
                 (Z_to_bv 64 (a + 20)) (Z_to_bv 64 (Z.shiftr (a + 20) 3 + SHB)) s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
            FT (Z_to_bv 64 2245208) fcT None m2 (seg_rom bgasegs))).
  { intros Σ1 m2 FT fcT q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 HEAP2 AG2 CR2 ST2 MI2.
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; clear - Hx SPT; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in BN; [| intros x Hx; right; right; exists bs; split; [exact INSd| cbn in Hx |- *; clear - Hx RS1 RS2; lia]].
    clear BN0.
    pose proof (AH_acc_in _ _ _ _ bs a 24 HEAP2 INSd RS1 RS2) as ACC2.
    assert (AGT : agree_on (aclient_addr (OWd ++ LB) (bv_unsigned sp)) m m2).
    { eapply agree_on_trans.
      - eapply agree_client_weaken; [exact AG1 | clear; lia | intros bk Hbk; apply in_app_or in Hbk; apply in_or_app; destruct Hbk as [Hbk|Hbk]; [left; exact (INCd _ Hbk) | right; exact Hbk]].
      - eapply agree_client_weaken; [exact AG2 | clear; lia | auto]. }
    clear ACC MU WM OFF SHB1 SHB2 HEAP HEAP1 ST MI.
    pose proof (munch_refl (@nil (Z * Z)) m2) as MU2.
    destruct (AH_shb _ _ _ _ HEAP2) as (SHB1 & SHB2).
    apply implA_from_evt.
    shl_with ACC2 AL. chk0.
    step. rewrite (zxb_small 0) by (clear; lia). step. step. if_false.
    do 5 step. release_frame FR ST2 (bv_unsigned sp). step. step.

    apply evt_done. apply (K Σ1). unfold bnfree_postA. do 17 eexists. exists m2.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact AGT|]. split; [exact CR2 | exact HEAP2]. }
  destruct o as [pd|] eqn:Eo; cbn [tfree_opt].
  -
    destruct (HO pd eq_refl) as (HinD & NEQ).
    assert (NLB : ~ In pd (map blk_id LB)).
    { intros H. rewrite map_app in NDL. eapply (nodup_app_disj _ _ pd NDL); [apply (in_map blk_id) in HinD; exact HinD| exact H]. }
    apply evt_done.
    eapply (W_freeA.bn_free_d0_walkA) with (p := pd) (D := D) (n := n) (f := 0) (a := a) (bs := bs) (lo := lo)
                                  (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
    + exact HEAP1.
    + exact HinD.
    + rewrite ESP. exact ST.
    + exact CEIL.
    + rewrite ESP. unfold W_freeA.BN_FREE_D0_STACK, CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia.
    + rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
    + rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
    + exact MI.
    + exact CS1.
    + unfold MallocRep.wz. exact BN0.
    + clear. lia.
    + exact INS.
    + exact RS1.
    + exact RS2.
    + exact AL.
    + rewrite ESP. exact UW1.
    + rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_free_224070 : uk_call W_freeA.BN_FREE 0x224258 W_expandA.BN_FREE_D) CTX).
    + intros Σ1 ms1 PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & AG2 & CR2 & HEAP2).
      rewrite ?ESP in *. rewrite (ret_pc_even 2245208) by (clear; lia).
      assert (EL2 : lb_remove pd (OW ++ LB) = lb_remove pd OW ++ LB) by (rewrite lb_remove_app, (lb_remove_notin pd LB NLB); reflexivity).
      rewrite EL2 in AG2.
      eapply (CONT Σ1 m2 F2 fc2); [exact HEAP2 | exact AG2 | exact CR2 | exact ST2 | exact MI2].
  -
    pose proof (HN eq_refl) as ->.
    apply evt_done.
    eapply (W_freeA.bn_free_d0_null_walkA) with (f := 0) (a := a) (bs := bs) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
    + exact HEAP1.
    + rewrite ESP. exact ST.
    + exact CEIL.
    + rewrite ESP. unfold W_freeA.BN_FREE_D0_STACK, CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia.
    + rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
    + rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
    + exact MI.
    + exact CS1.
    + unfold MallocRep.wz. exact BN0.
    + clear. lia.
    + exact INS.
    + exact RS1.
    + exact RS2.
    + exact AL.
    + rewrite ESP. exact UW1.
    + rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_free_224070 : uk_call W_freeA.BN_FREE 0x224258 W_expandA.BN_FREE_D) CTX).
    + intros ms1 PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & AG2).
      rewrite ?ESP in *. rewrite (ret_pc_even 2245208) by (clear; lia).
      eapply (CONT Σ m2 F2 fc2); [exact HEAP2 | exact AG2 | reflexivity | exact ST2 | exact MI2].
Qed.

End WithRT.

Lemma recp_free_treeA : forall bs : bstate bptr,
  bn_flags (getbn RRecpN bs) = 0 -> bn_flags (getbn RRecpNr bs) = 0 ->
  BN_RECP_CTX_free (tree_ops bptr) bs =
  tfree_opt (bn_d (getbn RRecpN bs)) (tfree_opt (bn_d (getbn RRecpNr bs))
    (TRet (tt, set_recp 0 0 (setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) bs))))).
Proof.
  intros bs F1 F2.
  assert (H1 : forall f, has_flag (getbn RRecpN bs) f = false) by (intros f; unfold has_flag; rewrite F1; reflexivity).
  assert (H2 : forall f, has_flag (getbn RRecpNr bs) f = false) by (intros f; unfold has_flag; rewrite F2; reflexivity).
  assert (H3 : forall b f, has_flag (getbn RRecpNr (setbn RRecpN b bs)) f = false)
    by (intros b f; rewrite getbn_setbn_other by (unfold RRecpN, RRecpNr; lia); apply H2).
  assert (D2' : forall b, bn_d (getbn RRecpNr (setbn RRecpN b bs)) = bn_d (getbn RRecpNr bs))
    by (intros b; rewrite getbn_setbn_other by (unfold RRecpN, RRecpNr; lia); reflexivity).
  unfold BN_RECP_CTX_free, BN_free, bbind, bget, bset, bret, bunr, bsetrecp. cbn [bind ret unreachable tree_ops tbind fst snd].
  rewrite !H1, !H2. cbn [orb]. cbv beta. rewrite !H1.
  destruct (bn_d (getbn RRecpN bs)) as [q1|];
    cbn [bfree_opt bfree bret bind ret lib_free tree_ops tbind fst snd tfree_opt];
    rewrite !H3, !D2'; cbv beta;
    (destruct (bn_d (getbn RRecpNr bs)) as [q2|];
     cbn [bfree_opt bfree bret bind ret lib_free tree_ops tbind fst snd tfree_opt]; reflexivity).
Qed.

Lemma lb_remove_opt_In : forall o (L : list block) b, In b (lb_remove_opt o L) <-> In b L /\ (forall p, o = Some p -> blk_id b <> p).
Proof.
  intros [p|] L b; cbn [W_freeA.lb_remove_opt].
  - rewrite lb_remove_In. split; [intros [H N]; split; [exact H| intros p' E; injection E as <-; exact N]| intros [H N]; split; [exact H| apply N; reflexivity]].
  - split; [intros H; split; [exact H| intros p E; discriminate E]| intros [H _]; exact H].
Qed.

Lemma lb_remove_opt_length : forall o (L : list block), List.NoDup (map blk_id L) -> (forall p, o = Some p -> In p (map blk_id L)) ->
  Z.of_nat (length (lb_remove_opt o L)) = Z.of_nat (length L) - match o with Some _ => 1 | None => 0 end.
Proof.
  intros [p|] L ND H; cbn [W_freeA.lb_remove_opt]; [| lia].
  pose proof (lb_remove_length p L ND (H p eq_refl)) as E. lia.
Qed.

Theorem lib_state_h_setbn_hole : forall cxo hs (s : bstate bptr) m OW PL EA r a b',
  lib_state_hc cxo hs s m OW PL EA -> List.NoDup (map blk_id OW) -> ref_at s OW PL r a -> In r hs -> r <> ROne ->
  bg_ok b' -> ids_ok (setbn r b' s) PL EA ->
  lib_state_hc cxo hs (setbn r b' s) m OW PL EA.
Proof.
  intros cxo hs s m OW PL EA r a b' HS ND HA Hin NE HOK HIDS.
  assert (HV : vref r s) by (eapply ref_at_valid; [exact HS | exact HA]).
  destruct HS as (HC & HE & HO & (S1 & S2 & S3 & HM)).
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split; [apply st_wf_setbn; assumption|]. split; [exact S2|]. split; [exact HIDS|].
  eapply gen_set; [exact HM| exact ND| exact HA| exact HV| left; exact Hin].
Qed.

Lemma all_ids_setbn_nil : forall (s : bstate bptr) PL EA r q, vref r s ->
  In q (all_ids (setbn r (bn_nil 0) s) PL EA) -> In q (all_ids s PL EA).
Proof.
  intros s PL EA r q HV H. unfold all_ids in *. rewrite !in_app_iff in *. destruct H as [H|[H|H]]; [left; exact H| right; left; exact H|].
  right; right. destruct (blocks_setbn r s HV) as (R & P1 & P2). specialize (P2 (bn_nil 0)). cbn [bn_blocks bn_nil bn_d app] in P2.
  apply (Permutation_map fst) in P1. apply (Permutation_map fst) in P2.
  eapply Permutation_in; [apply Permutation_sym; exact P1|]. rewrite map_app. apply in_or_app. right.
  eapply Permutation_in; [exact P2| exact H].
Qed.

Lemma all_ids_without : forall (s : bstate bptr) PL EA r p, ids_ok s PL EA -> vref r s -> bn_d (getbn r s) = Some p ->
  ~ In p (all_ids (setbn r (bn_nil 0) s) PL EA).
Proof.
  intros s PL EA r p IDS HV Hd H. unfold all_ids in H. rewrite !in_app_iff in H. pose proof (bn_in_m r s p HV Hd) as Hm.
  destruct H as [H|[H|H]].
  - exact (ids_pl_m s PL EA p p IDS H Hm eq_refl).
  - exact (ids_ea_m s PL EA p p IDS H Hm eq_refl).
  - exact (ids_without r s p (ids_m_nodup _ _ _ IDS) HV Hd H).
Qed.

Section WithRT2.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma BN_RECP_CTX_free_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL0 : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (an : Z) (bs : block),
  bn_preA Σ ls m OW LB (pl_place_recp PL0 an) EA sp lo RECP_FREE_STACK 0 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_RECP_CTX_FREE (bv_unsigned ra :: ras) ->
  tp = wz TP_A ->
  pl_wf PL0 -> pl_bn PL0 RRecpN = None -> pl_bn PL0 RRecpNr = None -> pl_recp PL0 = None ->
  In bs LB -> blk_addr bs <= an -> an + 64 <= blk_addr bs + blk_size bs -> an mod 8 = 0 ->
  a0 = wz an ->
  implA (BN_RECP_CTX_free (tree_ops bptr) ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m (pl_place_recp PL0 an) EA 0
              (fun _ _ _ PL' _ => PL' = PL0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_RECP_CTX_FREE) fc None m (seg_rom bgasegs)).
Proof.
  intros until bs. intros PRE UW CTX -> PWF0 E1 E2 E3 INB B1 B2 AL ->.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND. pose proof (AH_nodup _ _ _ _ HEAP) as NDL.
  pose proof LO as LO'. unfold RECP_FREE_STACK, W_freeA.BN_FREE_STACK, W_freeA.BN_FREE_D0_STACK, CRYPTO_FREE_STACK, RT_STACK in LO'.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof (recp_at_place PL0 an) as HRC.
  pose proof (recp_at_refN ls OW _ an HRC) as HAN. pose proof (recp_at_refNr ls OW _ an HRC) as HANr.
  assert (NRON : RRecpN <> ROne) by (unfold RRecpN, ROne; lia).
  assert (NRONr : RRecpNr <> ROne) by (unfold RRecpNr, ROne; lia).
  assert (NENr : RRecpN <> RRecpNr) by (unfold RRecpN, RRecpNr; lia).
  assert (HVN : vref RRecpN ls) by (eapply ref_at_valid; [exact LS | exact HAN]).
  assert (HVNr : vref RRecpNr ls) by (eapply ref_at_valid; [exact LS | exact HANr]).
  destruct (lib_state_open [] ls m OW _ EA RRecpN an LS ND HAN ltac:(intros []) NRON) as ((D1 & BN1 & ARR1) & (OK1a & OK1b & OK1c & OK1d) & LSH1).
  destruct (lib_state_open [RRecpN] ls m OW _ EA RRecpNr (an + 24) LSH1 ND HANr ltac:(intros [E|[]]; exact (NENr E)) NRONr)
    as ((D2 & BN2 & ARR2) & (OK2a & OK2b & OK2c & OK2d) & LSH2).
  pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LS (proj2 (proj2 HRC))) as RC. unfold recp_cells in RC.

  destruct OK1d as [F1|F1].
  2: { unfold BN_RECP_CTX_free, bbind, bget, bunr, has_flag. cbn [bind ret unreachable tree_ops tbind fst snd]. rewrite F1. apply implA_unr. }
  destruct OK2d as [F2|F2].
  2: { unfold BN_RECP_CTX_free, bbind, bget, bunr, has_flag. cbn [bind ret unreachable tree_ops tbind fst snd]. rewrite F1, F2. apply implA_unr. }
  rewrite (recp_free_treeA ls F1 F2).
  set (bsF := set_recp 0 0 (setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) ls))).
  unfold bn_arr in ARR1, ARR2. rewrite pl_of_place_recp_N in ARR1. rewrite pl_of_place_recp_Nr in ARR2.
  pose proof (proj1 (proj2 (proj2 PARTS))) as IDS.
  set (bN := getbn RRecpN ls) in *. set (bNr := getbn RRecpNr ls) in *.
  assert (INS1 : forall pd, bn_d bN = Some pd -> In (pd, D1, 8 * Z.of_nat (bn_dmax bN)) OW) by (intros pd E; rewrite E in ARR1; exact (proj1 ARR1)).
  assert (NONE1 : bn_d bN = None -> D1 = 0) by (intros E; rewrite E in ARR1; exact (proj1 ARR1)).
  assert (INS2 : forall pd, bn_d bNr = Some pd -> In (pd, D2, 8 * Z.of_nat (bn_dmax bNr)) OW) by (intros pd E; rewrite E in ARR2; exact (proj1 ARR2)).
  assert (NONE2 : bn_d bNr = None -> D2 = 0) by (intros E; rewrite E in ARR2; exact (proj1 ARR2)).
  assert (NE12 : forall p1 p2, bn_d bN = Some p1 -> bn_d bNr = Some p2 -> p1 <> p2)
    by (intros p1 p2 H1 H2; exact (ids_bn_neq RRecpN RRecpNr ls p1 p2 (ids_m_nodup _ _ _ IDS) HVN HVNr NENr H1 H2)).
  clear ARR1 ARR2.
  assert (INS : In bs (OW ++ LB)) by (apply in_or_app; right; exact INB).
  assert (NBS : forall pd D n, In (pd, D, n) OW -> blk_id bs <> pd).
  { intros pd D n Hin E. rewrite map_app in NDL. eapply (nodup_app_disj _ _ pd NDL); [apply (in_map blk_id) in Hin; exact Hin | rewrite <- E; apply in_map; exact INB]. }

  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bs HEAP INS) as (S0 & _ & _ & SC & SI).
  pose proof (AH_offsh _ _ _ _ bs HEAP INS) as OFA. unfold SHLO, SHHI in OFA.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  unfold bn_cells, MallocRep.wz in BN1, BN2. rewrite F1 in BN1. rewrite F2 in BN2.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 32, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  assert (EA0 : bv_unsigned (Z_to_bv 64 an) = an) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - S0 SC B1 B2 CE1 CE2 CE3; lia).
  unfold BN_RECP_CTX_FREE, MallocRep.wz.
  apply implA_from_evt.
  carve_frame 32%nat ST.
  do 6 step.
  step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EA0 in KA; clear - KA S0 B1; lia|]. clear KA.
  do 4 step. do 2 step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (AH_frame Σ OW LB m m1 _ HEAP MU WM). constructor; [left; cbn [fst snd]; unfold BnHeapA.ACEIL, USTACK_TOP in *; clear - CEIL LO' SPT; lia | constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (bv_unsigned sp) HEAP MU). constructor; [cbn [fst snd]; unfold BnHeapA.ACEIL in *; clear - CEIL LO'; lia | constructor]. }
  assert (CS1 : BnRepDefs.crypto_statics m1).
  { eapply BnRepA.crypto_statics_agree; [exact AG1 | | exact (proj1 LS)]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -32) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m1 _ (bv_unsigned sp) 32 [C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  set (OW1 := lb_remove_opt (bn_d bN) OW).
  set (OW2 := lb_remove_opt (bn_d bNr) OW1).
  assert (INC1 : forall b, In b OW1 -> In b OW) by (intros b Hb; unfold OW1 in Hb; apply lb_remove_opt_In in Hb; exact (proj1 Hb)).
  assert (INC2 : forall b, In b OW2 -> In b OW1) by (intros b Hb; unfold OW2 in Hb; apply lb_remove_opt_In in Hb; exact (proj1 Hb)).
  assert (INS2' : forall pd, bn_d bNr = Some pd -> In (pd, D2, 8 * Z.of_nat (bn_dmax bNr)) OW1).
  { intros pd E. unfold OW1. apply lb_remove_opt_In. split; [exact (INS2 pd E)|]. intros p1 E1'. cbn [blk_id fst]. intros Epd. exact (NE12 p1 pd E1' E (eq_sym Epd)). }
  assert (INSa : In bs (OW1 ++ LB)) by (apply in_or_app; right; exact INB).
  assert (INSb : In bs (OW2 ++ LB)) by (apply in_or_app; right; exact INB).

  apply evt_done.
  eapply (BN_free_frame_walkA) with (o := bn_d bN) (D := D1) (n := 8 * Z.of_nat (bn_dmax bN)) (a := an) (bs := bs) (lo := lo)
                                   (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
  { exact HEAP1. }
  { intros pd E. split; [exact (INS1 pd E) | exact (NBS _ _ _ (INS1 pd E))]. }
  { exact NONE1. }
  { rewrite ESP. exact ST. }
  { exact CEIL. }
  { rewrite ESP. unfold W_freeA.BN_FREE_STACK, W_freeA.BN_FREE_D0_STACK, CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia. }
  { rewrite ESP. unfold USTACK_TOP. clear - SPT. lia. }
  { rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia. }
  { exact MI. }
  { exact CS1. }
  { unfold MallocRep.wz. exact BN1. }
  { exact INS. }
  { exact B1. }
  { clear - B2. lia. }
  { exact AL. }
  { rewrite ESP. exact UW1. }
  { rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_RECP_CTX_free_2b1940 : uk_call BN_RECP_CTX_FREE 2825000 W_freeA.BN_FREE) CTX). }
  intros Σ1 ms1 PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Fx2 & fc2 & m2 & -> & MI2 & ST2 & AG2 & CR2 & HEAP2).
  fold OW1 in AG2, HEAP2.
  rewrite ?ESP in *. rewrite (ret_pc_even 2825000) by (clear; lia). unfold MallocRep.wz.
  assert (STKC : forall x L, bv_unsigned sp + -32 <= x < bv_unsigned sp -> aclient_addr L (bv_unsigned sp + -32) x).
  { intros x L Hx. left. unfold USTACK_TOP. clear - Hx SPT. lia. }
  assert (INB' : forall x L, In bs L -> an <= x < an + 60 -> aclient_addr L (bv_unsigned sp + -32) x).
  { intros x L HL Hx. right; right. exists bs. split; [exact HL | clear - Hx B1 B2; lia]. }
  apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply STKC; clear - Hx; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in BN2; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply (INB' x _ INSa); clear - Hx; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in RC; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply (INB' x _ INSa); clear - Hx; lia].
  assert (CS2 : BnRepDefs.crypto_statics m2).
  { eapply BnRepA.crypto_statics_agree; [exact AG2 | | exact CS1]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
  assert (UW2 : uw_chain USTACK_TOP m2 (bv_unsigned sp + -32) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_chain_agree m1 m2 _ _ _ UW1). eapply agree_on_mono; [exact AG2|]. intros x Hx. cbv beta in *. left. clear - Hx. lia. }
  clear BN1.
  apply implA_from_evt.
  do 2 step.

  apply evt_done.
  eapply (BN_free_frame_walkA) with (o := bn_d bNr) (D := D2) (n := 8 * Z.of_nat (bn_dmax bNr)) (a := an + 24) (bs := bs) (lo := lo)
                                   (ras := bv_unsigned ra :: ras) (OW := OW1) (LB := LB); try reflexivity.
  { exact HEAP2. }
  { intros pd E. split; [exact (INS2' pd E) | exact (NBS _ _ _ (INS2 pd E))]. }
  { exact NONE2. }
  { rewrite ESP. exact ST2. }
  { exact CEIL. }
  { rewrite ESP. unfold W_freeA.BN_FREE_STACK, W_freeA.BN_FREE_D0_STACK, CRYPTO_FREE_STACK, RT_STACK. clear - LO'. lia. }
  { rewrite ESP. unfold USTACK_TOP. clear - SPT. lia. }
  { rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia. }
  { exact MI2. }
  { exact CS2. }
  { unfold MallocRep.wz. exact BN2. }
  { exact INSa. }
  { clear - B1. lia. }
  { clear - B2. lia. }
  { clear - AL. Z.div_mod_to_equations. lia. }
  { rewrite ESP. exact UW2. }
  { rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_RECP_CTX_free_2b1948 : uk_call BN_RECP_CTX_FREE 2825008 W_freeA.BN_FREE) CTX). }
  intros Σ2 ms2 PO.
  destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & Fx3 & fc3 & m3 & -> & MI3 & ST3 & AG3 & CR3 & HEAP3).
  fold OW2 in AG3, HEAP3.
  rewrite ?ESP in *. rewrite (ret_pc_even 2825008) by (clear; lia). unfold MallocRep.wz.
  apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply STKC; clear - Hx; lia].
  apply (rw_cells_agree _ _ _ _ _ AG3) in RC; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply (INB' x _ INSb); clear - Hx; lia].
  pose proof (rw_cells_app_r m3 (an + 48) [C4 (wz (st_rbits ls)); C4 (wz (st_rshift ls))] [C4 (wz 0)] RC) as RCF.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in RCF. replace (an + 48 + 8) with (an + 56) in RCF by (clear; lia).
  assert (RCB : rw_cells bgasegs m3 (an + 56) [C1 (Z_to_bv 8 0); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]).
  { apply (rw_cells_recast m3 (an + 56) [C4 (wz 0)] _ RCF); [cbn; tauto | vm_compute; reflexivity | reflexivity]. }
  clear RCF.
  pose proof (AH_acc_in _ _ _ _ bs an 64 HEAP3 INSb B1 B2) as ACC3.
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND1.
  clear MU WM OFF SHB1 SHB2 HEAP HEAP1 HEAP2 ST ST2 MI MI2 BN2 RC.
  pose proof (munch_refl (@nil (Z * Z)) m3) as MU3.
  destruct (AH_shb _ _ _ _ HEAP3) as (SHB1 & SHB2).
  apply implA_from_evt.
  do 3 step. shl_with ACC3 AL. chk0.
  step. rewrite (zxb_small 0) by (clear; lia). step. step. if_false.
  do 4 step. release_frame FR ST3 (bv_unsigned sp). step. step.

  apply evt_done. apply implA_ret.

  assert (AGT : agree_on (aclient_addr (OW2 ++ LB) (bv_unsigned sp)) m m3).
  { eapply agree_on_trans; [eapply agree_on_trans|].
    - eapply agree_client_weaken; [exact AG1 | clear; lia | intros bk Hbk; apply in_app_or in Hbk; apply in_or_app; destruct Hbk as [Hbk|Hbk]; [left; exact (INC1 _ (INC2 _ Hbk)) | right; exact Hbk]].
    - eapply agree_client_weaken; [exact AG2 | clear; lia | intros bk Hbk; apply in_app_or in Hbk; apply in_or_app; destruct Hbk as [Hbk|Hbk]; [left; exact (INC2 _ Hbk) | right; exact Hbk]].
    - eapply agree_client_weaken; [exact AG3 | clear; lia | auto]. }

  set (bs1 := setbn RRecpN (bn_nil 0) ls).
  set (bsN := setbn RRecpNr (bn_nil 0) bs1).
  assert (IDS1 : ids_ok bs1 (pl_place_recp PL0 an) EA) by (apply ids_ok_setbn_none; [exact IDS| exact HVN| reflexivity]).
  assert (LSa : lib_state_h [RRecpNr; RRecpN] bs1 m OW (pl_place_recp PL0 an) EA).
  { eapply (lib_state_h_setbn_hole false [RRecpNr; RRecpN] ls m OW _ EA RRecpN an); [exact LSH2| exact ND| exact HAN| right; left; reflexivity| exact NRON
      | apply bg_ok_nil; left; reflexivity| exact IDS1]. }
  assert (HVNr1 : vref RRecpNr bs1) by (unfold vref, bs1; rewrite length_setbn; exact HVNr).
  assert (IDSN : ids_ok bsN (pl_place_recp PL0 an) EA) by (apply ids_ok_setbn_none; [exact IDS1| exact HVNr1| reflexivity]).
  assert (LSb : lib_state_h [RRecpNr; RRecpN] bsN m OW (pl_place_recp PL0 an) EA).
  { eapply (lib_state_h_setbn_hole false [RRecpNr; RRecpN] bs1 m OW _ EA RRecpNr (an + 24)); [exact LSa| exact ND| exact (recp_at_refNr bs1 OW _ an HRC)| left; reflexivity| exact NRONr
      | apply bg_ok_nil; left; reflexivity| exact IDSN]. }

  assert (FOR1 : forall p1, bn_d bN = Some p1 -> ~ In p1 (all_ids bsN (pl_place_recp PL0 an) EA)).
  { intros p1 E H. apply (all_ids_setbn_nil bs1 _ EA RRecpNr p1 HVNr1) in H. exact (all_ids_without ls _ EA RRecpN p1 IDS HVN E H). }
  assert (FOR2 : forall p2, bn_d bNr = Some p2 -> ~ In p2 (all_ids bsN (pl_place_recp PL0 an) EA)).
  { intros p2 E. apply (all_ids_without bs1 _ EA RRecpNr p2 IDS1 HVNr1). unfold bs1. rewrite getbn_setbn_other by exact NENr. exact E. }
  assert (LSc : lib_state_h [RRecpNr; RRecpN] bsN m OW2 (pl_place_recp PL0 an) EA).
  { eapply lib_state_h_ow; [exact LSb|]. intros q A n Hq Hin. unfold OW2, OW1. apply lb_remove_opt_In. split.
    - apply lb_remove_opt_In. split; [exact Hin|]. intros p1 E. cbn [blk_id fst]. intros ->. exact (FOR1 p1 E Hq).
    - intros p2 E. cbn [blk_id fst]. intros ->. exact (FOR2 p2 E Hq). }
  assert (LSd : lib_state_h [RRecpNr; RRecpN] bsN m3 OW2 (pl_place_recp PL0 an) EA).
  { eapply lib_state_h_heap_pres with (m := m) (LB := LB) (L := OW2 ++ LB) (SP := bv_unsigned sp) (SPX := bv_unsigned sp) (BX := USTACK_TOP);
      [exact LSc| exact FROK| clear; lia| clear; lia | exact AGT| intros b Hb; apply in_or_app; left; exact Hb | intros b Hb; apply in_or_app; right; exact Hb]. }
  assert (GN : getbn RRecpN bsN = bn_nil 0).
  { unfold bsN. rewrite getbn_setbn_other by (intros E; exact (NENr (eq_sym E))). unfold bs1. apply getbn_setbn_same. exact HVN. }
  assert (GNr : getbn RRecpNr bsN = bn_nil 0) by (unfold bsN; apply getbn_setbn_same; exact HVNr1).
  assert (LSF : lib_state bsF m3 OW2 PL0 EA).
  { unfold lib_state, bsF. fold bs1. fold bsN.
    eapply (lib_state_unplace_recp false [RRecpNr; RRecpN] [] bsN m3 OW2 PL0 EA an 0 0); [exact LSd| exact PWF0| exact E1| exact E2| exact E3| exact GN| exact GNr|].
    intros r [<-|[<-|[]]]; [right; left; reflexivity| left; reflexivity]. }
  unfold bn_postA. do 17 eexists. exists m3, OW2, PL0. split; [reflexivity|]. cbn [fst snd].
  split; [exact HEAP3|]. split; [exact LSF|]. split; [exact ST3|]. split; [exact MI3|].
  split. { eapply agree_on_mono; [exact AGT|]. intros x [_ [Hx|[Hx|(bk & Hbk & Hr)]]];
             [left; exact Hx | right; left; exact Hx | right; right; exists bk; split; [apply in_or_app; right; exact Hbk | exact Hr]]. }
  split; [rewrite CR3, CR2; clear; lia|].
  split.
  { unfold cnt_eq. change (cnt_bal bsF OW2) with (cnt_bal bsN OW2). unfold bsN.
    rewrite (cnt_bal_setbn RRecpNr (bn_nil 0) bs1 OW1 OW2 HVNr1). unfold bs1 at 1 2.
    rewrite (cnt_bal_setbn RRecpN (bn_nil 0) ls OW OW1 HVN).
    rewrite getbn_setbn_other by exact NENr. fold bN bNr.
    pose proof (lb_remove_opt_length (bn_d bN) OW ND ltac:(intros p E; exact (in_map blk_id _ _ (INS1 p E)))) as L1. fold OW1 in L1.
    pose proof (lb_remove_opt_length (bn_d bNr) OW1 ND1 ltac:(intros p E; exact (in_map blk_id _ _ (INS2' p E)))) as L2. fold OW2 in L2.
    unfold bn_blocks. cbn [bn_d bn_nil length]. clear - L1 L2. destruct (bn_d bN), (bn_d bNr); cbn [length] in *; lia. }
  split.
  { apply refs_stable_ow; [reflexivity|]. intros q H Hq HinH. unfold OW2, OW1. apply lb_remove_opt_In. split.
    + apply lb_remove_opt_In. split; [exact HinH|]. intros p1 E. cbn [blk_id fst]. intros ->.
      exact (ids_bn_item_neq RRecpN ls p1 p1 (ids_m_nodup _ _ _ IDS) HVN E Hq eq_refl).
    + intros p2 E. cbn [blk_id fst]. intros ->.
      exact (ids_bn_item_neq RRecpNr ls p2 p2 (ids_m_nodup _ _ _ IDS) HVNr E Hq eq_refl). }
  reflexivity.
Qed.

End WithRT2.

Lemma pl_frames_place_recp_old : forall PL an iv, pl_bn PL RRecpN = None -> pl_bn PL RRecpNr = None -> pl_recp PL = None ->
  In iv (pl_frames PL) -> In iv (pl_frames (pl_place_recp PL an)).
Proof.
  intros PL an iv E1 E2 E3 H. unfold pl_place_recp.
  assert (H2 : In iv (pl_frames (pl_set (pl_set PL RRecpN (Some (PFrame an))) RRecpNr (Some (PFrame (an + 24)))))).
  { apply pl_frames_set_In_old; [apply pl_frames_set_In_old; [exact H | left; exact E1] | left; rewrite pl_set_other by (unfold RRecpN, RRecpNr; lia); exact E2]. }
  apply pl_frames_In. apply pl_frames_In in H2. destruct H2 as [(k & Hk & H2)|H2].
  - left. exists k. split; [exact Hk | exact H2].
  - exfalso. cbn [pl_recp pl_set] in H2. rewrite E3 in H2. exact H2.
Qed.

Section Env.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma cenv_unplace_recpA : forall (objs LBo : list block) PL0 EA lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre used Σ (ls : bstate bptr) m OW an (q : bptr)
    Σ' (ls' : bstate bptr) m' OW',
  cenvA (objs ++ LBo) (pl_place_recp PL0 an) lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
  lib_state ls m OW (pl_place_recp PL0 an) EA ->
  In (q, an, 64) objs -> pl_bn PL0 RRecpN = None -> pl_bn PL0 RRecpNr = None -> pl_recp PL0 = None ->
  AHEAP Σ' OW' (objs ++ LBo) m' -> stk bgasegs m' lo FB -> mem_inv bgasegs m' ->
  ax_pres (objs ++ LBo) FB (XW (pl_place_recp PL0 an)) m m' ->
  rt_credit RT Σ <= rt_credit RT Σ' -> cnt_eq ls OW ls' OW' -> refs_stable ls OW ls' OW' ->
  cenvA (objs ++ LBo) PL0 lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m' pre used Σ' ls' m' OW'
  /\ ax_pres LBo SPv (XW PL0) m0 m'.
Proof.
  intros objs LBo PL0 EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW an q Σ' ls' m' OW'
         (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FRC & FSZ & UW) LS Hb E1 E2 E3 HEAP' ST' MI' AXP' CR' CNT' RS'.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
  assert (OLD : forall iv, In iv (pl_frames PL0) -> In iv (pl_frames (pl_place_recp PL0 an))) by (intros iv; apply pl_frames_place_recp_old; assumption).
  assert (HbL : In (q, an, 64) (objs ++ LBo)) by (apply in_or_app; left; exact Hb).
  pose proof (AH_range_gen _ _ _ _ _ HEAP ltac:(apply in_or_app; right; exact HbL)) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  assert (AG : agree_on (fun a => FB <= a < USTACK_TOP) m m').
  { eapply agree_on_mono; [exact AXP'|]. intros a Ha. cbv beta in Ha. split; [|left; lia].
    apply (xw_stack_out Σ OW (objs ++ LBo) m (pl_place_recp PL0 an) SPv USTACK_TOP a HEAP FROK). clear - Ha CEIL LOFB. lia. }
  split.
  - unfold cenvA, cenv_ok.
    split. { split; [exact CEIL|]. split; [exact LOFB|]. split; [exact FBSP|]. split; [exact SPT|]. split; [exact SP16|]. split; [exact FB16|]. split; [exact CNT0|]. split; [exact CRED0|].
             split; [split; [exact (pl_frames_lb_in _ _ _ OLD (proj1 FROK)) | exact (proj2 FROK)]|].
             split; [intros iv Hiv; exact (FAL iv (OLD iv Hiv))|].
             split; [exact (pl_frames_lb_in _ _ _ OLD (proj1 NOFR)) | intros iv Hiv; exact (proj2 NOFR iv (OLD iv Hiv))]. }
    split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|]. split; [apply ax_pres_refl|].
    split; [clear - CR CR'; lia|].
    split; [eapply cnt_eq_trans; eauto|].
    split; [eapply refs_stable_trans; eauto|].
    split. { eapply rw_cells_agree; [exact AG | exact FRC |]. intros a Ha. rewrite cells_size_app in Ha. cbn [cells_size csize Nat.add] in Ha.
             unfold USTACK_TOP in *. clear - Ha FSZ FBSP SPT. lia. }
    split; [exact FSZ|].
    unfold uw_opt in *. destruct rasO as [ras|]; [|exact I].
    apply (uw_chain_agree m m' ras SPv (bv_unsigned s0w) UW). eapply agree_on_mono; [exact AG|]. intros a Ha. cbv beta in *. clear - Ha FBSP. lia.
  - assert (AXT : ax_pres LBo SPv (XW (pl_place_recp PL0 an)) m0 m').
    { apply (ax_pres_outer objs LBo). eapply ax_pres_trans; [exact AXP|]. eapply ax_pres_weaken; [exact AXP'| clear - FBSP; lia]. }
    eapply agree_on_mono; [exact AXT|]. intros x [NX Hc]. split; [| exact Hc].
    intros HX. apply xw_place_recp in HX. destruct HX as [HX|HX]; [exact (NX HX)|].
    destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]].
    + unfold BnHeapA.ACEIL in *. clear - Hc HX BC CEIL LOFB FBSP. lia.
    + destruct Hc as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
      destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr HX BI; lia.
    + assert (NE : blk_id (q, an, 64) <> blk_id b').
      { intros E. pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite !map_app in ND. apply NoDup_app_remove_l in ND.
        eapply (nodup_app_disj _ _ (blk_id (q, an, 64)) ND); [apply in_map; exact Hb | rewrite E; apply in_map; exact Hb']. }
      pose proof (AH_disjoint_gen _ _ _ _ (q, an, 64) b' HEAP ltac:(apply in_or_app; right; exact HbL) ltac:(apply in_or_app; right; apply in_or_app; right; exact Hb') NE) as DJ.
      cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr HX. lia.
Qed.

End Env.

Section Calls.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation ops := (tree_ops bptr).

Lemma recp_free_lastA : forall (Q : unit * bstate bptr -> rts RT -> machine_state -> Prop)
    (objs LBo : list block) (PL0 : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (ras : list Z) (TOTAL : Z)
    (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem) (pre : list cell) (used : Z) (Σ : rts RT) (ls : bstate bptr) (m : mem) (OW : list block)
    (q : bptr) (an : Z)
    (rax gp tp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  cenvA (objs ++ LBo) (pl_place_recp PL0 an) lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
  lib_state ls m OW (pl_place_recp PL0 an) EA ->
  In (q, an, 64) objs -> an mod 8 = 0 ->
  pl_wf PL0 -> pl_bn PL0 RRecpN = None -> pl_bn PL0 RRecpNr = None -> pl_recp PL0 = None ->
  bv_unsigned x8 = SPv -> lo <= FB - RECP_FREE_STACK -> used <= TOTAL -> tp = wz TP_A ->
  uk_ctx BN_RECP_CTX_FREE (bv_unsigned rax :: bv_unsigned raw :: ras) ->
  (forall Σ' ls' m' OW' (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) F' fc',
      cenvA (objs ++ LBo) PL0 lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m' pre used Σ' ls' m' OW' ->
      lib_state ls' m' OW' PL0 EA ->
      ax_pres LBo SPv (XW PL0) m0 m' ->
      implA (TRet (tt, ls')) Σ' Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
            F' (ret_pc rax) fc' None m' (seg_rom bgasegs))) ->
  implA (BN_RECP_CTX_free ops ls) Σ Q
    (MS (mkR rax (Z_to_bv 64 FB) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 an) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (wz BN_RECP_CTX_FREE) fc None m (seg_rom bgasegs)).
Proof.
  intros until fc. intros ENV LS Hb A8 PWF0 E1 E2 E3 E8 HK HU -> CTX K.
  pose proof ENV as (OK & HEAP & _).
  assert (EF : bv_unsigned (Z_to_bv 64 FB) = FB) by (eapply ESPvA; [exact OK | exact HEAP]).
  assert (HbL : In (q, an, 64) (objs ++ LBo)) by (apply in_or_app; left; exact Hb).
  eapply implA_post.
  { eapply (BN_RECP_CTX_free_walkA) with (PL0 := PL0) (an := an) (bs := (q, an, 64)) (lo := lo) (ras := bv_unsigned raw :: ras) (LB := objs ++ LBo);
      [ eapply cenv_preA; [exact ENV | exact LS | exact HK | clear - HU; lia]
      | rewrite E8, EF; eapply cenv_uwA; [reflexivity | exact ENV]
      | exact CTX | reflexivity | exact PWF0 | exact E1 | exact E2 | exact E3 | exact HbL
      | cbn [blk_addr blk_size fst snd]; clear; lia | cbn [blk_addr blk_size fst snd]; clear; lia | exact A8 | reflexivity ]. }
  cbv beta. intros [v ls'] Σ' ms' PO. unfold bn_postA in PO. rewrite EF in PO. cbn [fst snd] in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m' & OW' & PL' & -> & HEAP' & LS' & ST' & MI' & AXP' & CR' & CNT' & RS' & ->).
  destruct v.
  destruct (cenv_unplace_recpA objs LBo PL0 EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW an q Σ' ls' m' OW'
              ENV LS Hb E1 E2 E3 HEAP' ST' MI' AXP' ltac:(clear - CR'; lia) CNT' RS') as (ENV' & AXO).
  eapply K; [exact ENV' | exact LS' | exact AXO].
Qed.

End Calls.
