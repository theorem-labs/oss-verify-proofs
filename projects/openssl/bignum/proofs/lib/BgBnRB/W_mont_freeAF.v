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
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA W_expandA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnAKitAF BnCallAF AFrameComp PlaceMont PlaceKitA W_recp_freeAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require W_freeA W_ctx_freeA W_mont_ctxAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation BN_MONT_CTX_FREE := W_mont_ctxAF.BN_MONT_CTX_FREE.
Notation BN_CLEAR_FREE := W_ctx_freeA.BN_CLEAR_FREE.
Notation BN_CLEAR_FREE_STACK := W_ctx_freeA.BN_CLEAR_FREE_STACK.
Definition BN_MONT_CTX_FREE_STACK : Z := 32 + BN_CLEAR_FREE_STACK.

Lemma mont_free_treeA : forall (bs : bstate bptr) (qm : bptr),
  bn_flags (getbn RMontRR bs) = 0 -> bn_flags (getbn RMontN bs) = 0 -> bn_flags (getbn RMontNi bs) = 0 ->
  BN_MONT_CTX_free (tree_ops bptr) qm bs =
  tfree_opt (bn_d (getbn RMontRR bs)) (tfree_opt (bn_d (getbn RMontN bs)) (tfree_opt (bn_d (getbn RMontNi bs))
    (TFree qm (TRet (tt, set_mont 0 0 (setbn RMontNi (bn_nil 0) (setbn RMontN (bn_nil 0) (setbn RMontRR (bn_nil 0) bs)))))))).
Proof.
  intros bs qm F1 F2 F3.
  assert (H1 : forall f, has_flag (getbn RMontRR bs) f = false) by (intros f; unfold has_flag; rewrite F1; reflexivity).
  assert (H2 : forall f, has_flag (getbn RMontN bs) f = false) by (intros f; unfold has_flag; rewrite F2; reflexivity).
  assert (H3 : forall f, has_flag (getbn RMontNi bs) f = false) by (intros f; unfold has_flag; rewrite F3; reflexivity).
  assert (G2 : forall b, getbn RMontN (setbn RMontRR b bs) = getbn RMontN bs)
    by (intros b; apply getbn_setbn_other; unfold RMontRR, RMontN; lia).
  assert (G3 : forall b b', getbn RMontNi (setbn RMontN b' (setbn RMontRR b bs)) = getbn RMontNi bs)
    by (intros b b'; rewrite !getbn_setbn_other by (unfold RMontRR, RMontN, RMontNi; lia); reflexivity).
  unfold BN_MONT_CTX_free, BN_clear_free, bbind, bget, bset, bret, bunr, bsetmont. cbn [bind ret unreachable tree_ops tbind fst snd].
  rewrite !H1, !H2, !H3. cbn [orb]. cbv beta. rewrite !H1.
  destruct (bn_d (getbn RMontRR bs)) as [q1|];
    cbn [bfree_opt bfree bret bind ret lib_free tree_ops tbind fst snd tfree_opt];
    rewrite !G2, !H2; cbv beta;
    (destruct (bn_d (getbn RMontN bs)) as [q2|];
     cbn [bfree_opt bfree bret bind ret lib_free tree_ops tbind fst snd tfree_opt];
     rewrite !G3, !H3; cbv beta;
     (destruct (bn_d (getbn RMontNi bs)) as [q3|];
      cbn [bfree_opt bfree bret bind ret lib_free tree_ops tbind fst snd tfree_opt]; reflexivity)).
Qed.

Lemma ref_at_mRR : forall (st : bstate bptr) OW PL am qm, pl_mont PL = Some (am, qm) -> ref_at st OW PL RMontRR am.
Proof. intros st OW PL am qm E. apply ref_at_fixed; [unfold RMontRR, NFIX; lia|]. exists (PHeap am qm 0). unfold pl_of. rewrite E. cbn. split; reflexivity. Qed.
Lemma ref_at_mN : forall (st : bstate bptr) OW PL am qm, pl_mont PL = Some (am, qm) -> ref_at st OW PL RMontN (am + 24).
Proof. intros st OW PL am qm E. apply ref_at_fixed; [unfold RMontN, NFIX; lia|]. exists (PHeap (am + 24) qm 24). unfold pl_of. rewrite E. cbn. split; reflexivity. Qed.
Lemma ref_at_mNi : forall (st : bstate bptr) OW PL am qm, pl_mont PL = Some (am, qm) -> ref_at st OW PL RMontNi (am + 48).
Proof. intros st OW PL am qm E. apply ref_at_fixed; [unfold RMontNi, NFIX; lia|]. exists (PHeap (am + 48) qm 48). unfold pl_of. rewrite E. cbn. split; reflexivity. Qed.

Lemma all_ids_unset_mont : forall (s : bstate bptr) PL EA am qm x y q, pl_mont PL = Some (am, qm) ->
  In q (all_ids (set_mont x y s) (pl_set_mont PL None) EA) -> In q (all_ids s PL EA).
Proof.
  intros s PL EA am qm x y q E H. unfold all_ids in *. change (blocks_of (set_mont x y s)) with (blocks_of s) in H.
  rewrite in_app_iff in *. destruct H as [H|H]; [left| right; exact H].
  eapply Permutation_in; [apply Permutation_sym; exact (pl_ids_unset_mont PL am qm E)|]. right. exact H.
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma BN_clear_free_optA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (o : option bptr) (D a lo : Z) (b : bignum bptr) (bs : block) (ras : list Z)
    (k : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  (forall p, o = Some p -> In (p, D, 8 * Z.of_nat (bn_dmax b)) OW /\ blk_id bs <> p) -> (o = None -> D = 0) ->
  stk bgbsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BN_CLEAR_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bgbsegs m -> tp = wz TP_A -> BnRepDefs.crypto_statics m ->
  rw_cells bgbsegs m a (BnRepDefs.bn_cells D b) -> bn_flags b = 0 -> Z.of_nat (bn_dmax b) <= 512 ->
  In bs (OW ++ LB) -> blk_addr bs <= a -> a + 24 <= blk_addr bs + blk_size bs -> a mod 8 = 0 ->
  a0 = wz a ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_CLEAR_FREE (bv_unsigned ra :: ras) ->
  (forall Σ' ms', bnfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB o lo m Σ' ms' -> implA k Σ' Q ms') ->
  implA (tfree_opt o k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_CLEAR_FREE) fc None m (seg_rom bgbsegs)).
Proof.
  intros until Q. intros HEAP HO HN ST CEIL LO SPT SP16 MI -> CS BN FL0 DM INS RS1 RS2 AL -> UW CTX K.
  destruct o as [pd|]; cbn [tfree_opt].
  -
    destruct (HO pd eq_refl) as (HinD & NEQ).
    pose proof (AH_nodup _ _ _ _ HEAP) as NDL.
    assert (NLB : ~ In pd (map blk_id LB)).
    { intros H. rewrite map_app in NDL. eapply (nodup_app_disj _ _ pd NDL); [apply (in_map blk_id) in HinD; exact HinD| exact H]. }
    eapply (W_ctx_freeA.BN_clear_free_poolA) with (p := pd) (D := D) (a := a) (b := b) (bs := bs) (lo := lo) (ras := ras) (OW := OW) (LB := LB);
      [exact HEAP | exact HinD | exact ST | exact CEIL | exact LO | exact SPT | exact SP16 | exact MI | reflexivity | exact CS | exact BN | exact FL0 | exact DM
      | exact INS | exact RS1 | exact RS2 | exact AL | exact NEQ | reflexivity | exact UW | exact CTX |].
    intros Σ1 ms1 PO. apply (K Σ1).
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & E & MI2 & ST2 & AG2 & CR2 & HEAP2).
    unfold bnfree_postA. do 17 eexists. exists m2. split; [exact E|]. split; [exact MI2|]. split; [exact ST2|].
    split; [| split; [exact CR2 | exact HEAP2]].
    cbn [W_freeA.lb_remove_opt]. rewrite lb_remove_app, (lb_remove_notin pd LB NLB) in AG2. exact AG2.
  -
    pose proof (HN eq_refl) as ->.
    pose proof LO as LO'. unfold W_ctx_freeA.BN_CLEAR_FREE_STACK, W_expandA.BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK in LO'.
    unfold W_ctx_freeA.BN_CLEAR_FREE, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (AH_range_gen _ _ _ _ bs HEAP INS) as (S0 & _ & _ & SC & SI).
    pose proof (AH_acc_in _ _ _ _ bs a 24 HEAP INS RS1 RS2) as ACC.
    pose proof (AH_offsh _ _ _ _ bs HEAP INS) as OFS. unfold SHLO, SHHI in OFS.
    destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
    unfold BnRepDefs.bn_cells, MallocRep.wz in BN. rewrite FL0 in BN.
    apply (flag_cell_split bgbsegs m a _ _ _ _ 0 ltac:(clear; lia)) in BN.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
    assert (OFF : offshW [(bv_unsigned sp - 48, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
    assert (EA0 : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - S0 SC RS1 RS2 CE1 CE2 CE3; lia).
    apply implA_from_evt.
    carve_frame 48%nat ST.
    do 7 step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EA0 in KA; clear - KA S0 RS1; lia|]. clear KA.
    step. step. step. if_cases KU; zify_cond KU; [exfalso; apply KU; rewrite ?EA0; change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; lia); change (2 ^ 3) with 8; exact AL|]. clear KU. do 3 step. do 2 step. shl_with ACC AL. chk0.
    step. step.
    step. if_true.

    do 2 step. shl_with ACC AL. chk0.
    step. rewrite (zxb_small 0) by (clear; lia). step. step. if_false.
    do 5 step. release_frame FR ST (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    apply evt_done. apply (K Σ). unfold bnfree_postA. do 17 eexists. exists m1.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. cbn [W_freeA.lb_remove_opt].
    split; [| split; [reflexivity|]].
    + eapply (stack_munch_agree Σ OW LB m m1 _ (bv_unsigned sp) HEAP MU). constructor; [cbn [fst snd]; unfold BnHeapA.ACEIL in *; clear - CEIL LO'; lia | constructor].
    + eapply (AH_frame Σ OW LB m m1 _ HEAP MU WM). constructor; [left; cbn [fst snd]; unfold BnHeapA.ACEIL, USTACK_TOP in *; clear - CEIL LO' SPT; lia | constructor].
Qed.

Lemma BN_MONT_CTX_free_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (am : Z) (qm : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo BN_MONT_CTX_FREE_STACK 0 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MONT_CTX_FREE (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> pl_mont PL = Some (am, qm) -> a0 = wz am ->
  implA (BN_MONT_CTX_free (tree_ops bptr) qm ls) Σ
    (bn_postA_p ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA 0
                (fun _ ls' OW' PL' _ => PL' = pl_set_mont PL None /\ cnt_bal ls' OW' = cnt_bal ls OW - 1 /\ refs_stable ls OW ls' OW'))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_MONT_CTX_FREE) fc None m (seg_rom bgbsegs)).
Proof.
  intros until qm. intros PRE UW CTX -> E ->.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND. pose proof (AH_nodup _ _ _ _ HEAP) as NDL.
  pose proof LO as LO'. unfold BN_MONT_CTX_FREE_STACK, W_ctx_freeA.BN_CLEAR_FREE_STACK, W_expandA.BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK in LO'.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof (ref_at_mRR ls OW PL am qm E) as HA1. pose proof (ref_at_mN ls OW PL am qm E) as HA2. pose proof (ref_at_mNi ls OW PL am qm E) as HA3.
  assert (NRO1 : RMontRR <> ROne) by (unfold RMontRR, ROne; lia).
  assert (NRO2 : RMontN <> ROne) by (unfold RMontN, ROne; lia).
  assert (NRO3 : RMontNi <> ROne) by (unfold RMontNi, ROne; lia).
  assert (NE12 : RMontRR <> RMontN) by (unfold RMontRR, RMontN; lia).
  assert (NE13 : RMontRR <> RMontNi) by (unfold RMontRR, RMontNi; lia).
  assert (NE23 : RMontN <> RMontNi) by (unfold RMontN, RMontNi; lia).
  assert (HV1 : vref RMontRR ls) by (eapply ref_at_valid; [exact LS | exact HA1]).
  assert (HV2 : vref RMontN ls) by (eapply ref_at_valid; [exact LS | exact HA2]).
  assert (HV3 : vref RMontNi ls) by (eapply ref_at_valid; [exact LS | exact HA3]).
  destruct (lib_state_open [] ls m OW _ EA RMontRR am LS ND HA1 ltac:(intros []) NRO1) as ((D1 & BN1 & ARR1) & (OK1a & OK1b & OK1c & OK1d) & LSH1).
  destruct (lib_state_open [RMontRR] ls m OW _ EA RMontN (am + 24) LSH1 ND HA2 ltac:(intros [X|[]]; exact (NE12 X)) NRO2)
    as ((D2 & BN2 & ARR2) & (OK2a & OK2b & OK2c & OK2d) & LSH2).
  destruct (lib_state_open [RMontN; RMontRR] ls m OW _ EA RMontNi (am + 48) LSH2 ND HA3 ltac:(intros [X|[X|[]]]; [exact (NE23 X)| exact (NE13 X)]) NRO3)
    as ((D3 & BN3 & ARR3) & (OK3a & OK3b & OK3c & OK3d) & LSH3).
  pose proof (lib_state_mont_cells _ _ _ _ _ _ _ _ _ LS E) as MCc. unfold mont_cells in MCc.
  assert (INQ : In (qm, am, 96) OW).
  { destruct LS as (_ & _ & _ & (_ & _ & _ & (_ & _ & _ & (M4 & _)))). rewrite E in M4. exact (proj1 M4). }

  destruct OK1d as [F1|F1].
  2: { unfold BN_MONT_CTX_free, bbind, bget, bunr, has_flag. cbn [bind ret unreachable tree_ops tbind fst snd]. rewrite F1. apply implA_unr. }
  destruct OK2d as [F2|F2].
  2: { unfold BN_MONT_CTX_free, bbind, bget, bunr, has_flag. cbn [bind ret unreachable tree_ops tbind fst snd]. rewrite F1, F2. apply implA_unr. }
  destruct OK3d as [F3|F3].
  2: { unfold BN_MONT_CTX_free, bbind, bget, bunr, has_flag. cbn [bind ret unreachable tree_ops tbind fst snd]. rewrite F1, F2, F3. apply implA_unr. }
  rewrite (mont_free_treeA ls qm F1 F2 F3).
  set (bsF := set_mont 0 0 (setbn RMontNi (bn_nil 0) (setbn RMontN (bn_nil 0) (setbn RMontRR (bn_nil 0) ls)))).
  unfold bn_arr in ARR1, ARR2, ARR3.
  replace (pl_of PL RMontRR) with (Some (PHeap am qm 0)) in ARR1 by (unfold pl_of; rewrite E; reflexivity).
  replace (pl_of PL RMontN) with (Some (PHeap (am + 24) qm 24)) in ARR2 by (unfold pl_of; rewrite E; reflexivity).
  replace (pl_of PL RMontNi) with (Some (PHeap (am + 48) qm 48)) in ARR3 by (unfold pl_of; rewrite E; reflexivity).
  pose proof (proj1 (proj2 (proj2 PARTS))) as IDS. pose proof (ids_m_nodup _ _ _ IDS) as NDM.
  set (b1 := getbn RMontRR ls) in *. set (b2 := getbn RMontN ls) in *. set (b3 := getbn RMontNi ls) in *.
  assert (INS1 : forall pd, bn_d b1 = Some pd -> In (pd, D1, 8 * Z.of_nat (bn_dmax b1)) OW) by (intros pd X; rewrite X in ARR1; exact (proj1 ARR1)).
  assert (NONE1 : bn_d b1 = None -> D1 = 0) by (intros X; rewrite X in ARR1; exact (proj1 ARR1)).
  assert (INS2 : forall pd, bn_d b2 = Some pd -> In (pd, D2, 8 * Z.of_nat (bn_dmax b2)) OW) by (intros pd X; rewrite X in ARR2; exact (proj1 ARR2)).
  assert (NONE2 : bn_d b2 = None -> D2 = 0) by (intros X; rewrite X in ARR2; exact (proj1 ARR2)).
  assert (INS3 : forall pd, bn_d b3 = Some pd -> In (pd, D3, 8 * Z.of_nat (bn_dmax b3)) OW) by (intros pd X; rewrite X in ARR3; exact (proj1 ARR3)).
  assert (NONE3 : bn_d b3 = None -> D3 = 0) by (intros X; rewrite X in ARR3; exact (proj1 ARR3)).
  assert (N12 : forall p q, bn_d b1 = Some p -> bn_d b2 = Some q -> p <> q) by (intros p q X Y; exact (ids_bn_neq RMontRR RMontN ls p q NDM HV1 HV2 NE12 X Y)).
  assert (N13 : forall p q, bn_d b1 = Some p -> bn_d b3 = Some q -> p <> q) by (intros p q X Y; exact (ids_bn_neq RMontRR RMontNi ls p q NDM HV1 HV3 NE13 X Y)).
  assert (N23 : forall p q, bn_d b2 = Some p -> bn_d b3 = Some q -> p <> q) by (intros p q X Y; exact (ids_bn_neq RMontN RMontNi ls p q NDM HV2 HV3 NE23 X Y)).
  assert (NQ : forall r p, vref r ls -> bn_d (getbn r ls) = Some p -> qm <> p).
  { intros r p HV X. apply (ids_pl_m ls PL EA qm p IDS); [|exact (bn_in_m r ls p HV X)].
    unfold pl_ids. rewrite E. cbn [opt_ids]. apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
  clear ARR1 ARR2 ARR3.
  unfold BG_DMAX in OK1c, OK2c, OK3c.
  set (OW1 := lb_remove_opt (bn_d b1) OW).
  set (OW2 := lb_remove_opt (bn_d b2) OW1).
  set (OW3 := lb_remove_opt (bn_d b3) OW2).
  set (OW4 := lb_remove qm OW3).
  assert (INC1 : forall b, In b OW1 -> In b OW) by (intros b Hb; unfold OW1 in Hb; apply lb_remove_opt_In in Hb; exact (proj1 Hb)).
  assert (INC2 : forall b, In b OW2 -> In b OW1) by (intros b Hb; unfold OW2 in Hb; apply lb_remove_opt_In in Hb; exact (proj1 Hb)).
  assert (INC3 : forall b, In b OW3 -> In b OW2) by (intros b Hb; unfold OW3 in Hb; apply lb_remove_opt_In in Hb; exact (proj1 Hb)).
  assert (INC4 : forall b, In b OW4 -> In b OW3) by (intros b Hb; unfold OW4 in Hb; eapply lb_remove_incl; exact Hb).
  assert (INS2' : forall pd, bn_d b2 = Some pd -> In (pd, D2, 8 * Z.of_nat (bn_dmax b2)) OW1).
  { intros pd X. unfold OW1. apply lb_remove_opt_In. split; [exact (INS2 pd X)|]. intros p1 X1. cbn [blk_id fst]. intros Y. exact (N12 p1 pd X1 X (eq_sym Y)). }
  assert (INS3' : forall pd, bn_d b3 = Some pd -> In (pd, D3, 8 * Z.of_nat (bn_dmax b3)) OW2).
  { intros pd X. unfold OW2, OW1. apply lb_remove_opt_In. split; [apply lb_remove_opt_In; split; [exact (INS3 pd X)|]|].
    - intros p1 X1. cbn [blk_id fst]. intros Y. exact (N13 p1 pd X1 X (eq_sym Y)).
    - intros p2 X2. cbn [blk_id fst]. intros Y. exact (N23 p2 pd X2 X (eq_sym Y)). }
  assert (INQ1 : In (qm, am, 96) OW1) by (unfold OW1; apply lb_remove_opt_In; split; [exact INQ | intros p1 X1; cbn [blk_id fst]; exact (NQ RMontRR p1 HV1 X1)]).
  assert (INQ2 : In (qm, am, 96) OW2) by (unfold OW2; apply lb_remove_opt_In; split; [exact INQ1 | intros p2 X2; cbn [blk_id fst]; exact (NQ RMontN p2 HV2 X2)]).
  assert (INQ3 : In (qm, am, 96) OW3) by (unfold OW3; apply lb_remove_opt_In; split; [exact INQ2 | intros p3 X3; cbn [blk_id fst]; exact (NQ RMontNi p3 HV3 X3)]).
  assert (QNLB : ~ In qm (map blk_id LB)).
  { intros H. rewrite map_app in NDL. eapply (nodup_app_disj _ _ qm NDL); [apply (in_map blk_id) in INQ; exact INQ| exact H]. }

  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range _ _ _ _ _ _ _ HEAP INQ) as (SA0 & SA16 & _ & SAC & SAI).
  assert (AL : am mod 8 = 0) by (clear - SA16; Z.div_mod_to_equations; lia).
  assert (INS : In (qm, am, 96) (OW ++ LB)) by (apply in_or_app; left; exact INQ).
  pose proof (AH_offsh _ _ _ _ (qm, am, 96) HEAP INS) as OFA. cbn [blk_addr blk_size fst snd] in OFA. unfold SHLO, SHHI in OFA.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 32, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  assert (EA0 : bv_unsigned (Z_to_bv 64 am) = am) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - SA0 SAC CE1 CE2 CE3; lia).
  unfold bn_cells in BN1, BN2, BN3.
  unfold W_mont_ctxAF.BN_MONT_CTX_FREE, MallocRep.wz.
  apply implA_from_evt.
  carve_frame 32%nat ST.
  do 6 step.
  step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EA0 in KA; clear - KA SA0; lia|]. clear KA.
  step. step. step. if_cases KU; zify_cond KU; [exfalso; apply KU; rewrite ?EA0; change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; lia); change (2 ^ 3) with 8; exact AL|]. clear KU. do 3 step. do 2 step.

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
  assert (UWm1 : uw_chain USTACK_TOP m1 (bv_unsigned sp) (bv_unsigned s0) ras).
  { eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  assert (STKC : forall x L, bv_unsigned sp + -32 <= x < bv_unsigned sp -> aclient_addr L (bv_unsigned sp + -32) x).
  { intros x L Hx. left. unfold USTACK_TOP. clear - Hx SPT. lia. }
  assert (INB' : forall x L, In (qm, am, 96) L -> am <= x < am + 96 -> aclient_addr L (bv_unsigned sp + -32) x).
  { intros x L HL Hx. right; right. exists (qm, am, 96). split; [exact HL | cbn [blk_addr blk_size fst snd]; clear - Hx; lia]. }

  apply evt_done.
  eapply (BN_clear_free_optA) with (o := bn_d b1) (D := D1) (a := am) (b := b1) (bs := (qm, am, 96)) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB);
    [ exact HEAP1 | intros pd X; split; [exact (INS1 pd X) | cbn [blk_id fst]; exact (NQ RMontRR pd HV1 X)] | exact NONE1
    | rewrite ESP; exact ST | exact CEIL | rewrite ESP; clear - LO'; unfold W_ctx_freeA.BN_CLEAR_FREE_STACK, W_expandA.BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK; lia
    | rewrite ESP; unfold USTACK_TOP; clear - SPT; lia | rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia | exact MI | reflexivity | exact CS1
    | exact BN1 | exact F1 | exact OK1c | exact INS | cbn [blk_addr fst snd]; clear; lia | cbn [blk_addr blk_size fst snd]; clear; lia | exact AL | reflexivity
    | rewrite ESP; exact UW1
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ (E_BN_MONT_CTX_free_22657c : uk_call W_mont_ctxAF.BN_MONT_CTX_FREE 2254692 W_ctx_freeA.BN_CLEAR_FREE) CTX) |].
  intros Σ1 ms1 PO.
  destruct PO as (u0 & u1 & u2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & Fx2 & fc2 & m2 & -> & MI2 & ST2 & AG2 & CR2 & HEAP2).
  fold OW1 in AG2, HEAP2.
  rewrite ?ESP in *. rewrite (ret_pc_even 2254692) by (clear; lia). unfold MallocRep.wz.
  assert (INSa : In (qm, am, 96) (OW1 ++ LB)) by (apply in_or_app; left; exact INQ1).
  apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply STKC; clear - Hx; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in BN2; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply (INB' x _ INSa); clear - Hx; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in BN3; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply (INB' x _ INSa); clear - Hx; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in MCc; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply (INB' x _ INSa); clear - Hx; lia].
  assert (CS2 : BnRepDefs.crypto_statics m2).
  { eapply BnRepA.crypto_statics_agree; [exact AG2 | | exact CS1]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
  assert (UW2 : uw_chain USTACK_TOP m2 (bv_unsigned sp + -32) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_chain_agree m1 m2 _ _ _ UW1). eapply agree_on_mono; [exact AG2|]. intros x Hx. cbv beta in *. left. clear - Hx. lia. }
  assert (UWm2 : uw_chain USTACK_TOP m2 (bv_unsigned sp) (bv_unsigned s0) ras).
  { apply (uw_chain_agree m1 m2 _ _ _ UWm1). eapply agree_on_mono; [exact AG2|]. intros x Hx. cbv beta in *. left. clear - Hx. lia. }
  clear BN1.
  apply implA_from_evt.
  do 2 step.

  apply evt_done.
  eapply (BN_clear_free_optA) with (o := bn_d b2) (D := D2) (a := am + 24) (b := b2) (bs := (qm, am, 96)) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW1) (LB := LB);
    [ exact HEAP2 | intros pd X; split; [exact (INS2' pd X) | cbn [blk_id fst]; exact (NQ RMontN pd HV2 X)] | exact NONE2
    | rewrite ESP; exact ST2 | exact CEIL | rewrite ESP; clear - LO'; unfold W_ctx_freeA.BN_CLEAR_FREE_STACK, W_expandA.BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK; lia
    | rewrite ESP; unfold USTACK_TOP; clear - SPT; lia | rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia | exact MI2 | reflexivity | exact CS2
    | exact BN2 | exact F2 | exact OK2c | exact INSa | cbn [blk_addr fst snd]; clear; lia | cbn [blk_addr blk_size fst snd]; clear; lia | clear - AL; Z.div_mod_to_equations; lia | reflexivity
    | rewrite ESP; exact UW2
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ (E_BN_MONT_CTX_free_226584 : uk_call W_mont_ctxAF.BN_MONT_CTX_FREE 2254700 W_ctx_freeA.BN_CLEAR_FREE) CTX) |].
  intros Σ2 ms2 PO.
  destruct PO as (v0 & v1 & v2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & v3 & v4 & v5 & v6 & Fx3 & fc3 & m3 & -> & MI3 & ST3 & AG3 & CR3 & HEAP3).
  fold OW2 in AG3, HEAP3.
  rewrite ?ESP in *. rewrite (ret_pc_even 2254700) by (clear; lia). unfold MallocRep.wz.
  assert (INSb : In (qm, am, 96) (OW2 ++ LB)) by (apply in_or_app; left; exact INQ2).
  apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply STKC; clear - Hx; lia].
  apply (rw_cells_agree _ _ _ _ _ AG3) in BN3; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply (INB' x _ INSb); clear - Hx; lia].
  apply (rw_cells_agree _ _ _ _ _ AG3) in MCc; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply (INB' x _ INSb); clear - Hx; lia].
  assert (CS3 : BnRepDefs.crypto_statics m3).
  { eapply BnRepA.crypto_statics_agree; [exact AG3 | | exact CS2]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
  assert (UW3 : uw_chain USTACK_TOP m3 (bv_unsigned sp + -32) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_chain_agree m2 m3 _ _ _ UW2). eapply agree_on_mono; [exact AG3|]. intros x Hx. cbv beta in *. left. clear - Hx. lia. }
  assert (UWm3 : uw_chain USTACK_TOP m3 (bv_unsigned sp) (bv_unsigned s0) ras).
  { apply (uw_chain_agree m2 m3 _ _ _ UWm2). eapply agree_on_mono; [exact AG3|]. intros x Hx. cbv beta in *. left. clear - Hx. lia. }
  clear BN2.
  apply implA_from_evt.
  do 2 step.

  apply evt_done.
  eapply (BN_clear_free_optA) with (o := bn_d b3) (D := D3) (a := am + 48) (b := b3) (bs := (qm, am, 96)) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW2) (LB := LB);
    [ exact HEAP3 | intros pd X; split; [exact (INS3' pd X) | cbn [blk_id fst]; exact (NQ RMontNi pd HV3 X)] | exact NONE3
    | rewrite ESP; exact ST3 | exact CEIL | rewrite ESP; clear - LO'; unfold W_ctx_freeA.BN_CLEAR_FREE_STACK, W_expandA.BN_FREE_D_STACK, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK; lia
    | rewrite ESP; unfold USTACK_TOP; clear - SPT; lia | rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia | exact MI3 | reflexivity | exact CS3
    | exact BN3 | exact F3 | exact OK3c | exact INSb | cbn [blk_addr fst snd]; clear; lia | cbn [blk_addr blk_size fst snd]; clear; lia | clear - AL; Z.div_mod_to_equations; lia | reflexivity
    | rewrite ESP; exact UW3
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ (E_BN_MONT_CTX_free_22658c : uk_call W_mont_ctxAF.BN_MONT_CTX_FREE 2254708 W_ctx_freeA.BN_CLEAR_FREE) CTX) |].
  intros Σ3 ms3 PO.
  destruct PO as (w0 & w1 & w2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & w3 & w4 & w5 & w6 & Fx4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & CR4 & HEAP4).
  fold OW3 in AG4, HEAP4.
  rewrite ?ESP in *. rewrite (ret_pc_even 2254708) by (clear; lia). unfold MallocRep.wz.
  assert (INSc : In (qm, am, 96) (OW3 ++ LB)) by (apply in_or_app; left; exact INQ3).
  apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply STKC; clear - Hx; lia].
  apply (rw_cells_agree _ _ _ _ _ AG4) in MCc; [| intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply (INB' x _ INSc); clear - Hx; lia].
  assert (CS4 : BnRepDefs.crypto_statics m4).
  { eapply BnRepA.crypto_statics_agree; [exact AG4 | | exact CS3]. intros x Hx. right; left. exact (ar_LIBW_cs x Hx). }
  assert (UWm4 : uw_chain USTACK_TOP m4 (bv_unsigned sp) (bv_unsigned s0) ras).
  { apply (uw_chain_agree m3 m4 _ _ _ UWm3). eapply agree_on_mono; [exact AG4|]. intros x Hx. cbv beta in *. left. clear - Hx. lia. }
  clear BN3.

  pose proof (rw_cells_app_r m4 (am + 72) [C8 (wz (st_n0 ls)); C8 (wz 0); C4 (wz (st_ri ls))] [C4 (wz BN_FLG_MALLOCED)] MCc) as MCF.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in MCF. replace (am + 72 + 20) with (am + 92) in MCF by (clear; lia).
  assert (MCB : rw_cells bgbsegs m4 (am + 92) [C1 (Z_to_bv 8 1); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]).
  { apply (rw_cells_recast m4 (am + 92) [C4 (wz BN_FLG_MALLOCED)] _ MCF); [cbn; tauto | vm_compute; reflexivity | reflexivity]. }
  clear MCF MCc.
  pose proof (AH_acc_in _ _ _ _ (qm, am, 96) am 96 HEAP4 INSc ltac:(cbn [blk_addr fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear; lia)) as ACC4.
  pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND1. pose proof (AH_nodup_l _ _ _ _ HEAP3) as ND2. pose proof (AH_nodup_l _ _ _ _ HEAP4) as ND3.
  clear MU WM OFF SHB1 SHB2 HEAP HEAP1 HEAP2 HEAP3 ST ST2 ST3 MI MI2 MI3 UW1 UW2 UW3.
  pose proof (munch_refl (@nil (Z * Z)) m4) as MU4.
  destruct (AH_shb _ _ _ _ HEAP4) as (SHB1 & SHB2).
  apply implA_from_evt.
  do 3 step. shl_with ACC4 AL. chk0.
  step. rewrite (zxb_small 1) by (clear; lia). step. step. if_true.
  do 4 step.
  do 4 step. release_frame FR ST4 (bv_unsigned sp). step. step.

  apply evt_done.
  eapply (CRYPTO_free_walkA) with (A := am) (n := 96) (lo := lo) (ras := ras) (OW := OW3) (LB := LB);
    [ exact HEAP4 | exact INQ3 | exact ST4 | exact CEIL | unfold CRYPTO_FREE_STACK, RT_STACK; clear - LO'; lia | unfold USTACK_TOP; clear - SPT; lia | exact SP16
    | exact MI4 | reflexivity | exact CS4 | reflexivity | exact UWm4
    | exact (uk_ctx_tail _ _ _ (E_BN_MONT_CTX_free_2265ec : uk_tail W_mont_ctxAF.BN_MONT_CTX_FREE BnRepDefs.CRYPTO_FREE) CTX) |].
  intros Σ4 ms4 PO.
  destruct PO as (z0 & z1 & z2 & i0 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & z3 & z4 & z5 & z6 & Fx5 & fc5 & m5 & -> & MI5 & ST5 & AG5 & CR5 & HEAP5).
  apply implA_ret.
  assert (EL5 : lb_remove qm (OW3 ++ LB) = OW4 ++ LB) by (unfold OW4; rewrite lb_remove_app, (lb_remove_notin qm LB QNLB); reflexivity).
  rewrite EL5 in AG5. fold OW4 in HEAP5.

  assert (UPL : forall (L L' : list block), (forall b, In b L' -> In b L) -> forall b, In b (L' ++ LB) -> In b (L ++ LB)).
  { intros L L' HI b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact (HI _ Hb) | right; exact Hb]. }
  assert (AGT : agree_on (aclient_addr (OW4 ++ LB) (bv_unsigned sp)) m m5).
  { eapply agree_on_trans; [eapply agree_on_trans; [eapply agree_on_trans; [eapply agree_on_trans|]|]|].
    - eapply agree_client_weaken; [exact AG1 | clear; lia | apply UPL; intros b Hb; exact (INC1 _ (INC2 _ (INC3 _ (INC4 _ Hb))))].
    - eapply agree_client_weaken; [exact AG2 | clear; lia | apply UPL; intros b Hb; exact (INC2 _ (INC3 _ (INC4 _ Hb)))].
    - eapply agree_client_weaken; [exact AG3 | clear; lia | apply UPL; intros b Hb; exact (INC3 _ (INC4 _ Hb))].
    - eapply agree_client_weaken; [exact AG4 | clear; lia | apply UPL; intros b Hb; exact (INC4 _ Hb)].
    - exact AG5. }

  set (bs1 := setbn RMontRR (bn_nil 0) ls).
  set (bs2 := setbn RMontN (bn_nil 0) bs1).
  set (bs3 := setbn RMontNi (bn_nil 0) bs2).
  assert (IDS1 : ids_ok bs1 PL EA) by (apply ids_ok_setbn_none; [exact IDS| exact HV1| reflexivity]).
  assert (LSa : lib_state_h [RMontNi; RMontN; RMontRR] bs1 m OW PL EA).
  { eapply (lib_state_h_setbn_hole false [RMontNi; RMontN; RMontRR] ls m OW PL EA RMontRR am); [exact LSH3| exact ND| exact HA1| right; right; left; reflexivity| exact NRO1
      | apply bg_ok_nil; left; reflexivity| exact IDS1]. }
  assert (HV2' : vref RMontN bs1) by (unfold vref, bs1; rewrite length_setbn; exact HV2).
  assert (IDS2 : ids_ok bs2 PL EA) by (apply ids_ok_setbn_none; [exact IDS1| exact HV2'| reflexivity]).
  assert (LSb : lib_state_h [RMontNi; RMontN; RMontRR] bs2 m OW PL EA).
  { eapply (lib_state_h_setbn_hole false [RMontNi; RMontN; RMontRR] bs1 m OW PL EA RMontN (am + 24)); [exact LSa| exact ND| exact (ref_at_mN bs1 OW PL am qm E)| right; left; reflexivity| exact NRO2
      | apply bg_ok_nil; left; reflexivity| exact IDS2]. }
  assert (HV3' : vref RMontNi bs2) by (unfold vref, bs2, bs1; rewrite !length_setbn; exact HV3).
  assert (IDS3 : ids_ok bs3 PL EA) by (apply ids_ok_setbn_none; [exact IDS2| exact HV3'| reflexivity]).
  assert (LSc : lib_state_h [RMontNi; RMontN; RMontRR] bs3 m OW PL EA).
  { eapply (lib_state_h_setbn_hole false [RMontNi; RMontN; RMontRR] bs2 m OW PL EA RMontNi (am + 48)); [exact LSb| exact ND| exact (ref_at_mNi bs2 OW PL am qm E)| left; reflexivity| exact NRO3
      | apply bg_ok_nil; left; reflexivity| exact IDS3]. }
  assert (G1 : getbn RMontRR bs3 = bn_nil 0).
  { unfold bs3, bs2. rewrite !getbn_setbn_other by (unfold RMontRR, RMontN, RMontNi; lia). unfold bs1. apply getbn_setbn_same. exact HV1. }
  assert (G2 : getbn RMontN bs3 = bn_nil 0).
  { unfold bs3. rewrite getbn_setbn_other by (unfold RMontN, RMontNi; lia). unfold bs2. apply getbn_setbn_same. exact HV2'. }
  assert (G3 : getbn RMontNi bs3 = bn_nil 0) by (unfold bs3; apply getbn_setbn_same; exact HV3').
  destruct (lib_state_unplace_mont false [RMontNi; RMontN; RMontRR] [] bs3 m OW PL EA am qm 0 0 LSc E G1 G2 G3) as [LSu NQF].
  { intros r [<-|[<-|[<-|[]]]]; left; reflexivity. }
  fold bsF in LSu, NQF.

  assert (FOR1 : forall p1, bn_d b1 = Some p1 -> ~ In p1 (all_ids bsF (pl_set_mont PL None) EA)).
  { intros p1 X H. apply (all_ids_unset_mont bs3 PL EA am qm 0 0 p1 E) in H.
    apply (all_ids_setbn_nil bs2 _ EA RMontNi p1 HV3') in H. apply (all_ids_setbn_nil bs1 _ EA RMontN p1 HV2') in H.
    exact (all_ids_without ls _ EA RMontRR p1 IDS HV1 X H). }
  assert (FOR2 : forall p2, bn_d b2 = Some p2 -> ~ In p2 (all_ids bsF (pl_set_mont PL None) EA)).
  { intros p2 X H. apply (all_ids_unset_mont bs3 PL EA am qm 0 0 p2 E) in H.
    apply (all_ids_setbn_nil bs2 _ EA RMontNi p2 HV3') in H.
    apply (all_ids_without bs1 _ EA RMontN p2 IDS1 HV2'); [|exact H]. unfold bs1. rewrite getbn_setbn_other by exact NE12. exact X. }
  assert (FOR3 : forall p3, bn_d b3 = Some p3 -> ~ In p3 (all_ids bsF (pl_set_mont PL None) EA)).
  { intros p3 X H. apply (all_ids_unset_mont bs3 PL EA am qm 0 0 p3 E) in H.
    apply (all_ids_without bs2 _ EA RMontNi p3 IDS2 HV3'); [|exact H]. unfold bs2, bs1. rewrite !getbn_setbn_other by (unfold RMontRR, RMontN, RMontNi; lia). exact X. }
  assert (KEEP : forall q A n, In q (all_ids bsF (pl_set_mont PL None) EA) -> In (q, A, n) OW -> In (q, A, n) OW4).
  { intros q A n Hq Hin. unfold OW4, OW3, OW2, OW1. apply lb_remove_In. split; [|cbn [blk_id fst]; intros ->; exact (NQF Hq)].
    apply lb_remove_opt_In. split; [|intros p3 X; cbn [blk_id fst]; intros ->; exact (FOR3 p3 X Hq)].
    apply lb_remove_opt_In. split; [|intros p2 X; cbn [blk_id fst]; intros ->; exact (FOR2 p2 X Hq)].
    apply lb_remove_opt_In. split; [exact Hin|]. intros p1 X. cbn [blk_id fst]. intros ->. exact (FOR1 p1 X Hq). }
  assert (LSv : lib_state bsF m OW4 (pl_set_mont PL None) EA) by (eapply lib_state_h_ow; [exact LSu| exact KEEP]).
  assert (LSF : lib_state bsF m5 OW4 (pl_set_mont PL None) EA).
  { unfold lib_state in *. eapply lib_state_h_heap_pres with (m := m) (LB := LB) (L := OW4 ++ LB) (SP := bv_unsigned sp) (SPX := bv_unsigned sp) (BX := USTACK_TOP);
      [exact LSv| exact (frames_ok_set_mont _ _ _ _ _ FROK) | clear; lia| clear; lia | exact AGT| intros b Hb; apply in_or_app; left; exact Hb | intros b Hb; apply in_or_app; right; exact Hb]. }
  unfold bn_postA_p. do 17 eexists. exists m5, OW4, (pl_set_mont PL None). split; [reflexivity|]. cbn [fst snd].
  split; [exact HEAP5|]. split; [exact LSF|]. split; [exact ST5|]. split; [exact MI5|].
  split. { eapply agree_on_mono; [exact AGT|]. intros x [_ [Hx|[Hx|(bk & Hbk & Hr)]]];
             [left; exact Hx | right; left; exact Hx | right; right; exists bk; split; [apply in_or_app; right; exact Hbk | exact Hr]]. }
  split; [rewrite CR5, CR4, CR3, CR2; clear; lia|].
  split; [reflexivity|].
  split.
  { change (cnt_bal bsF OW4) with (cnt_bal bs3 OW4). unfold bs3.
    rewrite (cnt_bal_setbn RMontNi (bn_nil 0) bs2 OW2 OW4 HV3'). unfold bs2 at 1 2.
    rewrite (cnt_bal_setbn RMontN (bn_nil 0) bs1 OW1 OW2 HV2'). unfold bs1 at 1 2.
    rewrite (cnt_bal_setbn RMontRR (bn_nil 0) ls OW OW1 HV1).
    rewrite !getbn_setbn_other by (unfold RMontRR, RMontN, RMontNi; lia). fold b1 b2 b3.
    pose proof (lb_remove_opt_length (bn_d b1) OW ND ltac:(intros p X; exact (in_map blk_id _ _ (INS1 p X)))) as L1. fold OW1 in L1.
    pose proof (lb_remove_opt_length (bn_d b2) OW1 ND1 ltac:(intros p X; exact (in_map blk_id _ _ (INS2' p X)))) as L2. fold OW2 in L2.
    pose proof (lb_remove_opt_length (bn_d b3) OW2 ND2 ltac:(intros p X; exact (in_map blk_id _ _ (INS3' p X)))) as L3. fold OW3 in L3.
    pose proof (lb_remove_length qm OW3 ND3 (in_map blk_id _ _ INQ3)) as L4. fold OW4 in L4.
    unfold bn_blocks. cbn [bn_d bn_nil length]. clear - L1 L2 L3 L4. destruct (bn_d b1), (bn_d b2), (bn_d b3); cbn [length] in *; lia. }
  apply refs_stable_ow; [reflexivity|]. intros q H Hq HinH. unfold OW4, OW3, OW2, OW1.
  apply lb_remove_In. split.
  2: { cbn [blk_id fst]. intros ->. apply (ids_pl_m ls PL EA qm qm IDS); [|exact (item_in_m ls qm Hq)| reflexivity].
       unfold pl_ids. rewrite E. cbn [opt_ids]. apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
  apply lb_remove_opt_In. split; [|intros p3 X; cbn [blk_id fst]; intros ->; exact (ids_bn_item_neq RMontNi ls p3 p3 NDM HV3 X Hq eq_refl)].
  apply lb_remove_opt_In. split; [|intros p2 X; cbn [blk_id fst]; intros ->; exact (ids_bn_item_neq RMontN ls p2 p2 NDM HV2 X Hq eq_refl)].
  apply lb_remove_opt_In. split; [exact HinH|]. intros p1 X. cbn [blk_id fst]. intros ->. exact (ids_bn_item_neq RMontRR ls p1 p1 NDM HV1 X Hq eq_refl).
Qed.

End WithRT.
