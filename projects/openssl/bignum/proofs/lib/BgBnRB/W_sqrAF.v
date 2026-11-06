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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith BgSqrCorrect.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnA Require Import BnAPure.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop AsLeaf.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA W_topA AsStruct2 AW_num_bits_word BnKaraMemA BnCallsKA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require Import BgLeaves BgLive DivModel.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR2 Require W_sqr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW2 Require W_sqr_words W_sqr_normal.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_callsAF W_calls3AF W_expandAF W_ctxAF W_ctx_endAF W_ctx_getAF AFrameKit AFrameCall AFrameTac AFrameEnv AFrameComp ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import ExpBodyKitF InvKitAF SqrKitAF Fr_sqr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require AW_sqr_words AW_sqr_normal AW_sqr_recursive AW_sqr_closedA W_mulA2F W_div_tailAF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).

Notation sqr_fin := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sqr.sqr_fin.
Notation sqr_model_fin := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_sqr.sqr_model_fin.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2298268 => 2
  | 2298272 => 1
  | 2298276 => 2
  | 2298364 => 1
  | 2298368 => 1
  | 2298372 => 2
  | 2298412 => 1
  | 2298416 => 2
  | 2298468 => 2
  | 2298472 => 1
  | 2298476 => 2
  | 2298536 => 1
  | 2298540 => 2
  | 2298712 => 1
  | 2298732 => 2
  | 2298936 => 2
  | 2298940 => 1
  | 2298944 => 2
  | 2298964 => 2
  | 2298972 => 1
  | 2298976 => 1
  | 2298980 => 2
  | 2299000 => 1
  | 2299004 => 1
  | 2299008 => 2
  | 2299100 => 1
  | 2299104 => 1
  | 2299108 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.

Definition SQR_CS : Z := AW_sqr_recursive.srec_stackA AW_sqr_closedA.CSLA 9.
Lemma SQR_CS_val : SQR_CS = 66656.
Proof. reflexivity. Qed.

Ltac sq_unf H := idtac.
Ltac sq_store_gen CF FBz SPz ENV LS ENV' LS' :=
  let STx := fresh "STx" in let MIx := fresh "MIx" in let FRx := fresh "FRx" in let FSZx := fresh "FSZx" in
  let MUx := fresh "MUx" in let WMx := fresh "WMx" in let SZx := fresh "SZx" in
  pose proof ENV as (_ & _ & STx & MIx & _ & _ & _ & _ & FRx & FSZx & _);
  sq_unf FRx; sq_unf FSZx; cbn [app] in FRx;
  assert (SZx : FBz + 72 <= SPz) by (cbn [app cells_size csize Nat.add] in FSZx; clear - FSZx; lia);
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(FBz, SPz)]%Z mm) as MUx; pose proof (wmono_refl bgbsegs mm) as WMx end;
  step;
  lazymatch type of FRx with
  | rw_cells _ ?mx _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: _) =>
      destruct (CF _ [c0; c1; c2; c3; c4; c5; c6; c7] _ _ _ _ mx _
                  ENV LS MUx WMx STx MIx FRx ltac:(cbn [app cells_size csize Nat.add] in FSZx |- *; exact FSZx)) as (ENV' & LS')
  end;
  clear STx MIx FRx FSZx MUx WMx SZx.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation FR := (@ar_FR AR).

Lemma MC_0 : MC = 0. Proof. reflexivity. Qed.

Section KitL.
  Variables (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (ras : list Z) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Notation CENV := (cenvA LB PL lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0).

  Lemma kcallT : forall {A C : Type} (t : btree bptr (A * ST)) (KT : A * ST -> btree bptr C)
      (phi : A * ST -> Prop)
      (RES : A -> ST -> list block -> placement -> word -> Prop)
      (Q : C -> rts RT -> machine_state -> Prop) (pre : list cell) (used cost used' KS : Z) (Σ : rts RT) (ls : ST) (m : mem) (OW : list block) (pc : word)
      (rax gp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    bv_unsigned x8 = SPv ->
    CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> lo <= FB - KS -> used + cost <= used' -> used' <= TOTAL ->
    leaves t phi ->
    (bn_preA Σ ls m OW LB PL EA (Z_to_bv 64 FB) lo KS cost ->
     uw_chain USTACK_TOP m (bv_unsigned (Z_to_bv 64 FB)) (bv_unsigned x8) (bv_unsigned raw :: ras) ->
     implA t Σ
       (bn_postA rax (Z_to_bv 64 FB) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Σ ls OW LB lo m PL EA cost RES)
       (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
           F pc fc None m (seg_rom bgbsegs))) ->
    (forall v ls' OW' PL' a0', RES v ls' OW' PL' a0' -> PL' = PL) ->
    (forall (v : A) Σ' ls' m' OW' (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) F' fc',
       CENV pre used' Σ' ls' m' OW' -> lib_state ls' m' OW' PL EA -> refs_stable ls OW ls' OW' -> RES v ls' OW' PL y3 -> phi (v, ls') ->
       implA (KT (v, ls')) Σ' Q
         (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
             F' (ret_pc rax) fc' None m' (seg_rom bgbsegs))) ->
    implA (tbind t KT) Σ Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F pc fc None m (seg_rom bgbsegs)).
  Proof.
    intros until fc. intros E8 ENV LS HK HU HT HL WALK HPL K1.
    pose proof ENV as (OK & HEAP & _).
    destruct (ESPs LB PL lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ ENV) as (ES & EF).
    eapply implA_bind.
    { eapply implA_leaves; [exact HL|]. apply WALK.
      - eapply cenv_preA; [exact ENV | exact LS | exact HK | clear - HU HT; lia].
      - rewrite E8, EF. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV). }
    cbv beta. intros [v ls'] Σ' ms' [PO LEAF].
    apply (bn_postA_cpost LB PL EA lo SPv FB TOTAL Σ0 ls0 OW0) in PO; [| exact OK | exact HEAP].
    cbn [fst snd] in *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m' & OW' & PL' & -> & CP & RES').
    pose proof (HPL _ _ _ _ _ RES') as EPL. subst PL'. specialize (CP eq_refl).
    destruct (cenv_postA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ _ _ _ _ _ ENV CP) as (ENV' & LS').
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS'.
    eapply K1; [eapply cenv_used_le; [exact ENV' | exact HU] | exact LS' | exact RS' | exact RES' | exact LEAF].
  Qed.
End KitL.

Section Body.
  Local Ltac hres := let H := fresh "HRES" in intros ? ? ? ? ? H; hnf in H; exact (proj1 H).
  Local Ltac retpc n := rewrite (ret_pc_even n) by (clear; lia).
  Local Ltac mc0 := rewrite ?MC_0; clear; lia.
  Local Ltac pre_wk PRE STK := eapply bn_preA_wk; [exact PRE | exact STK | clear; lia].

  Variables (gp s0r : word) (lo SPv FB : Z) (s0w raw : word) (ras : list Z) (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Variables (ac : Z) (qc : bptr) (f : Z) (g : nat) (junk : list byte).
  Variables (rr rx : bnref).
  Hypothesis ES0 : bv_unsigned s0r = SPv.
  Hypothesis LOF : lo <= FB - SQR_CS.
  Hypothesis HPC : pl_ctx PL = Some (ac, qc).
  Hypothesis HF : In (f, 3%nat) FR.
  Hypothesis FRESH : forall b, In b LB -> off_fr f 3 b.
  Hypothesis CTX : uk_ctx BN_MOD_SQR (bv_unsigned raw :: ras).
  Hypothesis TOT0 : 0 <= TOTAL.
  Hypothesis HPr : hpl PL rr.
  Hypothesis NROx : rx <> ROne.
  Hypothesis NBx : nbuf PL rx.
  Variable Q : unit * ST -> rts RT -> machine_state -> Prop.

  Notation CENV := (cenvA LB PL lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0).
  Notation KCALL := (kcallA LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0).
  Notation KCALLT := (kcallT LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0).
  Notation KLAST := (kcallA_last LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0).

  Lemma LOF16 : lo <= FB - 16. Proof using LOF. clear - LOF. rewrite SQR_CS_val in LOF. lia. Qed.
  Lemma LOFV : lo <= FB - 66656. Proof using LOF. clear - LOF. rewrite SQR_CS_val in LOF. exact LOF. Qed.
  Lemma STK_START : BN_CTX_START_STACK <= SQR_CS. Proof using. rewrite SQR_CS_val. unfold BN_CTX_START_STACK, CRYPTO_MALLOC_ARRAY_STACK, CRYPTO_MALLOC_STACK, RT_STACK. clear. lia. Qed.
  Lemma STK_GET : BN_CTX_GET_STACK <= SQR_CS. Proof using. rewrite SQR_CS_val. unfold BN_CTX_GET_STACK, CRYPTO_MALLOC_STACK, RT_STACK. clear. lia. Qed.
  Lemma STK_WEXP : BN_WEXPAND_STACK <= SQR_CS.
  Proof using. rewrite SQR_CS_val. unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK. clear. lia. Qed.
  Lemma STK_END : BN_CTX_END_STACK <= SQR_CS. Proof using. rewrite SQR_CS_val. unfold BN_CTX_END_STACK. clear. lia. Qed.

  Definition sfr (c3 c6 : cell) (j0 j1 j2 j4 j5 : list byte) : list cell :=
    [CB 8 j0; CB 8 j1; CB 8 j2; c3; CB 8 j4; CB 8 j5; c6; CB g junk].
  Ltac sq_unf H ::= unfold sfr in H.
  Local Ltac fr_store ENV LS ENV' LS' := sq_store_gen (cenv_frameA LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0) FB SPv ENV LS ENV' LS'.

  Hypothesis EPI : forall c3 j0 j1 j2 j4 j5 Σk lsk mk OWk
      (rax t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 x23 x25 x26 t3 t4 t5 t6 : word) F' fc',
    CENV (sfr c3 (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL Σk lsk mk OWk -> lib_state lsk mk OWk PL EA ->
    implA (TRet (tt, lsk)) Σk Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r x9 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) x20 x21 x22 x23 (Z_to_bv 64 1) x25 x26 (Z_to_bv 64 f) t3 t4 t5 t6)
          F' (wz SQR_EXIT) fc' None mk (seg_rom bgbsegs)).

  Lemma env_bounds : forall pre used Σ ls m OW, CENV pre used Σ ls m OW ->
    bv_unsigned (Z_to_bv 64 FB) = FB /\ bv_unsigned (Z_to_bv 64 SPv) = SPv /\ 12554240 <= FB /\ FB + 16 <= SPv /\ SPv + 16 <= 140737488355328.
  Proof using.
    intros pre used Σ ls m OW ENV. destruct (ESPs LB PL lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ ENV) as (E1 & E2).
    destruct ENV as ((CEIL & LOFB & FBSP & SPT & _) & HEAP & _). pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _).
    unfold SEGTOP_A, USTACK_TOP in *. split; [exact E2|]. split; [exact E1|]. clear - C1 CEIL LOFB FBSP SPT. lia.
  Qed.

  Lemma sqr_tailA : forall (max : nat) (R : Z) j0 j1 j2 j4 j5 ΣK lsK mK OWK
      (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x25 x26 t3 t4 t5 t6 : word) F1 fc1,
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
    ref_at lsK OWK PL rr R -> (max <= bn_dmax (getbn rr lsK))%nat ->
    implA (BN_CTX_end ops (setbn rr (sqr_fin (getbn rr lsK) max) lsK)) ΣK Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 R) x22 (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat max)) x25 x26 (Z_to_bv 64 f) t3 t4 t5 t6)
          F1 (wz 0x23152c) fc1 None mK (seg_rom bgbsegs)).
  Proof.
    intros until fc1. intros ENVK LSK HR HMAX.
    destruct (env_bounds _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
    pose proof (hpl_wref PL rr HPr) as WR.
    destruct (cenv_struct_openA LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 LOF16 _ _ _ _ _ _ rr R ENVK LSK HR WR)
      as (Dr & BNN & OKN & ACCN & ALN & AN0 & SEPN & OFRN & STN & MIN & CLOSEN).
    unfold BnRepDefs.bn_cells, MallocRep.wz in BNN.
    pose proof ENVK as (_ & _ & _ & _ & _ & _ & _ & _ & FRx & _). unfold sfr in FRx. cbn [app] in FRx.
    pose proof (munch_refl [(R, R + 24)]%Z mK) as MU. pose proof (wmono_refl bgbsegs mK) as WM.
    assert (OFF : offshW [(R, R + 24)]) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFRN; lia).
    assert (DMB : Z.of_nat (bn_dmax (getbn rr lsK)) <= 512) by (destruct OKN as (_ & _ & O3 & _); unfold BG_DMAX in O3; exact O3).
    unfold MallocRep.wz. apply implA_from_evt.
    do 3 zstep. shl_with ACCN ALN. chk0.
    zstep.
    do 3 zstep. shl_with ACCN ALN. chk0.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mq end.
    destruct (CLOSEN mq (sqr_fin (getbn rr lsK) max) MU WM) as (ENV7 & LS7);
      [ unfold BnRepDefs.bn_cells, sqr_fin, bn_dmax, MallocRep.wz; cbn [bn_top bn_buf bn_neg bn_flags bn_d Z.b2z]; exact BNN | reflexivity | reflexivity
      | destruct OKN as (O1 & O2 & O3 & O4); unfold bg_ok, sqr_fin, bn_dmax in *; cbn [bn_top bn_buf bn_flags]; auto
      | assumption | assumption |].
    clear CLOSEN BNN MU WM ENVK LSK.
    zstep. if_cases KE; zify_cond KE; [| exfalso; apply KE; reflexivity]. clear KE.
    zstep. step.
    step. step.
    apply evt_done.
    eapply (KLAST _ _ _ _ TOTAL 0 TOTAL BN_CTX_END_STACK); [exact ES0 | exact ENV7 | exact LS7 | pose proof STK_END; clear - LOF H; lia | clear; lia | clear; lia
      | intros PRE UW; eapply BN_CTX_end_walkA; [exact PRE | reflexivity | exact HPC | reflexivity]
      | intros v b o p a; cbv beta; intros [E _]; exact E |].
    intros u Σ' ls' m' OW' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F' fc' ENV' LS' RS'; cbv beta; intros (_ & EOW).
    retpc 2299268.
    destruct u. eapply EPI; [exact ENV' | exact LS'].
  Qed.

  Lemma off_all : forall Σ OW m, AHEAP Σ OW LB m -> forall b, In b (OW ++ LB) -> off_fr f 3 b.
  Proof using HF FRESH.
    intros Σ OW m HEAP b Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (AH_ow_off_fr Σ OW LB m f 3%nat b HEAP HF Hb) | exact (FRESH b Hb)].
  Qed.

  Lemma sqr_close1A : forall (max : nat) (R Dr TN CST : Z) (w : list Z) j0 j1 j2 j4 j5 ΣK lsK mK m4 OWK,
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
    ref_at lsK OWK PL rr R ->
    rw_cells bgbsegs mK R (bn_cells Dr (getbn rr lsK)) -> BnRepDefs.bn_arr mK OWK Dr (getbn rr lsK) ->
    limbs w -> length w = max -> (0 < max <= bn_dmax (getbn rr lsK))%nat ->
    0 <= TN <= 256 -> 0 <= CST -> lo <= FB - CST ->
    munch [(Dr, Dr + 8 * Z.of_nat max); (f + 32, f + 32 + TN); (FB - CST, FB)] mK m4 ->
    wmono bgbsegs mK m4 -> mem_inv bgbsegs m4 -> stk bgbsegs m4 lo FB ->
    limbs_at bgbsegs m4 Dr w ->
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK (setbn rr (bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0 w)) lsK) m4 OWK
    /\ lib_state (setbn rr (bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0 w)) lsK) m4 OWK PL EA.
  Proof.
    intros until OWK. intros ENV LS HR SR ARR LW ELW [HW0 HWD] HTN HCST LOC MU WM MI4 ST4 HR4.
    pose proof (proj1 HPr : not_one rr) as NROr.
    pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FRc & FSZ & UW). unfold sfr in FRc. cbn [app] in FRc.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (AH_fr_geo _ _ _ _ f 3%nat HEAP HF) as GEO. pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 3) with 512 in *.
    destruct (lib_state_open [] lsK mK OWK PL EA rr R LS ND HR ltac:(intros []) NROr) as (_ & OKR & LSH).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (bn_arr_facts_w lsK OWK PL EA SPv USTACK_TOP ΣK LB mK rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HPr)
                ltac:(first [exact ARR | exact (bn_arr_of_nofr PL rr _ _ _ _ PWF NOFR NROr ARR ltac:(solve_nbuf))])) as (U & LENW & D0 & DC & DI & DSEP).
    pose proof (DSEP rr R HR) as DSR.
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HR NROr) as (qs & As & ns & Hins & Ra1 & Ra2).
    pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
    pose proof (off_all _ _ _ HEAP _ Hins) as OFS. unfold off_fr in OFS. cbn [blk_addr blk_size fst snd] in OFS. change (fs_size 3) with 512 in OFS.
    set (br := getbn rr lsK) in *.
    assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
    unfold BnRepDefs.bn_arr, bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
    2:{ exfalso. destruct ARR as [_ Eb]. rewrite Eb in LBR. cbn [length] in LBR. clear - LBR HW0 HWD. lia. }
    destruct ARR as [HinR _].
    pose proof (off_all _ _ _ HEAP _ (in_or_app _ _ _ (or_introl HinR))) as OFD. unfold off_fr in OFD. cbn [blk_addr blk_size fst snd] in OFD. change (fs_size 3) with 512 in OFD.
    set (W := [(Dr, Dr + 8 * Z.of_nat max); (f + 32, f + 32 + TN); (FB - CST, FB)]) in *.
    assert (HW : Forall (w_frmix OWK LB lsK PL EA lo SPv [rr] f 3) W).
    { constructor; [left; split|].
      - right; left. exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)). cbn [blk_addr blk_size fst snd]. split; [exact HinR | clear - HWD; lia].
      - eapply (w_limbs OWK LB lsK PL EA SPv false [rr] _ rr pr Dr); [left; reflexivity | exact HVR | exact Edr | exact HinR | cbn [fst snd]; clear; lia | cbn [fst snd]; fold br; clear - HWD; lia].
      - constructor; [right; left; cbn [fst snd]; change (fs_size 3) with 512; clear - HTN; lia|].
        constructor; [left; split; [left; cbn [fst snd]; clear - LOC HCST FBSP; lia | apply w_stack; cbn [fst snd]; clear - LOC HCST CEIL FBSP; lia] | constructor]. }
    eapply (rw_cells_transport bgbsegs _ mK m4) in FRc; [| exact MU | exact WM |].
    2:{ subst W. cbn [disjoint_from cells_size csize Nat.add]. unfold BnHeapA.ACEIL in *. clear - DC CEIL LOFB HWD G3 HTN HCST. lia. }
    destruct (cenv_frmixA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) _ _ _ _ m4 _ W f 3%nat [rr]
                ENV LSH HF FRESH MU WM HW ST4 MI4 ltac:(unfold sfr; cbn [app]; exact FRc) FSZ) as (ENV4 & LSH4).
    assert (SR4 : rw_cells bgbsegs m4 R (bn_cells Dr br)).
    { eapply rw_cells_transport; [exact SR | exact MU | exact WM |]. subst W. unfold bn_cells. cbn [disjoint_from cells_size csize Nat.add]. unfold BnHeapA.ACEIL in *.
      clear - DSR SAC CEIL LOC HCST HWD OFS Ra1 Ra2 HTN. lia. }
    set (br' := bn_with_buf br (splice (bn_buf br) 0 w)).
    assert (LSP : length (splice (bn_buf br) 0 w) = bn_dmax br) by (rewrite splice_length; [exact LBR| rewrite LBR, ELW; clear - HWD; lia]).
    assert (LSN : lib_state (setbn rr br' lsK) m4 OWK PL EA).
    { unfold lib_state. eapply (lib_state_close [] lsK m4 OWK PL EA rr R); [exact LSH4 | exact ND | exact HR | exact NROr | | |].
      - exists Dr. split; [unfold br', bn_cells, bn_with_buf, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; rewrite LSP; exact SR4|].
        unfold BnRepDefs.bn_arr, bn_arr, br', bn_with_buf. cbn [bn_d]. rewrite Edr. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LSP.
        split; [exact HinR|].
        eapply arr_splice0; [exact U | exact MU | exact WM | exact HR4 | rewrite LBR, ELW; clear - HWD; lia | |]; subst W; cbn [disjoint_from]; rewrite ?LBR, ?ELW;
          unfold BnHeapA.ACEIL in *; clear - DC CEIL LOC HCST HWD OFD HTN; lia.
      - destruct OKR as (O1 & O2 & O3 & O4). unfold bg_ok, br', bn_with_buf, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. rewrite LSP.
        split; [apply splice_limbs; [exact O1| exact LW]|]. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVR |]. unfold bn_blocks, br', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite LSP. reflexivity. }
    assert (ENVN : CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK (setbn rr br' lsK) m4 OWK).
    { apply cenv_setbnA; [exact ENV4 | exact HVR |]. fold br. unfold br', bn_with_buf, bn_blocks. cbn [bn_d bn_buf bn_dmax bn_top]. rewrite ?Edr. reflexivity. }
    split; [exact ENVN | exact LSN].
  Qed.

  Lemma sqr_finish1A : forall (max : nat) (R Dr TN CST : Z) (w : list Z) j0 j1 j2 j4 j5 ΣK lsK mK m4 OWK
      (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x25 x26 t3 t4 t5 t6 : word) F1 fc1,
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
    ref_at lsK OWK PL rr R ->
    rw_cells bgbsegs mK R (bn_cells Dr (getbn rr lsK)) -> BnRepDefs.bn_arr mK OWK Dr (getbn rr lsK) ->
    limbs w -> length w = max -> (0 < max <= bn_dmax (getbn rr lsK))%nat ->
    0 <= TN <= 256 -> 0 <= CST -> lo <= FB - CST ->
    munch [(Dr, Dr + 8 * Z.of_nat max); (f + 32, f + 32 + TN); (FB - CST, FB)] mK m4 ->
    wmono bgbsegs mK m4 -> mem_inv bgbsegs m4 -> stk bgbsegs m4 lo FB ->
    limbs_at bgbsegs m4 Dr w ->
    implA (BN_CTX_end ops (setbn rr (sqr_fin (bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0 w)) max) lsK)) ΣK Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 R) x22 (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat max)) x25 x26 (Z_to_bv 64 f) t3 t4 t5 t6)
          F1 (wz 0x23152c) fc1 None m4 (seg_rom bgbsegs)).
  Proof.
    intros until fc1. intros ENV LS HR SR ARR LW ELW HWB HTN HCST LOC MU WM MI4 ST4 HR4.
    destruct (sqr_close1A max R Dr TN CST w j0 j1 j2 j4 j5 ΣK lsK mK m4 OWK ENV LS HR SR ARR LW ELW HWB HTN HCST LOC MU WM MI4 ST4 HR4) as (ENVN & LSN).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    set (br' := bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0 w)) in *.
    replace (setbn rr (sqr_fin br' max) lsK) with (setbn rr (sqr_fin (getbn rr (setbn rr br' lsK)) max) (setbn rr br' lsK))
      by (rewrite getbn_setbn_same by exact HVR; apply setbn_setbn_same).
    eapply sqr_tailA; [exact ENVN | exact LSN | apply ref_at_setbn; exact HR |].
    rewrite getbn_setbn_same by exact HVR. unfold br', bn_with_buf, bn_dmax. cbn [bn_buf].
    rewrite splice_length; [exact (proj2 HWB) | rewrite ELW; exact (proj2 HWB)].
  Qed.

  Lemma arr_posS : forall Σ OW m D (b : bignum bptr), AHEAP Σ OW LB m -> BnRepDefs.bn_arr m OW D b -> (0 < bn_dmax b)%nat ->
    0 < D /\ (D + 8 * Z.of_nat (bn_dmax b) <= 65536 \/ 12554240 <= D).
  Proof using.
    intros Σ OW m D b HEAP ARR HD. unfold BnRepDefs.bn_arr in ARR. destruct (bn_d b) as [p|] eqn:E.
    - destruct ARR as [Hin _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & _ & AI). clear - A0 AI. lia.
    - destruct ARR as [_ Eb]. exfalso. unfold bn_dmax in HD. rewrite Eb in HD. cbn in HD. clear - HD. lia.
  Qed.

  Lemma sqr_path_comba4A : forall (R X : Z) j0 j1 j2 j4 j5 ΣK lsK mK OWK
      (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x26 t3 t4 t5 t6 : word) F1 fc1,
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
    ref_at lsK OWK PL rr R -> ref_at lsK OWK PL rx X -> rx <> rr ->
    (4 <= bn_top (getbn rx lsK))%nat -> (8 <= bn_dmax (getbn rr lsK))%nat ->
    implA (BN_CTX_end ops (setbn rr (sqr_fin (bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0 (sqr_comba4 (firstn 4 (bn_buf (getbn rx lsK)))))) 8) lsK)) ΣK Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat 8)) x25 x26 (Z_to_bv 64 f) t3 t4 t5 t6)
          F1 (wz 0x23122c) fc1 None mK (seg_rom bgbsegs)).
  Proof.
    intros until fc1. intros ENV LS HR HX NXR HAL HDM.
    pose proof (proj1 HPr : not_one rr) as NROr. change (not_one rx) in NROx.
    destruct (env_bounds _ _ _ _ _ _ ENV) as (ESP & ESPS & B1 & B2 & B3).
    pose proof LOFV as LO'.
    pose proof ENV as (OK & HEAP & ST & MI & _ & _ & _ & _ & FRc & _). unfold sfr in FRc. cbn [app] in FRc.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
    destruct (open_full ΣK OWK LB mK lsK PL EA SPv rr R HEAP LS FROK NOFR HR NROr ltac:(solve_nbuf)) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEPR).
    destruct (operand_view_ne ΣK OWK LB mK lsK PL EA SPv rr R Dr rx X 4 HEAP LS FROK NOFR HR NROr SR ARR HX NROx HAL NXR NBx)
      as (Dx & SX & LX & UX & ARX & X0 & XC & DX0 & DXC & XR & RDX & XDR & DRX).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & _).
    pose proof (st_wf_ok rx lsK WFS HVX NROx) as (LMX & TDX & DMX & _). unfold BG_DMAX in DMX.
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HR NROr) as (ACR & ALR & OFR).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HX NROx) as (ACX & ALX & OFX).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACDR & ALDR & OFDR).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARX) as (ACDX & ALDX & _).
    destruct (arr_posS _ _ _ _ _ HEAP ARR ltac:(clear - HDM; lia)) as (PDR & IDR).
    destruct (arr_posS _ _ _ _ _ HEAP ARX ltac:(clear - HAL TDX; lia)) as (PDX & _).
    set (br := getbn rr lsK) in *. set (bx := getbn rx lsK) in *. set (la := firstn 4 (bn_buf bx)) in *.
    assert (LLA : length la = 4%nat) by (unfold la; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in TDX; clear - TDX HAL; lia]).
    assert (LIA : limbs la) by (apply limbs_firstn; exact LMX).
    pose proof (proj1 (limbarr_limbs_at bgbsegs mK Dr (bn_buf br)) UR) as [_ HW]. fold (bn_dmax br) in HW.
    assert (EDr : bv_unsigned (Z_to_bv 64 Dr) = Dr) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - DR0 DRC CEIL LO' B2 B3; lia).
    assert (EDx : bv_unsigned (Z_to_bv 64 Dx) = Dx) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - DX0 DXC CEIL LO' B2 B3; lia).
    pose proof SR as SR'. unfold bn_cells, MallocRep.wz in SR'. unfold MallocRep.wz in SX.
    pose proof (munch_refl (@nil (Z * Z)) mK) as MU0.
    assert (OFF0 : offshW (@nil (Z * Z))) by exact I.
    unfold MallocRep.wz. apply implA_from_evt.
    ub. do 2 zstep. shl_with ACR ALR. chk0.
    do 2 zstep. shl_with ACX ALX. chk0.
    step. step. clear SR' SX.
    step.
    eapply evt_cut.
    { eapply AW_sqr_closedA.sqr_comba4_okA with (a := la) (lo := lo) (m := mK); rewrite ?EDr, ?EDx, ?ESP; unfold AW_sqr_closedA.CSQ4A;
        [ exact LIA | exact LLA | exact LX | replace Dr with (Dr + 0) by lia; eapply wr_at_sub; [exact HW| | |]; clear - HDM; lia
        | clear - DRX HDM TDX HAL; unfold bn_dmax in *; lia | exact ST | clear - LO'; lia
        | unfold BnHeapA.ACEIL in *; clear - DRC CEIL LO' HDM; lia | unfold BnHeapA.ACEIL in *; clear - DXC CEIL LO' TDX HAL; unfold bn_dmax in *; lia | exact MI
        | exact (AH_shb _ _ _ _ HEAP)
        | replace Dr with (Dr + 0) by lia; eapply acc_sub; [exact ACDR | clear; lia | clear - HDM; lia]
        | replace Dx with (Dx + 0) by lia; eapply acc_sub; [exact ACDX | clear; lia | clear - TDX HAL; unfold bn_dmax in *; lia]
        | unfold AW_sqr_words.aptrs2; split; [exact ALDR|]; split; [exact ALDX|]; split; [clear - OFDR HDM; lia | unfold SHHI, BnHeapA.ACEIL in *; clear - C2 CEIL; lia]
        | exact PDR | exact PDX | clear - IDR HDM; lia ]. }
    intros ms' PO. unfold AW_sqr_recursive.vl_post, W_mul_normal.vl_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MIc & RES & STc).
    subst ms'. rewrite ?EDr, ?ESP in *. unfold AW_sqr_closedA.CSQ4A in MUc.
    retpc 2298464.
    step.
    apply evt_done.
    eapply (sqr_finish1A 8 R Dr 0 112 (sqr_comba4 la) j0 j1 j2 j4 j5 ΣK lsK mK m4 OWK);
      [ exact ENV | exact LS | exact HR | exact SR | exact ARR
      | apply to_limbs_limbs | apply to_limbs_length | fold br; clear - HDM; lia | clear; lia | clear; lia | clear - LO'; lia
      | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros z Hz; clear - Hz; lia
      | exact WMc | exact MIc | exact STc | exact RES ].
  Qed.

  Lemma sqr_path_comba8A : forall (R X : Z) j0 j1 j2 j4 j5 ΣK lsK mK OWK
      (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x26 t3 t4 t5 t6 : word) F1 fc1,
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
    ref_at lsK OWK PL rr R -> ref_at lsK OWK PL rx X -> rx <> rr ->
    (8 <= bn_top (getbn rx lsK))%nat -> (16 <= bn_dmax (getbn rr lsK))%nat ->
    implA (BN_CTX_end ops (setbn rr (sqr_fin (bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0 (sqr_comba8 (firstn 8 (bn_buf (getbn rx lsK)))))) 16) lsK)) ΣK Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat 16)) x25 x26 (Z_to_bv 64 f) t3 t4 t5 t6)
          F1 (wz 0x2312a8) fc1 None mK (seg_rom bgbsegs)).
  Proof.
    intros until fc1. intros ENV LS HR HX NXR HAL HDM.
    pose proof (proj1 HPr : not_one rr) as NROr. change (not_one rx) in NROx.
    destruct (env_bounds _ _ _ _ _ _ ENV) as (ESP & ESPS & B1 & B2 & B3).
    pose proof LOFV as LO'.
    pose proof ENV as (OK & HEAP & ST & MI & _ & _ & _ & _ & FRc & _). unfold sfr in FRc. cbn [app] in FRc.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
    destruct (open_full ΣK OWK LB mK lsK PL EA SPv rr R HEAP LS FROK NOFR HR NROr ltac:(solve_nbuf)) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEPR).
    destruct (operand_view_ne ΣK OWK LB mK lsK PL EA SPv rr R Dr rx X 8 HEAP LS FROK NOFR HR NROr SR ARR HX NROx HAL NXR NBx)
      as (Dx & SX & LX & UX & ARX & X0 & XC & DX0 & DXC & XR & RDX & XDR & DRX).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & _).
    pose proof (st_wf_ok rx lsK WFS HVX NROx) as (LMX & TDX & DMX & _). unfold BG_DMAX in DMX.
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HR NROr) as (ACR & ALR & OFR).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HX NROx) as (ACX & ALX & OFX).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACDR & ALDR & OFDR).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARX) as (ACDX & ALDX & _).
    destruct (arr_posS _ _ _ _ _ HEAP ARR ltac:(clear - HDM; lia)) as (PDR & IDR).
    destruct (arr_posS _ _ _ _ _ HEAP ARX ltac:(clear - HAL TDX; lia)) as (PDX & _).
    set (br := getbn rr lsK) in *. set (bx := getbn rx lsK) in *. set (la := firstn 8 (bn_buf bx)) in *.
    assert (LLA : length la = 8%nat) by (unfold la; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in TDX; clear - TDX HAL; lia]).
    assert (LIA : limbs la) by (apply limbs_firstn; exact LMX).
    pose proof (proj1 (limbarr_limbs_at bgbsegs mK Dr (bn_buf br)) UR) as [_ HW]. fold (bn_dmax br) in HW.
    assert (EDr : bv_unsigned (Z_to_bv 64 Dr) = Dr) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - DR0 DRC CEIL LO' B2 B3; lia).
    assert (EDx : bv_unsigned (Z_to_bv 64 Dx) = Dx) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - DX0 DXC CEIL LO' B2 B3; lia).
    pose proof SR as SR'. unfold bn_cells, MallocRep.wz in SR'. unfold MallocRep.wz in SX.
    pose proof (munch_refl (@nil (Z * Z)) mK) as MU0.
    assert (OFF0 : offshW (@nil (Z * Z))) by exact I.
    unfold MallocRep.wz. apply implA_from_evt.
    ub. do 2 zstep. shl_with ACR ALR. chk0.
    do 2 zstep. shl_with ACX ALX. chk0.
    step. step. clear SR' SX.
    step.
    eapply evt_cut.
    { eapply AW_sqr_closedA.sqr_comba8_okA with (a := la) (lo := lo) (m := mK); rewrite ?EDr, ?EDx, ?ESP; unfold AW_sqr_closedA.CSQ8A;
        [ exact LIA | exact LLA | exact LX | replace Dr with (Dr + 0) by lia; eapply wr_at_sub; [exact HW| | |]; clear - HDM; lia
        | clear - DRX HDM TDX HAL; unfold bn_dmax in *; lia | exact ST | clear - LO'; lia
        | unfold BnHeapA.ACEIL in *; clear - DRC CEIL LO' HDM; lia | unfold BnHeapA.ACEIL in *; clear - DXC CEIL LO' TDX HAL; unfold bn_dmax in *; lia | exact MI
        | exact (AH_shb _ _ _ _ HEAP)
        | replace Dr with (Dr + 0) by lia; eapply acc_sub; [exact ACDR | clear; lia | clear - HDM; lia]
        | replace Dx with (Dx + 0) by lia; eapply acc_sub; [exact ACDX | clear; lia | clear - TDX HAL; unfold bn_dmax in *; lia]
        | unfold AW_sqr_words.aptrs2; split; [exact ALDR|]; split; [exact ALDX|]; split; [clear - OFDR HDM; lia | unfold SHHI, BnHeapA.ACEIL in *; clear - C2 CEIL; lia]
        | exact PDR | exact PDX | clear - IDR HDM; lia ]. }
    intros ms' PO. unfold AW_sqr_recursive.vl_post, W_mul_normal.vl_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MIc & RES & STc).
    subst ms'. rewrite ?EDr, ?ESP in *. unfold AW_sqr_closedA.CSQ8A in MUc.
    retpc 2298588.
    step.
    apply evt_done.
    eapply (sqr_finish1A 16 R Dr 0 352 (sqr_comba8 la) j0 j1 j2 j4 j5 ΣK lsK mK m4 OWK);
      [ exact ENV | exact LS | exact HR | exact SR | exact ARR
      | apply to_limbs_limbs | apply to_limbs_length | fold br; clear - HDM; lia | clear; lia | clear; lia | clear - LO'; lia
      | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros z Hz; clear - Hz; lia
      | exact WMc | exact MIc | exact STc | exact RES ].
  Qed.

  Lemma fr_shadow_cells : forall Σ OW m, AHEAP Σ OW LB m ->
    exists js0 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 js1,
      rw_cells bgbsegs m (shad f)
        [CB 4 js0; CB 1 b0; CB 1 b1; CB 1 b2; CB 1 b3; CB 1 b4; CB 1 b5; CB 1 b6; CB 1 b7; CB 1 b8; CB 1 b9; CB 1 b10; CB 1 b11; CB 1 b12; CB 1 b13; CB 1 b14; CB 1 b15;
         CB 1 b16; CB 1 b17; CB 1 b18; CB 1 b19; CB 1 b20; CB 1 b21; CB 1 b22; CB 1 b23; CB 1 b24; CB 1 b25; CB 1 b26; CB 1 b27; CB 1 b28; CB 1 b29; CB 1 b30; CB 1 b31; CB 28 js1].
  Proof using HF.
    intros Σ OW m HEAP.
    destruct (AH_fr_wr _ _ _ _ f 3%nat HEAP HF) as (_ & WS). change (fs_size 3) with 512 in WS.
    destruct (wr_at_rw_CB m (shad f) _ WS ltac:(clear; lia)) as (js & FRS). change (Z.to_nat (512 / 8)) with 64%nat in FRS.
    apply (rw_cells_split_CB bgbsegs _ _ [] 64 _ [] [4; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 28]%nat) in FRS; [| reflexivity].
    cbn [mk_CB_cells app] in FRS.
    do 34 eexists. exact FRS.
  Qed.

  Lemma sqr_path_stackA : forall (R X : Z) (al : nat) j0 j1 j2 j4 j5 ΣK lsK mK OWK
      (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x26 t3 t4 t5 t6 : word) F1 fc1,
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
    ref_at lsK OWK PL rr R -> ref_at lsK OWK PL rx X -> rx <> rr ->
    (1 <= al <= bn_top (getbn rx lsK))%nat -> (al < 16)%nat -> (2 * al <= bn_dmax (getbn rr lsK))%nat ->
    implA (BN_CTX_end ops (setbn rr (sqr_fin (bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0
                                    (fst (sqr_normal (firstn al (bn_buf (getbn rx lsK))) (firstn (2 * al) (bn_buf (getbn rr lsK))))))) (2 * al)) lsK)) ΣK Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat (2 * al))) (Z_to_bv 64 (Z.of_nat al)) x26 (Z_to_bv 64 f) t3 t4 t5 t6)
          F1 (wz 0x2312e8) fc1 None mK (seg_rom bgbsegs)).
  Proof.
    intros until fc1. intros ENV LS HR HX NXR [HAL1 HAL] HAL16 HDM.
    pose proof (proj1 HPr : not_one rr) as NROr. change (not_one rx) in NROx.
    destruct (env_bounds _ _ _ _ _ _ ENV) as (ESP & ESPS & B1 & B2 & B3).
    pose proof LOFV as LO'.
    pose proof ENV as (OK & HEAP & ST & MI & _ & _ & _ & _ & FRc & FSZ & _). unfold sfr in FRc. cbn [app] in FRc.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
    pose proof (AH_fr_geo _ _ _ _ f 3%nat HEAP HF) as GEO. pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 3) with 512 in *. unfold SEGTOP_A in G4.
    assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - G1 G3 C3; lia).
    assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
    assert (SHR : 2147450880 <= shad f /\ shad f + 64 <= 17594333495296).
    { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)).
      assert (f / 8 + 64 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 64); [apply Z.div_lt_upper_bound; unfold BnHeapA.ACEIL in *; clear - G1 G3 C3; lia | lia]). lia. }
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HR NROr) as (_ & ALR0 & _).
    destruct (open_ro ΣK OWK LB mK lsK PL EA SPv rr R HEAP LS FROK NOFR HR NROr) as (Dr00 & _ & _ & _ & R00 & RC00 & _).

    destruct (fr_shadow_cells _ _ _ HEAP) as (js0 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & b10 & b11 & b12 & b13 & b14 & b15 & b16 & b17 & b18 & b19
        & b20 & b21 & b22 & b23 & b24 & b25 & b26 & b27 & b28 & b29 & b30 & b31 & js1 & FRS).
    pose proof (munch_refl [(shad f, shad f + 64)]%Z mK) as MU. pose proof (wmono_refl bgbsegs mK) as WM.
    unfold MallocRep.wz. apply implA_from_evt.
    do 28 sbstep. ub1 ub_kind. do 4 sbstep. ub.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HW1 : Forall (w_frmix OWK LB lsK PL EA lo SPv [] f 3) [(shad f, shad f + 64)]).
    { constructor; [right; right; cbn [fst snd]; change (fs_size 3 / 8) with 64; clear; lia | constructor]. }
    destruct (cenv_frmixA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) _ _ _ _ m1 _ _ f 3%nat []
                ENV LS HF FRESH MU WM HW1 ltac:(assumption) ltac:(assumption) ltac:(unfold sfr; cbn [app]; exact FRc) FSZ) as (ENV1 & LS1).
    change (lib_state_hc false [] lsK m1 OWK PL EA) with (lib_state lsK m1 OWK PL EA) in LS1.
    lazymatch type of FRS with rw_cells _ _ _ (?c0 :: ?rest) =>
      pose proof (proj2 (proj1 (bk_rw_cells_app bgbsegs m1 (shad f) [c0] rest) FRS)) as FRS4;
      cbn [cells_size csize Nat.add] in FRS4; replace (shad f + Z.of_nat 4) with (shad f + 4) in FRS4 by (clear; lia)
    end.
    assert (ACT : acc bgbsegs m1 (f + 32) 256).
    { apply (acc_of_shadow_cells m1 (shad f + 4) _ 0%nat (f + 32) 256 FRS4); [clear - F8; Z.div_mod_to_equations; lia | clear - G1; lia | clear; lia
        | rewrite (shad_aligned_add f 32 F8) by (clear; lia); change (32 / 8) with 4; clear; lia | cbn; clear; lia | reflexivity]. }
    clear FRS FRS4 MU WM ENV LS HEAP ST MI FRc HW1.

    pose proof ENV1 as (_ & HEAP & ST & MI & _ & _ & _ & _ & FRc & _). unfold sfr in FRc. cbn [app] in FRc.
    destruct (AH_fr_wr _ _ _ _ f 3%nat HEAP HF) as (WF & _). change (fs_size 3) with 512 in WF.
    destruct (open_full ΣK OWK LB m1 lsK PL EA SPv rr R HEAP LS1 FROK NOFR HR NROr ltac:(solve_nbuf)) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEPR).
    destruct (operand_view_ne ΣK OWK LB m1 lsK PL EA SPv rr R Dr rx X al HEAP LS1 FROK NOFR HR NROr SR ARR HX NROx HAL NXR NBx)
      as (Dx & SX & LX & UX & ARX & X0 & XC & DX0 & DXC & XR & RDX & XDR & DRX).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS1 HX) as HVX. pose proof (lib_state_h_parts _ _ _ _ _ _ LS1) as PARTS. pose proof PARTS as (WFS & PWF & _).
    pose proof (st_wf_ok rx lsK WFS HVX NROx) as (LMX & TDX & DMX & _). unfold BG_DMAX in DMX.
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS1 NOFR HR NROr) as (ACR & ALR & OFR).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS1 NOFR HX NROx) as (ACX & ALX & OFX).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACDR & ALDR & OFDR).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARX) as (ACDX & ALDX & _).
    destruct (arr_posS _ _ _ _ _ HEAP ARR ltac:(clear - HDM HAL1; lia)) as (PDR & IDR).
    destruct (arr_posS _ _ _ _ _ HEAP ARX ltac:(clear - HAL HAL1 TDX; lia)) as (PDX & _).
    pose proof OKR as (LMR & _ & DMR & _). unfold BG_DMAX in DMR.
    pose proof (off_all _ _ _ HEAP) as OFA.
    assert (OFD : Dr + 8 * Z.of_nat (bn_dmax (getbn rr lsK)) <= f \/ f + 512 <= Dr).
    { unfold BnRepDefs.bn_arr in ARR. destruct (bn_d (getbn rr lsK)) as [pr|] eqn:Edr.
      - destruct ARR as [HinR _]. pose proof (OFA _ (in_or_app _ _ _ (or_introl HinR))) as O. unfold off_fr in O. cbn [blk_addr blk_size fst snd] in O. change (fs_size 3) with 512 in O. exact O.
      - exfalso. destruct ARR as [_ Eb]. unfold bn_dmax in HDM. rewrite Eb in HDM. cbn [length] in HDM. clear - HDM HAL1. lia. }
    assert (OFX2 : Dx + 8 * Z.of_nat (bn_dmax (getbn rx lsK)) <= f \/ f + 512 <= Dx).
    { unfold BnRepDefs.bn_arr in ARX. destruct (bn_d (getbn rx lsK)) as [px|] eqn:Edx.
      - destruct ARX as [HinX _]. pose proof (OFA _ (in_or_app _ _ _ (or_introl HinX))) as O. unfold off_fr in O. cbn [blk_addr blk_size fst snd] in O. change (fs_size 3) with 512 in O. exact O.
      - exfalso. destruct ARX as [_ Eb]. unfold bn_dmax in TDX. rewrite Eb in TDX. cbn [length] in TDX. clear - TDX HAL HAL1. lia. }
    set (br := getbn rr lsK) in *. set (bx := getbn rx lsK) in *. set (la := firstn al (bn_buf bx)) in *.
    assert (LLA : length la = al) by (unfold la; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in TDX; clear - TDX HAL; lia]).
    assert (LIA : limbs la) by (apply limbs_firstn; exact LMX).
    set (r0 := firstn (2 * al) (bn_buf br)).
    assert (LR0 : length r0 = (2 * al)%nat) by (unfold r0; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in HDM; exact HDM]).
    assert (LIR0 : limbs r0) by (apply limbs_firstn; exact LMR).
    pose proof (proj1 (limbarr_split bgbsegs m1 Dr (bn_buf br) (2 * al) ltac:(unfold bn_dmax in HDM; exact HDM)) UR) as [UR1 _].
    pose proof (proj1 (limbarr_limbs_at bgbsegs m1 Dr r0) UR1) as [RR0 WR0]. rewrite LR0 in WR0.
    assert (AL31 : 2 * Z.of_nat al < 2147483648) by (clear - HAL16; lia).
    assert (WT : wr_at bgbsegs m1 (f + 32) (8 * (2 * Z.of_nat al))).
    { eapply wr_at_sub; [exact WF | clear; lia | clear - HAL16; lia | clear - HAL16; lia]. }
    assert (EDr : bv_unsigned (Z_to_bv 64 Dr) = Dr) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - DR0 DRC CEIL LO' B2 B3; lia).
    assert (EDx : bv_unsigned (Z_to_bv 64 Dx) = Dx) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - DX0 DXC CEIL LO' B2 B3; lia).
    assert (EAL : bv_unsigned (Z_to_bv 64 (Z.of_nat al)) = Z.of_nat al) by (apply unsigned_lit; clear - AL31; lia).
    assert (EST : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - G1 G3 C3; lia).
    pose proof SR as SR'. unfold bn_cells, MallocRep.wz in SR'. unfold MallocRep.wz in SX.
    pose proof (munch_refl (@nil (Z * Z)) m1) as MU0.
    assert (OFF0 : offshW (@nil (Z * Z))) by exact I.
    do 2 zstep. shl_with ACR ALR. chk0.
    do 2 zstep. shl_with ACX ALX. chk0.
    step. step. clear SR' SX.
    zstep. rewrite ?Ef. zstep.
    step.
    eapply evt_cut.
    { eapply AW_sqr_normal.bn_sqr_normal_aspec with (A := la) (r0 := r0) (lo := lo) (m := m1); rewrite ?EDr, ?EDx, ?EST, ?ESP, ?EAL, ?LLA;
        [ exact LIA | exact LIR0 | exact LR0 | clear - HAL1; lia | exact AL31 | reflexivity | exact LX | exact RR0
        | replace (8 * (2 * Z.of_nat al)) with (8 * Z.of_nat (2 * al)) by (clear; lia); exact WR0
        | exact WT
        | clear - DRX HDM TDX HAL; unfold bn_dmax in *; lia
        | clear - OFD HDM HAL16; unfold br, bn_dmax in *; lia
        | clear - OFX2 TDX HAL HAL16; unfold bx, bn_dmax in *; lia
        | exact ST | clear - LO'; lia
        | unfold BnHeapA.ACEIL in *; clear - DRC CEIL LO' HDM; lia
        | unfold BnHeapA.ACEIL in *; clear - DXC CEIL LO' TDX HAL; unfold bn_dmax in *; lia
        | unfold BnHeapA.ACEIL in *; clear - G3 CEIL LO' HAL16; lia
        | exact MI | exact (AH_shb _ _ _ _ HEAP)
        | replace Dr with (Dr + 0) by (clear; lia); eapply acc_sub; [exact ACDR | clear; lia | clear - HDM; unfold br, bn_dmax in *; lia]
        | replace Dx with (Dx + 0) by (clear; lia); eapply acc_sub; [exact ACDX | clear; lia | clear - TDX HAL; unfold bx, bn_dmax in *; lia]
        | replace (f + 32) with (f + 32 + 0) by (clear; lia); eapply acc_sub; [exact ACT | clear; lia | clear - HAL16; lia]
        | unfold AW_sqr_normal.sqn_ptrs; split; [exact ALDR|]; split; [exact ALDX|]; split; [clear - F8; Z.div_mod_to_equations; lia|];
          split; [clear - OFDR HDM; unfold br, bn_dmax in *; lia|]; split; [unfold SHLO, SHHI; clear - G5 HAL16; lia|];
          split; [unfold SHHI, BnHeapA.ACEIL in *; clear - C2 CEIL; lia|]; split; [clear - IDR HDM; unfold br, bn_dmax in *; lia | clear - G4; lia]
        | intros _; split; [exact PDR | exact ALDR]
        | intros _; split; [exact PDX | exact ALDX]
        | intros _; split; [clear - G1; lia | clear - F8; Z.div_mod_to_equations; lia] ]. }
    intros ms' PO. unfold AW_sqr_normal.vl_post2, W_sqr_normal.vl_post2 in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MIc & RES & REST & STc).
    subst ms'. rewrite ?EDr, ?EST, ?ESP, ?LLA in *.
    retpc 2298788.
    pose proof (sqr_normal_spec la LIA r0 ltac:(rewrite LLA; exact HAL1) LIR0 ltac:(rewrite LLA; exact LR0)) as SNS.
    change (fst (sqr_normal (firstn al (bn_buf (getbn rx lsK))) (firstn (2 * al) (bn_buf (getbn rr lsK))))) with (fst (sqr_normal la r0)).
    destruct (sqr_normal la r0) as [ro to] eqn:ESN. destruct SNS as (LRO & LENRO & _ & ETO). cbn [fst] in RES |- *. rewrite LLA in LENRO.
    destruct (sqr_close1A (2 * al)%nat R Dr (8 * (2 * Z.of_nat al)) 288 ro j0 j1 j2 j4 j5 ΣK lsK m1 m4 OWK ENV1 LS1 HR SR ARR LRO LENRO
                ltac:(fold br; clear - HDM HAL1; lia) ltac:(clear - HAL16; lia) ltac:(clear; lia) ltac:(clear - LO'; lia)
                ltac:(eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros z Hz; clear - Hz; lia)
                WMc MIc STc RES) as (ENVN & LSN).
    fold br in ENVN, LSN. set (br' := bn_with_buf br (splice (bn_buf br) 0 ro)) in *.
    clear ENV1 LS1 HEAP ST MI FRc SR ARR UR UR1 RR0 WR0 LX UX ARX ACR ACX ACDR ACDX ACT WT WF MU0 MUc WMc RES REST.

    pose proof ENVN as (_ & HEAP & ST & MI & _ & _ & _ & _ & FRc & _). unfold sfr in FRc. cbn [app] in FRc.
    destruct (fr_shadow_cells _ _ _ HEAP) as (js0' & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & c14 & c15 & c16 & c17 & c18 & c19
        & c20 & c21 & c22 & c23 & c24 & c25 & c26 & c27 & c28 & c29 & c30 & c31 & js1' & FRS).
    pose proof (munch_refl [(shad f, shad f + 64)]%Z m4) as MU. pose proof (wmono_refl bgbsegs m4) as WM.
    zstep.
    do 32 sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    assert (HW3 : Forall (w_frmix OWK LB (setbn rr br' lsK) PL EA lo SPv [] f 3) [(shad f, shad f + 64)]).
    { constructor; [right; right; cbn [fst snd]; change (fs_size 3 / 8) with 64; clear; lia | constructor]. }
    destruct (cenv_frmixA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) _ _ _ _ m5 _ _ f 3%nat []
                ENVN LSN HF FRESH MU WM HW3 ltac:(assumption) ltac:(assumption) ltac:(unfold sfr; cbn [app]; exact FRc) FSZ) as (ENV5 & LS5).
    change (lib_state_hc false [] (setbn rr br' lsK) m5 OWK PL EA) with (lib_state (setbn rr br' lsK) m5 OWK PL EA) in LS5.
    step.
    apply evt_done.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSN HR) as HVR'.
    assert (HVR : vref rr lsK) by (revert HVR'; unfold vref; rewrite ?length_setbn; exact (fun H => H)).
    replace (setbn rr (sqr_fin br' (2 * al)) lsK) with (setbn rr (sqr_fin (getbn rr (setbn rr br' lsK)) (2 * al)) (setbn rr br' lsK))
      by (rewrite getbn_setbn_same by exact HVR; apply setbn_setbn_same).
    eapply sqr_tailA; [exact ENV5 | exact LS5 | apply ref_at_setbn; exact HR |].
    rewrite getbn_setbn_same by exact HVR. unfold br', bn_with_buf, bn_dmax. cbn [bn_buf].
    rewrite splice_length; [exact HDM | rewrite LENRO; exact HDM].
  Qed.

  Lemma arr_splice_agree : forall (P : Z -> Prop) (m mc : mem) D (buf w : list Z),
    u64arr bgbsegs m D (wlimbs buf) -> agree_on P m mc -> (length w <= length buf)%nat ->
    (forall a, D + 8 * Z.of_nat (length w) <= a < D + 8 * Z.of_nat (length buf) -> P a) ->
    limbs_at bgbsegs mc D w -> wr_at bgbsegs mc D (8 * Z.of_nat (length buf)) ->
    u64arr bgbsegs mc D (wlimbs (splice buf 0 w)).
  Proof using.
    intros P m mc D buf w U AG HL HP HW WR.
    apply (proj1 (limbarr_split bgbsegs m D buf (length w) HL)) in U. destruct U as [_ Uhi].
    eapply (u64arr_agree _ _ _ _ _ AG) in Uhi; [| intros a Ha; rewrite wlimbs_len, length_skipn in Ha; apply HP; clear - Ha HL; lia].
    unfold splice. rewrite firstn_O. cbn [app Nat.add]. apply limbarr_app. split; [| exact Uhi].
    apply limbarr_limbs_at. split; [exact HW|].
    rewrite <- (Z.add_0_r D) at 1. eapply wr_at_sub; [exact WR | clear; lia | clear; lia | clear - HL; lia].
  Qed.

  Lemma sqr_close2R : forall (max : nat) (t : bnref) (R TT Dr Dt : Z) (w tw : list Z) j0 j1 j2 j4 j5 ΣK lsK mK mc OWK,
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
    ref_at lsK OWK PL rr R -> ref_at lsK OWK PL t TT -> t <> rr -> hpl PL t ->
    rw_cells bgbsegs mK R (bn_cells Dr (getbn rr lsK)) -> BnRepDefs.bn_arr mK OWK Dr (getbn rr lsK) ->
    rw_cells bgbsegs mK TT (bn_cells Dt (getbn t lsK)) -> BnRepDefs.bn_arr mK OWK Dt (getbn t lsK) ->
    limbs w -> length w = max -> (0 < max <= bn_dmax (getbn rr lsK))%nat ->
    limbs tw -> (0 < length tw <= bn_dmax (getbn t lsK))%nat ->
    AHEAP ΣK OWK LB mc ->
    agree_on (fun a => aclient_addr (OWK ++ LB) FB a /\ ~ (Dr <= a < Dr + 8 * Z.of_nat max) /\ ~ (Dt <= a < Dt + 8 * Z.of_nat (length tw))) mK mc ->
    limbs_at bgbsegs mc Dr w -> limbs_at bgbsegs mc Dt tw -> mem_inv bgbsegs mc -> stk bgbsegs mc lo FB ->
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK
         (setbn rr (bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0 w)) (setbn t (bn_with_buf (getbn t lsK) (splice (bn_buf (getbn t lsK)) 0 tw)) lsK)) mc OWK
    /\ lib_state (setbn rr (bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0 w)) (setbn t (bn_with_buf (getbn t lsK) (splice (bn_buf (getbn t lsK)) 0 tw)) lsK)) mc OWK PL EA.
  Proof.
    intros until OWK. intros ENV LS HR HT NTR HPt SR ARR STT ARRT LW ELW [HW0 HWD] LTW [HT0 HTD] HEAPc AGc HRO HTO MIc STc.
    pose proof (proj1 HPt : not_one t) as NROt. pose proof (proj1 HPr : not_one rr) as NROr.
    pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FRc & FSZ & UW). unfold sfr in FRc. cbn [app] in FRc.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_open [] lsK mK OWK PL EA rr R LS ND HR ltac:(intros []) NROr) as (_ & OKR & LSH1).
    destruct (lib_state_open [rr] lsK mK OWK PL EA t TT LSH1 ND HT ltac:(intros [E|[]]; apply NTR; symmetry; exact E) NROt) as (_ & OKT & LSH2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HT) as HVT.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
    destruct (bn_arr_facts_w lsK OWK PL EA SPv USTACK_TOP ΣK LB mK rr Dr HEAP PARTS FROK HVR (hpl_wref PL rr HPr)
                ltac:(first [exact ARR | exact (bn_arr_of_nofr PL rr _ _ _ _ PWF NOFR NROr ARR ltac:(solve_nbuf))])) as (U & _ & D0 & DC & _ & DSEP).
    destruct (bn_arr_facts_w lsK OWK PL EA SPv USTACK_TOP ΣK LB mK t Dt HEAP PARTS FROK HVT (hpl_wref PL t HPt)
                ltac:(first [exact ARRT | exact (bn_arr_of_nofr PL t _ _ _ _ PWF NOFR NROt ARRT ltac:(solve_nbuf))])) as (UT & _ & DT0 & DTC & _ & DSEPT).
    pose proof (DSEP rr R HR) as DSR. pose proof (DSEP t TT HT) as DSRT. pose proof (DSEPT rr R HR) as DSTR. pose proof (DSEPT t TT HT) as DSTT.
    pose proof (struct_disj ΣK OWK LB mK HEAP lsK PL EA SPv USTACK_TOP PARTS FROK t rr TT R NTR HT HR) as SDT.
    pose proof (bn_arrs_disj ΣK OWK LB mK lsK PL EA rr t R TT Dr Dt HEAP LS ltac:(congruence) HR HT ARR ARRT) as ADJ.
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HR NROr) as (qs & As & ns & Hins & Ra1 & Ra2).
    pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hins) as (SA0 & _ & _ & SAC & SAI).
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HT NROt) as (qt & At & nt & Hint & Rt1 & Rt2).
    pose proof (AH_range_in _ _ _ _ _ _ _ HEAP Hint) as (TA0 & _ & _ & TAC & TAI).
    set (br := getbn rr lsK) in *. set (tb := getbn t lsK) in *.
    assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity. assert (LBT : length (bn_buf tb) = bn_dmax tb) by reflexivity.
    unfold BnRepDefs.bn_arr, bn_arr in ARR. destruct (bn_d br) as [pr|] eqn:Edr.
    2:{ exfalso. destruct ARR as [_ Eb]. rewrite Eb in LBR. cbn [length] in LBR. clear - LBR HW0 HWD. lia. }
    destruct ARR as [HinR _].
    unfold BnRepDefs.bn_arr, bn_arr in ARRT. destruct (bn_d tb) as [pt|] eqn:Edt.
    2:{ exfalso. destruct ARRT as [_ Eb]. rewrite Eb in LBT. cbn [length] in LBT. clear - LBT HT0 HTD. lia. }
    destruct ARRT as [HinT _].
    assert (INR : In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) (OWK ++ LB)) by (apply in_or_app; left; exact HinR).
    assert (INT : In (pt, Dt, 8 * Z.of_nat (bn_dmax tb)) (OWK ++ LB)) by (apply in_or_app; left; exact HinT).
    pose proof (W_mulA2F.cenv_icall2A LB PL lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ _
                  Dr (8 * Z.of_nat max) (pr, Dr, 8 * Z.of_nat (bn_dmax br)) Dt (8 * Z.of_nat (length tw)) (pt, Dt, 8 * Z.of_nat (bn_dmax tb))
                  ENV HinR ltac:(cbn [blk_addr blk_size fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear - HWD; lia)
                  HinT ltac:(cbn [blk_addr blk_size fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear - HTD; lia) HEAPc STc MIc AGc) as ENVc.
    assert (LSHc : lib_state_h [t; rr] lsK mc OWK PL EA).
    { eapply (lib_state_h_icall2 ΣK LB [t; rr] lsK mK mc OWK PL EA FB SPv Dr (8 * Z.of_nat max) Dt (8 * Z.of_nat (length tw)) HEAP LSH2 FROK ltac:(clear - FBSP; lia) AGc).
      - eapply (w_limbs OWK LB lsK PL EA SPv false [t; rr] _ rr pr Dr); [right; left; reflexivity | exact HVR | exact Edr | exact HinR | cbn [fst snd]; clear; lia | cbn [fst snd]; fold br; clear - HWD; lia].
      - eapply (w_limbs OWK LB lsK PL EA SPv false [t; rr] _ t pt Dt); [left; reflexivity | exact HVT | exact Edt | exact HinT | cbn [fst snd]; clear; lia | cbn [fst snd]; fold tb; clear - HTD; lia]. }
    assert (STTc : rw_cells bgbsegs mc TT (bn_cells Dt tb)).
    { eapply (rw_cells_agree _ _ _ _ _ AGc); [exact STT|]. intros a Ha. unfold bn_cells in Ha. cbn [cells_size csize Nat.add] in Ha. split;
        [right; right; exists (qt, At, nt); split; [exact Hint | cbn [blk_addr blk_size fst snd]; clear - Ha Rt1 Rt2; lia] | clear - Ha DSRT DSTT HWD HTD; lia]. }
    assert (SRc : rw_cells bgbsegs mc R (bn_cells Dr br)).
    { eapply (rw_cells_agree _ _ _ _ _ AGc); [exact SR|]. intros a Ha. unfold bn_cells in Ha. cbn [cells_size csize Nat.add] in Ha. split;
        [right; right; exists (qs, As, ns); split; [exact Hins | cbn [blk_addr blk_size fst snd]; clear - Ha Ra1 Ra2; lia] | clear - Ha DSR DSTR HWD HTD; lia]. }
    destruct (AH_acc _ _ _ _ _ HEAPc INT) as [WRT _]. destruct (AH_acc _ _ _ _ _ HEAPc INR) as [WRR _]. cbn [blk_addr blk_size fst snd] in WRT, WRR.
    assert (UTc : u64arr bgbsegs mc Dt (wlimbs (splice (bn_buf tb) 0 tw))).
    { eapply (arr_splice_agree _ mK mc Dt (bn_buf tb) tw UT AGc); [rewrite LBT; clear - HTD; lia | | exact HTO | rewrite LBT; exact WRT].
      intros a Ha. rewrite LBT in Ha. split; [right; right; exists (pt, Dt, 8 * Z.of_nat (bn_dmax tb)); split; [exact INT | cbn [blk_addr blk_size fst snd]; clear - Ha; lia]|].
      clear - Ha ADJ HWD. lia. }
    assert (URc : u64arr bgbsegs mc Dr (wlimbs (splice (bn_buf br) 0 w))).
    { eapply (arr_splice_agree _ mK mc Dr (bn_buf br) w U AGc); [rewrite LBR, ELW; clear - HWD; lia | | exact HRO | rewrite LBR; exact WRR].
      intros a Ha. rewrite LBR, ELW in Ha. split; [right; right; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); split; [exact INR | cbn [blk_addr blk_size fst snd]; clear - Ha; lia]|].
      clear - Ha ADJ HTD. lia. }

    assert (LST : length (splice (bn_buf tb) 0 tw) = bn_dmax tb) by (apply splice_length; rewrite LBT; clear - HTD; lia).
    set (tb' := bn_with_buf tb (splice (bn_buf tb) 0 tw)).
    assert (LSH1' : lib_state_h [rr] (setbn t tb' lsK) mc OWK PL EA).
    { eapply (lib_state_close [rr] lsK mc OWK PL EA t TT); [exact LSHc | exact ND| exact HT| exact NROt| | |].
      - exists Dt. split.
        + unfold tb', bn_cells, bn_with_buf, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. rewrite LST. exact STTc.
        + unfold BnRepDefs.bn_arr, bn_arr, tb', bn_with_buf. cbn [bn_d]. rewrite Edt. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LST. split; [exact HinT | exact UTc].
      - destruct OKT as (O1 & O2 & O3 & O4). unfold bg_ok, tb', bn_with_buf, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. rewrite LST.
        split; [apply splice_limbs; [exact O1 | exact LTW]|]. auto.
      - apply ids_ok_setbn_same; [exact IDS | exact HVT |]. unfold bn_blocks, tb', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite LST. reflexivity. }

    assert (LSP : length (splice (bn_buf br) 0 w) = bn_dmax br) by (apply splice_length; rewrite LBR, ELW; clear - HWD; lia).
    set (lsT := setbn t tb' lsK) in *.
    assert (EGR : getbn rr lsT = br) by (unfold lsT; apply getbn_setbn_other; exact NTR).
    assert (HR' : ref_at lsT OWK PL rr R) by (apply ref_at_setbn; exact HR).
    pose proof (W_div_tailAF.vref_setbn rr t tb' lsK HVR) as HVR'. fold lsT in HVR'.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LSH1') as (_ & _ & IDS' & _).
    set (br' := bn_with_buf br (splice (bn_buf br) 0 w)).
    assert (LSN : lib_state (setbn rr br' lsT) mc OWK PL EA).
    { unfold lib_state. eapply (lib_state_close [] lsT mc OWK PL EA rr R); [exact LSH1' | exact ND| exact HR'| exact NROr| | |].
      - exists Dr. split; [unfold br', bn_cells, bn_with_buf, bn_dmax; cbn [bn_top bn_buf bn_neg bn_flags]; rewrite LSP; exact SRc|].
        unfold BnRepDefs.bn_arr, bn_arr, br', bn_with_buf. cbn [bn_d]. rewrite Edr. unfold bn_dmax at 1. cbn [bn_buf]. rewrite LSP. split; [exact HinR | exact URc].
      - destruct OKR as (O1 & O2 & O3 & O4). unfold bg_ok, br', bn_with_buf, bn_dmax in *. cbn [bn_top bn_buf bn_flags]. rewrite LSP.
        split; [apply splice_limbs; [exact O1 | exact LW]|]. auto.
      - apply ids_ok_setbn_same; [exact IDS' | exact HVR' |]. rewrite EGR. unfold bn_blocks, br', bn_with_buf, bn_dmax. cbn [bn_d bn_buf]. rewrite LSP. reflexivity. }
    split; [| exact LSN].
    apply cenv_setbnA; [| exact HVR' | rewrite EGR; unfold br', bn_with_buf, bn_blocks; cbn [bn_d bn_buf bn_dmax bn_top]; rewrite ?Edr; reflexivity].
    apply cenv_setbnA; [exact ENVc | exact HVT |]. fold tb. unfold tb', bn_with_buf, bn_blocks. cbn [bn_d bn_buf bn_dmax bn_top]. rewrite ?Edt. reflexivity.
  Qed.

  Lemma sqr_finish2A : forall (max : nat) (t : bnref) (R TT Dr Dt : Z) (w tw : list Z) j0 j1 j2 j4 j5 ΣK lsK mK mc OWK
      (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x25 x26 t3 t4 t5 t6 : word) F1 fc1,
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
    ref_at lsK OWK PL rr R -> ref_at lsK OWK PL t TT -> t <> rr -> hpl PL t ->
    rw_cells bgbsegs mK R (bn_cells Dr (getbn rr lsK)) -> BnRepDefs.bn_arr mK OWK Dr (getbn rr lsK) ->
    rw_cells bgbsegs mK TT (bn_cells Dt (getbn t lsK)) -> BnRepDefs.bn_arr mK OWK Dt (getbn t lsK) ->
    limbs w -> length w = max -> (0 < max <= bn_dmax (getbn rr lsK))%nat ->
    limbs tw -> (0 < length tw <= bn_dmax (getbn t lsK))%nat ->
    AHEAP ΣK OWK LB mc ->
    agree_on (fun a => aclient_addr (OWK ++ LB) FB a /\ ~ (Dr <= a < Dr + 8 * Z.of_nat max) /\ ~ (Dt <= a < Dt + 8 * Z.of_nat (length tw))) mK mc ->
    limbs_at bgbsegs mc Dr w -> limbs_at bgbsegs mc Dt tw -> mem_inv bgbsegs mc -> stk bgbsegs mc lo FB ->
    implA (BN_CTX_end ops (setbn rr (sqr_fin (bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0 w)) max)
                                 (setbn t (bn_with_buf (getbn t lsK) (splice (bn_buf (getbn t lsK)) 0 tw)) lsK))) ΣK Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 R) x22 (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat max)) x25 x26 (Z_to_bv 64 f) t3 t4 t5 t6)
          F1 (wz 0x23152c) fc1 None mc (seg_rom bgbsegs)).
  Proof.
    intros until fc1. intros ENV LS HR HT NTR HPt SR ARR STT ARRT LW ELW HWB LTW HTB HEAPc AGc HRO HTO MIc STc.
    destruct (sqr_close2R max t R TT Dr Dt w tw j0 j1 j2 j4 j5 ΣK lsK mK mc OWK ENV LS HR HT NTR HPt SR ARR STT ARRT LW ELW HWB LTW HTB HEAPc AGc HRO HTO MIc STc) as (ENVN & LSN).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HR) as HVR.
    set (lsT := setbn t (bn_with_buf (getbn t lsK) (splice (bn_buf (getbn t lsK)) 0 tw)) lsK) in *.
    pose proof (W_div_tailAF.vref_setbn rr t (bn_with_buf (getbn t lsK) (splice (bn_buf (getbn t lsK)) 0 tw)) lsK HVR) as HVR'. fold lsT in HVR'.
    set (br' := bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0 w)) in *.
    replace (setbn rr (sqr_fin br' max) lsT) with (setbn rr (sqr_fin (getbn rr (setbn rr br' lsT)) max) (setbn rr br' lsT))
      by (rewrite getbn_setbn_same by exact HVR'; apply setbn_setbn_same).
    eapply sqr_tailA; [exact ENVN | exact LSN | apply ref_at_setbn; apply ref_at_setbn; exact HR |].
    rewrite getbn_setbn_same by exact HVR'. unfold br', bn_with_buf, bn_dmax. cbn [bn_buf].
    rewrite splice_length; [exact (proj2 HWB) | rewrite ELW; exact (proj2 HWB)].
  Qed.

  Lemma munch2_agree : forall Σ OW (m m' : mem) D1 n1 D2 n2 CST,
    AHEAP Σ OW LB m -> ACEIL <= lo -> 0 <= CST -> lo <= FB - CST ->
    munch [(D1, D1 + n1); (D2, D2 + n2); (FB - CST, FB)] m m' ->
    agree_on (fun a => aclient_addr (OW ++ LB) FB a /\ ~ (D1 <= a < D1 + n1) /\ ~ (D2 <= a < D2 + n2)) m m'.
  Proof using.
    intros Σ OW m m' D1 n1 D2 n2 CST HEAP CEIL HC LOC MU.
    eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a (HA & N1 & N2). cbn [outside].
    split; [exact N1|]. split; [exact N2|]. split; [| exact I].
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A in C1.
    destruct HA as [HA|[HA|(b & Hb & Hr)]].
    - clear - HA. lia.
    - destruct HA as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
      clear - Hin Hr C1 CEIL LOC HC. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). clear - BC Hr CEIL LOC HC. lia.
  Qed.

  Lemma sqr_path_ntmpA : forall (t : bnref) (R X TT : Z) (al : nat) j0 j1 j2 j4 j5 ΣK lsK mK OWK
      (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F1 fc1,
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
    ref_at lsK OWK PL rr R -> ref_at lsK OWK PL rx X -> rx <> rr ->
    ref_at lsK OWK PL t TT -> hpl PL t -> t <> rr -> rx <> t ->
    (1 <= al <= bn_top (getbn rx lsK))%nat -> (2 * al <= bn_dmax (getbn rr lsK))%nat -> (2 * al <= bn_dmax (getbn t lsK))%nat ->
    implA (BN_CTX_end ops
              (setbn rr (sqr_fin (bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0
                                    (fst (sqr_normal (firstn al (bn_buf (getbn rx lsK))) (firstn (2 * al) (bn_buf (getbn rr lsK))))))) (2 * al))
                 (setbn t (bn_with_buf (getbn t lsK) (splice (bn_buf (getbn t lsK)) 0 (sqr_words (firstn al (bn_buf (getbn rx lsK)))))) lsK))) ΣK Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat (2 * al))) (Z_to_bv 64 (Z.of_nat al)) (Z_to_bv 64 TT) (Z_to_bv 64 f) t3 t4 t5 t6)
          F1 (wz 0x2314dc) fc1 None mK (seg_rom bgbsegs)).
  Proof.
    intros until fc1. intros ENV LS HR HX NXR HT HPt NTR NXT [HAL1 HAL] HDM HDT.
    pose proof (proj1 HPr : not_one rr) as NROr. change (not_one rx) in NROx. pose proof (proj1 HPt : not_one t) as NROt.
    destruct (env_bounds _ _ _ _ _ _ ENV) as (ESP & ESPS & B1 & B2 & B3).
    pose proof LOFV as LO'.
    pose proof ENV as (OK & HEAP & ST & MI & _ & _ & _ & _ & FRc & FSZ & _). unfold sfr in FRc. cbn [app] in FRc.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
    destruct (open_full ΣK OWK LB mK lsK PL EA SPv rr R HEAP LS FROK NOFR HR NROr ltac:(solve_nbuf)) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEPR).
    destruct (open_full ΣK OWK LB mK lsK PL EA SPv t TT HEAP LS FROK NOFR HT NROt ltac:(solve_nbuf)) as (Dt & STT & ARRT & OKT & UT & T0 & TC & DT0 & DTC & DSEPT).
    destruct (operand_view_ne ΣK OWK LB mK lsK PL EA SPv rr R Dr rx X al HEAP LS FROK NOFR HR NROr SR ARR HX NROx HAL NXR NBx)
      as (Dx & SX & LX & UX & ARX & X0 & XC & DX0 & DXC & XR & RDX & XDR & DRX).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & _).
    pose proof (st_wf_ok rx lsK WFS HVX NROx) as (LMX & TDX & DMX & _). unfold BG_DMAX in DMX.
    pose proof OKR as (LMR & _ & DMR & _). unfold BG_DMAX in DMR. pose proof OKT as (LMT & _ & DMT & _). unfold BG_DMAX in DMT.
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HR NROr) as (ACR & ALR & OFR).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HX NROx) as (ACX & ALX & OFX).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HT NROt) as (ACT & ALT & OFT).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACDR & ALDR & OFDR).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARX) as (ACDX & ALDX & _).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARRT) as (ACDT & ALDT & OFDT).
    destruct (arr_posS _ _ _ _ _ HEAP ARR ltac:(clear - HDM HAL1; lia)) as (PDR & IDR).
    destruct (arr_posS _ _ _ _ _ HEAP ARX ltac:(clear - HAL HAL1 TDX; lia)) as (PDX & _).
    destruct (arr_posS _ _ _ _ _ HEAP ARRT ltac:(clear - HDT HAL1; lia)) as (PDT & IDT).
    pose proof (bn_arrs_disj ΣK OWK LB mK lsK PL EA rr t R TT Dr Dt HEAP LS ltac:(congruence) HR HT ARR ARRT) as DRT.
    pose proof (bn_arrs_disj ΣK OWK LB mK lsK PL EA t rx TT X Dt Dx HEAP LS ltac:(congruence) HT HX ARRT ARX) as DTX.
    set (br := getbn rr lsK) in *. set (bx := getbn rx lsK) in *. set (tb := getbn t lsK) in *. set (la := firstn al (bn_buf bx)) in *.
    assert (AL512 : Z.of_nat al <= 512) by (clear - HAL TDX DMX; unfold bn_dmax in *; lia).
    assert (LLA : length la = al) by (unfold la; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in TDX; clear - TDX HAL; lia]).
    assert (LIA : limbs la) by (apply limbs_firstn; exact LMX).
    set (r0 := firstn (2 * al) (bn_buf br)).
    assert (LR0 : length r0 = (2 * al)%nat) by (unfold r0; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in HDM; exact HDM]).
    assert (LIR0 : limbs r0) by (apply limbs_firstn; exact LMR).
    pose proof (proj1 (limbarr_split bgbsegs mK Dr (bn_buf br) (2 * al) ltac:(unfold bn_dmax in HDM; exact HDM)) UR) as [UR1 _].
    pose proof (proj1 (limbarr_limbs_at bgbsegs mK Dr r0) UR1) as [RR0 WR0]. rewrite LR0 in WR0.
    pose proof (proj1 (limbarr_limbs_at bgbsegs mK Dt (bn_buf tb)) UT) as [_ WT0]. fold (bn_dmax tb) in WT0.
    assert (AL31 : 2 * Z.of_nat al < 2147483648) by (clear - AL512; lia).
    assert (EDr : bv_unsigned (Z_to_bv 64 Dr) = Dr) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - DR0 DRC CEIL LO' B2 B3; lia).
    assert (EDx : bv_unsigned (Z_to_bv 64 Dx) = Dx) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - DX0 DXC CEIL LO' B2 B3; lia).
    assert (EDt : bv_unsigned (Z_to_bv 64 Dt) = Dt) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - DT0 DTC CEIL LO' B2 B3; lia).
    assert (EAL : bv_unsigned (Z_to_bv 64 (Z.of_nat al)) = Z.of_nat al) by (apply unsigned_lit; clear - AL31; lia).
    pose proof SR as SR'. pose proof STT as STT'. unfold bn_cells, MallocRep.wz in SR', STT'. unfold MallocRep.wz in SX.
    pose proof (munch_refl (@nil (Z * Z)) mK) as MU0.
    assert (OFF0 : offshW (@nil (Z * Z))) by exact I.
    unfold MallocRep.wz. apply implA_from_evt.
    ub1 ub_kind. ub1 ub_kind. setreg 10%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7; apply mod8_lor; assumption). ub.
    do 2 zstep. shl_with ACX ALX. chk0.
    do 2 zstep. shl_with ACR ALR. chk0.
    do 2 zstep. shl_with ACT ALT. chk0.
    step. step. step. clear SR' SX STT'.
    zstep.
    step.
    eapply evt_cut.
    { eapply AW_sqr_normal.bn_sqr_normal_aspec with (A := la) (r0 := r0) (lo := lo) (m := mK); rewrite ?EDr, ?EDx, ?EDt, ?ESP, ?EAL, ?LLA;
        [ exact LIA | exact LIR0 | exact LR0 | clear - HAL1; lia | exact AL31 | reflexivity | exact LX | exact RR0
        | replace (8 * (2 * Z.of_nat al)) with (8 * Z.of_nat (2 * al)) by (clear; lia); exact WR0
        | replace Dt with (Dt + 0) by (clear; lia); eapply wr_at_sub; [exact WT0 | clear; lia | clear; lia | clear - HDT; lia]
        | clear - DRX HDM TDX HAL; unfold bn_dmax in *; lia
        | clear - DRT HDM HDT; unfold br, tb, bn_dmax in *; lia
        | clear - DTX TDX HAL HDT; unfold bx, tb, bn_dmax in *; lia
        | exact ST | clear - LO'; lia
        | unfold BnHeapA.ACEIL in *; clear - DRC CEIL LO' HDM; lia
        | unfold BnHeapA.ACEIL in *; clear - DXC CEIL LO' TDX HAL; unfold bn_dmax in *; lia
        | unfold BnHeapA.ACEIL in *; clear - DTC CEIL LO' HDT; lia
        | exact MI | exact (AH_shb _ _ _ _ HEAP)
        | replace Dr with (Dr + 0) by (clear; lia); eapply acc_sub; [exact ACDR | clear; lia | clear - HDM; unfold br, bn_dmax in *; lia]
        | replace Dx with (Dx + 0) by (clear; lia); eapply acc_sub; [exact ACDX | clear; lia | clear - TDX HAL; unfold bx, bn_dmax in *; lia]
        | replace Dt with (Dt + 0) by (clear; lia); eapply acc_sub; [exact ACDT | clear; lia | clear - HDT; unfold tb, bn_dmax in *; lia]
        | unfold AW_sqr_normal.sqn_ptrs; split; [exact ALDR|]; split; [exact ALDX|]; split; [exact ALDT|];
          split; [clear - OFDR HDM; unfold br, bn_dmax in *; lia|]; split; [clear - OFDT HDT; unfold tb, bn_dmax in *; lia|];
          split; [unfold SHHI, BnHeapA.ACEIL in *; clear - C2 CEIL; lia|]; split; [clear - IDR HDM; unfold br, bn_dmax in *; lia | clear - IDT HDT; unfold tb, bn_dmax in *; lia]
        | intros _; split; [exact PDR | exact ALDR]
        | intros _; split; [exact PDX | exact ALDX]
        | intros _; split; [exact PDT | exact ALDT] ]. }
    intros ms' PO. unfold AW_sqr_normal.vl_post2, W_sqr_normal.vl_post2 in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MIc & RES & REST & STc).
    subst ms'. rewrite ?EDr, ?EDt, ?ESP, ?LLA in *.
    retpc 2299180.
    pose proof (sqr_normal_spec la LIA r0 ltac:(rewrite LLA; exact HAL1) LIR0 ltac:(rewrite LLA; exact LR0)) as SNS.
    change (fst (sqr_normal (firstn al (bn_buf (getbn rx lsK))) (firstn (2 * al) (bn_buf (getbn rr lsK))))) with (fst (sqr_normal la r0)).
    destruct (sqr_normal la r0) as [ro to] eqn:ESN. destruct SNS as (LRO & LENRO & _ & ETO). cbn [fst] in RES |- *. rewrite LLA in LENRO.
    assert (LSW : length (sqr_words la) = (2 * al)%nat) by (rewrite W_sqr_words.sqr_words_length, LLA; reflexivity).
    apply evt_done.
    assert (EM : Z.of_nat (2 * al) = 2 * Z.of_nat al) by (clear; lia).
    eapply (sqr_finish2A (2 * al)%nat t R TT Dr Dt ro (sqr_words la) j0 j1 j2 j4 j5 ΣK lsK mK m4 OWK);
      [ exact ENV | exact LS | exact HR | exact HT | exact NTR | exact HPt | exact SR | exact ARR | exact STT | exact ARRT
      | exact LRO | exact LENRO | fold br; clear - HDM HAL1; lia
      | apply W_sqr_words.sqr_words_limbs; exact LIA | rewrite LSW; fold tb; clear - HDT HAL1; lia
      | | | exact RES | exact REST | exact MIc | exact STc ].
    -
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS'.
      eapply (seg_heap ΣK lsK OWK LB PL EA SPv mK m4 _ lo FB HEAP PARTS' FROK MUc WMc); [| exact CEIL | unfold USTACK_TOP; clear - B2 B3; lia].
      unfold BnRepDefs.bn_arr in ARR, ARRT.
      destruct (bn_d br) as [pr|] eqn:Edr; [| exfalso; destruct ARR as [_ Eb]; unfold bn_dmax in HDM; rewrite Eb in HDM; cbn [length] in HDM; clear - HDM HAL1; lia].
      destruct (bn_d tb) as [pt|] eqn:Edt; [| exfalso; destruct ARRT as [_ Eb]; unfold bn_dmax in HDT; rewrite Eb in HDT; cbn [length] in HDT; clear - HDT HAL1; lia].
      destruct ARR as [HinR _]. destruct ARRT as [HinT _].
      constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact HinR | clear - HDM; lia]|].
      constructor; [right; left; exists (pt, Dt, 8 * Z.of_nat (bn_dmax tb)); cbn [blk_addr blk_size fst snd]; split; [exact HinT | clear - HDT; lia]|].
      constructor; [left; cbn [fst snd]; clear - LO'; lia | constructor].
    - rewrite LSW, EM. eapply (munch2_agree ΣK OWK mK m4 Dr (8 * (2 * Z.of_nat al)) Dt (8 * (2 * Z.of_nat al)) 288 HEAP CEIL ltac:(clear; lia) ltac:(clear - LO'; lia)).
      exact MUc.
  Qed.

  Lemma sqr_path_recA : forall (t : bnref) (R X TT : Z) (k : nat) j0 j1 j2 j4 j5 ΣK lsK mK OWK
      (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F1 fc1,
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) TOTAL ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
    ref_at lsK OWK PL rr R -> ref_at lsK OWK PL rx X -> rx <> rr ->
    ref_at lsK OWK PL t TT -> hpl PL t -> t <> rr -> rx <> t ->
    (k <= 9)%nat -> (Nat.pow 2 k <= bn_top (getbn rx lsK))%nat -> (2 * Nat.pow 2 k <= bn_dmax (getbn rr lsK))%nat -> (sqr_scratch k <= bn_dmax (getbn t lsK))%nat ->
    implA (BN_CTX_end ops
              (setbn rr (sqr_fin (bn_with_buf (getbn rr lsK) (splice (bn_buf (getbn rr lsK)) 0
                                    (fst (sqr_recursive k (firstn (Nat.pow 2 k) (bn_buf (getbn rx lsK))) (firstn (2 * Nat.pow 2 k) (bn_buf (getbn rr lsK))) (bn_buf (getbn t lsK)))))) (2 * Nat.pow 2 k))
                 (setbn t (bn_with_buf (getbn t lsK)
                                    (snd (sqr_recursive k (firstn (Nat.pow 2 k) (bn_buf (getbn rx lsK))) (firstn (2 * Nat.pow 2 k) (bn_buf (getbn rr lsK))) (bn_buf (getbn t lsK))))) lsK))) ΣK Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 R) (Z_to_bv 64 X) (Z_to_bv 64 R) (Z_to_bv 64 (Z.of_nat (2 * Nat.pow 2 k))) (Z_to_bv 64 (Z.of_nat (Nat.pow 2 k))) (Z_to_bv 64 TT) (Z_to_bv 64 f) t3 t4 t5 t6)
          F1 (wz 0x231478) fc1 None mK (seg_rom bgbsegs)).
  Proof.
    intros until fc1. intros ENV LS HR HX NXR HT HPt NTR NXT HK HAL HDM HDT.
    set (al := Nat.pow 2 k) in *. assert (HAL1 : (1 <= al)%nat) by (unfold al; clear; induction k; cbn; lia).
    pose proof (proj1 HPr : not_one rr) as NROr. change (not_one rx) in NROx. pose proof (proj1 HPt : not_one t) as NROt.
    destruct (env_bounds _ _ _ _ _ _ ENV) as (ESP & ESPS & B1 & B2 & B3).
    pose proof LOFV as LO'.
    pose proof ENV as (OK & HEAP & ST & MI & _ & _ & _ & _ & FRc & FSZ & _). unfold sfr in FRc. cbn [app] in FRc.
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
    destruct (open_full ΣK OWK LB mK lsK PL EA SPv rr R HEAP LS FROK NOFR HR NROr ltac:(solve_nbuf)) as (Dr & SR & ARR & OKR & UR & R0 & RC & DR0 & DRC & DSEPR).
    destruct (open_full ΣK OWK LB mK lsK PL EA SPv t TT HEAP LS FROK NOFR HT NROt ltac:(solve_nbuf)) as (Dt & STT & ARRT & OKT & UT & T0 & TC & DT0 & DTC & DSEPT).
    destruct (operand_view_ne ΣK OWK LB mK lsK PL EA SPv rr R Dr rx X al HEAP LS FROK NOFR HR NROr SR ARR HX NROx HAL NXR NBx)
      as (Dx & SX & LX & UX & ARX & X0 & XC & DX0 & DXC & XR & RDX & XDR & DRX).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HX) as HVX. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & _).
    pose proof (st_wf_ok rx lsK WFS HVX NROx) as (LMX & TDX & DMX & _). unfold BG_DMAX in DMX.
    pose proof OKR as (LMR & _ & DMR & _). unfold BG_DMAX in DMR. pose proof OKT as (LMT & _ & DMT & _). unfold BG_DMAX in DMT.
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HR NROr) as (ACR & ALR & OFR).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HX NROx) as (ACX & ALX & OFX).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HT NROt) as (ACT & ALT & OFT).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACDR & ALDR & OFDR).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARX) as (ACDX & ALDX & _).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARRT) as (ACDT & ALDT & OFDT).
    pose proof (sqr_scratch_ge k) as SGE. fold al in SGE.
    destruct (arr_posS _ _ _ _ _ HEAP ARR ltac:(clear - HDM HAL1; lia)) as (PDR & _).
    destruct (arr_posS _ _ _ _ _ HEAP ARX ltac:(clear - HAL HAL1 TDX; lia)) as (PDX & _).
    destruct (arr_posS _ _ _ _ _ HEAP ARRT ltac:(clear - SGE HDT HAL1; lia)) as (PDT & _).
    pose proof (bn_arrs_disj ΣK OWK LB mK lsK PL EA rr t R TT Dr Dt HEAP LS ltac:(congruence) HR HT ARR ARRT) as DRT.
    pose proof (bn_arrs_disj ΣK OWK LB mK lsK PL EA t rx TT X Dt Dx HEAP LS ltac:(congruence) HT HX ARRT ARX) as DTX.
    set (br := getbn rr lsK) in *. set (bx := getbn rx lsK) in *. set (tb := getbn t lsK) in *. set (la := firstn al (bn_buf bx)) in *.
    assert (LBT : length (bn_buf tb) = bn_dmax tb) by reflexivity.
    assert (HT0 : (0 < bn_dmax tb)%nat) by (clear - SGE HDT HAL1; lia).
    destruct (W_mulA2F.arr_block _ _ _ _ ARR ltac:(fold br; clear - HDM HAL1; lia)) as (pr & Edr & HinR).
    destruct (W_mulA2F.arr_block _ _ _ _ ARRT HT0) as (pt & Edt & HinT).
    destruct (W_mulA2F.arr_block _ _ _ _ ARX ltac:(fold bx; clear - HAL HAL1 TDX; lia)) as (px & Edx & HinX).
    assert (AL512 : Z.of_nat al <= 512) by (clear - HAL TDX DMX; unfold bn_dmax in *; lia).
    assert (LLA : length la = al) by (unfold la; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in TDX; clear - TDX HAL; lia]).
    assert (LIA : limbs la) by (apply limbs_firstn; exact LMX).
    set (r0 := firstn (2 * al) (bn_buf br)).
    assert (LR0 : length r0 = (2 * al)%nat) by (unfold r0; rewrite firstn_length_le; [reflexivity| unfold bn_dmax in HDM; exact HDM]).
    assert (LIR0 : limbs r0) by (apply limbs_firstn; exact LMR).
    pose proof (proj1 (limbarr_split bgbsegs mK Dr (bn_buf br) (2 * al) ltac:(unfold bn_dmax in HDM; exact HDM)) UR) as [UR1 _].
    pose proof (proj1 (limbarr_limbs_at bgbsegs mK Dr r0) UR1) as [RR0 WR0].
    pose proof (proj1 (limbarr_limbs_at bgbsegs mK Dt (bn_buf tb)) UT) as [TT0 WT0].
    assert (AL31 : 2 * Z.of_nat al < 2147483648) by (clear - AL512; lia).
    assert (EDr : bv_unsigned (Z_to_bv 64 Dr) = Dr) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - DR0 DRC CEIL LO' B2 B3; lia).
    assert (EDx : bv_unsigned (Z_to_bv 64 Dx) = Dx) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - DX0 DXC CEIL LO' B2 B3; lia).
    assert (EDt : bv_unsigned (Z_to_bv 64 Dt) = Dt) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - DT0 DTC CEIL LO' B2 B3; lia).
    assert (EAL : bv_unsigned (Z_to_bv 64 (Z.of_nat al)) = Z.of_nat al) by (apply unsigned_lit; clear - AL31; lia).
    assert (SRK : 0 <= AW_sqr_recursive.srec_stackA AW_sqr_closedA.CSLA k <= 66656) by (unfold AW_sqr_recursive.srec_stackA, AW_sqr_closedA.CSLA; clear - HK; lia).
    pose proof SR as SR'. pose proof STT as STT'. unfold bn_cells, MallocRep.wz in SR', STT'. unfold MallocRep.wz in SX.
    pose proof (munch_refl (@nil (Z * Z)) mK) as MU0.
    assert (OFF0 : offshW (@nil (Z * Z))) by exact I.
    unfold MallocRep.wz. apply implA_from_evt.
    ub1 ub_kind. ub1 ub_kind. setreg 10%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7; apply mod8_lor; assumption). ub.
    do 2 zstep. shl_with ACX ALX. chk0.
    do 2 zstep. shl_with ACR ALR. chk0.
    do 2 zstep. shl_with ACT ALT. chk0.
    step. step. step. clear SR' SX STT'.
    zstep.
    step.
    apply evt_done.
    eapply implA_step_same.
    { eapply (AW_sqr_closedA.bn_sqr_recursive_closedA k) with (a := la) (R := r0) (T := bn_buf tb) (lo := lo)
               (bR := (pr, Dr, 8 * Z.of_nat (bn_dmax br))) (bT := (pt, Dt, 8 * Z.of_nat (bn_dmax tb))) (bA := (px, Dx, 8 * Z.of_nat (bn_dmax bx)));
        rewrite ?EDr, ?EDx, ?EDt, ?ESP, ?EAL, ?LLA, ?LR0, ?LBT;
        [ exact LIA | exact LIR0 | exact LMT | clear - HK; lia | reflexivity | reflexivity | exact HDT | reflexivity | exact LX | exact RR0 | exact TT0
        | rewrite LR0 in WR0; exact WR0 | rewrite LBT in WT0; exact WT0
        | clear - DRX HDM TDX HAL; unfold bn_dmax in *; lia
        | clear - DTX TDX HAL; unfold bx, tb, bn_dmax in *; lia
        | clear - DRT HDM; unfold br, tb, bn_dmax in *; lia
        | exact ST | clear - LO' SRK; lia
        | unfold BnHeapA.ACEIL in *; clear - DRC CEIL LO' HDM SRK; lia
        | unfold BnHeapA.ACEIL in *; clear - DTC CEIL LO' SRK; lia
        | unfold BnHeapA.ACEIL in *; clear - DXC CEIL LO' TDX HAL SRK; unfold bn_dmax in *; lia
        | exact MI | exact HEAP
        | unfold AW_mul_recursive.kara_blocks; cbn [blk_addr blk_size fst snd];
          split; [exact HinR|]; split; [exact HinT|]; split; [apply in_or_app; left; exact HinX|]; split; [apply in_or_app; left; exact HinX|];
          split; [clear - HDM; lia|]; split; [clear; lia|]; split; [clear - TDX HAL; unfold bx, bn_dmax in *; lia|]; split; [clear - TDX HAL; unfold bx, bn_dmax in *; lia|];
          exact (conj ALDR (conj ALDT (conj ALDX ALDX)))
        | exact CEIL | unfold USTACK_TOP; clear - B2 B3; lia | exact FB16 | reflexivity
        | unfold AW_mul_recursive.kara_ub, BnUTac.ub_ptr_ok; split; [intros _; split; [exact PDR | exact ALDR]|]; split; [intros _; split; [exact PDX | exact ALDX]|];
          split; [intros _; split; [exact PDX | exact ALDX]|]; intros _; split; [exact PDT | exact ALDT] ]. }
    intros ms2 PO. unfold AW_mul_recursive.kr_apost in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & HR2 & HT2).
    rewrite ?EDr, ?EDt, ?ESP, ?LR0, ?LBT in *.
    retpc 2299080.
    pose proof (sqr_recursive_spec k la r0 (bn_buf tb) LIA LIR0 LMT LLA LR0 ltac:(rewrite LBT; exact HDT)) as SNS. unfold sqr_post in SNS.
    change (sqr_recursive k (firstn (2 ^ k) (bn_buf (getbn rx lsK))) (firstn (2 * 2 ^ k) (bn_buf (getbn rr lsK))) (bn_buf (getbn t lsK))) with (sqr_recursive k la r0 (bn_buf tb)).
    destruct (sqr_recursive k la r0 (bn_buf tb)) as [ro to] eqn:ESN. destruct SNS as (LRO & LENRO & _ & LTO & LENTO). cbn [fst snd] in HR2, HT2 |- *. rewrite LR0 in LENRO.
    replace (bn_with_buf tb to) with (bn_with_buf tb (splice (bn_buf tb) 0 to)) by (rewrite W_sqr.splice_full by exact LENTO; reflexivity).
    apply implA_from_evt. step. apply evt_done.
    eapply (sqr_finish2A (2 * al)%nat t R TT Dr Dt ro to j0 j1 j2 j4 j5 ΣK lsK mK m2 OWK);
      [ exact ENV | exact LS | exact HR | exact HT | exact NTR | exact HPt | exact SR | exact ARR | exact STT | exact ARRT
      | exact LRO | exact LENRO | fold br; clear - HDM HAL1; lia
      | exact LTO | rewrite LENTO, LBT; fold tb; clear - HT0; lia
      | exact HEAP2 | | exact HR2 | exact HT2 | exact MI2 | exact ST2 ].
    rewrite LENTO, LBT. exact AG2.
  Qed.

  Lemma sqr_bodyA : forall (ar ax : Z) j0 j1 j2 j4 j5 ΣK lsK mK OWK
      (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x24 x25 x26 t3 t4 t5 t6 : word) F1 fc1,
    CENV (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
    ref_at lsK OWK PL rr ar -> ref_at lsK OWK PL rx ax ->
    implA (bn_sqr_fixed_top ops rr rx lsK) ΣK Q
      (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 ar) (Z_to_bv 64 ax) x23 x24 x25 x26 (Z_to_bv 64 f) t3 t4 t5 t6)
          F1 (wz SQR_BODY) fc1 None mK (seg_rom bgbsegs)).
  Proof.
    intros until fc1. intros ENV LS HR HX.
    pose proof (proj1 HPr : not_one rr) as NROr. change (not_one rx) in NROx.
    destruct (env_bounds _ _ _ _ _ _ ENV) as (ESP & ESPS & B1 & B2 & B3).
    pose proof LOFV as LO'.
    pose proof ENV as (OK & HEAP & _).
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROK & FAL & NOFR).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.

    unfold bn_sqr_fixed_top. rewrite bn_live_run.
    destruct (live_refs (st_ctx lsK) [rr; rx]) eqn:LIVE; [| apply implA_unr].
    apply live_refs_true_iff in LIVE.
    assert (LTR0 : (rr < NFIX + gx_used (st_ctx lsK))%nat) by exact (Forall_inv LIVE).
    assert (LTX0 : (rx < NFIX + gx_used (st_ctx lsK))%nat) by exact (Forall_inv (Forall_inv_tail LIVE)).
    clear LIVE.
    destruct (open_ro ΣK OWK LB mK lsK PL EA SPv rx ax HEAP LS FROK NOFR HX NROx) as (Dx0 & SX & OKX & _ & X0 & XC & _).
    pose proof OKX as (_ & TDX & DMX & _). unfold BG_DMAX in DMX.
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS NOFR HX NROx) as (ACX & ALX & OFX).
    set (al := bn_top (getbn rx lsK)) in *.
    assert (AL512 : Z.of_nat al <= 512) by (clear - TDX DMX; unfold al, bn_dmax in *; lia).
    assert (AX : 0 < ax /\ ax + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - X0 XC CEIL LO' B2 B3; lia).
    pose proof (munch_refl (@nil (Z * Z)) mK) as MU0.
    assert (OFF0 : offshW (@nil (Z * Z))) by exact I.
    unfold bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd]. fold al.
    unfold SQR_BODY, MallocRep.wz. apply implA_from_evt.
    pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & FRc & _). unfold sfr in FRc. cbn [app] in FRc.
    unfold bn_cells, MallocRep.wz in SX. fold al in SX.
    pose proof ENV as ENV1. pose proof LS as LS1.
    ub.
    do 3 zstep. shl_with ACX ALX. chk0.
    step. rewrite (sx32_small (Z.of_nat al)) by (clear - AL512; lia).
    step.
    clear MU0 FRc.
    zstep. rewrite lts_signed by (clear - AL512; lia).
    destruct (Z.ltb_spec 0 (Z.of_nat al)) as [KA0|KA0]; cbn [negb].
    2:{
      replace (al =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; clear - KA0; lia).
      clear SX.
      pose proof (hpl_wref PL rr HPr) as WR.
      destruct (cenv_struct_openA LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 LOF16 _ _ _ _ _ _ rr ar ENV1 LS1 HR WR)
        as (Dr & BNN & OKN & ACCN & ALN & AN0 & SEPN & OFRN & STN & MIN & CLOSEN).
      unfold BnRepDefs.bn_cells, MallocRep.wz in BNN.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(ar, ar + 24)]%Z mx) as MU; pose proof (wmono_refl bgbsegs mx) as WM end.
      assert (OFF : offshW [(ar, ar + 24)]) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFRN; lia).
      ub. do 3 zstep. shl_with ACCN ALN. chk0.
      zstep.
      do 3 zstep. shl_with ACCN ALN. chk0.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mq end.
      destruct (CLOSEN mq (mkBN (bn_d (getbn rr lsK)) (bn_buf (getbn rr lsK)) 0 false (bn_flags (getbn rr lsK))) MU WM) as (ENV7 & LS7);
        [ unfold BnRepDefs.bn_cells, bn_dmax, MallocRep.wz; cbn [bn_top bn_buf bn_neg bn_flags bn_d Z.b2z Z.of_nat]; exact BNN | reflexivity | reflexivity
        | destruct OKN as (O1 & O2 & O3 & O4); unfold bg_ok, bn_dmax in *; cbn [bn_top bn_buf bn_flags]; split; [exact O1|]; split; [clear; lia|]; split; [exact O3 | exact O4]
        | assumption | assumption |].
      zstep. step.
      apply evt_done.
      eapply EPI; [eapply cenv_used_le; [exact ENV7 | exact TOT0] | exact LS7]. }
    replace (al =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; clear - KA0; lia).
    assert (ALP : 0 < Z.of_nat al) by (clear - KA0; lia). clear KA0 SX.

    zstep. step.
    apply evt_done.
    eapply (KCALLT _ _ (start_leaf lsK) _ _ _ 0 MC TOTAL BN_CTX_START_STACK); [exact ES0 | exact ENV1 | exact LS1 | pose proof STK_START as SS; clear - LOF SS; lia | rewrite ?MC_0; clear - TOT0; lia | clear; lia
      | apply (BN_CTX_start_leaves lsK)
      | intros PRE UW; eapply BN_CTX_start_walkA; [exact PRE | exact UW
            | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_bn_sqr_fixed_top_230fe8 CTX) | reflexivity | exact HPC | reflexivity]
      | hres |].
    intros u2 Σ2 ls2 mq2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F2 fc2 ENV2 LS2 RS2 _ LEAF2. clear ENV1 LS1 HEAP.
    retpc 2298320. cbn [fst snd].
    unfold start_leaf in LEAF2. cbn [fst snd] in LEAF2. destruct LEAF2 as (EGs & _ & EU2 & _).
    assert (EG2 : forall r0, getbn r0 ls2 = getbn r0 lsK) by (intros r0; unfold getbn; rewrite EGs; reflexivity).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HR) as HR2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HX) as HX2.

    destruct (Nat.eq_dec rr rx) as [EQ|NRX].
    { subst rx. rewrite Nat.eqb_refl. unfold bunr. cbn [unreachable tree_ops tbind]. apply implA_unr. }
    replace (rr =? rx)%nat with false by (symmetry; apply Nat.eqb_neq; exact NRX).
    pose proof ENV2 as (_ & HEAP2 & _).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
    pose proof (struct_disj Σ2 OW2 LB mq2 HEAP2 ls2 PL EA SPv USTACK_TOP PARTS2 FROK rr rx ar ax NRX HR2 HX2) as SDJ.
    destruct (open_ro Σ2 OW2 LB mq2 ls2 PL EA SPv rr ar HEAP2 LS2 FROK NOFR HR2 NROr) as (Dr0 & _ & _ & _ & R0 & RC & _).
    assert (ARB : 0 < ar /\ ar + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - R0 RC CEIL LO' B2 B3; lia).
    apply implA_from_evt.
    zstep. zstep. if_cases KE; zify_cond KE; [| exfalso; clear - KE SDJ; lia]. clear KE.

    pose proof ENV2 as ENV3. pose proof LS2 as LS3. clear ENV2 LS2 HEAP2.
    zstep. step.
    apply evt_done.
    apply implA_tbind_assoc.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS3) as PARTS3.
    pose proof (st_wf_get_pre ls2 (proj1 PARTS3)) as (GP1 & GP2 & GP3).
    eapply (KCALLT _ _ (get_leaf ls2) _ _ _ TOTAL MC TOTAL BN_CTX_GET_STACK); [exact ES0 | exact ENV3 | exact LS3 | pose proof STK_GET as SS; clear - LOF SS; lia | rewrite ?MC_0; clear; lia | clear; lia
      | apply (BN_CTX_get_leaves ls2 GP1 GP2)
      | intros PRE UW; eapply BN_CTX_get_walkA; [exact PRE | exact UW
            | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_bn_sqr_fixed_top_231004 CTX) | reflexivity | exact HPC | reflexivity]
      | hres |].
    intros t Σ4 ls4 mq4 OW4 ? ? ? yT ? ? ? ? ? ? ? ? ? ? ? F4 fc4 ENV4 LS4 RS4 RES4 LEAF4. hnf in RES4. destruct RES4 as (_ & (ti & Et) & (at_ & HAt & EyT) & _). clear ENV3 LS3.
    retpc 2298348. subst yT. unfold MallocRep.wz in *. cbn [fst snd].
    unfold get_leaf in LEAF4. cbn [fst snd] in LEAF4. destruct LEAF4 as (LT1 & _ & _ & LT4 & _).
    assert (ETU : t = RPool (gx_used (st_ctx lsK))) by (rewrite LT1, GP3, EU2; reflexivity).
    assert (NTR : t <> rr) by (rewrite ETU; clear - LTR0; unfold RPool; lia).
    assert (NXT : rx <> t) by (rewrite ETU; clear - LTX0; unfold RPool; lia).
    assert (HPT : hpl PL t) by (rewrite Et; apply hpl_pool).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HR2) as HR4. pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HX2) as HX4.
    assert (EA4 : getbn rx ls4 = getbn rx lsK) by (rewrite LT4 by (rewrite <- LT1; exact NXT); apply EG2).
    assert (ER4 : getbn rr ls4 = getbn rr lsK) by (rewrite LT4 by (rewrite <- LT1; intros E; apply NTR; symmetry; exact E); apply EG2).
    pose proof ENV4 as (_ & HEAP4 & _).
    destruct (open_ro Σ4 OW4 LB mq4 ls4 PL EA SPv t at_ HEAP4 LS4 FROK NOFR HAt (proj1 HPT)) as (Dt0 & _ & _ & _ & T0 & TC & _).
    assert (ATB : 0 < at_ /\ at_ + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - T0 TC CEIL LO' B2 B3; lia).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS4 HR4) as HVR4.
    pose proof (st_wf_ok rr ls4 (proj1 (lib_state_h_parts _ _ _ _ _ _ LS4)) HVR4 NROr) as (_ & TDR4 & _).
    apply implA_from_evt.
    zstep.
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ ARB; lia|]. clear KZ.
    zstep.
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ ATB; lia|]. clear KZ.
    ub.
    zstep. setreg 24%Z (Z_to_bv 64 (Z.of_nat (2 * al))) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); rewrite bn_swrap32_small by (clear - AL512; lia); clear; lia).

    zstep. zstep. step.
    apply evt_done.
    apply implA_tbind_assoc.
    eapply (KCALLT _ _ (wexp_leaf rr ls4) _ _ _ TOTAL MC TOTAL BN_WEXPAND_STACK); [exact ES0 | exact ENV4 | exact LS4 | pose proof STK_WEXP as SS; clear - LOF SS; lia | rewrite ?MC_0; clear; lia | clear; lia
      | apply (bn_wexpand_leaves rr (2 * al) ls4 HVR4 TDR4)
      | intros PRE UW; eapply (bn_wexpand_walkA) with (r := rr) (a := ar) (words := (2 * al)%nat); [exact PRE | exact UW
            | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_bn_sqr_fixed_top_231030 CTX) | reflexivity | exact HR4 | exact (hpl_wref PL rr HPr)
            | reflexivity | reflexivity | clear - AL512; lia]
      | hres |].
    intros u5 Σ5 ls5 mq5 OW5 ? ? ? yR ? ? ? ? ? ? ? ? ? ? ? F5 fc5 ENV5 LS5 RS5 RES5 LEAF5. hnf in RES5. destruct RES5 as (_ & EyR & HDM & _). clear ENV4 LS4 HEAP4.
    retpc 2298392. subst yR. unfold MallocRep.wz in *. cbn [fst snd].
    unfold wexp_leaf in LEAF5. cbn [fst snd] in LEAF5. destruct LEAF5 as (LW1 & _).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS5 HR4) as HR5. pose proof (ref_at_stable _ _ _ _ PL _ _ RS5 HX4) as HX5. pose proof (ref_at_stable _ _ _ _ PL _ _ RS5 HAt) as HT5.
    assert (EA5 : getbn rx ls5 = getbn rx lsK) by (rewrite LW1 by (intros E; apply NRX; exact E); exact EA4).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS5 HR5) as HVR5.
    assert (ALT : (al <= bn_top (getbn rx ls5))%nat) by (rewrite EA5; unfold al; clear; lia).
    assert (NXR : rx <> rr) by (intros E; apply NRX; symmetry; exact E).
    apply implA_from_evt.
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ ARB; lia|]. clear KZ.

    zstep. zstep. if_cases K8; zify_cond K8.
    {
      assert (E8 : al = 8%nat) by (clear - K8; lia). clear K8.
      replace (al =? 4)%nat with false by (rewrite E8; reflexivity). replace (al =? 8)%nat with true by (rewrite E8; reflexivity).
      apply evt_done. cbn [tbind fst snd]. rewrite sqr_model_fin by exact HVR5. rewrite <- EA5. rewrite E8 in *.
      eapply sqr_path_comba8A; [exact ENV5 | exact LS5 | exact HR5 | exact HX5 | exact NXR | exact ALT | exact HDM]. }
    assert (N8 : al <> 8%nat) by (clear - K8; lia). clear K8.
    replace (al =? 8)%nat with false by (symmetry; apply Nat.eqb_neq; exact N8).
    zstep. zstep. if_cases K4; zify_cond K4.
    2:{
      assert (E4 : al = 4%nat) by (clear - K4; lia). clear K4.
      replace (al =? 4)%nat with true by (rewrite E4; reflexivity).
      apply evt_done. cbn [tbind fst snd]. rewrite sqr_model_fin by exact HVR5. rewrite <- EA5. rewrite E4 in *.
      eapply sqr_path_comba4A; [exact ENV5 | exact LS5 | exact HR5 | exact HX5 | exact NXR | exact ALT | exact HDM]. }
    assert (N4 : al <> 4%nat) by (clear - K4; lia). clear K4.
    replace (al =? 4)%nat with false by (symmetry; apply Nat.eqb_neq; exact N4).
    zstep. zstep. if_cases K16; zify_cond K16.
    2:{
      assert (L16 : (al < 16)%nat) by (clear - K16; lia). clear K16.
      replace (al <? 16)%nat with true by (symmetry; apply Nat.ltb_lt; exact L16).
      apply evt_done. cbn [tbind fst snd]. rewrite sqr_model_fin by exact HVR5. rewrite <- EA5.
      eapply sqr_path_stackA; [exact ENV5 | exact LS5 | exact HR5 | exact HX5 | exact NXR | split; [clear - ALP; lia | exact ALT] | exact L16 | exact HDM]. }
    assert (G16 : (16 <= al)%nat) by (clear - K16; lia). clear K16.
    replace (al <? 16)%nat with false by (symmetry; apply Nat.ltb_ge; exact G16).

    set (nb := num_bits_word (Z.of_nat al)) in *.
    assert (NBR : 5 <= nb <= 10).
    { unfold nb, num_bits_word. replace (Z.of_nat al =? 0) with false by (symmetry; apply Z.eqb_neq; clear - G16; lia).
      pose proof (Z.log2_le_mono 16 (Z.of_nat al) ltac:(clear - G16; lia)) as L1. pose proof (Z.log2_le_mono (Z.of_nat al) 512 AL512) as L2.
      change (Z.log2 16) with 4 in L1. change (Z.log2 512) with 9 in L2. clear - L1 L2. lia. }
    set (kj := Z.to_nat (nb - 1)) in *.
    assert (EKJ : Z.of_nat kj = nb - 1) by (unfold kj; clear - NBR; lia).
    assert (KJR : (4 <= kj <= 9)%nat) by (clear - EKJ NBR; lia).
    pose proof ENV5 as (_ & HEAP5 & ST5 & MI5 & _ & _ & _ & _ & FR5 & FSZ5 & _). unfold sfr in FR5. cbn [app] in FR5.
    zstep. step.
    eapply evt_cut.
    { eapply (BN_num_bits_word_aspec (Z_to_bv 64 0x231434) (Z_to_bv 64 FB)) with (lo := lo); [rewrite ESP; exact ST5 | rewrite ESP; clear - LO'; lia | exact MI5]. }
    intros ms' (n0 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & n8 & n9 & n10 & n11 & n12 & n13 & mN & -> & MUn & WMn & MIn & STn).
    rewrite ESP in MUn, STn. rewrite (unsigned_lit (Z.of_nat al)) by (clear - AL512; lia). fold nb.
    retpc 2298932.
    eapply (rw_cells_transport bgbsegs _ mq5 mN) in FR5; [| exact MUn | exact WMn | cbn [disjoint_from cells_size csize Nat.add]; clear; lia].
    assert (HWn : Forall (w_frmix OW5 LB ls5 PL EA lo SPv [] f 3) [(FB - 16, FB)]).
    { constructor; [left; split; [left; cbn [fst snd]; clear - LO' B2; lia | apply w_stack; cbn [fst snd]; clear - LO' CEIL B2; lia] | constructor]. }
    destruct (cenv_frmixA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 _ (sfr (C8 (Z_to_bv 64 ac)) (C8 (Z_to_bv 64 f)) j0 j1 j2 j4 j5) _ _ _ _ mN _ _ f 3%nat []
                ENV5 LS5 HF FRESH MUn WMn HWn STn MIn ltac:(unfold sfr; cbn [app]; exact FR5) FSZ5) as (ENV6 & LS6).
    change (lib_state_hc false [] ls5 mN OW5 PL EA) with (lib_state ls5 mN OW5 PL EA) in LS6.
    clear ENV5 LS5 HEAP5 ST5 MI5 FR5 MUn WMn MIn STn HWn.
    assert (HC : nb = 5 \/ nb = 6 \/ nb = 7 \/ nb = 8 \/ nb = 9 \/ nb = 10) by (clear - NBR; lia).
    assert (J512 : (16 <= 2 ^ kj <= 512)%nat).
    { unfold kj. clear - HC. destruct HC as [E|[E|[E|[E|[E|E]]]]]; rewrite E; [change (16 <= 16 <= 512)%nat | change (16 <= 32 <= 512)%nat | change (16 <= 64 <= 512)%nat | change (16 <= 128 <= 512)%nat | change (16 <= 256 <= 512)%nat | change (16 <= 512 <= 512)%nat]; clear; lia. }
    zstep. setreg 11%Z (Z_to_bv 64 (nb + -1)) ltac:(f_equal; symmetry; apply bn_swrap32_small; clear - NBR; lia).
    ub.
    zstep. zstep.
    assert (EJ1 : Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 ((nb + -1) mod 32))) = Z_to_bv 64 (Z.of_nat (2 ^ kj))).
    { unfold kj. clear - HC. destruct HC as [E|[E|[E|[E|[E|E]]]]]; rewrite E; reflexivity. }
    assert (EJ4 : Z_to_bv 64 (bv_swrap 32 (Z.shiftl 4 ((nb + -1) mod 32))) = Z_to_bv 64 (Z.of_nat (4 * 2 ^ kj))).
    { unfold kj. clear - HC. destruct HC as [E|[E|[E|[E|[E|E]]]]]; rewrite E; reflexivity. }
    clear HC EJ4.
    assert (J2 : 32 <= Z.of_nat (2 * 2 ^ kj) <= 1024) by (clear - J512; lia).
    rewrite EJ1.
    zstep. setreg 10%Z (Z_to_bv 64 (Z.of_nat (2 * 2 ^ kj))) ltac:(f_equal; rewrite ?unsigned_lit by (clear - J512; lia); clear; lia).
    zstep. setreg 12%Z (Z_to_bv 64 (Z.of_nat (2 * 2 ^ kj))) ltac:(f_equal; rewrite ?unsigned_lit by (clear - J512; lia); rewrite bn_swrap32_small by (clear - J512; lia); clear; lia).
    ub.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS6 HT5) as HVT5.
    pose proof (st_wf_ok t ls5 (proj1 (lib_state_h_parts _ _ _ _ _ _ LS6)) HVT5 (proj1 HPT)) as (_ & TDT & _).
    assert (NRT : rr <> t) by (intros E; apply NTR; symmetry; exact E).
    zstep. if_cases KJ; zify_cond KJ.
    2:{
      assert (EJ : al = (2 ^ kj)%nat) by (clear - KJ; lia). clear KJ.
      replace (al =? 2 ^ kj)%nat with true by (symmetry; apply Nat.eqb_eq; exact EJ).
      ub.
      zstep. setreg 11%Z (Z_to_bv 64 (Z.of_nat (4 * 2 ^ kj))) ltac:(f_equal; rewrite ?unsigned_lit by (clear - J512; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); rewrite bn_swrap32_small by (clear - J512; lia); clear; lia).
      zstep. step.
      apply evt_done.
      apply implA_tbind_assoc. apply implA_tbind_assoc.
      eapply (KCALLT _ _ (wexp_leaf t ls5) _ _ _ TOTAL MC TOTAL BN_WEXPAND_STACK); [exact ES0 | exact ENV6 | exact LS6 | pose proof STK_WEXP as SS; clear - LOF SS; lia | rewrite ?MC_0; clear; lia | clear; lia
        | apply (bn_wexpand_leaves t (4 * 2 ^ kj) ls5 HVT5 TDT)
        | intros PRE UW; eapply (bn_wexpand_walkA) with (r := t) (a := at_) (words := (4 * 2 ^ kj)%nat); [exact PRE | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_bn_sqr_fixed_top_23128c CTX) | reflexivity | exact HT5 | exact (hpl_wref PL t HPT)
              | reflexivity | reflexivity | clear - J512; lia]
        | hres |].
      intros u7 Σ7 ls7 mq7 OW7 ? ? ? yT ? ? ? ? ? ? ? ? ? ? ? F7 fc7 ENV7 LS7 RS7 RES7 LEAF7. hnf in RES7. destruct RES7 as (_ & EyT & HDT & _). clear ENV6 LS6.
      retpc 2298996. subst yT. unfold MallocRep.wz in *. cbn [fst snd].
      unfold wexp_leaf in LEAF7. cbn [fst snd] in LEAF7. destruct LEAF7 as (LV1 & _).
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS7 HR5) as HR7. pose proof (ref_at_stable _ _ _ _ PL _ _ RS7 HX5) as HX7. pose proof (ref_at_stable _ _ _ _ PL _ _ RS7 HT5) as HT7.
      assert (EA7 : getbn rx ls7 = getbn rx lsK) by (rewrite LV1 by (intros E; apply NXT; symmetry; exact E); exact EA5).
      assert (ER7 : getbn rr ls7 = getbn rr ls5) by (apply LV1; exact NTR).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS7 HR7) as HVR7.
      apply implA_from_evt.
      zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ ATB; lia|]. clear KZ.
      apply evt_done.
      rewrite <- EA7. rewrite EJ in *.
      set (X := sqr_recursive kj (firstn (2 ^ kj) (bn_buf (getbn rx ls7))) (firstn (2 * 2 ^ kj) (bn_buf (getbn rr ls7))) (bn_buf (getbn t ls7))).
      assert (EX : X = (fst X, snd X)) by (destruct X; reflexivity). rewrite EX. cbn [tbind fst snd].
      rewrite sqr_model_fin by (rewrite length_setbn; exact HVR7). subst X.
      eapply sqr_path_recA; [exact ENV7 | exact LS7 | exact HR7 | exact HX7 | exact NXR | exact HT7 | exact HPT | exact NTR | exact NXT
        | clear - KJR; lia | rewrite EA7; fold al; rewrite EJ; apply Nat.le_refl | rewrite ER7; exact HDM
        | pose proof (sqr_scratch_le kj) as SL; clear - SL HDT; lia ]. }

    assert (NJ : al <> (2 ^ kj)%nat) by (clear - KJ; lia). clear KJ.
    replace (al =? 2 ^ kj)%nat with false by (symmetry; apply Nat.eqb_neq; exact NJ).
    zstep. zstep. step.
    apply evt_done.
    apply implA_tbind_assoc. apply implA_tbind_assoc.
    eapply (KCALLT _ _ (wexp_leaf t ls5) _ _ _ TOTAL MC TOTAL BN_WEXPAND_STACK); [exact ES0 | exact ENV6 | exact LS6 | pose proof STK_WEXP as SS; clear - LOF SS; lia | rewrite ?MC_0; clear; lia | clear; lia
      | apply (bn_wexpand_leaves t (2 * al) ls5 HVT5 TDT)
      | intros PRE UW; eapply (bn_wexpand_walkA) with (r := t) (a := at_) (words := (2 * al)%nat); [exact PRE | exact UW
            | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_bn_sqr_fixed_top_2312f0 CTX) | reflexivity | exact HT5 | exact (hpl_wref PL t HPT)
            | reflexivity | reflexivity | clear - AL512; lia]
      | hres |].
    intros u7 Σ7 ls7 mq7 OW7 ? ? ? yT ? ? ? ? ? ? ? ? ? ? ? F7 fc7 ENV7 LS7 RS7 RES7 LEAF7. hnf in RES7. destruct RES7 as (_ & EyT & HDT & _). clear ENV6 LS6.
    retpc 2299096. subst yT. unfold MallocRep.wz in *. cbn [fst snd].
    unfold wexp_leaf in LEAF7. cbn [fst snd] in LEAF7. destruct LEAF7 as (LV1 & _).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS7 HR5) as HR7. pose proof (ref_at_stable _ _ _ _ PL _ _ RS7 HX5) as HX7. pose proof (ref_at_stable _ _ _ _ PL _ _ RS7 HT5) as HT7.
    assert (EA7 : getbn rx ls7 = getbn rx lsK) by (rewrite LV1 by (intros E; apply NXT; symmetry; exact E); exact EA5).
    assert (ER7 : getbn rr ls7 = getbn rr ls5) by (apply LV1; exact NTR).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS7 HR7) as HVR7.
    apply implA_from_evt.
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ ATB; lia|]. clear KZ.
    apply evt_done.
    rewrite <- EA7.
    set (X := sqr_normal (firstn al (bn_buf (getbn rx ls7))) (firstn (2 * al) (bn_buf (getbn rr ls7)))).
    assert (EX : X = (fst X, sqr_words (firstn al (bn_buf (getbn rx ls7))))) by reflexivity. rewrite EX. cbn [tbind fst snd].
    rewrite sqr_model_fin by (rewrite length_setbn; exact HVR7). subst X.
    eapply sqr_path_ntmpA; [exact ENV7 | exact LS7 | exact HR7 | exact HX7 | exact NXR | exact HT7 | exact HPT | exact NTR | exact NXT
      | split; [clear - ALP; lia| rewrite EA7; fold al; apply Nat.le_refl] | rewrite ER7; exact HDM | exact HDT ].
  Qed.

End Body.
End WithRT.

Section Top.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).

  Definition BN_SQR_FIXED_STACKA : Z := SQR_FRAME + SQR_CS.
  Definition BN_SQR_FIXED_COST : Z := 1.
  Lemma BN_SQR_FIXED_STACKA_val : BN_SQR_FIXED_STACKA = 66832.
  Proof. reflexivity. Qed.

  Lemma bn_sqr_fixed_top_walkA0 : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo BN_SQR_FIXED_STACKA BN_SQR_FIXED_COST ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MOD_SQR (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> hpl PL rr -> rx <> ROne -> nbuf PL rx -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
    implA (bn_sqr_fixed_top (tree_ops bptr) rr rx ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_SQR_FIXED_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_SQR) fc None m (seg_rom bgbsegs)).
  Proof.
    intros until qc. intros PRE ROOM UW CTX -> HR HX HPr NROx NBx EC -> -> ->.
    unfold BN_SQR_FIXED_STACKA, BN_SQR_FIXED_COST in *.
    pose proof PRE as (HEAP0 & LS0 & FROK0 & _ & CEIL0 & LOSP0 & SPT0 & _ & _ & _ & _ & _ & NOFR0).
    destruct (open_ro Σ OW LB m ls PL EA (bv_unsigned sp) rx ax HEAP0 LS0 FROK0 NOFR0 HX NROx) as (Dx0 & _ & _ & _ & X0 & XC & _).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (EAX : bv_unsigned (wz ax) = ax).
    { unfold MallocRep.wz. apply unsigned_lit. rewrite SQR_CS_val in LOSP0. unfold SQR_FRAME, BnHeapA.ACEIL in *. clear - X0 XC CEIL0 LOSP0 SPR. lia. }
    eapply (pro_sqr _ _) with (d := 0%nat); [exact PRE | exact ROOM | exact UW | reflexivity | unfold SQR_FRAME, RT_STACK; rewrite SQR_CS_val; clear; lia | clear; lia |].
    intros Σ1 m1 f spa g junk gj ra' u0 u1 u2 x10 x11 x12 x13 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' j0 j1 j2 j4 j5 FE GSZ SAVJ FR.
    unfold MallocRep.wz in FR.
    pose proof FE as (HEAP1 & LS1 & FROK1 & ST1 & CEIL & LOK & SPT & SP16 & MI1 & CNT1 & CRED1 & FAL & NOFR1 & ROOM1 & SPA32 & SPAL & SPAH & CR1 & AXO & UW1 & FRESH & GEO).
    pose proof (fr_env_cenv0 160 0 f 3 [] Σ ls m OW LB PL EA sp lo _ (1 - 1) s0 ra ras spa Σ1 m1
                  ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 ac); CB 8 j4; CB 8 j5; C8 (Z_to_bv 64 f)] ++ [CB g junk])
                  FE ltac:(clear; lia) ltac:(unfold SQR_FRAME; rewrite SQR_CS_val; clear; lia) FR
                  ltac:(cbn [app cells_size csize Nat.add]; clear - GSZ; lia)) as EV0.
    cbn [app] in EV0 |- *.

    eapply (@sqr_bodyA (push AR f 3) UK BE gp sp lo (bv_unsigned sp) spa s0 ra ras LB PL EA (1 - 1) Σ1 ls OW m1 ac qc f g junk rr rx);
      try eassumption; try reflexivity.
    - left. reflexivity.
    - intros c3 k0 k1 k2 k4 k5 Σk lsk mk OWk rax z0 z1 z2 x9 y0 y1 y2 y3 y4 y5 y6 y7 x20 x21 x22 x23 x25 x26 z3 z4 z5 z6 Fk fck ENVk LSk.
      eapply (epi_sqr tt _) with (mb := m1) (used := 1 - 1) (gj := gj) (d := 0%nat) (m1 := m1) (Σ1 := Σ1) (loc := [CB 8 k0; CB 8 k1; CB 8 k2; c3; CB 8 k4; CB 8 k5; C8 (Z_to_bv 64 f)]);
        [exact PRE | exact FE | unfold SQR_FRAME, RT_STACK; rewrite SQR_CS_val; clear; lia | exact GSZ | exact SAVJ
        | exact AXO | exact ENVk | exact LSk | clear; lia | split; reflexivity].
  Qed.

  Lemma bn_sqr_fixed_top_walkA : forall (CS CM : Z), BN_SQR_FIXED_STACKA <= CS -> BN_SQR_FIXED_COST <= CM -> forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MOD_SQR (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> hpl PL rr -> rx <> ROne -> nbuf PL rx -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
    implA (bn_sqr_fixed_top (tree_ops bptr) rr rx ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_SQR) fc None m (seg_rom bgbsegs)).
  Proof.
    intros CS CM HCS HCM. intros until qc. intros PRE ROOM UW CTX E0 HR HX HPr NROx NBx EC E1 E2 E3.
    eapply implA_cost_wk; [| exact HCM].
    eapply bn_sqr_fixed_top_walkA0; [eapply bn_preA_wk; [exact PRE | exact HCS | exact HCM] | exact ROOM | exact UW | exact CTX | exact E0 | exact HR | exact HX | exact HPr | exact NROx | exact NBx | exact EC
      | exact E1 | exact E2 | exact E3].
  Qed.
End Top.
