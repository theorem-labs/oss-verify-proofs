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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require BnDivWords.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct AsByte RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgWords BgArith.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_callsAF W_calls3AF W_small3A W_small4A W_calls4AF AFrameKit AFrameEnv ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import W_ctxAF W_ctx_getAF W_ctx_endAF W_copyAF W_cmpAF W_uaddAF W_usubAF W_subAF W_set_wordAF ShiftKitAF W_shiftAF W_nnmodAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import InvKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).

Definition INT_BN_MOD_INVERSE : Z := 0x231dfc.
Definition BN_RSHIFT1 : Z := 0x2359c4.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2301768 => 1
  | 2301788 => 2
  | 2301792 => 2
  | 2302136 => 2
  | 2302140 => 2
  | 2302384 => 2
  | 2302388 => 1
  | 2302392 => 2
  | 2302420 => 2
  | 2302424 => 1
  | 2302428 => 2
  | 2302624 => 2
  | 2302628 => 1
  | 2302632 => 2
  | 2302936 => 2
  | 2302940 => 1
  | 2302944 => 2
  | 2302972 => 2
  | 2302976 => 1
  | 2302980 => 2
  | 2303176 => 2
  | 2303244 => 2
  | 2303876 => 2
  | 2303880 => 1
  | 2303884 => 2
  | 2304180 => 2
  | 2304516 => 1
  | 2304520 => 2
  | 2304592 => 2
  | 2304596 => 1
  | 2304600 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.

Section Stmt.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).

Definition rshift1_stmtA (STACK COST : Z) : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rx : bnref) (ax : Z),
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_RSHIFT1 (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz ax ->
  implA (BN_rshift1 (tree_ops bptr) rx rx ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA COST
       (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_RSHIFT1) fc None m (seg_rom bgbsegs)).

End Stmt.

Lemma bbind_get : forall {B} r (f : bignum bptr -> BM (M := btree bptr) B) (bs : bstate bptr),
  bbind ops (bget ops r) f bs = f (getbn r bs) bs.
Proof. reflexivity. Qed.
Lemma bbind_ret : forall {A B} (a : A) (f : A -> BM (M := btree bptr) B) (bs : bstate bptr),
  bbind ops (bret ops a) f bs = f a bs.
Proof. reflexivity. Qed.

Lemma nbits_range : forall b : bignum bptr, bg_ok b -> 0 <= num_bits_pure b <= 32768.
Proof.
  intros b (LIM & TD & DM & _). unfold BG_DMAX in DM. unfold num_bits_pure.
  destruct (Nat.eqb_spec (bn_top b) 0) as [E|NE]; [lia|].
  pose proof (limbs_nth (bn_buf b) (bn_top b - 1) LIM) as LN. unfold limb, BW in LN.
  pose proof (BnDivWords.num_bits_word_le (nth (bn_top b - 1) (bn_buf b) 0) 64 ltac:(lia) LN). unfold bn_dmax in *. lia.
Qed.

Ltac fr_unf H := idtac.
Ltac fr_store_gen CF FBz SPz ENV LS ENV' LS' :=
  let STx := fresh "STx" in let MIx := fresh "MIx" in let FRx := fresh "FRx" in let FSZx := fresh "FSZx" in
  let MUx := fresh "MUx" in let WMx := fresh "WMx" in let SZx := fresh "SZx" in
  pose proof ENV as (_ & _ & STx & MIx & _ & _ & _ & _ & FRx & FSZx & _);
  fr_unf FRx; fr_unf FSZx; cbn [app] in FRx;
  assert (SZx : FBz + 168 <= SPz) by (cbn [app cells_size csize Nat.add] in FSZx; clear - FSZx; lia);
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(FBz, SPz)]%Z mm) as MUx; pose proof (wmono_refl bgbsegs mm) as WMx end;
  step;
  lazymatch type of FRx with
  | rw_cells _ ?mx _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: _) =>
      destruct (CF _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19] _ _ _ _ mx _
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

Lemma MC_0 : MC = 0. Proof. reflexivity. Qed.

Section Proofs.

  Variable CS : Z.
  Hypothesis CS112 : BN_NUM_BITS_STACK <= CS.
  Hypothesis CS16 : 16 <= CS.
  Hypothesis STK_START : BN_CTX_START_STACK <= CS.
  Hypothesis STK_GET : BN_CTX_GET_STACK <= CS.
  Hypothesis STK_END : BN_CTX_END_STACK <= CS.
  Hypothesis STK_SETW : BN_SET_WORD_STACK <= CS.
  Hypothesis STK_COPY : BN_COPY_STACK <= CS.
  Hypothesis STK_UCMP : BN_UCMP_STACK <= CS.
  Hypothesis STK_UADD : BN_UADD_STACK <= CS.
  Hypothesis STK_USUB : BN_USUB_STACK <= CS.
  Hypothesis STK_SUB : BN_SUB_STACK <= CS.
  Hypothesis STK_RSH : BN_RSHIFT_W_STACK <= CS.
  Hypothesis STK_NNMOD : BN_NNMOD_STACK <= CS.
  Hypothesis BN_rshift1_walkA : rshift1_stmtA CS MC.
  Hypothesis STK_ONE : BN_IS_ONE_STACK <= CS.

  Section Main.
    Variables (gp s0r : word) (lo SPv FB : Z) (s0w raw : word) (ras : list Z) (LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (TOTAL : Z).
    Variables (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem).
    Variables (rR ra_ rn : bnref) (aR aa an ac : Z) (qc : bptr) (f pn : Z) (g : nat) (junk : list byte).
    Hypothesis ES0 : bv_unsigned s0r = SPv.
    Hypothesis LOF : lo <= FB - CS.
    Hypothesis TOT0 : 0 <= TOTAL.
    Hypothesis HPC : pl_ctx PL = Some (ac, qc).
    Hypothesis WRR : hpl PL rR.
    Hypothesis NROa : ra_ <> ROne.
    Hypothesis NROn : rn <> ROne.
    Hypothesis CTX : uk_ctx INT_BN_MOD_INVERSE (bv_unsigned raw :: ras).
    Variable Q : unit * ST -> rts RT -> machine_state -> Prop.

    Notation CENV := (cenvA LB PL lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0).
    Notation KCALL := (kcallA LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0).
    Notation KCALLE := (kcallA_end LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0).
    Notation KCALLL := (kcallA_last LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0).

    Lemma LOF16 : lo <= FB - 16. Proof using LOF CS16. clear - LOF CS16. lia. Qed.
    Lemma LOFNB : lo <= FB - BN_NUM_BITS_STACK. Proof using LOF CS112. clear - LOF CS112. lia. Qed.

    Notation KZERO := (is_zero_callA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOF16).
    Notation KODD := (is_odd_callA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOF16).
    Notation KBIT := (is_bit_set_callA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOF16).
    Notation KFLAGS := (get_flags_callA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOF16).
    Notation KBITS := (num_bits_callA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0).
    Lemma LOFONE : lo <= FB - BN_IS_ONE_STACK. Proof using LOF STK_ONE. clear - LOF STK_ONE. lia. Qed.
    Notation KONE := (is_one_callA LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOFONE).
    Notation KZEROX := (zero_callA LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 LOF16).

    Definition ifrc (j0 j1 j2 j3 j4 j5 j6 : list byte) (c7 c8 c10 c11 c12 c13 c14 : cell) (j16 j17 : list byte) : list cell :=
      [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; c7; c8; C8 (Z_to_bv 64 (shad pn)); c10; c11; c12; c13;
       c14; C8 (Z_to_bv 64 aR); CB 8 j16; CB 8 j17; C8 (Z_to_bv 64 f); CB g junk].
    Definition ifr (j0 j1 j2 j3 j4 j5 j6 : list byte) (wT wM wA wB wX wY : word) (c14 : cell) (j16 j17 : list byte) : list cell :=
      ifrc j0 j1 j2 j3 j4 j5 j6 (C8 wT) (C8 wM) (C8 wA) (C8 wB) (C8 wX) (C8 wY) c14 j16 j17.

    Hypothesis EPI : forall j0 j1 j2 j3 j4 j5 j6 wT wM wA wB wX wY j14 j16 j17 Σk lsk mk OWk
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x23 x24 x25 x26 t3 t4 t5 t6 : word) F' fc',
      CENV (ifr j0 j1 j2 j3 j4 j5 j6 wT wM wA wB wX wY (CB 8 j14) j16 j17) 0 Σk lsk mk OWk -> lib_state lsk mk OWk PL EA ->
      implA (TRet (tt, lsk)) Σk Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 f) x20 (Z_to_bv 64 aR) (Z_to_bv 64 pn) x23 x24 x25 x26 (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
            F' (wz 0x231f80) fc' None mk (seg_rom bgbsegs)).

    Local Ltac hres := let H := fresh "HRES" in intros ? ? ? ? ? H; hnf in H; exact (proj1 H).
    Local Ltac retpc n := rewrite (ret_pc_even n) by (clear; lia).
    Local Ltac mc0 := rewrite ?MC_0; clear; lia.
    Local Ltac pre_wk PRE STK := eapply bn_preA_wk; [exact PRE | exact STK | clear; lia].

    Lemma inv_exit : forall j0 j1 j2 j3 j4 j5 j6 wT wM wA wB wX wY j14 j16 j17 ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x23 x25 x26 t3 t4 t5 t6 : word) F1 fc1,
      CENV (ifr j0 j1 j2 j3 j4 j5 j6 wT wM wA wB wX wY (CB 8 j14) j16 j17) 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
      implA (BN_CTX_end ops lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 f) x20 (Z_to_bv 64 aR) (Z_to_bv 64 pn) x23 (Z_to_bv 64 ac) x25 x26 (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
            F1 (wz 0x23274c) fc1 None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc1. intros ENVK LSK.
      unfold MallocRep.wz.
      apply implA_from_evt. do 3 step. apply evt_done.
      eapply (KCALLL _ _ Q _ 0 0 0 BN_CTX_END_STACK); [exact ES0 | exact ENVK | exact LSK | clear - LOF STK_END; lia | clear; lia | exact TOT0
        | intros PRE UW; eapply BN_CTX_end_walkA; [exact PRE | reflexivity | exact HPC | reflexivity]
        | intros v b o p a; cbv beta; intros [E _]; exact E |].
      intros u Σ' ls' m' OW' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F' fc' ENV' LS' RS'; cbv beta; intros (_ & EOW).
      retpc 2303492.
      apply implA_from_evt. step. apply evt_done.
      destruct u. eapply EPI; [exact ENV' | exact LS'].
    Qed.

    Lemma env_bounds : forall pre used Σ ls m OW, CENV pre used Σ ls m OW ->
      bv_unsigned (Z_to_bv 64 FB) = FB /\ bv_unsigned (Z_to_bv 64 SPv) = SPv /\ 12554240 <= FB /\ FB + 16 <= SPv /\ SPv + 16 <= 140737488355328.
    Proof using.
      intros pre used Σ ls m OW ENV. destruct (ESPs LB PL lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 _ _ _ _ _ _ ENV) as (E1 & E2).
      destruct ENV as ((CEIL & LOFB & FBSP & SPT & _) & HEAP & _). pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _).
      unfold SEGTOP_A, USTACK_TOP in *. split; [exact E2|]. split; [exact E1|]. clear - C1 CEIL LOFB FBSP SPT. lia.
    Qed.

    Lemma env_ok_of : forall pre used Σ ls m OW r a, CENV pre used Σ ls m OW -> lib_state ls m OW PL EA -> ref_at ls OW PL r a -> r <> ROne ->
      bg_ok (getbn r ls) /\ 0 < a < 2^47.
    Proof using LOF CS16.
      intros pre used Σ ls m OW r a ENV LS HA NRO.
      destruct (open_for_call LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOF16 _ _ _ _ _ _ _ _ ENV LS HA NRO)
        as (D & _ & OKB & _ & _ & _ & SEP & _ & _ & _ & _ & _ & A0).
      destruct (env_bounds _ _ _ _ _ _ ENV) as (_ & _ & _ & B2 & B3).
      split; [exact OKB|]. change (2^47) with 140737488355328. clear - SEP A0 B2 B3. lia.
    Qed.

    Lemma cenv_recast : forall pre pre' used Σ ls m OW, CENV pre used Σ ls m OW ->
      cells_wf pre' -> cells_bytes pre' = cells_bytes pre -> cells_size pre' = cells_size pre -> CENV pre' used Σ ls m OW.
    Proof using.
      intros pre pre' used Σ ls m OW (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) W EB ES.
      unfold cenvA. split; [exact OK|]. split; [exact HEAP|]. split; [exact ST|]. split; [exact MI|]. split; [exact AXP|]. split; [exact CR|].
      split; [exact CNT|]. split; [exact RS|]. split; [| split; [rewrite ES; exact FSZ | exact UW]].
      pose proof FR as [[WF _] _]. apply cells_wf_app in WF as [_ WT].
      apply (rw_cells_recast m FB _ _ FR); [apply cells_wf_app; split; [exact W | exact WT] | rewrite !cells_bytes_app, EB; reflexivity | rewrite !cells_size_app, ES; reflexivity].
    Qed.

    Section Loops.
      Variables (rA rB rX rY : bnref) (aA aB aX aY aT aM : Z) (j0 j1 j2 j3 j4 j5 j6 j16 j17 : list byte).
      Hypothesis HPA : hpl PL rA.
      Hypothesis HPB : hpl PL rB.
      Hypothesis HPX : hpl PL rX.
      Hypothesis HPY : hpl PL rY.

      Notation IFR := (ifr j0 j1 j2 j3 j4 j5 j6 (Z_to_bv 64 aT) (Z_to_bv 64 aM) (Z_to_bv 64 aA) (Z_to_bv 64 aB) (Z_to_bv 64 aX) (Z_to_bv 64 aY) (C8 (Z_to_bv 64 ac)) j16 j17).
      Notation IFRJ j14 := (ifr j0 j1 j2 j3 j4 j5 j6 (Z_to_bv 64 aT) (Z_to_bv 64 aM) (Z_to_bv 64 aA) (Z_to_bv 64 aB) (Z_to_bv 64 aX) (Z_to_bv 64 aY) (CB 8 j14) j16 j17).
      Definition IREFS (lsK : ST) (OWK : list block) : Prop :=
        ref_at lsK OWK PL rA aA /\ ref_at lsK OWK PL rB aB /\ ref_at lsK OWK PL rX aX /\ ref_at lsK OWK PL rY aY
        /\ ref_at lsK OWK PL rn an /\ ref_at lsK OWK PL rR aR.
      Lemma irefs_stable : forall lsK OWK ls' OW', IREFS lsK OWK -> refs_stable lsK OWK ls' OW' -> IREFS ls' OW'.
      Proof using.
        intros lsK OWK ls' OW' (H1 & H2 & H3 & H4 & H5 & H6) RS.
        repeat split; eapply (ref_at_stable _ _ _ _ PL _ _ RS); assumption.
      Qed.

      Notation IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x25 x26 t3 t4 t5 t6 F pc fc mem :=
        (MS (mkR rax (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 aR) (Z_to_bv 64 pn) (Z_to_bv 64 an) x24 x25 x26 (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
            F (Z_to_bv 64 pc) fc None mem (seg_rom bgbsegs)).

      Definition SHQ (pcq : Z) (lsK : ST) (OWK : list block) (lo25 hi25 : Z) (r : Z * ST) (Σ' : rts RT) (ms' : machine_state) : Prop :=
        exists mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x26 t3 t4 t5 t6 : word) F' fc',
          ms' = IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 (Z_to_bv 64 (fst r)) x26 t3 t4 t5 t6 F' pcq fc' mK'
          /\ CENV IFR 0 Σ' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA /\ refs_stable lsK OWK (snd r) OWK' /\ lo25 <= fst r <= hi25.

      Lemma shl_O : forall r1 r2 r3 shift (lsK : ST), inv_shift_loop ops 0 r1 r2 r3 shift lsK = bunr ops lsK.
      Proof using. reflexivity. Qed.
      Lemma shl_S : forall fu r1 r2 r3 shift (lsK : ST),
        inv_shift_loop ops (S fu) r1 r2 r3 shift lsK =
        if is_bit_set_pure (getbn r1 lsK) shift then bret ops shift lsK
        else bbind ops (if is_odd_pure (getbn r2 lsK) then BN_uadd ops r2 r2 r3 else bret ops tt)
               (fun _ => bbind ops (BN_rshift1 ops r2 r2) (fun _ => inv_shift_loop ops fu r1 r2 r3 (shift + 1))) lsK.
      Proof using. intros. cbn [inv_shift_loop]. rewrite bbind_get. destruct (is_bit_set_pure (getbn r1 lsK) shift); [reflexivity|]. rewrite bbind_get. reflexivity. Qed.

      Local Ltac fr_of ENV FRc := pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & FRc & _); unfold ifr, ifrc in FRc; cbn [app] in FRc.
      Local Ltac sh_norm SH0 SHF sh :=
        rewrite (unsigned_lit sh) by (clear - SH0 SHF; change (2^30) with 1073741824 in SHF; lia);
        rewrite (bn_swrap32_small (sh + 1)) by (clear - SH0 SHF; change (2^30) with 1073741824 in SHF; lia).

      Lemma shift1_loop : forall fu shift ΣK lsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x26 t3 t4 t5 t6 : word) F1 fc1,
        CENV IFR 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> IREFS lsK OWK ->
        0 <= shift -> shift + Z.of_nat fu < 2^30 ->
        implA (inv_shift_loop ops fu rB rX rn shift lsK) ΣK (SHQ 0x232498 lsK OWK shift (shift + Z.of_nat fu))
          (IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 (Z_to_bv 64 shift) x26 t3 t4 t5 t6 F1 0x232488 fc1 mK).
      Proof.
        induction fu as [|fu IH]; intros until fc1; intros ENVK LSK IR SH0 SHF.
        { rewrite shl_O. unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
        pose proof IR as (HAA & HAB & HAX & HAY & HAN & HAR).
        destruct (env_bounds _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
        rewrite shl_S.
        apply implA_from_evt. fr_of ENVK FRc. do 3 step. clear FRc.
        eapply KBIT; [exact ENVK | exact LSK | exact HAB | exact (proj1 HPB) | clear - SH0 SHF; change (2^30) with 1073741824 in SHF; lia |].
        intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
        retpc 2303124.
        destruct (is_bit_set_pure (getbn rB lsK) shift) eqn:EB; cbn [Z.b2z].
        - step. if_false.
          apply evt_done. unfold bret. cbn [ret tree_ops]. apply implA_ret.
          unfold SHQ. exists m1, OWK. do 20 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact ENV1|]. split; [exact LS1|]. split; [apply refs_stable_refl|]. clear - SH0. lia.
        - step. if_true.
          step. sh_norm SH0 SHF shift.
          ub. fr_of ENV1 FRc. do 3 step. clear FRc.
          eapply KODD; [exact ENV1 | exact LS1 | exact HAX | exact (proj1 HPX) |].
          intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
          retpc 2303260.
          assert (JOIN : forall ΣJ lsJ mJ OWJ (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) FJ fcJ,
                    CENV IFR 0 ΣJ lsJ mJ OWJ -> lib_state lsJ mJ OWJ PL EA -> refs_stable lsK OWK lsJ OWJ ->
                    implA (bbind ops (BN_rshift1 ops rX rX) (fun _ => inv_shift_loop ops fu rB rX rn (shift + 1)) lsJ) ΣJ
                      (SHQ 0x232498 lsK OWK shift (shift + Z.of_nat (S fu)))
                      (IMS rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x24 (Z_to_bv 64 aX) (Z_to_bv 64 (shift + 1)) t3' t4' t5' t6' FJ 0x232534 fcJ mJ)).
          { intros until fcJ. intros ENVJ LSJ RSJ.
            pose proof (irefs_stable _ _ _ _ IR RSJ) as IRJ. pose proof IRJ as (HAAj & HABj & HAXj & HAYj & HANj & HARj).
            apply implA_from_evt. do 3 step. apply evt_done.
            eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENVJ | exact LSJ | exact LOF | mc0 | exact TOT0
              | intros PRE UW; eapply BN_rshift1_walkA; [exact PRE | exact UW | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232358 CTX)
                                                         | reflexivity | exact HAXj | exact (hpl_wref PL rX HPX) | reflexivity | reflexivity]
              | hres |].
            intros u Σ2 ls2 m2' OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F2 fc2 ENV2' LS2' RS2 RES2. hnf in RES2. destruct RES2 as (_ & -> & _). unfold MallocRep.wz.
            retpc 2303296.
            apply implA_from_evt. step. step. if_true. apply evt_done.
            eapply implA_mono.
            { eapply IH; [exact ENV2' | exact LS2' | exact (irefs_stable _ _ _ _ IRJ RS2) | clear - SH0; lia | clear - SHF; rewrite Nat2Z.inj_succ in SHF; lia]. }
            cbv beta. intros r Σ' ms' (mK' & OWK' & R).
            destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3 & K4).
            unfold SHQ. exists mK', OWK'. do 20 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2|].
            split; [eapply refs_stable_trans; [exact RSJ| eapply refs_stable_trans; [exact RS2| exact K3]]|].
            clear - K4. rewrite Nat2Z.inj_succ. lia. }
          destruct (is_odd_pure (getbn rX lsK)) eqn:EO; cbn [Z.b2z].
          + step. if_false. do 4 step. apply evt_done.
            eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV2 | exact LS2 | exact LOF | mc0 | exact TOT0
              | intros PRE UW; eapply BN_uadd_walkA; [pre_wk PRE STK_UADD | exact UW
                                                      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232348 CTX)
                                                      | reflexivity | exact HAX | exact HPX | exact HAX | exact (proj1 HPX)
                                                      | exact HAN | exact NROn | reflexivity | reflexivity | reflexivity]
              | hres |].
            intros u Σ3 ls3 m3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F3 fc3 ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & -> & _). unfold MallocRep.wz.
            retpc 2303280.
            apply implA_from_evt. step. if_false. apply evt_done.
            eapply JOIN; [exact ENV3 | exact LS3 | exact RS3].
          + step. if_true. apply evt_done. rewrite bbind_ret.
            eapply JOIN; [exact ENV2 | exact LS2 | apply refs_stable_refl].
      Qed.

      Lemma shift2_loop : forall fu shift ΣK lsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x26 t3 t4 t5 t6 : word) F1 fc1,
        CENV IFR 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> IREFS lsK OWK ->
        0 <= shift -> shift + Z.of_nat fu < 2^30 ->
        implA (inv_shift_loop ops fu rA rY rn shift lsK) ΣK (SHQ 0x23254c lsK OWK shift (shift + Z.of_nat fu))
          (IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 (Z_to_bv 64 shift) x26 t3 t4 t5 t6 F1 0x2324b4 fc1 mK).
      Proof.
        induction fu as [|fu IH]; intros until fc1; intros ENVK LSK IR SH0 SHF.
        { rewrite shl_O. unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
        pose proof IR as (HAA & HAB & HAX & HAY & HAN & HAR).
        destruct (env_bounds _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
        rewrite shl_S.
        apply implA_from_evt. fr_of ENVK FRc. do 3 step. clear FRc.
        eapply KBIT; [exact ENVK | exact LSK | exact HAA | exact (proj1 HPA) | clear - SH0 SHF; change (2^30) with 1073741824 in SHF; lia |].
        intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
        retpc 2303168.
        destruct (is_bit_set_pure (getbn rA lsK) shift) eqn:EB; cbn [Z.b2z].
        - step. if_true.
          apply evt_done. unfold bret. cbn [ret tree_ops]. apply implA_ret.
          unfold SHQ. exists m1, OWK. do 20 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact ENV1|]. split; [exact LS1|]. split; [apply refs_stable_refl|]. clear - SH0. lia.
        - step. if_false.
          step. sh_norm SH0 SHF shift.
          ub. fr_of ENV1 FRc. do 3 step. clear FRc.
          eapply KODD; [exact ENV1 | exact LS1 | exact HAY | exact (proj1 HPY) |].
          intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
          retpc 2303192.
          assert (JOIN : forall ΣJ lsJ mJ OWJ (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) FJ fcJ,
                    CENV IFR 0 ΣJ lsJ mJ OWJ -> lib_state lsJ mJ OWJ PL EA -> refs_stable lsK OWK lsJ OWJ ->
                    implA (bbind ops (BN_rshift1 ops rY rY) (fun _ => inv_shift_loop ops fu rA rY rn (shift + 1)) lsJ) ΣJ
                      (SHQ 0x23254c lsK OWK shift (shift + Z.of_nat (S fu)))
                      (IMS rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (shift + 1)) (Z_to_bv 64 aY) x26 t3' t4' t5' t6' FJ 0x2324f0 fcJ mJ)).
          { intros until fcJ. intros ENVJ LSJ RSJ.
            pose proof (irefs_stable _ _ _ _ IR RSJ) as IRJ. pose proof IRJ as (HAAj & HABj & HAXj & HAYj & HANj & HARj).
            apply implA_from_evt. do 3 step. apply evt_done.
            eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENVJ | exact LSJ | exact LOF | mc0 | exact TOT0
              | intros PRE UW; eapply BN_rshift1_walkA; [exact PRE | exact UW | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232314 CTX)
                                                         | reflexivity | exact HAYj | exact (hpl_wref PL rY HPY) | reflexivity | reflexivity]
              | hres |].
            intros u Σ2 ls2 m2' OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F2 fc2 ENV2' LS2' RS2 RES2. hnf in RES2. destruct RES2 as (_ & -> & _). unfold MallocRep.wz.
            retpc 2303228.
            apply implA_from_evt. step. step. if_false. step. apply evt_done.
            eapply implA_mono.
            { eapply IH; [exact ENV2' | exact LS2' | exact (irefs_stable _ _ _ _ IRJ RS2) | clear - SH0; lia | clear - SHF; rewrite Nat2Z.inj_succ in SHF; lia]. }
            cbv beta. intros r Σ' ms' (mK' & OWK' & R).
            destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3 & K4).
            unfold SHQ. exists mK', OWK'. do 20 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2|].
            split; [eapply refs_stable_trans; [exact RSJ| eapply refs_stable_trans; [exact RS2| exact K3]]|].
            clear - K4. rewrite Nat2Z.inj_succ. lia. }
          destruct (is_odd_pure (getbn rY lsK)) eqn:EO; cbn [Z.b2z].
          + step. if_false. do 4 step. apply evt_done.
            eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV2 | exact LS2 | exact LOF | mc0 | exact TOT0
              | intros PRE UW; eapply BN_uadd_walkA; [pre_wk PRE STK_UADD | exact UW
                                                      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232304 CTX)
                                                      | reflexivity | exact HAY | exact HPY | exact HAY | exact (proj1 HPY)
                                                      | exact HAN | exact NROn | reflexivity | reflexivity | reflexivity]
              | hres |].
            intros u Σ3 ls3 m3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F3 fc3 ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & -> & _). unfold MallocRep.wz.
            retpc 2303212.
            apply implA_from_evt. step. if_false. apply evt_done.
            eapply JOIN; [exact ENV3 | exact LS3 | exact RS3].
          + step. if_true. apply evt_done. rewrite bbind_ret.
            eapply JOIN; [exact ENV2 | exact LS2 | apply refs_stable_refl].
      Qed.

      Definition inv_iter_k {C : Type} (K : BM (M := btree bptr) C) (nb : Z) : BM (M := btree bptr) C :=
        bbind ops (inv_shift_loop ops (Z.to_nat nb + 1) rB rX rn 0) (fun shift =>
        bbind ops (if 0 <? shift then BN_rshift ops rB rB shift else bret ops tt) (fun _ =>
        bbind ops (bget ops rA) (fun a =>
        bbind ops (inv_shift_loop ops (Z.to_nat (num_bits_pure a) + 1) rA rY rn 0) (fun shift =>
        bbind ops (if 0 <? shift then BN_rshift ops rA rA shift else bret ops tt) (fun _ =>
        bbind ops (BN_ucmp ops rB rA) (fun c =>
        bbind ops (if 0 <=? c then bbind ops (BN_uadd ops rX rX rY) (fun _ => BN_usub ops rB rB rA)
                   else bbind ops (BN_uadd ops rY rY rX) (fun _ => BN_usub ops rA rA rB)) (fun _ => K))))))).

      Lemma bin_O : forall (lsK : ST), inv_binary_loop ops 0 rA rB rX rY rn lsK = bunr ops lsK.
      Proof using. reflexivity. Qed.
      Lemma bin_S : forall fu (lsK : ST),
        inv_binary_loop ops (S fu) rA rB rX rY rn lsK =
        if is_zero_pure (getbn rB lsK) then bret ops tt lsK
        else inv_iter_k (inv_binary_loop ops fu rA rB rX rY rn) (num_bits_pure (getbn rB lsK)) lsK.
      Proof using. intros. cbn [inv_binary_loop]. rewrite bbind_get. destruct (is_zero_pure (getbn rB lsK)); reflexivity. Qed.

      Definition XQ (pcq : Z) (lsK : ST) (OWK : list block) (r : unit * ST) (Σ' : rts RT) (ms' : machine_state) : Prop :=
        exists mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x26 t3 t4 t5 t6 : word) F' fc',
          ms' = IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 aB) x25 x26 t3 t4 t5 t6 F' pcq fc' mK'
          /\ CENV IFR 0 Σ' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA /\ refs_stable lsK OWK (snd r) OWK'.

      Local Ltac shpos KS SH30 := rewrite ?signed_small in KS by (clear - SH30; change (2^30) with 1073741824 in SH30; lia).

      Lemma iter_body : forall {C : Type} (K : BM (M := btree bptr) C) (QK : C * ST -> rts RT -> machine_state -> Prop) nb ΣK lsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 x26 t3 t4 t5 t6 : word) F1 fc1,
        CENV IFR 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> IREFS lsK OWK -> 0 <= nb <= 32768 ->
        (forall ΣJ lsJ mJ OWJ (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x25' x26' t3' t4' t5' t6' : word) FJ fcJ,
            CENV IFR 0 ΣJ lsJ mJ OWJ -> lib_state lsJ mJ OWJ PL EA -> refs_stable lsK OWK lsJ OWJ ->
            implA (K lsJ) ΣJ QK
              (IMS rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 aB) x25' x26' t3' t4' t5' t6' FJ 0x2325c8 fcJ mJ)) ->
        implA (inv_iter_k K nb lsK) ΣK QK
          (IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x24 (Z_to_bv 64 0) x26 t3 t4 t5 t6 F1 0x232488 fc1 mK).
      Proof.
        intros until fc1. intros ENVK LSK IR NB KK.
        destruct (env_bounds _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
        unfold inv_iter_k.

        assert (J3 : forall Σ3 ls3 m3 OW3 (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x24' x25' x26' t3' t4' t5' t6' : word) F3 fc3,
                  CENV IFR 0 Σ3 ls3 m3 OW3 -> lib_state ls3 m3 OW3 PL EA -> refs_stable lsK OWK ls3 OW3 ->
                  implA (bbind ops (BN_ucmp ops rB rA) (fun c =>
                         bbind ops (if 0 <=? c then bbind ops (BN_uadd ops rX rX rY) (fun _ => BN_usub ops rB rB rA)
                                    else bbind ops (BN_uadd ops rY rY rX) (fun _ => BN_usub ops rA rA rB)) (fun _ => K)) ls3) Σ3 QK
                    (IMS rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x24' x25' x26' t3' t4' t5' t6' F3 0x232564 fc3 m3)).
        { intros until fc3. intros ENV3 LS3 RS3.
          pose proof (irefs_stable _ _ _ _ IR RS3) as IR3. pose proof IR3 as (HAA & HAB & HAX & HAY & HAN & HAR).
          apply implA_from_evt. fr_of ENV3 FRc. do 3 step. clear FRc. apply evt_done.
          eapply (KCALL _ _ _ _ _ 0 0 0 CS); [exact ES0 | exact ENV3 | exact LS3 | exact LOF | clear; lia | exact TOT0
            | intros PRE UW; eapply BN_ucmp_walkA; [pre_wk PRE STK_UCMP | reflexivity | exact HAB | exact HAA
                                                     | exact (proj1 HPB) | exact (proj1 HPA) | reflexivity | reflexivity]
            | intros ? ? ? ? ? HRES; exact (proj1 (proj1 HRES)) |].
          intros c Σ4 ls4 m4 OW4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F4 fc4 ENV4 LS4 RS4 RES4. destruct RES4 as ((_ & -> & CR & _ & _) & _).
          pose proof (irefs_stable _ _ _ _ IR3 RS4) as IR4. pose proof IR4 as (HAA4 & HAB4 & HAX4 & HAY4 & HAN4 & HAR4).
          retpc 2303344.
          eapply implA_bind with (Q1 := XQ 0x2325c8 ls4 OW4).
          2:{ cbv beta. intros [u ls5] Σ5 ms5 (m5 & OW5 & R).
              destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENV5 & LS5 & RS5). cbn [fst snd] in *.
              eapply KK; [exact ENV5 | exact LS5 | eapply refs_stable_trans; [exact RS3| eapply refs_stable_trans; [exact RS4| exact RS5]]]. }
          apply implA_from_evt.
          step. rewrite lts_signed by (clear - CR; lia).
          destruct (Z.ltb_spec c 0) as [CN|CP]; cbn [negb].
          -
            replace (0 <=? c) with false by (symmetry; apply Z.leb_gt; exact CN).
            fr_of ENV4 FRc. do 4 step. clear FRc. apply evt_done.
            eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV4 | exact LS4 | exact LOF | mc0 | exact TOT0
              | intros PRE UW; eapply BN_uadd_walkA; [pre_wk PRE STK_UADD | exact UW
                                                      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_2323c4 CTX)
                                                      | reflexivity | exact HAY4 | exact HPY | exact HAY4 | exact (proj1 HPY)
                                                      | exact HAX4 | exact (proj1 HPX) | reflexivity | reflexivity | reflexivity]
              | hres |].
            intros u Σ6 ls6 m6 OW6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F6 fc6 ENV6 LS6 RS6 RES6. hnf in RES6. destruct RES6 as (_ & -> & _). unfold MallocRep.wz.
            pose proof (irefs_stable _ _ _ _ IR4 RS6) as IR6. pose proof IR6 as (HAA6 & HAB6 & HAX6 & HAY6 & HAN6 & HAR6).
            retpc 2303404.
            apply implA_from_evt. step. if_false. fr_of ENV6 FRc. do 5 step. clear FRc. apply evt_done.
            eapply (KCALLE _ _ (XQ 0x2325c8 ls4 OW4) _ 0 MC 0 CS); [exact ES0 | exact ENV6 | exact LS6 | exact LOF | mc0 | exact TOT0
              | intros PRE UW; eapply BN_usub_walkA; [pre_wk PRE STK_USUB | exact UW
                                                      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_2323dc CTX)
                                                      | reflexivity | exact HAA6 | exact HPA | exact HAA6 | exact (proj1 HPA)
                                                      | exact HAB6 | exact (proj1 HPB) | reflexivity | reflexivity | reflexivity]
              | hres |].
            intros u' Σ7 ls7 m7 OW7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F7 fc7 ENV7 LS7 RS7 RES7. hnf in RES7. destruct RES7 as (_ & -> & _). unfold MallocRep.wz.
            retpc 2303428.
            step. if_false.
            apply evt_done. unfold XQ. exists m7, OW7. do 20 eexists. split; [reflexivity|]. cbn [fst snd].
            split; [exact ENV7|]. split; [exact LS7|]. eapply refs_stable_trans; [exact RS6| exact RS7].
          -
            replace (0 <=? c) with true by (symmetry; apply Z.leb_le; exact CP).
            fr_of ENV4 FRc. do 4 step. clear FRc. apply evt_done.
            eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV4 | exact LS4 | exact LOF | mc0 | exact TOT0
              | intros PRE UW; eapply BN_uadd_walkA; [pre_wk PRE STK_UADD | exact UW
                                                      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_23239c CTX)
                                                      | reflexivity | exact HAX4 | exact HPX | exact HAX4 | exact (proj1 HPX)
                                                      | exact HAY4 | exact (proj1 HPY) | reflexivity | reflexivity | reflexivity]
              | hres |].
            intros u Σ6 ls6 m6 OW6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F6 fc6 ENV6 LS6 RS6 RES6. hnf in RES6. destruct RES6 as (_ & -> & _). unfold MallocRep.wz.
            pose proof (irefs_stable _ _ _ _ IR4 RS6) as IR6. pose proof IR6 as (HAA6 & HAB6 & HAX6 & HAY6 & HAN6 & HAR6).
            retpc 2303364.
            apply implA_from_evt. step. if_false. fr_of ENV6 FRc. do 6 step. clear FRc. apply evt_done.
            eapply (KCALLE _ _ (XQ 0x2325c8 ls4 OW4) _ 0 MC 0 CS); [exact ES0 | exact ENV6 | exact LS6 | exact LOF | mc0 | exact TOT0
              | intros PRE UW; eapply BN_usub_walkA; [pre_wk PRE STK_USUB | exact UW
                                                      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_2323dc CTX)
                                                      | reflexivity | exact HAB6 | exact HPB | exact HAB6 | exact (proj1 HPB)
                                                      | exact HAA6 | exact (proj1 HPA) | reflexivity | reflexivity | reflexivity]
              | hres |].
            intros u' Σ7 ls7 m7 OW7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F7 fc7 ENV7 LS7 RS7 RES7. hnf in RES7. destruct RES7 as (_ & -> & _). unfold MallocRep.wz.
            retpc 2303428.
            step. if_false.
            apply evt_done. unfold XQ. exists m7, OW7. do 20 eexists. split; [reflexivity|]. cbn [fst snd].
            split; [exact ENV7|]. split; [exact LS7|]. eapply refs_stable_trans; [exact RS6| exact RS7]. }

        assert (J2 : forall Σ2 ls2 m2 OW2 (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x24' x25' x26' t3' t4' t5' t6' : word) F2 fc2,
                  CENV IFR 0 Σ2 ls2 m2 OW2 -> lib_state ls2 m2 OW2 PL EA -> refs_stable lsK OWK ls2 OW2 ->
                  implA (bbind ops (bget ops rA) (fun a =>
                         bbind ops (inv_shift_loop ops (Z.to_nat (num_bits_pure a) + 1) rA rY rn 0) (fun shift =>
                         bbind ops (if 0 <? shift then BN_rshift ops rA rA shift else bret ops tt) (fun _ =>
                         bbind ops (BN_ucmp ops rB rA) (fun c =>
                         bbind ops (if 0 <=? c then bbind ops (BN_uadd ops rX rX rY) (fun _ => BN_usub ops rB rB rA)
                                    else bbind ops (BN_uadd ops rY rY rX) (fun _ => BN_usub ops rA rA rB)) (fun _ => K))))) ls2) Σ2 QK
                    (IMS rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x24' x25' x26' t3' t4' t5' t6' F2 0x2324b0 fc2 m2)).
        { intros until fc2. intros ENV2 LS2 RS2.
          pose proof (irefs_stable _ _ _ _ IR RS2) as IR2. pose proof IR2 as (HAA & HAB & HAX & HAY & HAN & HAR).
          rewrite bbind_get.
          destruct (env_ok_of _ _ _ _ _ _ rA aA ENV2 LS2 HAA (proj1 HPA)) as (OKA & _).
          pose proof (nbits_range _ OKA) as NBA. clear OKA.
          apply implA_from_evt. step. apply evt_done.
          unfold bbind at 1. cbn [bind tree_ops]. eapply implA_bind.
          { eapply (shift2_loop (Z.to_nat (num_bits_pure (getbn rA ls2)) + 1) 0); [exact ENV2 | exact LS2 | exact IR2 | clear; lia
              | clear - NBA; change (2^30) with 1073741824; lia]. }
          cbv beta. intros [sh ls3] Σ3 ms3 (m3 & OW3 & R).
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENV3 & LS3 & RS3 & SHR). cbn [fst snd] in *.
          pose proof (irefs_stable _ _ _ _ IR2 RS3) as IR3. pose proof IR3 as (HAA3 & HAB3 & HAX3 & HAY3 & HAN3 & HAR3).
          assert (SH30 : 0 <= sh < 2^30) by (clear - SHR NBA; change (2^30) with 1073741824; lia).
          apply implA_from_evt.
          step. if_cases KS; shpos KS SH30; zify_cond KS;
          [apply Bool.andb_false_iff in KS; assert (KS0 : sh <= 0) by (destruct KS as [KS|KS]; apply Z.ltb_ge in KS; clear - KS SH30; change (2^30) with 1073741824 in SH30; lia); clear KS; rename KS0 into KS
          | rename KS0 into KS].
          -
            replace (0 <? sh) with false by (symmetry; apply Z.ltb_ge; clear - KS; lia).
            apply evt_done. rewrite bbind_ret.
            eapply J3; [exact ENV3 | exact LS3 | eapply refs_stable_trans; [exact RS2| exact RS3]].
          - replace (0 <? sh) with true by (symmetry; apply Z.ltb_lt; clear - KS SH30; lia).
            fr_of ENV3 FRc. do 4 step. clear FRc. apply evt_done.
            eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV3 | exact LS3 | exact LOF | mc0 | exact TOT0
              | intros PRE UW; eapply BN_rshift_walkA; [pre_wk PRE STK_RSH | exact UW
                                                        | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232378 CTX)
                                                        | reflexivity | exact HAA3 | exact HPA | exact HAA3 | exact (proj1 HPA) | exact (hpl_nbuf PL rA HPA)
                                                        | reflexivity | reflexivity | reflexivity | clear - SH30; change (2^31) with 2147483648; change (2^30) with 1073741824 in *; lia]
              | hres |].
            intros u Σ4 ls4 m4 OW4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F4 fc4 ENV4 LS4 RS4 RES4. hnf in RES4. destruct RES4 as (_ & -> & _). unfold MallocRep.wz.
            retpc 2303328.
            apply implA_from_evt. step. if_false. apply evt_done.
            eapply J3; [exact ENV4 | exact LS4 | eapply refs_stable_trans; [exact RS2| eapply refs_stable_trans; [exact RS3| exact RS4]]]. }

        pose proof IR as (HAA & HAB & HAX & HAY & HAN & HAR).
        unfold bbind at 1. cbn [bind tree_ops]. eapply implA_bind.
        { eapply (shift1_loop (Z.to_nat nb + 1) 0); [exact ENVK | exact LSK | exact IR | clear; lia | clear - NB; change (2^30) with 1073741824; lia]. }
        cbv beta. intros [sh ls1] Σ1 ms1 (m1 & OW1 & R).
        destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENV1 & LS1 & RS1 & SHR). cbn [fst snd] in *.
        pose proof (irefs_stable _ _ _ _ IR RS1) as IR1. pose proof IR1 as (HAA1 & HAB1 & HAX1 & HAY1 & HAN1 & HAR1).
        assert (SH30 : 0 <= sh < 2^30) by (clear - SHR NB; change (2^30) with 1073741824; lia).
        apply implA_from_evt.
        step. if_cases KS; shpos KS SH30; zify_cond KS;
          [apply Bool.andb_false_iff in KS; assert (KS0 : sh <= 0) by (destruct KS as [KS|KS]; apply Z.ltb_ge in KS; clear - KS SH30; change (2^30) with 1073741824 in SH30; lia); clear KS; rename KS0 into KS
          | rename KS0 into KS].
        - replace (0 <? sh) with false by (symmetry; apply Z.ltb_ge; clear - KS; lia).
          apply evt_done. rewrite bbind_ret.
          eapply J2; [exact ENV1 | exact LS1 | exact RS1].
        - replace (0 <? sh) with true by (symmetry; apply Z.ltb_lt; clear - KS SH30; lia).
          fr_of ENV1 FRc. do 4 step. clear FRc. apply evt_done.
          eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV1 | exact LS1 | exact LOF | mc0 | exact TOT0
            | intros PRE UW; eapply BN_rshift_walkA; [pre_wk PRE STK_RSH | exact UW
                                                      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_2322c4 CTX)
                                                      | reflexivity | exact HAB1 | exact HPB | exact HAB1 | exact (proj1 HPB) | exact (hpl_nbuf PL rB HPB)
                                                      | reflexivity | reflexivity | reflexivity | clear - SH30; change (2^31) with 2147483648; change (2^30) with 1073741824 in *; lia]
            | hres |].
          intros u Σ2 ls2 m2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F2 fc2 ENV2 LS2 RS2 RES2. hnf in RES2. destruct RES2 as (_ & -> & _). unfold MallocRep.wz.
          retpc 2303148.
          apply implA_from_evt. step. if_false. apply evt_done.
          eapply J2; [exact ENV2 | exact LS2 | eapply refs_stable_trans; [exact RS1| exact RS2]].
      Qed.

      Ltac fr_unf H ::= unfold ifr, ifrc in H.

      Definition PLQ (lsK : ST) (OWK : list block) (r : unit * ST) (Σ' : rts RT) (ms' : machine_state) : Prop :=
        exists mK' OWK' j14 (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
          ms' = IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ac) (Z_to_bv 64 aY) (Z_to_bv 64 aA) t3 t4 t5 t6 F' 0x232764 fc' mK'
          /\ CENV (IFRJ j14) 0 Σ' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA /\ refs_stable lsK OWK (snd r) OWK'.

      Lemma ifr_recast : forall used Σ ls m OW, CENV IFR used Σ ls m OW -> CENV (IFRJ (le8 (Z_to_bv 64 ac))) used Σ ls m OW.
      Proof.
        intros used Σ ls m OW ENV. eapply cenv_recast; [exact ENV | | reflexivity | reflexivity].
        destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & FRc & _). destruct FRc as [[WFc _] _]. apply cells_wf_app in WFc as [WFc _].
        unfold ifr, ifrc in WFc |- *. cbn [cells_wf cell_wf] in WFc |- *. intuition auto.
      Qed.

      Lemma bin_check : forall fu ΣK lsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 x26 t3 t4 t5 t6 : word) F1 fc1,
        CENV IFR 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> IREFS lsK OWK ->
        implA (inv_binary_loop ops fu rA rB rX rY rn lsK) ΣK (PLQ lsK OWK)
          (IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 aB) x25 x26 t3 t4 t5 t6 F1 0x2325c8 fc1 mK).
      Proof.
        induction fu as [|fu IH]; intros until fc1; intros ENVK LSK IR.
        { rewrite bin_O. unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
        pose proof IR as (HAA & HAB & HAX & HAY & HAN & HAR).
        destruct (env_bounds _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
        rewrite bin_S.
        apply implA_from_evt. do 2 step.
        eapply KZERO; [exact ENVK | exact LSK | exact HAB | exact (proj1 HPB) |].
        intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1.
        retpc 2303440.
        step. fr_of ENV1 FRc. step.
        change (is_zero_pure (getbn rB lsK)) with ((bn_top (getbn rB lsK) =? 0)%nat).
        destruct ((bn_top (getbn rB lsK) =? 0)%nat) eqn:EZ; cbn [Z.b2z].
        - step. if_false. do 3 step. clear FRc.
          apply evt_done. unfold bret. cbn [ret tree_ops]. apply implA_ret.
          unfold PLQ. exists m1, OWK, (le8 (Z_to_bv 64 ac)). do 18 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact (ifr_recast _ _ _ _ _ ENV1)|]. split; [exact LS1|]. apply refs_stable_refl.
        - step. if_true. clear FRc.
          destruct (env_ok_of _ _ _ _ _ _ rB aB ENV1 LS1 HAB (proj1 HPB)) as (OKB & _).
          pose proof (nbits_range _ OKB) as NBB. clear OKB.
          apply evt_done.
          eapply iter_body; [exact ENV1 | exact LS1 | exact IR | exact NBB |].
          intros until fcJ. intros ENVJ LSJ RSJ.
          eapply implA_mono; [eapply IH; [exact ENVJ | exact LSJ | exact (irefs_stable _ _ _ _ IR RSJ)]|].
          cbv beta. intros r Σ' ms' (mK' & OWK' & j14 & R).
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3).
          unfold PLQ. exists mK', OWK', j14. do 18 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2|].
          eapply refs_stable_trans; [exact RSJ| exact K3].
      Qed.

      Lemma bin_top : forall fu j14 ΣK lsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x26 t3 t4 t5 t6 : word) F1 fc1,
        CENV (IFRJ j14) 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> IREFS lsK OWK ->
        implA (inv_binary_loop ops fu rA rB rX rY rn lsK) ΣK (PLQ lsK OWK)
          (IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ac) (Z_to_bv 64 aY) x26 t3 t4 t5 t6 F1 0x232474 fc1 mK).
      Proof.
        intros until fc1; intros ENVK LSK IR.
        destruct fu as [|fu].
        { rewrite bin_O. unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
        pose proof IR as (HAA & HAB & HAX & HAY & HAN & HAR).
        destruct (env_bounds _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
        rewrite bin_S.
        apply implA_from_evt. fr_of ENVK FRc. do 2 step. clear FRc.
        eapply KZERO; [exact ENVK | exact LSK | exact HAB | exact (proj1 HPB) |].
        intros mq1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1.
        retpc 2303100.
        change (is_zero_pure (getbn rB lsK)) with ((bn_top (getbn rB lsK) =? 0)%nat).
        destruct ((bn_top (getbn rB lsK) =? 0)%nat) eqn:EZ; cbn [Z.b2z].
        - step. if_true. fr_of ENV1 FRc. step. clear FRc.
          apply evt_done. unfold bret. cbn [ret tree_ops]. apply implA_ret.
          unfold PLQ. exists mq1, OWK, j14. do 18 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact ENV1|]. split; [exact LS1|]. apply refs_stable_refl.
        - step. if_false. step.
          remember (Z_to_bv 64 ac) as wC eqn:EwC.
          fr_store_gen (cenv_frameA LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0) FB SPv ENV1 LS1 ENV2 LS2. clear ENV1 LS1.
          subst wC.
          destruct (env_ok_of _ _ _ _ _ _ rB aB ENV2 LS2 HAB (proj1 HPB)) as (OKB & _).
          pose proof (nbits_range _ OKB) as NBB. clear OKB.
          apply evt_done.
          eapply iter_body; [exact ENV2 | exact LS2 | exact IR | exact NBB |].
          intros until fcJ. intros ENVJ LSJ RSJ.
          eapply implA_mono; [eapply (bin_check fu); [exact ENVJ | exact LSJ | exact (irefs_stable _ _ _ _ IR RSJ)]|].
          cbv beta. intros r Σ' ms' (mK' & OWK' & j14' & R).
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3).
          unfold PLQ. exists mK', OWK', j14'. do 18 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2|].
          eapply refs_stable_trans; [exact RSJ| exact K3].
      Qed.

      Lemma ucmp_eq : forall r1 r2 (lsK : ST), bg_ok (getbn r1 lsK) -> bg_ok (getbn r2 lsK) ->
        BN_ucmp ops r1 r2 lsK = bret ops (ucmp_pure (getbn r1 lsK) (getbn r2 lsK)) lsK.
      Proof using.
        intros r1 r2 lsK (_ & _ & _ & FLA) (_ & _ & _ & FLB).
        unfold BN_ucmp. rewrite !bbind_get. unfold has_flag.
        assert (EL4A : Z.land (bn_flags (getbn r1 lsK)) BN_FLG_CONSTTIME = 0) by (destruct FLA as [E|E]; rewrite E; reflexivity).
        assert (EL4B : Z.land (bn_flags (getbn r2 lsK)) BN_FLG_CONSTTIME = 0) by (destruct FLB as [E|E]; rewrite E; reflexivity).
        rewrite EL4A, EL4B. reflexivity.
      Qed.
      Lemma ucmp_bind_eq : forall {C : Type} r1 r2 (K : Z -> BM (M := btree bptr) C) (lsK : ST), bg_ok (getbn r1 lsK) -> bg_ok (getbn r2 lsK) ->
        bbind ops (BN_ucmp ops r1 r2) K lsK = K (ucmp_pure (getbn r1 lsK) (getbn r2 lsK)) lsK.
      Proof using. intros C r1 r2 K lsK O1 O2. unfold bbind at 1. rewrite (ucmp_eq r1 r2 lsK O1 O2). reflexivity. Qed.

      Definition EXQ (lsK : ST) (OWK : list block) (r : unit * ST) (Σ' : rts RT) (ms' : machine_state) : Prop :=
        exists mK' OWK' j14 (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x25 x26 t3 t4 t5 t6 : word) F' fc',
          ms' = MS (mkR rax (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 f) (Z_to_bv 64 f) x20 (Z_to_bv 64 aR) (Z_to_bv 64 pn) (Z_to_bv 64 an) (Z_to_bv 64 ac) x25 x26 (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
                   F' (Z_to_bv 64 0x23274c) fc' None mK' (seg_rom bgbsegs)
          /\ CENV (IFRJ j14) 0 Σ' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA /\ refs_stable lsK OWK (snd r) OWK'.

      Lemma inv_fin : forall j14 ΣK lsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F1 fc1,
        CENV (IFRJ j14) 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> IREFS lsK OWK -> 0 < aR < 2^47 ->
        implA (bbind ops (BN_sub ops rY rn rY) (fun _ =>
               bbind ops (bget ops rA) (fun bA =>
               bbind ops (if is_one_pure bA then
                            bbind ops (bget ops rY) (fun y => bbind ops (BN_ucmp ops rY rn) (fun c =>
                            if negb (bn_neg y) && (c <? 0) then BN_copy ops rR rY else BN_nnmod ops rR rY rn))
                          else bunr ops) (fun _ => BN_CTX_end ops))) lsK) ΣK Q
          (IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ac) (Z_to_bv 64 aY) (Z_to_bv 64 aA) t3 t4 t5 t6 F1 0x232764 fc1 mK).
      Proof.
        intros until fc1. intros ENVK LSK IR ARR.
        pose proof IR as (HAA & HAB & HAX & HAY & HAN & HAR).
        destruct (env_bounds _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).
        apply implA_from_evt. do 4 step. apply evt_done.
        eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENVK | exact LSK | exact LOF | mc0 | exact TOT0
          | intros PRE UW; eapply BN_sub_walkA; [pre_wk PRE STK_SUB | exact UW
                                                 | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_23258c CTX)
                                                 | reflexivity | exact HAY | exact HPY | exact HAN | exact NROn
                                                 | exact HAY | exact (proj1 HPY) | reflexivity | reflexivity | reflexivity]
          | hres |].
        intros u Σ1 ls1 mq1 OW1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F2 fc2 ENV1 LS1 RS1 RES1. hnf in RES1. destruct RES1 as (_ & ->). unfold MallocRep.wz.
        pose proof (irefs_stable _ _ _ _ IR RS1) as IR1. pose proof IR1 as (HAA1 & HAB1 & HAX1 & HAY1 & HAN1 & HAR1).
        retpc 2303860.
        rewrite bbind_get.
        destruct (is_one_pure (getbn rA ls1)) eqn:E1.
        2:{ unfold bbind, bunr. cbn [bind unreachable tree_ops tbind]. apply implA_unr. }
        eapply implA_bind with (Q1 := EXQ ls1 OW1).
        2:{ cbv beta. intros [u2 ls5] Σ5 ms5 (m5 & OW5 & j14' & R).
            destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENV5 & LS5 & RS5). cbn [fst snd] in *.
            eapply inv_exit; [exact ENV5 | exact LS5]. }
        rewrite bbind_get.
        apply implA_from_evt. step. if_false. do 2 step.
        eapply KONE; [exact ENV1 | exact LS1 | exact HAA1 | exact (proj1 HPA) |].
        intros mq2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
        retpc 2303872. rewrite E1. cbn [Z.b2z].
        step. if_false.
        destruct (open_for_call LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOF16 _ _ _ _ _ _ rY aY ENV2 LS2 HAY1 (proj1 HPY))
          as (DY & BNY & OKY & _ & _ & _ & SEPY & SHBC & ACCY & ALY & SLO & OFRY & AY0).
        destruct (env_ok_of _ _ _ _ _ _ rn an ENV2 LS2 HAN1 NROn) as (OKN & _).
        destruct (env_ok_of _ _ _ _ _ _ rY aY ENV2 LS2 HAY1 (proj1 HPY)) as (_ & AYR).
        change (2^47) with 140737488355328 in AYR, ARR.
        unfold BnRepDefs.bn_cells, MallocRep.wz in BNY.
        pose proof (munch_refl [] mq2) as MUy.
        ub. do 3 step. shl_with ACCY ALY. chk0.
        step.
        fr_of ENV2 FRc. step. clear FRc.
        clear BNY MUy ACCY.
        assert (NN : forall Σ3 m3 (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x26' t3' t4' t5' t6' : word) F3 fc3,
                  CENV (IFRJ j14) 0 Σ3 ls1 m3 OW1 -> lib_state ls1 m3 OW1 PL EA ->
                  implA (BN_nnmod ops rR rY rn ls1) Σ3 (EXQ ls1 OW1)
                    (MS (mkR rax' (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0r (Z_to_bv 64 FB) a0' a1' a2' a3' a4' a5' a6' a7'
                             (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 aR) (Z_to_bv 64 aR) (Z_to_bv 64 pn) (Z_to_bv 64 an) (Z_to_bv 64 ac) (Z_to_bv 64 aY) x26' (Z_to_bv 64 (shad f)) t3' t4' t5' t6')
                        F3 (Z_to_bv 64 0x2327c0) fc3 None m3 (seg_rom bgbsegs))).
        { intros until fc3. intros ENV3 LS3.
          apply implA_from_evt. do 5 step. apply evt_done.
          eapply (KCALLE _ _ (EXQ ls1 OW1) _ 0 BN_NNMOD_COST 0 CS); [exact ES0 | exact ENV3 | exact LS3 | exact LOF | vm_compute; intro HH; discriminate HH | exact TOT0
            | intros PRE UW; eapply BN_nnmod_walkA; [pre_wk PRE STK_NNMOD | exact UW
                                                     | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_2325ec CTX)
                                                     | reflexivity | exact HAR1 | exact HAY1 | exact HAN1 | exact WRR | exact (proj1 HPY) | exact NROn | exact (hpl_nbuf PL rY HPY) | exact HPC
                                                     | reflexivity | reflexivity | reflexivity | reflexivity]
            | hres |].
          intros u' Σ7 ls7 m7 OW7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F7 fc7 ENV7 LS7 RS7 RES7. hnf in RES7. destruct RES7 as (_ & ->). unfold MallocRep.wz.
          retpc 2303956.
          step. if_false. step.
          apply evt_done. unfold EXQ. exists m7, OW7, j14. do 21 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact ENV7|]. split; [exact LS7| exact RS7]. }
        destruct (bn_neg (getbn rY ls1)) eqn:EN; cbn [Z.b2z negb andb].
        -
          step. if_true.
          apply evt_done. rewrite (ucmp_bind_eq rY rn _ ls1 OKY OKN). cbn [negb andb].
          eapply NN; [exact ENV2 | exact LS2].
        - step. if_false. do 3 step. apply evt_done.
          eapply (KCALL _ _ _ _ _ 0 0 0 CS); [exact ES0 | exact ENV2 | exact LS2 | exact LOF | clear; lia | exact TOT0
            | intros PRE UW; eapply BN_ucmp_walkA; [pre_wk PRE STK_UCMP | reflexivity | exact HAY1 | exact HAN1
                                                     | exact (proj1 HPY) | exact NROn | reflexivity | reflexivity]
            | intros ? ? ? ? ? HRES; exact (proj1 (proj1 HRES)) |].
          intros c Σ4 ls4 m4 OW4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F4 fc4 ENV4 LS4 RS4 RES4. destruct RES4 as ((_ & -> & CR & -> & ->) & _).
          retpc 2303932.
          apply implA_from_evt.
          step. rewrite lts_signed by (clear - CR; lia).
          destruct (Z.ltb_spec c 0) as [CN|CP]; cbn [negb].
          +
            do 3 step. apply evt_done.
            eapply (KCALLE _ _ (EXQ ls1 OW1) _ 0 MC 0 CS); [exact ES0 | exact ENV4 | exact LS4 | exact LOF | mc0 | exact TOT0
              | intros PRE UW; eapply BN_copy_walkA; [pre_wk PRE STK_COPY | exact UW
                                                      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232960 CTX)
                                                      | reflexivity | exact HAR1 | exact HAY1 | exact (hpl_wref PL rR WRR)
                                                      | exact (proj1 HPY) | reflexivity | reflexivity]
              | hres |].
            intros u' Σ7 ls7 m7 OW7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F7 fc7 ENV7 LS7 RS7 RES7. hnf in RES7. destruct RES7 as (_ & -> & _). unfold MallocRep.wz.
            retpc 2304840.
            step. if_cases KR; rewrite ?unsigned_lit in KR by (clear - ARR; lia); zify_cond KR. { exfalso. clear - KR ARR. lia. }
            step.
            apply evt_done. unfold EXQ. exists m7, OW7, j14. do 21 eexists. split; [reflexivity|]. cbn [fst snd].
            split; [exact ENV7|]. split; [exact LS7| exact RS7].
          + apply evt_done. eapply NN; [exact ENV4 | exact LS4].
      Qed.

    End Loops.

    Lemma zero_bind_eq : forall {C : Type} r (K : unit -> BM (M := btree bptr) C) (lsK : ST),
      bbind ops (BN_zero ops r) K lsK = K tt (setbn r (bn_zero_pure (getbn r lsK)) lsK).
    Proof using. reflexivity. Qed.
    Lemma get_set_bind_eq : forall {C : Type} r (gg : bignum bptr -> bignum bptr) (K : unit -> BM (M := btree bptr) C) (lsK : ST),
      bbind ops (bbind ops (bget ops r) (fun b => bset ops r (gg b))) K lsK = K tt (setbn r (gg (getbn r lsK)) lsK).
    Proof using. reflexivity. Qed.
    Lemma num_bits_bind_eq : forall {C : Type} r (K : Z -> BM (M := btree bptr) C) (lsK : ST), bg_ok (getbn r lsK) ->
      bbind ops (BN_num_bits ops r) K lsK = K (num_bits_pure (getbn r lsK)) lsK.
    Proof using.
      intros C r K lsK (_ & _ & _ & FL). unfold bbind at 1. unfold BN_num_bits. rewrite bbind_get. unfold has_flag.
      assert (EL4 : Z.land (bn_flags (getbn r lsK)) BN_FLG_CONSTTIME = 0) by (destruct FL as [E|E]; rewrite E; reflexivity).
      rewrite EL4. reflexivity.
    Qed.

    Definition ifr0 (j0 j1 j2 j3 j4 j5 j6 j7 j8 j10 j11 j12 j13 j14 j16 j17 : list byte) : list cell :=
      ifrc j0 j1 j2 j3 j4 j5 j6 (CB 8 j7) (CB 8 j8) (CB 8 j10) (CB 8 j11) (CB 8 j12) (CB 8 j13) (CB 8 j14) j16 j17.

    Ltac fr_unf H ::= unfold ifr0, ifr, ifrc in H.
    Local Ltac fr_store ENV LS ENV' LS' :=
      fr_store_gen (cenv_frameA LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0) FB SPv ENV LS ENV' LS'.
    Local Ltac frc ENV FRc := pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & FRc & _); unfold ifr0, ifr, ifrc in FRc; cbn [app] in FRc.

    Lemma inv_start : forall j0 j1 j2 j3 j4 j5 j6 j7 j8 j10 j11 j12 j13 j14 j16 j17 ΣK lsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) F1 fc1,
      CENV (ifr0 j0 j1 j2 j3 j4 j5 j6 j7 j8 j10 j11 j12 j13 j14 j16 j17) 0 ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
      ref_at lsK OWK PL rR aR -> ref_at lsK OWK PL ra_ aa -> ref_at lsK OWK PL rn an -> 0 < aR < 2^47 ->
      implA (bbind ops (BN_CTX_start ops) (fun _ =>
             bbind ops (BN_CTX_get ops) (fun rA =>
             bbind ops (BN_CTX_get ops) (fun rB =>
             bbind ops (BN_CTX_get ops) (fun rX =>
             bbind ops (BN_CTX_get ops) (fun rD =>
             bbind ops (BN_CTX_get ops) (fun rM =>
             bbind ops (BN_CTX_get ops) (fun rY =>
             bbind ops (BN_CTX_get ops) (fun rT =>
             bbind ops (BN_one ops rX) (fun _ =>
             bbind ops (BN_zero ops rY) (fun _ =>
             bbind ops (BN_copy ops rB ra_) (fun _ =>
             bbind ops (BN_copy ops rA rn) (fun _ =>
             bbind ops (bbind ops (bget ops rA) (fun b => bset ops rA (bn_with_neg b false))) (fun _ =>
             bbind ops (bget ops rB) (fun bB =>
             bbind ops (BN_ucmp ops rB rA) (fun c =>
             bbind ops (if bn_neg bB || (0 <=? c) then BN_nnmod ops rB rB rA else bret ops tt) (fun _ =>
             bbind ops (BN_num_bits ops rn) (fun nb =>
             bbind ops (bget ops rn) (fun n2 =>
             bbind ops (if is_odd_pure n2 && (nb <=? 2048) then inv_binary_loop ops (Z.to_nat (2 * nb) + 2) rA rB rX rY rn else bunr ops) (fun _ =>
             bbind ops (BN_sub ops rY rn rY) (fun _ =>
             bbind ops (bget ops rA) (fun bA =>
             bbind ops (if is_one_pure bA then
                          bbind ops (bget ops rY) (fun y => bbind ops (BN_ucmp ops rY rn) (fun c =>
                          if negb (bn_neg y) && (c <? 0) then BN_copy ops rR rY else BN_nnmod ops rR rY rn))
                        else bunr ops) (fun _ => BN_CTX_end ops)))))))))))))))))))))) lsK) ΣK Q
        (MS (mkR rax (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0r (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 SHB) x21 (Z_to_bv 64 pn) (Z_to_bv 64 an) (Z_to_bv 64 ac) (Z_to_bv 64 aa) (Z_to_bv 64 aR) (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
            F1 (Z_to_bv 64 0x232320) fc1 None mK (seg_rom bgbsegs)).
    Proof.
      intros until fc1. intros ENVK LSK HAR HAa HAn ARR.
      destruct (env_bounds _ _ _ _ _ _ ENVK) as (ESP & ESPS & B1 & B2 & B3).

      apply implA_from_evt. do 2 step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENVK | exact LSK | exact LOF | mc0 | exact TOT0
        | intros PRE UW; eapply BN_CTX_start_walkA; [pre_wk PRE STK_START | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232140 CTX) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros u Σ0' ls0' mq0 OW0' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F0 fc0 ENV0 LS0 RS0 _. clear ENVK LSK.
      retpc 2302760.

      apply implA_from_evt. do 2 step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV0 | exact LS0 | exact LOF | mc0 | exact TOT0
        | intros PRE UW; eapply BN_CTX_get_walkA; [pre_wk PRE STK_GET | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232148 CTX) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rA Σ1 ls1 mq1 OW1 ? ? ? yA ? ? ? ? ? ? ? ? ? ? ? F1' fc1' ENV1 LS1 RS1 RES1. hnf in RES1. destruct RES1 as (_ & (iA & EiA) & (aA & HAA & EyA) & _). clear ENV0 LS0.
      retpc 2302768.
      apply implA_from_evt. fr_store ENV1 LS1 ENV1b LS1b. clear ENV1 LS1. subst yA. unfold MallocRep.wz in *.

      do 2 step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV1b | exact LS1b | exact LOF | mc0 | exact TOT0
        | intros PRE UW; eapply BN_CTX_get_walkA; [pre_wk PRE STK_GET | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232154 CTX) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rB Σ2 ls2 mq2 OW2 ? ? ? yB ? ? ? ? ? ? ? ? ? ? ? F2' fc2' ENV2 LS2 RS2 RES2. hnf in RES2. destruct RES2 as (_ & (iB & EiB) & (aB & HAB & EyB) & _). clear ENV1b LS1b.
      retpc 2302780.
      apply implA_from_evt. fr_store ENV2 LS2 ENV2b LS2b. clear ENV2 LS2. subst yB. unfold MallocRep.wz in *.

      do 2 step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV2b | exact LS2b | exact LOF | mc0 | exact TOT0
        | intros PRE UW; eapply BN_CTX_get_walkA; [pre_wk PRE STK_GET | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232160 CTX) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rX Σ3 ls3 mq3 OW3 ? ? ? yX ? ? ? ? ? ? ? ? ? ? ? F3' fc3' ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & (iX & EiX) & (aX & HAX & EyX) & _). clear ENV2b LS2b.
      retpc 2302792.
      apply implA_from_evt. fr_store ENV3 LS3 ENV3b LS3b. clear ENV3 LS3. subst yX. unfold MallocRep.wz in *.

      do 2 step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV3b | exact LS3b | exact LOF | mc0 | exact TOT0
        | intros PRE UW; eapply BN_CTX_get_walkA; [pre_wk PRE STK_GET | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_23216c CTX) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rD Σ4 ls4 mq4 OW4 ? ? ? yD ? ? ? ? ? ? ? ? ? ? ? F4' fc4' ENV4 LS4 RS4 RES4. hnf in RES4. destruct RES4 as (_ & (iD & EiD) & (aD & HAD & EyD) & _). clear ENV3b LS3b.
      retpc 2302804.
      subst yD. unfold MallocRep.wz in *.

      apply implA_from_evt. do 3 step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV4 | exact LS4 | exact LOF | mc0 | exact TOT0
        | intros PRE UW; eapply BN_CTX_get_walkA; [pre_wk PRE STK_GET | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232178 CTX) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rM Σ5 ls5 mq5 OW5 ? ? ? yM ? ? ? ? ? ? ? ? ? ? ? F5' fc5' ENV5 LS5 RS5 RES5. hnf in RES5. destruct RES5 as (_ & (iM & EiM) & (aM & HAM & EyM) & _). clear ENV4 LS4.
      retpc 2302816.
      apply implA_from_evt. fr_store ENV5 LS5 ENV5b LS5b. clear ENV5 LS5. subst yM. unfold MallocRep.wz in *.

      do 2 step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV5b | exact LS5b | exact LOF | mc0 | exact TOT0
        | intros PRE UW; eapply BN_CTX_get_walkA; [pre_wk PRE STK_GET | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232184 CTX) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rY Σ6 ls6 mq6 OW6 ? ? ? yY ? ? ? ? ? ? ? ? ? ? ? F6' fc6' ENV6 LS6 RS6 RES6. hnf in RES6. destruct RES6 as (_ & (iY & EiY) & (aY & HAY & EyY) & _). clear ENV5b LS5b.
      retpc 2302828.
      apply implA_from_evt. fr_store ENV6 LS6 ENV6b LS6b. clear ENV6 LS6. subst yY. unfold MallocRep.wz in *.

      do 2 step. apply evt_done.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV6b | exact LS6b | exact LOF | mc0 | exact TOT0
        | intros PRE UW; eapply BN_CTX_get_walkA; [pre_wk PRE STK_GET | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232190 CTX) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rT Σ7 ls7 mq7 OW7 ? ? ? yT ? ? ? ? ? ? ? ? ? ? ? F7' fc7' ENV7 LS7 RS7 RES7. hnf in RES7. destruct RES7 as (_ & (iT & EiT) & (aT & HAT & EyT) & _). clear ENV6b LS6b.
      retpc 2302840.

      assert (HPA : hpl PL rA) by (rewrite EiA; apply hpl_pool).
      assert (HPB : hpl PL rB) by (rewrite EiB; apply hpl_pool).
      assert (HPX : hpl PL rX) by (rewrite EiX; apply hpl_pool).
      assert (HPY : hpl PL rY) by (rewrite EiY; apply hpl_pool).
      assert (HPT : hpl PL rT) by (rewrite EiT; apply hpl_pool).
      pose proof (refs_stable_trans _ _ _ _ _ _ RS2 (refs_stable_trans _ _ _ _ _ _ RS3 (refs_stable_trans _ _ _ _ _ _ RS4 (refs_stable_trans _ _ _ _ _ _ RS5 (refs_stable_trans _ _ _ _ _ _ RS6 RS7))))) as RS17.
      pose proof (refs_stable_trans _ _ _ _ _ _ RS0 (refs_stable_trans _ _ _ _ _ _ RS1 RS17)) as RS07.
      assert (IR7 : IREFS rA rB rX rY aA aB aX aY ls7 OW7).
      { unfold IREFS. split; [exact (ref_at_stable _ _ _ _ PL _ _ RS17 HAA)|].
        split; [exact (ref_at_stable _ _ _ _ PL _ _ (refs_stable_trans _ _ _ _ _ _ RS3 (refs_stable_trans _ _ _ _ _ _ RS4 (refs_stable_trans _ _ _ _ _ _ RS5 (refs_stable_trans _ _ _ _ _ _ RS6 RS7)))) HAB)|].
        split; [exact (ref_at_stable _ _ _ _ PL _ _ (refs_stable_trans _ _ _ _ _ _ RS4 (refs_stable_trans _ _ _ _ _ _ RS5 (refs_stable_trans _ _ _ _ _ _ RS6 RS7))) HAX)|].
        split; [exact (ref_at_stable _ _ _ _ PL _ _ RS7 HAY)|].
        split; [exact (ref_at_stable _ _ _ _ PL _ _ RS07 HAn)| exact (ref_at_stable _ _ _ _ PL _ _ RS07 HAR)]. }
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS07 HAa) as HAa7.
      destruct (env_ok_of _ _ _ _ _ _ rT aT ENV7 LS7 HAT (proj1 HPT)) as (_ & ATR).
      destruct (env_ok_of _ _ _ _ _ _ rA aA ENV7 LS7 (proj1 IR7) (proj1 HPA)) as (_ & AAR).
      destruct (env_ok_of _ _ _ _ _ _ rB aB ENV7 LS7 (proj1 (proj2 IR7)) (proj1 HPB)) as (_ & ABR).
      change (2^47) with 140737488355328 in ATR, AAR, ABR, ARR.
      clear RS0 RS1 RS2 RS3 RS4 RS5 RS6 RS7 RS17 RS07 HAA HAB HAX HAY HAn HAR HAa HAT HAD HAM EiA EiB EiX EiY EiT EiD EiM iA iB iX iY iT iD iM.
      apply implA_from_evt.
      step. if_cases KT; subst yT; unfold MallocRep.wz in *; rewrite ?unsigned_lit in KT by (clear - ATR; lia); zify_cond KT. { exfalso. clear - KT ATR. lia. }
      remember (Z_to_bv 64 aT) as wT eqn:EwT.
      fr_store ENV7 LS7 ENV7b LS7b. clear ENV7 LS7.
      subst wT.
      frc ENV7b FRc. do 2 step. clear FRc.
      step. if_cases KIN; rewrite ?unsigned_lit in KIN by (clear - ARR; lia); zify_cond KIN. 2:{ exfalso. clear - KIN ARR. lia. }
      clear KT KIN.

      pose proof IR7 as (HAA & HAB & HAX & HAY & HAN & HAR).
      frc ENV7b FRc. do 3 step. clear FRc. apply evt_done.
      unfold BN_one.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV7b | exact LS7b | exact LOF | mc0 | exact TOT0
        | intros PRE UW; eapply BN_set_word_walkA; [pre_wk PRE STK_SETW | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_2321bc CTX)
              | reflexivity | exact HAX | exact (hpl_wref PL rX HPX) | reflexivity | reflexivity | clear; lia]
        | hres |].
      intros u9 Σ9 ls9 mq9 OW9 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F9 fc9 ENV9 LS9 RS9 RES9. hnf in RES9. destruct RES9 as (_ & -> & _). unfold MallocRep.wz.
      pose proof (irefs_stable _ _ _ _ _ _ _ _ _ _ _ _ IR7 RS9) as IR9. pose proof (ref_at_stable _ _ _ _ PL _ _ RS9 HAa7) as HAa9.
      clear ENV7b LS7b IR7 HAa7 HAA HAB HAX HAY HAN HAR RS9.
      pose proof IR9 as (HAA & HAB & HAX & HAY & HAN & HAR).
      retpc 2302884.

      apply implA_from_evt. step. if_false.
      frc ENV9 FRc. do 2 step. clear FRc.
      eapply KZEROX; [exact ENV9 | exact LS9 | exact HAY | exact (hpl_wref PL rY HPY) |].
      intros mq10 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ls10 ENV10 LS10.
      assert (IR10 : IREFS rA rB rX rY aA aB aX aY ls10 OW9).
      { unfold IREFS, ls10. repeat split; apply ref_at_setbn; assumption. }
      assert (HAa10 : ref_at ls10 OW9 PL ra_ aa) by (apply ref_at_setbn; exact HAa9).
      clear ENV9 LS9 IR9 HAa9 HAA HAB HAX HAY HAN HAR.
      pose proof IR10 as (HAA & HAB & HAX & HAY & HAN & HAR).
      retpc 2302896.

      frc ENV10 FRc. do 3 step. clear FRc. apply evt_done. rewrite zero_bind_eq. fold ls10.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV10 | exact LS10 | exact LOF | mc0 | exact TOT0
        | intros PRE UW; eapply BN_copy_walkA; [pre_wk PRE STK_COPY | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_2321d4 CTX)
              | reflexivity | exact HAB | exact HAa10 | exact (hpl_wref PL rB HPB) | exact NROa | reflexivity | reflexivity]
        | hres |].
      intros u11 Σ11 ls11 mq11 OW11 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F11 fc11 ENV11 LS11 RS11 RES11. hnf in RES11. destruct RES11 as (_ & -> & _). unfold MallocRep.wz.
      pose proof (irefs_stable _ _ _ _ _ _ _ _ _ _ _ _ IR10 RS11) as IR11.
      clear ENV10 LS10 IR10 HAa10 HAA HAB HAX HAY HAN HAR RS11.
      pose proof IR11 as (HAA & HAB & HAX & HAY & HAN & HAR).
      retpc 2302908.

      apply implA_from_evt.
      step. if_cases KB; rewrite ?unsigned_lit in KB by (clear - ABR; lia); zify_cond KB. { exfalso. clear - KB ABR. lia. }
      frc ENV11 FRc. do 4 step. clear FRc. apply evt_done.
      eapply (KCALL _ _ _ _ _ 0 MC 0 CS); [exact ES0 | exact ENV11 | exact LS11 | exact LOF | mc0 | exact TOT0
        | intros PRE UW; eapply BN_copy_walkA; [pre_wk PRE STK_COPY | exact UW
              | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_2321e8 CTX)
              | reflexivity | exact HAA | exact HAN | exact (hpl_wref PL rA HPA) | exact NROn | reflexivity | reflexivity]
        | hres |].
      intros u12 Σ12 ls12 mq12 OW12 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F12 fc12 ENV12 LS12 RS12 RES12. hnf in RES12. destruct RES12 as (_ & -> & _). unfold MallocRep.wz.
      pose proof (irefs_stable _ _ _ _ _ _ _ _ _ _ _ _ IR11 RS12) as IR12.
      clear ENV11 LS11 IR11 HAA HAB HAX HAY HAN HAR RS12 KB.
      pose proof IR12 as (HAA & HAB & HAX & HAY & HAN & HAR).
      retpc 2302928.

      rewrite get_set_bind_eq.
      apply implA_from_evt.
      step. if_cases KA; rewrite ?unsigned_lit in KA by (clear - AAR; lia); zify_cond KA. { exfalso. clear - KA AAR. lia. }
      frc ENV12 FRc. step. clear FRc.
      destruct (cenv_struct_openA LB PL EA lo SPv FB s0w raw ras TOTAL Σ0 ls0 OW0 m0 LOF16 _ _ _ _ _ _ rA aA ENV12 LS12 HAA (hpl_wref PL rA HPA))
        as (DA & BNA & OKA & ACCA & ALA & A0 & SEPA & OFRA & ST12 & MI12 & CLOSEA).
      unfold BnRepDefs.bn_cells, MallocRep.wz in BNA.
      pose proof (munch_refl [(aA, aA + 24)]%Z mq12) as MU. pose proof (wmono_refl bgbsegs mq12) as WM.
      assert (OFF : offshW [(aA, aA + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFRA; lia).
      ub. do 3 step. shl_with ACCA ALA. chk0.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mq13 end.
      destruct (CLOSEA mq13 (bn_with_neg (getbn rA ls12) false) MU WM) as (ENV13 & LS13);
        [ exact BNA | reflexivity | reflexivity | exact OKA | exact ST12 | exact MI12 |].
      clear BNA MU WM ST12 MI12 CLOSEA DA OKA SEPA KA ACCA OFF.
      set (ls13 := setbn rA (bn_with_neg (getbn rA ls12) false) ls12) in *.
      assert (IR13 : IREFS rA rB rX rY aA aB aX aY ls13 OW12).
      { unfold IREFS, ls13. repeat split; apply ref_at_setbn; assumption. }
      clear ENV12 LS12 IR12 HAA HAB HAX HAY HAN HAR.
      pose proof IR13 as (HAA & HAB & HAX & HAY & HAN & HAR).

      assert (J5 : forall ΣJ5 lsJ5 mJ5 OWJ5 (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) FJ5 fcJ5,
                CENV (ifr j0 j1 j2 j3 j4 j5 j6 (Z_to_bv 64 aT) (Z_to_bv 64 aM) (Z_to_bv 64 aA) (Z_to_bv 64 aB) (Z_to_bv 64 aX) (Z_to_bv 64 aY) (CB 8 j14) j16 j17) 0 ΣJ5 lsJ5 mJ5 OWJ5 ->
                lib_state lsJ5 mJ5 OWJ5 PL EA -> IREFS rA rB rX rY aA aB aX aY lsJ5 OWJ5 ->
                implA (bbind ops (BN_num_bits ops rn) (fun nb =>
                       bbind ops (bget ops rn) (fun n2 =>
                       bbind ops (if is_odd_pure n2 && (nb <=? 2048) then inv_binary_loop ops (Z.to_nat (2 * nb) + 2) rA rB rX rY rn else bunr ops) (fun _ =>
                       bbind ops (BN_sub ops rY rn rY) (fun _ =>
                       bbind ops (bget ops rA) (fun bA =>
                       bbind ops (if is_one_pure bA then
                                    bbind ops (bget ops rY) (fun y => bbind ops (BN_ucmp ops rY rn) (fun c =>
                                    if negb (bn_neg y) && (c <? 0) then BN_copy ops rR rY else BN_nnmod ops rR rY rn))
                                  else bunr ops) (fun _ => BN_CTX_end ops)))))) lsJ5) ΣJ5 Q
                  (MS (mkR rax' (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0r (Z_to_bv 64 FB) a0' a1' a2' a3' a4' a5' a6' a7'
                           (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 aR) (Z_to_bv 64 pn) (Z_to_bv 64 an) (Z_to_bv 64 ac) (Z_to_bv 64 aY) (Z_to_bv 64 aD) (Z_to_bv 64 (shad f)) t3' t4' t5' t6')
                      FJ5 (Z_to_bv 64 0x232454) fcJ5 None mJ5 (seg_rom bgbsegs))).
      { intros until fcJ5. intros ENV5' LS5' IR5.
        pose proof IR5 as (HAA5 & HAB5 & HAX5 & HAY5 & HAN5 & HAR5).
        destruct (env_ok_of _ _ _ _ _ _ rn an ENV5' LS5' HAN5 NROn) as (OKN & _).
        rewrite (num_bits_bind_eq rn _ lsJ5 OKN). rewrite bbind_get.
        pose proof (nbits_range _ OKN) as NBR.
        destruct (is_odd_pure (getbn rn lsJ5)) eqn:EO; cbn [andb].
        2:{ unfold bbind, bunr. cbn [bind unreachable tree_ops tbind]. apply implA_unr. }
        destruct (Z.leb_spec (num_bits_pure (getbn rn lsJ5)) 2048) as [NB|NB].
        2:{ unfold bbind, bunr. cbn [bind unreachable tree_ops tbind]. apply implA_unr. }
        apply implA_from_evt. do 2 step.
        eapply KODD; [exact ENV5' | exact LS5' | exact HAN5 | exact NROn |].
        intros m6' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV6' LS6'. clear ENV5' LS5'.
        retpc 2303068. rewrite EO. cbn [Z.b2z].
        step. if_false. do 2 step.
        eapply KBITS; [exact ENV6' | exact LS6' | exact HAN5 | exact NROn | exact LOFNB |].
        intros m7' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV7' LS7'. clear ENV6' LS6'.
        retpc 2303080.
        do 2 step.
        step. if_cases KN; rewrite ?unsigned_lit in KN by (clear - NBR; lia); zify_cond KN.
        { exfalso. rewrite signed_small in KN by (clear - NBR; lia). clear - KN NB. lia. }
        clear KN. apply evt_done.
        unfold bbind at 1. cbn [bind tree_ops]. eapply implA_bind.
        { eapply (bin_top rA rB rX rY aA aB aX aY aT aM j0 j1 j2 j3 j4 j5 j6 j16 j17 HPA HPB HPX HPY); [exact ENV7' | exact LS7' | exact IR5]. }
        cbv beta. intros [u' ls8'] Σ8' ms8' PO. unfold PLQ in PO. destruct PO as (m8' & OW8' & j14' & R).
        destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENV8' & LS8' & RS8'). cbn [fst snd] in *.
        eapply (inv_fin rA rB rX rY aA aB aX aY aT aM j0 j1 j2 j3 j4 j5 j6 j16 j17 HPA HPY); [exact ENV8' | exact LS8' | exact (irefs_stable _ _ _ _ _ _ _ _ _ _ _ _ IR5 RS8') | exact ARR]. }

      rewrite bbind_get.
      destruct (open_for_call LB PL EA lo SPv FB s0w raw (Some ras) TOTAL Σ0 ls0 OW0 m0 LOF16 _ _ _ _ _ _ rB aB ENV13 LS13 HAB (proj1 HPB))
        as (DB & BNB & OKB & _ & _ & _ & SEPB & SHBC & ACCB & ALB & SLO & OFRB & AB0).
      destruct (env_ok_of _ _ _ _ _ _ rA aA ENV13 LS13 HAA (proj1 HPA)) as (OKA13 & _).
      unfold BnRepDefs.bn_cells, MallocRep.wz in BNB.
      pose proof (munch_refl [] mq13) as MUb.
      ub. do 3 step. shl_with ACCB ALB. chk0.
      step.
      frc ENV13 FRc. step. clear FRc.
      clear BNB MUb ACCB.
      assert (NN : forall ΣN3 mN3 (rax' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6' : word) FN3 fcN3,
                CENV (ifr j0 j1 j2 j3 j4 j5 j6 (Z_to_bv 64 aT) (Z_to_bv 64 aM) (Z_to_bv 64 aA) (Z_to_bv 64 aB) (Z_to_bv 64 aX) (Z_to_bv 64 aY) (CB 8 j14) j16 j17) 0 ΣN3 ls13 mN3 OW12 ->
                lib_state ls13 mN3 OW12 PL EA ->
                implA (bbind ops (BN_nnmod ops rB rB rA) (fun _ =>
                       bbind ops (BN_num_bits ops rn) (fun nb =>
                       bbind ops (bget ops rn) (fun n2 =>
                       bbind ops (if is_odd_pure n2 && (nb <=? 2048) then inv_binary_loop ops (Z.to_nat (2 * nb) + 2) rA rB rX rY rn else bunr ops) (fun _ =>
                       bbind ops (BN_sub ops rY rn rY) (fun _ =>
                       bbind ops (bget ops rA) (fun bA =>
                       bbind ops (if is_one_pure bA then
                                    bbind ops (bget ops rY) (fun y => bbind ops (BN_ucmp ops rY rn) (fun c =>
                                    if negb (bn_neg y) && (c <? 0) then BN_copy ops rR rY else BN_nnmod ops rR rY rn))
                                  else bunr ops) (fun _ => BN_CTX_end ops))))))) ls13) ΣN3 Q
                  (MS (mkR rax' (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0r (Z_to_bv 64 FB) a0' a1' a2' (Z_to_bv 64 aB) a4' a5' a6' a7'
                           (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 aR) (Z_to_bv 64 pn) (Z_to_bv 64 an) (Z_to_bv 64 ac) (Z_to_bv 64 aY) (Z_to_bv 64 aD) (Z_to_bv 64 (shad f)) t3' t4' t5' t6')
                      FN3 (Z_to_bv 64 0x23243c) fcN3 None mN3 (seg_rom bgbsegs))).
      { intros until fcN3. intros ENV3' LS3'.
        apply implA_from_evt. frc ENV3' FRc. do 5 step. clear FRc. apply evt_done.
        eapply (KCALL _ _ _ _ _ 0 BN_NNMOD_COST 0 CS); [exact ES0 | exact ENV3' | exact LS3' | exact LOF | vm_compute; intro HH; discriminate HH | exact TOT0
          | intros PRE UW; eapply BN_nnmod_walkA; [pre_wk PRE STK_NNMOD | exact UW
                | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_int_bn_mod_inverse_232268 CTX)
                | reflexivity | exact HAB | exact HAB | exact HAA | exact HPB | exact (proj1 HPB) | exact (proj1 HPA) | exact (hpl_nbuf PL rB HPB) | exact HPC
                | reflexivity | reflexivity | reflexivity | reflexivity]
          | hres |].
        intros u' ΣN7 lsN7 mN7 OWN7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? FN7 fcN7 ENVN7 LSN7 RSN7 RES7. hnf in RES7. destruct RES7 as (_ & ->). unfold MallocRep.wz.
        retpc 2303056.
        apply implA_from_evt. step. if_false. apply evt_done.
        eapply J5; [exact ENVN7 | exact LSN7 | exact (irefs_stable _ _ _ _ _ _ _ _ _ _ _ _ IR13 RSN7)]. }
      destruct (bn_neg (getbn rB ls13)) eqn:EN; cbn [Z.b2z orb].
      -
        step. if_true.
        apply evt_done. rewrite (ucmp_bind_eq rB rA _ ls13 OKB OKA13).
        eapply NN; [exact ENV13 | exact LS13].
      - step. if_false. frc ENV13 FRc. do 3 step. clear FRc. apply evt_done.
        eapply (KCALL _ _ _ _ _ 0 0 0 CS); [exact ES0 | exact ENV13 | exact LS13 | exact LOF | clear; lia | exact TOT0
          | intros PRE UW; eapply BN_ucmp_walkA; [pre_wk PRE STK_UCMP | reflexivity | exact HAB | exact HAA
                                                   | exact (proj1 HPB) | exact (proj1 HPA) | reflexivity | reflexivity]
          | intros ? ? ? ? ? HRES; exact (proj1 (proj1 HRES)) |].
        intros c Σ14 ls14 mq14 OW14 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? F14 fc14 ENV14 LS14 RS14 RES14. destruct RES14 as ((_ & -> & CR & -> & ->) & _).
        retpc 2303028.
        apply implA_from_evt.
        frc ENV14 FRc. step. clear FRc.
        step. rewrite lts_signed by (clear - CR; lia).
        destruct (Z.ltb_spec c 0) as [CN|CP]; cbn [negb].
        +
          replace (0 <=? c) with false by (symmetry; apply Z.leb_gt; exact CN).
          apply evt_done. rewrite bbind_ret.
          eapply J5; [exact ENV14 | exact LS14 | exact IR13].
        + replace (0 <=? c) with true by (symmetry; apply Z.leb_le; exact CP).
          apply evt_done.
          eapply NN; [exact ENV14 | exact LS14].
    Qed.
  End Main.

  Definition INT_INV_BODY : Z := 0x231f3c.
  Definition INT_INV_EXIT : Z := 0x231f80.

  Definition ifrP (f : Z) (g : nat) (junk : list byte) (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 : list byte) : list cell :=
    [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; CB 8 j10; CB 8 j11; CB 8 j12; CB 8 j13;
     CB 8 j14; CB 8 j15; CB 8 j16; CB 8 j17; C8 (Z_to_bv 64 f); CB g junk].
  Ltac fr_unf H ::= unfold ifrP, ifr0, ifr, ifrc in H.

  Lemma acc4_byte : forall (m : mem) pn ad, acc bgbsegs m pn 4 -> pn mod 8 = 0 -> 0 <= pn /\ pn + 4 <= 140737488355328 -> ad = wa (shad pn) ->
    exists b : byte, ov_read_bytes bgbsegs m ad 1 = Some [b] /\ (b = z8 \/ exists k, 4 <= k < 8 /\ sxb b = Z_to_bv 64 k).
  Proof using.
    intros m pn ad ACC AL R E.
    assert (E3 : ad = wa (shad (pn + 3))) by (rewrite E; f_equal; unfold shad; f_equal; clear - AL; Z.div_mod_to_equations; lia).
    assert (H1 : pn <= pn + 3 < pn + 4) by (clear; lia). assert (H2 : 0 <= pn + 3 < 140737488355328) by (clear - R; lia).
    destruct (acc_rd1 bgbsegs [] m m pn 4 (pn + 3) ad ACC (munch_refl [] m) I H1 H2 E3) as (b & RD & OK).
    exists b. split; [exact RD|].
    destruct (sh_ok_cases b (pn + 3) OK) as [Ez|(k & K1 & K2 & K3 & _)]; [left; exact Ez | right].
    exists k. split; [| exact K3]. clear - K1 K2 AL. Z.div_mod_to_equations. lia.
  Qed.

  Lemma int_inv_body : forall (Q : unit * ST -> rts RT -> machine_state -> Prop)
      (ra' sp gp u0 u1 u2 x10 x11 x12 x13 x14 b5 b6 b7 x21 u3 u4 u5 u6 s0w raw r_ a_ n_ c_ p_ : word) (F' : bvmap 5 word) (fc' : bv 32)
      (Σ1 : rts RT) (ls : ST) (m1 : mem) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo spa f : Z) (ras : list Z)
      (g : nat) (junk : list byte) (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 : list byte)
      (rR ra_ rn : bnref) (aR aa an ac : Z) (qc : bptr) (pn : Z) (qn : bptr) (TOTAL : Z),
    cenvA LB PL lo (bv_unsigned sp) spa s0w raw (Some ras) TOTAL Σ1 ls OW m1
          (ifrP f g junk j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17) 0 Σ1 ls m1 OW ->
    lib_state ls m1 OW PL EA -> lo <= spa - CS -> 0 <= TOTAL ->
    In (qn, pn, 4) LB -> pn mod 8 = 0 -> (forall x, pn <= x < pn + 4 -> ~ rin_ivs (pl_frames PL) x) ->
    uk_ctx INT_BN_MOD_INVERSE (bv_unsigned raw :: ras) ->
    ref_at ls OW PL rR aR -> hpl PL rR -> ref_at ls OW PL ra_ aa -> ra_ <> ROne -> ref_at ls OW PL rn an -> rn <> ROne -> pl_ctx PL = Some (ac, qc) ->
    r_ = wz aR -> a_ = wz aa -> n_ = wz an -> c_ = wz ac -> p_ = wz pn ->
    (forall (Σk : rts RT) (lsk : ST) (mk : mem) (OWk : list block) (loc : list cell) (mb : mem)
            (x1 x5 x6 x7 y10 y11 y12 y13 y14 y15 y16 y17 x20' x23 x24 x25 x26 x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32),
       cenvA LB PL lo (bv_unsigned sp) spa s0w raw (Some ras) TOTAL Σ1 ls OW mb (loc ++ [CB g junk]) 0 Σk lsk mk OWk ->
       lib_state lsk mk OWk PL EA -> ax_pres LB (bv_unsigned sp) (XW PL ++ [(pn, pn + 4)]) m1 mb -> rw_cells bgbsegs mb pn [C4 (Z_to_bv 64 0)] ->
       implA (TRet (tt, lsk)) Σk Q
         (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) y10 y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 f) (Z_to_bv 64 f) x20' (Z_to_bv 64 aR) (Z_to_bv 64 pn) x23 x24 x25 x26 (Z_to_bv 64 (shad f)) x28 x29 x30 x31)
             Fk (wz INT_INV_EXIT) fck None mk (seg_rom bgbsegs))) ->
    implA (BN_mod_inverse ops rR ra_ rn ls) Σ1 Q
      (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) u0 u1 u2 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 b5 b6 b7
               (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 SHB) x21 p_ n_ c_ a_ r_ (Z_to_bv 64 (shad f)) u3 u4 u5 u6)
          F' (wz INT_INV_BODY) fc' None m1 (seg_rom bgbsegs)).
  Proof.
    intros until TOTAL. intros ENV0 LS0 LOF TOT0 HQN ALN WOWN CTX HAR WRR HAa NROa HAn NROn HPC -> -> -> -> -> KK.
    unfold INT_INV_BODY, INT_INV_EXIT, MallocRep.wz in *.
    assert (LOF16' : lo <= spa - 16) by (clear - LOF CS16; lia).
    destruct (ESPs LB PL lo (bv_unsigned sp) spa s0w raw ras TOTAL Σ1 ls OW m1 _ _ _ _ _ _ ENV0) as (_ & ESP).
    pose proof ENV0 as ((CEIL & LOFB & FBSP & SPT & _) & HEAP0 & _).
    pose proof (AH_ceil _ _ _ _ HEAP0) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (AH_range_gen _ _ _ _ (qn, pn, 4) HEAP0 ltac:(apply in_or_app; right; exact HQN)) as (PN0 & _ & _ & PNC & PNI).
    pose proof (AH_offsh _ _ _ _ (qn, pn, 4) HEAP0 ltac:(apply in_or_app; right; exact HQN)) as PNO.
    cbn [blk_addr blk_size fst snd] in PN0, PNC, PNI, PNO. unfold SHLO, SHHI in PNO.
    assert (PNR : 0 < pn /\ pn + 4 <= spa /\ spa < 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - PN0 PNC CEIL LOFB FBSP SPT; lia).
    destruct (env_ok_of lo (bv_unsigned sp) spa s0w raw ras LB PL EA TOTAL Σ1 ls OW m1 LOF _ _ _ _ _ _ rR aR ENV0 LS0 HAR (proj1 (hpl_wref PL rR WRR))) as (_ & ARR).
    destruct (env_ok_of lo (bv_unsigned sp) spa s0w raw ras LB PL EA TOTAL Σ1 ls OW m1 LOF _ _ _ _ _ _ ra_ aa ENV0 LS0 HAa NROa) as (OKa & _).
    destruct (env_ok_of lo (bv_unsigned sp) spa s0w raw ras LB PL EA TOTAL Σ1 ls OW m1 LOF _ _ _ _ _ _ rn an ENV0 LS0 HAn NROn) as (OKn & _).
    unfold BN_mod_inverse. rewrite !bbind_get.

    destruct (abs_is_word_pure (getbn rn ls) 1) eqn:EW; cbn [orb].
    { unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
    destruct (is_zero_pure (getbn rn ls)) eqn:EZ.
    { unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
    assert (EFA : has_flag (getbn ra_ ls) BN_FLG_CONSTTIME = false).
    { destruct OKa as (_ & _ & _ & FL). unfold has_flag. destruct FL as [E|E]; rewrite E; reflexivity. }
    assert (EFN : has_flag (getbn rn ls) BN_FLG_CONSTTIME = false).
    { destruct OKn as (_ & _ & _ & FL). unfold has_flag. destruct FL as [E|E]; rewrite E; reflexivity. }
    rewrite EFA, EFN. cbn [orb].
    apply implA_from_evt. do 3 step.
    eapply (abs_is_word_callA LB PL EA lo (bv_unsigned sp) spa s0w raw (Some ras) TOTAL Σ1 ls OW m1 LOF16'); [exact ENV0 | exact LS0 | exact HAn | exact NROn |].
    intros mq1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENV0 LS0.
    rewrite (ret_pc_even 2301768) by (clear; lia).
    rewrite (unsigned_lit 1) by (clear; lia). rewrite EW. cbn [Z.b2z].
    assert (PN64 : 0 < pn < 18446744073709551616) by (clear - PNR; lia).
    ub. step. if_false. do 2 step.
    eapply (is_zero_callA LB PL EA lo (bv_unsigned sp) spa s0w raw (Some ras) TOTAL Σ1 ls OW m1 LOF16'); [exact ENV1 | exact LS1 | exact HAn | exact NROn |].
    intros mq2 z0 z1 z2 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV2 LS2. clear ENV1 LS1.
    rewrite (ret_pc_even 2301784) by (clear; lia).
    change ((bn_top (getbn rn ls) =? 0)%nat) with (is_zero_pure (getbn rn ls)). rewrite EZ. cbn [Z.b2z].
    step. if_true.
    remember (Z_to_bv 64 aR) as wR eqn:EwR.
    fr_store_gen (cenv_frameA LB PL EA lo (bv_unsigned sp) spa s0w raw ras TOTAL Σ1 ls OW m1) spa (bv_unsigned sp) ENV2 LS2 ENV2b LS2b. clear ENV2 LS2.
    subst wR.
    ub.
    do 2 step.
    setreg 21%Z (Z_to_bv 64 (shad pn)) ltac:(f_equal; rewrite (unsigned_lit pn) by (clear - PNR; lia); unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity).
    assert (EL4a : Z.land (bn_flags (getbn ra_ ls)) 4 = 0).
    { destruct OKa as (_ & _ & _ & FL). destruct FL as [E|E]; rewrite E; reflexivity. }
    assert (EL4n : Z.land (bn_flags (getbn rn ls)) 4 = 0).
    { destruct OKn as (_ & _ & _ & FL). destruct FL as [E|E]; rewrite E; reflexivity. }

    lazymatch goal with |- evt _ (fun ms' => implA ?t _ _ ms') (MS _ _ _ _ _ ?mc _) =>
      assert (CONT : forall (a0' a1' : word),
                implA t Σ1 Q
                  (MS (mkR (Z_to_bv 64 2301784) (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) z0 z1 z2 sp (Z_to_bv 64 spa) a0' a1' z5 z6 z7 z8 z9 z10
                           (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 (shad pn)) (Z_to_bv 64 pn) (Z_to_bv 64 an) (Z_to_bv 64 ac) (Z_to_bv 64 aa)
                           (Z_to_bv 64 aR) (Z_to_bv 64 (shad f)) z11 z12 z13 z14)
                      F' (Z_to_bv 64 0x2320d0) fc' None mc (seg_rom bgbsegs)))
    end.
    { intros a0' a1'.
      apply implA_from_evt.

      pose proof ENV2b as (OKc & HEAPc & STc & MIc & AXPc & _ & _ & _ & FRc & FSZc & UWc). cbn [app] in FRc.
      pose proof OKc as (_ & _ & _ & _ & _ & _ & _ & _ & FROKc & _).
      destruct (AH_acc _ _ _ _ (qn, pn, 4) HEAPc ltac:(apply in_or_app; right; exact HQN)) as (WRN & _). cbn [blk_addr blk_size fst snd] in WRN.
      destruct (wr_at_rw_CB _ pn 4 WRN ltac:(clear; lia)) as (jn & CELLN). change (Z.to_nat 4) with 4%nat in CELLN.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (munch_refl [(pn, pn + 4)]%Z mm) as MUn; pose proof (wmono_refl bgbsegs mm) as WMn end.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mq3 end.
      assert (HEAP3 : AHEAP Σ1 OW LB mq3).
      { eapply AH_frame; [exact HEAPc | exact MUn | exact WMn |].
        constructor; [right; right; exists (qn, pn, 4); split; [apply in_or_app; right; exact HQN | cbn [blk_addr blk_size fst snd]; clear; lia] | constructor]. }
      assert (LS3 : lib_state ls mq3 OW PL EA).
      { unfold lib_state in *. eapply (lib_state_frame_lb Σ1 LB (bv_unsigned sp) USTACK_TOP); [exact HEAPc | exact LS2b | exact MUn | exact WMn | exact FROKc |].
        constructor; [right; exists (qn, pn, 4); split; [exact HQN|]; cbn [blk_addr blk_size fst snd]; split; [clear; lia|]; split; [clear; lia| exact WOWN] | constructor]. }
      assert (UW3 : uw_chain USTACK_TOP mq3 (bv_unsigned sp) (bv_unsigned s0w) ras).
      { unfold uw_opt in UWc. eapply uw_chain_munch_nw; [exact UWc | exact MUn |]. constructor; [cbn [snd]; clear - PNR FBSP; lia | constructor]. }
      lazymatch type of FRc with rw_cells _ _ _ ?cs =>
        lazymatch cs with
        | ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: _ =>
            pose proof (cenv_rebaseX LB PL lo (bv_unsigned sp) spa s0w raw ras TOTAL Σ1 ls OW m1 _
                          [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19] _ _ _ _ mq3 _
                          ENV2b HEAP3 STc MIc FRc FSZc UW3) as ENV3
        end end.
      replace (TOTAL - 0) with TOTAL in ENV3 by (clear; lia).
      assert (AXB : ax_pres LB (bv_unsigned sp) (XW PL ++ [(pn, pn + 4)]) m1 mq3).
      { eapply agree_on_trans.
        - eapply agree_on_mono; [exact AXPc|]. intros a [Ha1 Ha2]. split; [| exact Ha2].
          intros Hx. apply Ha1. apply rin_ivs_app. left. exact Hx.
        - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUn)|]. intros a [Ha1 _]. cbn [outside]. split; [| exact I].
          intros Hr. apply Ha1. apply rin_ivs_app. right. cbn [rin_ivs fst snd]. left. exact Hr. }
      clear ENV2b LS2b OKc HEAPc STc MIc AXPc FRc FSZc UWc FROKc WRN MUn WMn.

      do 3 step.
      eapply (get_flags_callA LB PL EA lo (bv_unsigned sp) spa s0w raw (Some ras) TOTAL Σ1 ls OW mq3 LOF16'); [exact ENV3 | exact LS3 | exact HAa | exact NROa |].
      intros mq4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV4 LS4. clear ENV3 LS3.
      rewrite (ret_pc_even 2302176) by (clear; lia).
      rewrite (unsigned_lit 4) by (clear; lia). rewrite EL4a.
      remember (Z_to_bv 64 (shad pn)) as wS eqn:EwS.
      fr_store_gen (cenv_frameA LB PL EA lo (bv_unsigned sp) spa s0w raw ras TOTAL Σ1 ls OW mq3) spa (bv_unsigned sp) ENV4 LS4 ENV4b LS4b. clear ENV4 LS4.
      subst wS.
      step. if_false.
      do 3 step.
      eapply (get_flags_callA LB PL EA lo (bv_unsigned sp) spa s0w raw (Some ras) TOTAL Σ1 ls OW mq3 LOF16'); [exact ENV4b | exact LS4b | exact HAn | exact NROn |].
      intros mq5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV5 LS5. clear ENV4b LS4b.
      rewrite (ret_pc_even 2302196) by (clear; lia).
      rewrite (unsigned_lit 4) by (clear; lia). rewrite EL4n.
      step. if_true.
      apply evt_done.
      eapply (inv_start gp sp lo (bv_unsigned sp) spa s0w raw ras LB PL EA TOTAL Σ1 ls OW mq3 rR ra_ rn aR aa an ac qc f pn g junk
                eq_refl LOF TOT0 HPC WRR NROa NROn CTX Q);
        [| exact ENV5 | exact LS5 | exact HAR | exact HAa | exact HAn | exact ARR].
      intros e0 e1 e2 e3 e4 e5 e6 eT eM eA eB eX eY e14 e16 e17. intros.
      eapply (KK Σk lsk mk OWk
                [CB 8 e0; CB 8 e1; CB 8 e2; CB 8 e3; CB 8 e4; CB 8 e5; CB 8 e6; C8 eT; C8 eM; C8 (Z_to_bv 64 (shad pn)); C8 eA; C8 eB; C8 eX; C8 eY;
                 CB 8 e14; C8 (Z_to_bv 64 aR); CB 8 e16; CB 8 e17; C8 (Z_to_bv 64 f)] mq3);
        [eassumption | eassumption | exact AXB | exact CELLN]. }

    pose proof ENV2b as (_ & HEAP2 & _).
    destruct (AH_acc _ _ _ _ (qn, pn, 4) HEAP2 ltac:(apply in_or_app; right; exact HQN)) as (_ & ACCN). cbn [blk_addr blk_size fst snd] in ACCN.
    assert (PNB : 0 <= pn /\ pn + 4 <= 140737488355328) by (clear - PNR; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      let ad := cur_mem_addr in
        destruct (acc4_byte mc pn ad ACCN ALN PNB ltac:(first [reflexivity | sh_addr_s | sh_addr])) as (bsh & RD & CASES) end.
    step. clear RD.
    destruct CASES as [-> | (k & K1 & K3)].
    - rewrite ?sxb_z8. step. if_false. apply evt_done. apply CONT.
    - rewrite K3. step. if_cases KB; rewrite ?unsigned_lit in KB by (clear - K1; lia); zify_cond KB. 2:{ exfalso. clear - KB K1. lia. }
      do 2 step.
      step. if_cases KS; zify_cond KS.
      + apply evt_done. apply CONT.
      + exfalso. revert KS. rewrite ?land7_mod8 by (clear - PNR; lia). rewrite ?(unsigned_lit pn) by (clear - PNR; lia).
        rewrite ?signed_small by (clear - K1; lia). intros KS. clear - KS K1 ALN PNR. lia.
  Qed.

End Proofs.
End WithRT.
