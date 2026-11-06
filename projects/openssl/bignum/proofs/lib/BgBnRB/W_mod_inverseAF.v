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
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgWords BgArith.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_callsAF W_calls3AF W_small3A W_small4A AFrameKit AFrameCall AFrameTac AFrameEnv AFrameComp ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import W_ctxAF W_ctx_getAF W_ctx_endAF W_copyAF W_cmpAF W_uaddAF W_usubAF W_subAF W_set_wordAF ShiftKitAF W_shiftAF W_nnmodAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import CtxKit InvKitAF W_int_invAF Fr_int_inv Fr_mod_inv.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).

Section Stmt.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).

Definition int_inv_stmtA (STACK COST : Z) (d : nat) : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rR ra_ rn : bnref) (aR aa an ac : Z) (qc : bptr) (pn : Z) (qn : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST -> fr_room d ls OW LB ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx INT_BN_MOD_INVERSE (bv_unsigned ra :: ras) ->
  tp = wz TP_A ->
  ref_at ls OW PL rR aR -> hpl PL rR -> ref_at ls OW PL ra_ aa -> ra_ <> ROne -> ref_at ls OW PL rn an -> rn <> ROne ->
  pl_ctx PL = Some (ac, qc) ->
  In (qn, pn, 4) LB -> pn mod 8 = 0 -> (forall x, pn <= x < pn + 4 -> ~ rin_ivs (pl_frames PL) x) ->
  a0 = wz aR -> a1 = wz aa -> a2 = wz an -> a3 = wz ac -> a4 = wz pn ->
  implA (BN_mod_inverse (tree_ops bptr) rR ra_ rn ls) Σ
    (bn_postAX [(pn, pn + 4)] ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA COST
       (fun _ _ _ PL' a0' m' => PL' = PL /\ a0' = wz aR /\ rw_cells bgbsegs m' pn [C4 (Z_to_bv 64 0)]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz INT_BN_MOD_INVERSE) fc None m (seg_rom bgbsegs)).
End Stmt.

Section Aux.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma blk_not_libw : forall (Σ : rts RT) OW LB' m b x, AHEAP Σ OW LB' m -> In b (OW ++ LB') -> blk_addr b <= x < blk_addr b + blk_size b -> ~ rin_ivs LIBW_bgr x.
Proof.
  intros Σ OW LB' m b x HEAP Hb Hx HL.
  pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & _ & BI).
  revert HL. unfold LIBW_bgr, LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. clear - BI Hx. lia.
Qed.
End Aux.

Section Top.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

  Variable CS : Z.
  Hypothesis CSRT : RT_STACK <= CS.
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
  Hypothesis STK_ONE : BN_IS_ONE_STACK <= CS.
  Hypothesis BN_rshift1_walkA : forall AR1 : ARun, @rshift1_stmtA AR1 UK CS MC.

  Definition INT_INV_STACK : Z := INT_INV_FRAME + CS.
  Definition INT_INV_COST : Z := 1.

  Lemma int_bn_mod_inverse_walkA : int_inv_stmtA INT_INV_STACK INT_INV_COST 1.
  Proof.
    unfold int_inv_stmtA. intros until qn. intros PRE ROOM UW CTX -> HAR WRR HAa NROa HAn NROn HPC HQN ALN WOWN -> -> -> -> ->.
    unfold INT_INV_STACK, INT_INV_COST in *.
    change INT_BN_MOD_INVERSE with INT_BN_MOD_INVERSE_E.
    eapply (pro_int_inv _ _) with (d := 0%nat); [exact PRE | exact ROOM | exact UW | reflexivity | clear - CSRT; lia | clear; lia |].
    intros Σ1 m1 f spa g junk gj ra' u0 u1 u2 x10 x11 x12 x13 x14 b5 b6 b7 u3 u4 u5 u6 F' fc' j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 FE GSZ SAVJ FR.
    pose proof FE as (HEAP1 & LS1 & FROK1 & ST1 & CEIL & LOK & SPT & SP16 & MI1 & CNT1 & CRED1 & FAL & NOFR1 & ROOM1 & SPA32 & SPAL & SPAH & CR1 & AXO & UW1 & FRESH & GEO).
    pose proof (fr_env_cenv0 256 0 f 2 [] Σ ls m OW LB PL EA sp lo _ (1 - 1) s0 ra ras spa Σ1 m1
                  ([CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; CB 8 j10; CB 8 j11; CB 8 j12; CB 8 j13;
                    CB 8 j14; CB 8 j15; CB 8 j16; CB 8 j17; C8 (Z_to_bv 64 f)] ++ [CB g junk])
                  FE ltac:(clear; lia) ltac:(unfold INT_INV_FRAME, RT_STACK in *; clear - CSRT; lia) FR
                  ltac:(cbn [app cells_size csize Nat.add]; clear - GSZ; lia)) as EV0.
    cbn [app] in EV0.
    change INT_INV_BODY_E with INT_INV_BODY.
    eapply (@int_inv_body (push AR f 2) UK BE CS CS112 CS16 STK_START STK_GET STK_END STK_SETW STK_COPY STK_UCMP STK_UADD STK_USUB STK_SUB STK_RSH STK_NNMOD
              (BN_rshift1_walkA (push AR f 2)) STK_ONE _ ra' sp gp u0 u1 u2 x10 x11 x12 x13 x14 b5 b6 b7 s5 u3 u4 u5 u6 s0 ra (wz aR) (wz aa) (wz an) (wz ac) (wz pn) F' fc'
              Σ1 ls m1 OW LB PL EA lo spa f ras g junk j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 rR ra_ rn aR aa an ac qc pn qn (1 - 1));
      [exact EV0 | exact LS1 | unfold INT_INV_FRAME in LOK; clear - LOK; lia | clear; lia | exact HQN | exact ALN | exact WOWN | exact CTX
      | exact HAR | exact WRR | exact HAa | exact NROa | exact HAn | exact NROn | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
    intros Σk lsk mk OWk loc mb x1 x5 x6 x7 y10 y11 y12 y13 y14 y15 y16 y17 x21' x23 x24 x25 x26 x28 x29 x30 x31 Fk fck EVk LSk AXB CELL.
    change INT_INV_EXIT with INT_INV_EXIT_E.
    eapply (epi_int_inv tt [(pn, pn + 4)] _) with (mb := mb) (used := 0) (gj := gj) (d := 0%nat) (m1 := m1) (Σ1 := Σ1);
      [exact PRE | exact FE | unfold INT_INV_FRAME, RT_STACK in *; clear - CSRT; lia | exact GSZ | exact SAVJ
      | | exact EVk | exact LSk | clear; lia |].
    -
      eapply ax_pres_trans; [| exact AXB].
      eapply agree_on_mono; [exact AXO|]. intros a [Ha1 Ha2]. split; [| exact Ha2]. intros Hx. apply Ha1. apply rin_ivs_app. left. exact Hx.
    -
      intros m' AGE. split; [reflexivity|]. split; [reflexivity|].
      pose proof EVk as (_ & HEAPk & _ & _ & AXPk & _).
      assert (INB : forall a, pn <= a < pn + Z.of_nat (cells_size [C4 (Z_to_bv 64 0)]) -> in_block LB a).
      { intros a Ha. cbn [cells_size csize Nat.add] in Ha. exists (qn, pn, 4). split; [exact HQN|]. cbn [blk_addr blk_size fst snd]. clear - Ha. lia. }
      eapply (rw_cells_agree _ mk m'); [exact AGE | | intros a Ha; right; right; destruct (INB a Ha) as (b & Hb & Hr); exists b; split; [apply in_or_app; right; exact Hb | exact Hr]].
      eapply (rw_cells_agree _ mb mk); [exact AXPk | exact CELL |].
      intros a Ha. split; [| right; right; exact (INB a Ha)].
      intros HX. unfold XW in HX. apply rin_ivs_app in HX. cbn [cells_size csize Nat.add] in Ha. destruct HX as [HX|HX].
      + revert HX. eapply (@blk_not_libw (push AR f 2) Σk OWk LB mk (qn, pn, 4) a HEAPk); [apply in_or_app; right; exact HQN | cbn [blk_addr blk_size fst snd]; clear - Ha; lia].
      + exact (WOWN a ltac:(clear - Ha; lia) HX).
  Qed.

End Top.

Definition BN_CTX_FREE_E : Z := 0x227418.

Lemma BN_CTX_free_null_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk bgbsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 112)%Z -> mem_inv bgbsegs m ->
  a0 = Z_to_bv 64 0 ->
  evt bgbsegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 112, bv_unsigned sp)]%Z lo m (fun _ _ => True))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_CTX_FREE_E) fc None m (seg_rom bgbsegs)).
Proof.
  intros until lo. intros ST LO MI ->. unfold BN_CTX_FREE_E.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  carve_frame 112%nat ST.
  apply (rw_cells_split_CB bgbsegs _ _ [] 112 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 14 step. step.
  step. if_true.
  do 13 step. release_frame FR ST (bv_unsigned sp). step. step.
  finish. exact I.
Qed.

Section Body2.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

  Variables (WSTACK WCOST : Z).
  Hypothesis WS96 : 112 <= WSTACK.
  Hypothesis INTW : int_inv_stmtA WSTACK WCOST 1.

  Lemma mod_inv_body : forall (Q : unit * ST -> rts RT -> machine_state -> Prop)
      (ra' sp gp u0 u1 u2 x10 x11 x12 x13 b4 b5 b6 b7 s7 s8 s11 u3 u4 u5 u6 s0w raw r_ a_ n_ c_ : word) (F' : bvmap 5 word) (fc' : bv 32)
      (Σ1 : rts RT) (ls : ST) (m1 : mem) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo spa f : Z) (q : bptr) (ras : list Z)
      (g : nat) (junk : list byte) (j0 j1 j2 : list byte)
      (rR ra_ rn : bnref) (aR aa an ac : Z) (qc : bptr) (TOTAL : Z),
    cenvA ((q, f + 32, 4) :: LB) PL lo (bv_unsigned sp) spa s0w raw (Some ras) TOTAL Σ1 ls OW m1
          ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 f)] ++ [CB g junk]) 0 Σ1 ls m1 OW ->
    lib_state ls m1 OW PL EA -> fr_room 1 ls OW ((q, f + 32, 4) :: LB) -> lo <= spa - WSTACK -> WCOST <= TOTAL ->
    f mod 8 = 0 -> (forall x, f + 32 <= x < f + 32 + 4 -> ~ rin_ivs (pl_frames PL) x) ->
    uk_ctx BN_MOD_INVERSE (bv_unsigned raw :: ras) ->
    ref_at ls OW PL rR aR -> hpl PL rR -> ref_at ls OW PL ra_ aa -> ra_ <> ROne -> ref_at ls OW PL rn an -> rn <> ROne -> pl_ctx PL = Some (ac, qc) ->
    r_ = wz aR -> a_ = wz aa -> n_ = wz an -> c_ = wz ac ->
    (forall (Σk : rts RT) (lsk : ST) (mk : mem) (OWk : list block) (loc : list cell) (used : Z) (mb : mem)
            (x1 x5 x6 x7 x9 y10 y11 y12 y13 y14 y15 y16 y17 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32),
       cenvA ((q, f + 32, 4) :: LB) PL lo (bv_unsigned sp) spa s0w raw (Some ras) TOTAL Σ1 ls OW mb (loc ++ [CB g junk]) used Σk lsk mk OWk ->
       lib_state lsk mk OWk PL EA -> used <= TOTAL -> ax_pres LB (bv_unsigned sp) (XW PL) m1 mb ->
       implA (TRet (tt, lsk)) Σk Q
         (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp x9 y10 y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 f) (Z_to_bv 64 aR) x20 x21 x22 x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) s11 x28 x29 x30 x31)
             Fk (wz MOD_INV_EXIT) fck None mk (seg_rom bgbsegs))) ->
    implA (BN_mod_inverse ops rR ra_ rn ls) Σ1 Q
      (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) u0 u1 u2 sp (Z_to_bv 64 spa) x10 x11 x12 x13 b4 b5 b6 b7
               (Z_to_bv 64 f) n_ a_ c_ r_ (Z_to_bv 64 0) s8 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) s11 u3 u4 u5 u6)
          F' (wz MOD_INV_BODY) fc' None m1 (seg_rom bgbsegs)).
  Proof.
    intros until TOTAL. intros ENV0 LS0 ROOM LOF HTOT F8 WOWN CTX HAR WRR HAa NROa HAn NROn HPC -> -> -> -> KK.
    unfold MOD_INV_BODY, MOD_INV_EXIT, MallocRep.wz in *.
    set (LB' := (q, f + 32, 4) :: LB) in *.
    destruct (ESPs LB' PL lo (bv_unsigned sp) spa s0w raw ras TOTAL Σ1 ls OW m1 _ _ _ _ _ _ ENV0) as (_ & ESP).
    pose proof ENV0 as (OK0 & HEAP0 & ST0 & MI0 & _ & CR0 & _ & _ & FR0 & FSZ0 & UW0).
    pose proof OK0 as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK0 & FAL0 & NOFR0).
    pose proof (AH_ceil _ _ _ _ HEAP0) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    assert (HQN : In (q, f + 32, 4) LB') by (left; reflexivity).
    pose proof (AH_range_gen _ _ _ _ (q, f + 32, 4) HEAP0 ltac:(apply in_or_app; right; exact HQN)) as (PN0 & _ & _ & PNC & PNI).
    cbn [blk_addr blk_size fst snd] in PN0, PNC, PNI.

    destruct (lib_state_cx_open [] ls m1 OW PL EA LS0) as (Hs & IX & CV & _).
    apply (cx_view_some _ _ _ _ _ _ _ _ HPC) in CV. destruct CV as (BC & _). change BN_CTX_SZ with 72 in BC.
    pose proof (AH_range _ _ _ _ _ _ _ HEAP0 BC) as (CA0 & _ & _ & CAC & _). clear BC Hs IX.
    apply implA_from_evt.
    step. if_cases KC; rewrite ?unsigned_lit in KC by (unfold BnHeapA.ACEIL in *; clear - CA0 CAC CEIL LOFB FBSP SPT; lia); zify_cond KC. 2:{ exfalso. clear - KC CA0. lia. }
    do 7 step.
    apply evt_done.

    eapply implA_postT.
    { eapply INTW with (lo := lo) (OW := OW) (LB := LB') (PL := PL) (EA := EA) (ras := bv_unsigned raw :: ras) (pn := f + 32) (qn := q);
        [ | exact ROOM | | | reflexivity | exact HAR | exact WRR | exact HAa | exact NROa | exact HAn | exact NROn | exact HPC | exact HQN
        | clear - F8; Z.div_mod_to_equations; lia | exact WOWN | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact ENV0 | exact LS0 | exact LOF | clear - HTOT; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV0).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_inverse_232b7c CTX). }
    cbv beta. intros [u lsk] Σk msk PO. unfold bn_postAX in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & Fk & fck & mk & OWk & PLk & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & (EPL & EY3 & CELL)).
    cbn [fst snd] in *. subst PLk y3. rewrite ESP in P3, P5.
    rewrite (ret_pc_even 2305380) by (clear; lia).

    assert (AGS : agree_on (fun a => spa <= a < 140737488355328) m1 mk).
    { eapply agree_on_mono; [exact P5|]. intros a Ha. split; [| left; exact Ha].
      intros HX. apply rin_ivs_app in HX. destruct HX as [HX|HX].
      - revert HX. apply (xw_stack_out Σ1 OW LB' m1 PL (bv_unsigned sp) 140737488355328 a HEAP0 FROK0). unfold BnHeapA.ACEIL in *. clear - Ha CEIL LOFB FBSP. lia.
      - cbn [rin_ivs fst snd] in HX. unfold BnHeapA.ACEIL in *. clear - HX Ha PNC CEIL LOFB. lia. }
    assert (EVk : cenvA LB' PL lo (bv_unsigned sp) spa s0w raw (Some ras) TOTAL Σ1 ls OW mk ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 f)] ++ [CB g junk]) WCOST Σk lsk mk OWk).
    { unfold cenvA. split; [exact OK0|]. split; [exact P1|]. split; [exact P3|]. split; [exact P4|]. split; [apply ax_pres_refl|].
      split; [clear - P6; lia|]. split; [exact P7|]. split; [exact P8|].
      split. { eapply rw_cells_agree; [exact AGS | exact FR0 |]. intros a Ha. rewrite cells_size_app, Nat2Z.inj_add, FSZ0 in Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta. clear - Ha SPT. lia. }
      split; [exact FSZ0|].
      unfold uw_opt in *. apply (uw_chain_agree m1 mk ras (bv_unsigned sp) (bv_unsigned s0w) UW0). eapply agree_on_mono; [exact AGS|]. intros a Ha. cbv beta in *. unfold USTACK_TOP in *. clear - Ha FBSP. lia. }
    assert (AXB : ax_pres LB (bv_unsigned sp) (XW PL) m1 mk).
    { eapply agree_on_mono; [exact P5|]. intros a [Ha1 Ha2]. split.
      - intros HX. apply rin_ivs_app in HX. destruct HX as [HX|HX]; [exact (Ha1 HX)|].
        cbn [rin_ivs fst snd] in HX. destruct HX as [HX|[]].
        destruct Ha2 as [Ha2|[Ha2|(b & Hb & Hr)]].
        + unfold BnHeapA.ACEIL in *. clear - HX Ha2 PNC CEIL LOFB FBSP. lia.
        + destruct Ha2 as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
          clear - Hin Hr HX PNI. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
        + assert (NE : blk_id b <> blk_id (q, f + 32, 4)).
          { intros E. pose proof (AH_nodup _ _ _ _ HEAP0) as ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND. unfold LB' in ND. cbn [map] in ND.
            inversion ND as [|? ? NI _]. apply NI. rewrite <- E. apply in_map. exact Hb. }
          pose proof (AH_disjoint_gen _ _ _ _ b (q, f + 32, 4) HEAP0 ltac:(apply in_or_app; right; right; exact Hb) ltac:(apply in_or_app; right; exact HQN) NE) as DJ.
          cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr HX. lia.
      - destruct Ha2 as [Ha2|[Ha2|(b & Hb & Hr)]]; [left; clear - Ha2 FBSP; lia | right; left; exact Ha2 | right; right; exists b; split; [right; exact Hb | exact Hr]]. }

    apply implA_from_evt.
    step. step. step. if_true.
    do 2 step.
    eapply evt_cut.
    { eapply (BN_CTX_free_null_specA _ (Z_to_bv 64 spa)) with (lo := lo); [rewrite ESP; exact P3 | rewrite ESP; clear - LOF WS96; lia | exact P4 | reflexivity]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m' & E & MUc & WMc & MIc & STc & _).
    subst ms'. rewrite ESP in *.
    destruct (cenv_belowA LB' PL EA lo (bv_unsigned sp) spa s0w raw (Some ras) TOTAL Σ1 ls OW mk _ _ _ _ _ _ _ 112 EVk P2 ltac:(clear; lia) ltac:(clear - LOF WS96; lia) MUc WMc MIc STc) as (EVk' & LSk').
    rewrite (ret_pc_even 2305444) by (clear; lia).
    apply evt_done. destruct u.
    eapply (KK Σk lsk m' OWk [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 f)] WCOST mk); [exact EVk' | exact LSk' | exact HTOT | exact AXB].
  Qed.
End Body2.

Section Top2.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

  Variable CS : Z.
  Hypothesis CSRT : RT_STACK <= CS.
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
  Hypothesis STK_ONE : BN_IS_ONE_STACK <= CS.
  Hypothesis BN_rshift1_walkA : forall AR1 : ARun, @rshift1_stmtA AR1 UK CS MC.

  Definition BN_MOD_INVERSE_STACK : Z := MOD_INV_FRAME + INT_INV_STACK CS.
  Definition BN_MOD_INVERSE_COST : Z := 2.

  Lemma BN_mod_inverse_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rR ra_ rn : bnref) (aR aa an ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo BN_MOD_INVERSE_STACK BN_MOD_INVERSE_COST -> fr_room 2 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MOD_INVERSE (bv_unsigned ra :: ras) ->
    tp = wz TP_A ->
    ref_at ls OW PL rR aR -> hpl PL rR -> ref_at ls OW PL ra_ aa -> ra_ <> ROne -> ref_at ls OW PL rn an -> rn <> ROne ->
    pl_ctx PL = Some (ac, qc) ->
    a0 = wz aR -> a1 = wz aa -> a2 = wz an -> a3 = wz ac ->
    implA (BN_mod_inverse (tree_ops bptr) rR ra_ rn ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_MOD_INVERSE_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz aR))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_INVERSE) fc None m (seg_rom bgbsegs)).
  Proof.
    intros until qc. intros PRE ROOM UW CTX -> HAR WRR HAa NROa HAn NROn HPC -> -> -> ->.
    unfold BN_MOD_INVERSE_STACK, BN_MOD_INVERSE_COST, INT_INV_STACK in *.
    eapply (pro_mod_inv _ _) with (d := 1%nat); [exact PRE | exact ROOM | exact UW | reflexivity | unfold MOD_INV_FRAME, INT_INV_FRAME; clear - CSRT; lia | clear; lia |].
    intros Σ1 m1 f spa q g junk gj ra' u0 u1 u2 x10 x11 x12 x13 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' j0 j1 j2 nv FE GSZ SAVJ FR FRV ACN.
    pose proof FE as (HEAP1 & LS1 & FROK1 & ST1 & CEIL & LOK & SPT & SP16 & MI1 & CNT1 & CRED1 & FAL & NOFR1 & ROOM1 & SPA32 & SPAL & SPAH & CR1 & AXO & UW1 & FRESH & GEO).
    pose proof (fr_env_cenv0 128 1 f 0 [(q, f + 32, 4)] Σ ls m OW LB PL EA sp lo _ (2 - 1) s0 ra ras spa Σ1 m1
                  ([CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 f)] ++ [CB g junk])
                  FE ltac:(clear; lia) ltac:(unfold MOD_INV_FRAME, INT_INV_FRAME, RT_STACK in *; clear - CSRT; lia) FR
                  ltac:(cbn [app cells_size csize Nat.add]; clear - GSZ; lia)) as EV0.
    cbn [app] in EV0 |- *.
    assert (F8 : f mod 8 = 0) by (destruct GEO as (_ & G2 & _); clear - G2; Z.div_mod_to_equations; lia).
    assert (WOWN : forall x, f + 32 <= x < f + 32 + 4 -> ~ rin_ivs (pl_frames PL) x).
    { intros x Hx HX. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (NLB & _)).
      apply rin_ivs_In in HX. destruct HX as (iv & Hiv & Hr). destruct (NLB iv Hiv) as (b & Hb & B1 & B2).
      pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 0) with 64 in O. clear - O B1 B2 Hr Hx. lia. }
    assert (W96 : 112 <= INT_INV_FRAME + CS) by (unfold INT_INV_FRAME; clear - CS16; lia).
    eapply (@mod_inv_body (push AR f 0) UK BE (INT_INV_FRAME + CS) 1 W96
              (@int_bn_mod_inverse_walkA (push AR f 0) UK BE CS CSRT CS112 CS16 STK_START STK_GET STK_END STK_SETW STK_COPY STK_UCMP STK_UADD STK_USUB STK_SUB STK_RSH STK_NNMOD STK_ONE BN_rshift1_walkA)
              _ ra' sp gp u0 u1 u2 x10 x11 x12 x13 b4 b5 b6 b7 (Z_to_bv 64 0) s8 s11 u3 u4 u5 u6 s0 ra (wz aR) (wz aa) (wz an) (wz ac) F' fc'
              Σ1 ls m1 OW LB PL EA lo spa f q ras g junk j0 j1 j2 rR ra_ rn aR aa an ac qc (2 - 1));
      [exact EV0 | exact LS1 | exact ROOM1 | unfold MOD_INV_FRAME, INT_INV_FRAME in *; clear - LOK; lia | clear; lia | exact F8 | exact WOWN | exact CTX
      | exact HAR | exact WRR | exact HAa | exact NROa | exact HAn | exact NROn | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity |].
    intros Σk lsk mk OWk loc used mb x1 x5 x6 x7 x9 y10 y11 y12 y13 y14 y15 y16 y17 x20 x21 x22 x23 x24 x28 x29 x30 x31 Fk fck EVk LSk USED AXB.
    eapply (epi_mod_inv tt _) with (mb := mb) (used := used) (gj := gj) (d := 1%nat) (m1 := m1) (Σ1 := Σ1);
      [exact PRE | exact FE | unfold MOD_INV_FRAME, INT_INV_FRAME, RT_STACK in *; clear - CSRT; lia | exact GSZ | exact SAVJ
      | exact (ax_pres_trans _ _ _ _ _ _ AXO AXB) | exact EVk | exact LSk | exact USED | split; reflexivity].
  Qed.

End Top2.
