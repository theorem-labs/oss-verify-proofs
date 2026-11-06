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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnDivWords BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith BgMont BgExp.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import MState Mem Cells Step Arr Bytes Frame.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnAKitAF BnCallAF W_expandAF W_callsAF W_ctxAF W_ctx_getAF W_ctx_endAF W_lshiftAF W_div_tailAF W_divAF W_bndivAF W_uaddAF W_addAF W_subAF W_set_wordAF W_cmpAF AFrameComp ExpKitAF W_small3A W_calls3AF W_nnmodAF ExpStmtF ExpBodyKitF PlaceMont PlaceKitA W_mont_ctxAF W_mont_freeAF MontKitAF Fr_exp_mont W_exp_montAF W_exp_mont_gAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Top.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).

  Variables (CS CMM CFM CMS : Z).
  Hypothesis CSstart : BN_CTX_START_STACK <= CS.
  Hypothesis CSget : BN_CTX_GET_STACK <= CS.
  Hypothesis CSend : BN_CTX_END_STACK <= CS.
  Hypothesis CSnnmod : BN_NNMOD_STACK <= CS.
  Hypothesis CSsetw : BN_SET_WORD_STACK <= CS.
  Hypothesis CSnb : BN_NUM_BITS_STACK <= CS.
  Hypothesis CSucmp : BN_UCMP_STACK <= CS.
  Hypothesis CSwexp : BN_WEXPAND_STACK <= CS.
  Hypothesis CSnew : BN_MONT_CTX_NEW_STACK <= CS.
  Hypothesis CSfree : BN_MONT_CTX_FREE_STACK <= CS.
  Hypothesis CSrt : RT_STACK <= CS.
  Hypothesis CMM0 : 0 <= CMM.
  Hypothesis CFM0 : 0 <= CFM.
  Hypothesis CMS0 : 0 <= CMS.

  Hypothesis bn_mul_mont_fixed_top_walkA : forall (AR1 : ARun)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR1)) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ rb : bnref) (ar aa ab am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x227550 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> ref_at ls OW PL rb ab -> wref PL rr -> rb <> ROne -> nbuf PL ra_ -> nbuf PL rb ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz ab -> a3 = wz am -> a4 = wz ac ->
    implA (bn_mul_mont_fixed_top (tree_ops bptr) rr ra_ rb ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x227550) fc None m (seg_rom bgasegs)).
  Hypothesis bn_to_mont_fixed_top_walkA : forall (AR1 : ARun)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR1)) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ : bnref) (ar aa am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x227c1c (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> wref PL rr -> nbuf PL ra_ ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz am -> a3 = wz ac ->
    implA (bn_to_mont_fixed_top (tree_ops bptr) rr ra_ ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x227c1c) fc None m (seg_rom bgasegs)).
  Hypothesis BN_from_montgomery_walkA : forall (AR1 : ARun)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR1)) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ : bnref) (ar aa am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CFM ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x227b30 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> wref PL rr -> ra_ <> ROne ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz am -> a3 = wz ac ->
    implA (BN_from_montgomery (tree_ops bptr) rr ra_ ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CFM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x227b30) fc None m (seg_rom bgasegs)).
  Hypothesis BN_MONT_CTX_set_walkA : forall (AR1 : ARun)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR1)) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rd : bnref) (ad am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CMS ->
    fr_room 3 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x227e44 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rd ad -> rd <> ROne -> pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) -> pl_bn PL RTmod = None ->
    a0 = wz am -> a1 = wz ad -> a2 = wz ac ->
    implA (BN_MONT_CTX_set (tree_ops bptr) rd ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMS (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x227e44) fc None m (seg_rom bgasegs)).

  Definition BN_MOD_EXP_MONT_STACK : Z := EXP_MONT_FRAME + CS.
  Definition BN_MOD_EXP_MONT_COST : Z := 1 + EXP_MONT_TOTAL CMM CFM CMS.

  Lemma BN_mod_exp_mont_walkA : exp_stmtAn_f BN_MOD_EXP_MONT BN_MOD_EXP_MONT_STACK BN_MOD_EXP_MONT_COST 4 (BN_mod_exp_mont (tree_ops bptr)) (Some (wz 0)).
  Proof.
    unfold exp_stmtAn_f, BN_MOD_EXP_MONT_STACK, BN_MOD_EXP_MONT_COST. intros until qc. intros PRE ROOM UW CTX -> HArr HAra HArp HArm HPr NRa NRp NRm NBa EC HFR -> -> -> -> -> E5.
    rewrite (E5 (wz 0) eq_refl). clear E5.
    destruct HFR as (_ & _ & _ & HFM & HFT).
    assert (T0 : 0 <= EXP_MONT_TOTAL CMM CFM CMS) by (unfold EXP_MONT_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST, MC; clear - CMM0 CFM0 CMS0; lia).
    eapply (pro_exp_mont _ _) with (d := 3%nat); [exact PRE | exact ROOM | exact UW | reflexivity | clear - CSrt; lia | clear - T0; lia |].
    intros Σ1 m1 f spa q g junk gj ra' u0 u1 u2 x10 x11 x12 x13 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j16 j17 jv FE GSZ SAVJ FR FRV ACN.
    pose proof FE as (HEAP1 & LS1 & FROK1 & ST1 & CEIL & LOK & SPT & SP16 & MI1 & CNT1 & CRED1 & FAL & NOFR1 & ROOM1 & SPA32 & SPAL & SPAH & CR1 & AXO & UW1 & FRESH & GEO).
    replace (1 + EXP_MONT_TOTAL CMM CFM CMS - 1) with (EXP_MONT_TOTAL CMM CFM CMS) in * by (clear; lia).
    pose proof (fr_env_cenv0 256 3%nat f 3 [(q, f + 32, 256)] Σ ls m OW LB PL EA sp lo _ (EXP_MONT_TOTAL CMM CFM CMS) s0 ra ras spa Σ1 m1
                  ([CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; CB 8 j10; CB 8 j11; CB 8 j12; CB 8 j13; CB 8 j14; C8 (wz arp); CB 8 j16; CB 8 j17; C8 (Z_to_bv 64 f)] ++ [CB g junk])
                  FE ltac:(clear; lia) ltac:(unfold EXP_MONT_FRAME, RT_STACK in *; clear - CSrt; lia) FR
                  ltac:(cbn [app cells_size csize Nat.add]; clear - GSZ; lia)) as EV0.
    pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NOFR).
    assert (LOKB : lo <= spa - CS) by (unfold EXP_MONT_FRAME in LOK; clear - LOK; lia).
    assert (TIGHT : cnt_bal ls OW + Z.of_nat (length ((q, f + 32, 256) :: LB)) + 72 <= LIVE_MAX).
    { destruct ROOM as [_ R]. cbn [length]. clear - R. unfold block in *. lia. }
    eapply (@body_main (push AR f 3) UK BE CS CMM CFM CMS CSstart CSget CSend CSnnmod CSsetw CSnb CSucmp CSnew CSfree CMM0 CFM0 CMS0
              (bn_mul_mont_fixed_top_walkA (push AR f 3)) (bn_to_mont_fixed_top_walkA (push AR f 3)) (BN_from_montgomery_walkA (push AR f 3)) (BN_MONT_CTX_set_walkA (push AR f 3))
              _ sp gp s0 ra Σ1 ls m1 OW LB PL EA lo spa f (EXP_MONT_TOTAL CMM CFM CMS) q ras g junk rr ra_ rp rm arr ara arp arm ac qc);
      [ apply Z.le_refl
      | exact LOKB
      | exact ROOM1
      | exact TIGHT
      | left; reflexivity
      | intros xq Hxq; apply (fr_no_placed PL LB f 3%nat xq NOFR FRESH); unfold fs_size; change (Z.shiftl 64 (Z.of_nat 3)) with 512; clear - Hxq; lia
      | exact CTX | exact EC | exact HFM | exact HFT | exact HArr | exact HAra | exact HArp | exact HArm | exact HPr | exact NRa | exact NRp | exact NRm | exact NBa
      |
      | intros am qm; exact (@gueron_fill_allA (push AR f 3) UK BE CS CSwexp sp gp s0 ra Σ1 ls OW LB PL EA lo spa f (EXP_MONT_TOTAL CMM CFM CMS) q ras g junk rm arr arp arm ac
                               LOKB CTX NRm am qm)
      | exact EV0 | exact LS1 | exact FRV ].
    intros Σk lsk mk OWk loc used mb x1 x5 x6 x7 x9 y10 y11 y12 y13 y14 y15 y16 y17 x20 x21 rv x24 x25 x26 x27 x28 x29 x30 x31 Fk fck EVk LSk USED AXB ->.
    eapply (epi_exp_mont tt _) with (mb := mb) (used := used) (gj := gj) (d := 3%nat) (m1 := m1) (Σ1 := Σ1);
      [exact PRE | replace (1 + EXP_MONT_TOTAL CMM CFM CMS - 1) with (EXP_MONT_TOTAL CMM CFM CMS) by (clear; lia); exact FE | unfold EXP_MONT_FRAME, RT_STACK in *; clear - CSrt; lia | exact GSZ | exact SAVJ
      | exact (ax_pres_trans _ _ _ _ _ _ AXO AXB) | replace (1 + EXP_MONT_TOTAL CMM CFM CMS - 1) with (EXP_MONT_TOTAL CMM CFM CMS) by (clear; lia); exact EVk | exact LSk | clear - USED; lia | split; reflexivity].
  Qed.
End Top.
