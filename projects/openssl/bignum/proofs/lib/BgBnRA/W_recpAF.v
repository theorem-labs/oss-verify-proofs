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
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_expandAF W_callsAF W_ctxAF W_ctx_getAF W_ctx_endAF AFrameKit AFrameEnv ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_MOD_MUL_RECIPROCAL : Z := 0x2b1c78.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Proofs.

  Variables (CS CM CDR : Z).
  Hypothesis CSstart : BN_CTX_START_STACK <= CS.
  Hypothesis CSget : BN_CTX_GET_STACK <= CS.
  Hypothesis CSend : BN_CTX_END_STACK <= CS.
  Hypothesis CM0 : 0 <= CM.
  Hypothesis CDR0 : 0 <= CDR.
  Definition BN_MOD_MUL_RECP_STACK : Z := 64 + CS.
  Definition BN_MOD_MUL_RECP_COST : Z := 2 * MC + CM + CDR.

  Hypothesis BN_sqr_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x23002c (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> hpl PL rr -> rx <> ROne -> nbuf PL rx -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ac ->
    implA (BN_sqr (tree_ops bptr) rr rx ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x23002c) fc None m (seg_rom bgasegs)).

  Hypothesis BN_mul_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx ry : bnref) (ar ax ay ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CM ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x22a8e0 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> ref_at ls OW PL ry ay -> hpl PL rr -> rx <> ROne -> ry <> ROne -> nbuf PL rx -> nbuf PL ry -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz ac ->
    implA (BN_mul (tree_ops bptr) rr rx ry ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x22a8e0) fc None m (seg_rom bgasegs)).

  Hypothesis BN_div_recp_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rm : bnref) (ar am an ac : Z) (qc : bptr) (q : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CDR ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x2b1d58 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rm am -> hpl PL rr -> rm <> ROne -> nbuf PL rm -> recp_at PL an -> In (q, an, 64) LB -> an mod 8 = 0 -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz 0 -> a1 = wz ar -> a2 = wz am -> a3 = wz an -> a4 = wz ac ->
    implA (BN_div_recp (tree_ops bptr) None (Some rr) rm ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CDR (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x2b1d58) fc None m (seg_rom bgasegs)).

  Lemma BN_mod_mul_reciprocal_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx ry : bnref) (ar ax ay an ac : Z) (qc : bptr) (q : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo BN_MOD_MUL_RECP_STACK BN_MOD_MUL_RECP_COST ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MOD_MUL_RECIPROCAL (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> ref_at ls OW PL ry ay -> hpl PL rr -> rx <> ROne -> ry <> ROne -> nbuf PL rx -> nbuf PL ry ->
    recp_at PL an -> In (q, an, 64) LB -> an mod 8 = 0 -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz an -> a4 = wz ac ->
    implA (BN_mod_mul_reciprocal (tree_ops bptr) rr rx ry ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_MOD_MUL_RECP_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_MUL_RECIPROCAL) fc None m (seg_rom bgasegs)).
  Proof.
    intros until q. intros PRE ROOM UW CTX -> HAr HAx HAy WRr NROx NROy NBx NBy HRC INQ AL8 HPC -> -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold BN_MOD_MUL_RECP_STACK in LO'.
    pose proof MC0 as MCP.
    assert (CS16 : 16 <= CS) by (pose proof CSend as H; unfold BN_CTX_END_STACK in H; clear - H; lia).
    unfold BN_MOD_MUL_RECIPROCAL, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    assert (AxR : 0 < ax < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAx NROx) as (X & Y & _); clear - X Y C3; lia).
    assert (AyR : 0 < ay < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAy NROy) as (X & Y & _); clear - X Y C3; lia).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    unfold BN_mod_mul_reciprocal, bbind, bret. cbn [bind ret tree_ops tbind fst snd].
    apply implA_from_evt.

    carve_frame 64%nat ST. do 16 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mP OW PL EA _ HEAP LS MU WM FROK WOK) as LS0.
    assert (EV0 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_MOD_MUL_RECP_COST Σ ls OW m [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls mP OW).
    { unfold cenvA, cenv_ok.
      split; [split; [exact CEIL|]; split; [lia|]; split; [lia|]; split; [unfold USTACK_TOP; lia|]; split; [exact SP16|];
              split; [clear - SP16; Z.div_mod_to_equations; lia|]; split; [exact CNT|]; split; [exact CRED|]; split; [exact FROK|]; split; [exact FAL| exact NOFR]|].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
      split; [exact ST|]. split; [exact MI|].
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))|].
      split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
      split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
      eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
    pose proof EV0 as (OK & _).
    pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & FROKK & _ & _).
    clear HEAP LS ST MI MU WM HWL WOK FR PRE PARTS.

    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_start_walkA) with (lo := lo) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV0 | exact LS0 | clear - LO' CSstart; lia | unfold BN_MOD_MUL_RECP_COST; clear - MCP CM0 CDR0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV0).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_mul_reciprocal_2b1ad4 CTX).
    }
    cbv beta. intros [u1 ls1] Σ1 ms1 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) BN_MOD_MUL_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV0))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m1 & OW1 & PL1 & -> & CP1 & (EPL1 & INCL1)).
    subst PL1. specialize (CP1 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_MOD_MUL_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV0 CP1) as (EV1 & LS1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
    rewrite (ret_pc_even 2825404) by (clear; lia).

    apply implA_from_evt. step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OW1) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV1 | exact LS1 | clear - LO' CSget; lia | unfold BN_MOD_MUL_RECP_COST; clear - MCP CM0 CDR0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV1).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_mul_reciprocal_2b1adc CTX).
    }
    cbv beta. intros [u2 ls2] Σ2 ms2 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) BN_MOD_MUL_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV1))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F2 & fc2 & m2 & OW2 & PL2 & -> & CP2 & (EPL2 & (ti & Et) & (at_ & HAt & ->) & INCL2)).
    subst PL2. specialize (CP2 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_MOD_MUL_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV1 CP2) as (EV2 & LS2).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP2) as RS2.
    rewrite (ret_pc_even 2825412) by (clear; lia).
    pose proof (refs_stable_trans _ _ _ _ _ _ RS1 RS2) as RS02.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS02 HAr) as HAr2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS02 HAx) as HAx2.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS02 HAy) as HAy2.
    pose proof (proj1 (proj2 EV2)) as HEAP2. pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2. pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
    assert (NROt : u2 <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROKK HAt NROt) as (At0 & AtC & _).
    assert (AtR : 0 < at_ < 2^64) by (clear - At0 AtC C3; lia). clear AtC.
    unfold MallocRep.wz.
    apply implA_from_evt.

    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
    step. if_cases KY; rewrite ?unsigned_lit in KY by (clear - AyR; lia); zify_cond KY; [exfalso; clear - KY AyR; lia| clear KY].
    step. step.

    step. if_cases KE; rewrite ?unsigned_lit in KE by (clear - AxR AyR; lia); zify_cond KE.
    -
      assert (Exy : rx = ry).
      { destruct (Nat.eq_dec rx ry) as [E|NE]; [exact E| exfalso].
        pose proof (struct_disj Σ2 OW2 LB m2 HEAP2 ls2 PL EA _ _ PARTS2 FROKK rx ry ax ay NE HAx2 HAy2) as D. clear - D KE. lia. }
      subst ry. rewrite Nat.eqb_refl.
      do 2 step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_sqr_walkA) with (lo := lo) (OW := OW2) (LB := LB) (PL := PL) (EA := EA);
        [| | | | reflexivity | exact HAt | exact HAx2 | rewrite Et; apply hpl_pool | exact NROx | first [exact NBx | exact NBy] | exact HPC | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV2 | exact LS2 | clear - LO'; lia | unfold BN_MOD_MUL_RECP_COST; clear - MCP CM0 CDR0; lia].
      - eapply cenv_roomA; [exact EV2 | exact ROOM | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV2).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_mul_reciprocal_2b1b14 CTX).
    }
    cbv beta. intros [u3 ls3] Σ3 ms3 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) BN_MOD_MUL_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV2))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & OW3 & PL3 & -> & CP3 & (EPL3 & ->)).
    subst PL3. specialize (CP3 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_MOD_MUL_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV2 CP3) as (EV3 & LS3).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP3) as RS3.
    rewrite (ret_pc_even 2825468) by (clear; lia).
      apply implA_from_evt. step. if_false.

      do 5 step. step.
      pose proof (refs_stable_trans _ _ _ _ _ _ RS02 RS3) as RS03.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_div_recp_walkA) with (lo := lo) (OW := OW3) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS03 HAr) | exact (ref_at_stable _ _ _ _ PL _ _ RS3 HAt) | exact WRr | exact NROt | rewrite Et; apply nbuf_pool | exact HRC | exact INQ | exact AL8 | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV3 | exact LS3 | clear - LO'; lia | unfold BN_MOD_MUL_RECP_COST; clear - MCP CM0 CDR0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV3).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_mul_reciprocal_2b1b30 CTX).
    }
    cbv beta. intros [u4 ls4] Σ4 ms4 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) BN_MOD_MUL_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV3))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F4 & fc4 & m4 & OW4 & PL4 & -> & CP4 & (EPL4 & ->)).
    subst PL4. specialize (CP4 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_MOD_MUL_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV3 CP4) as (EV4 & LS4).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP4) as RS4.
    rewrite (ret_pc_even 2825496) by (clear; lia).

      apply implA_from_evt. step. step. step. step.
    apply evt_done.
    eapply implA_post_evt.
    { eapply (BN_CTX_end_walkA) with (lo := lo) (OW := OW4) (LB := LB) (PL := PL) (EA := EA);
        [| reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV4 | exact LS4 | clear - LO' CSend; lia | unfold BN_MOD_MUL_RECP_COST; clear - MCP CM0 CDR0; lia].
    }
    cbv beta. intros [u5 ls5] Σ5 ms5 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) BN_MOD_MUL_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV4))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & EOW5)).
    subst PL5. specialize (CP5 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_MOD_MUL_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV4 CP5) as (EV5 & LS5).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5.
    rewrite (ret_pc_even 2825516) by (clear; lia).
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_MOD_MUL_RECP_COST Σ ls OW m _ _ _ _ _ _ EV5 LS5 ltac:(unfold BN_MOD_MUL_RECP_COST; clear - MCP CM0 CDR0; lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof EV5 as (_ & _ & STF & _ & _ & _ & _ & _ & FRF & _ & _). cbn [app] in FRF.
    step. do 8 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_postA. do 17 eexists. exists m5, OW5, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact G1|]. split; [exact G2|]. split; [exact STF|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
    split; reflexivity.
    -
      assert (NE : rx <> ry).
      { intros E. subst ry. pose proof (ref_at_fun _ _ _ _ _ _ ND2 HAx2 HAy2) as EA_. clear - EA_ KE. lia. }
      replace ((rx =? ry)%nat) with false by (symmetry; apply Nat.eqb_neq; exact NE).
      do 3 step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_mul_walkA) with (lo := lo) (OW := OW2) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAt | exact HAx2 | exact HAy2 | rewrite Et; apply hpl_pool | exact NROx | exact NROy | exact NBx | exact NBy | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV2 | exact LS2 | clear - LO'; lia | unfold BN_MOD_MUL_RECP_COST; clear - MCP CM0 CDR0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV2).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_mul_reciprocal_2b1afc CTX).
    }
    cbv beta. intros [u3 ls3] Σ3 ms3 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) BN_MOD_MUL_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV2))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & OW3 & PL3 & -> & CP3 & (EPL3 & ->)).
    subst PL3. specialize (CP3 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_MOD_MUL_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV2 CP3) as (EV3 & LS3).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP3) as RS3.
    rewrite (ret_pc_even 2825444) by (clear; lia).
      apply implA_from_evt. step. if_true.

      do 5 step. step.
      pose proof (refs_stable_trans _ _ _ _ _ _ RS02 RS3) as RS03.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_div_recp_walkA) with (lo := lo) (OW := OW3) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS03 HAr) | exact (ref_at_stable _ _ _ _ PL _ _ RS3 HAt) | exact WRr | exact NROt | rewrite Et; apply nbuf_pool | exact HRC | exact INQ | exact AL8 | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV3 | exact LS3 | clear - LO'; lia | unfold BN_MOD_MUL_RECP_COST; clear - MCP CM0 CDR0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV3).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_mul_reciprocal_2b1b30 CTX).
    }
    cbv beta. intros [u4 ls4] Σ4 ms4 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) BN_MOD_MUL_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV3))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F4 & fc4 & m4 & OW4 & PL4 & -> & CP4 & (EPL4 & ->)).
    subst PL4. specialize (CP4 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_MOD_MUL_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV3 CP4) as (EV4 & LS4).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP4) as RS4.
    rewrite (ret_pc_even 2825496) by (clear; lia).

      apply implA_from_evt. step. step. step. step.
    apply evt_done.
    eapply implA_post_evt.
    { eapply (BN_CTX_end_walkA) with (lo := lo) (OW := OW4) (LB := LB) (PL := PL) (EA := EA);
        [| reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV4 | exact LS4 | clear - LO' CSend; lia | unfold BN_MOD_MUL_RECP_COST; clear - MCP CM0 CDR0; lia].
    }
    cbv beta. intros [u5 ls5] Σ5 ms5 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) BN_MOD_MUL_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV4))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & EOW5)).
    subst PL5. specialize (CP5 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_MOD_MUL_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV4 CP5) as (EV5 & LS5).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5.
    rewrite (ret_pc_even 2825516) by (clear; lia).
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_MOD_MUL_RECP_COST Σ ls OW m _ _ _ _ _ _ EV5 LS5 ltac:(unfold BN_MOD_MUL_RECP_COST; clear - MCP CM0 CDR0; lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof EV5 as (_ & _ & STF & _ & _ & _ & _ & _ & FRF & _ & _). cbn [app] in FRF.
    step. do 8 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_postA. do 17 eexists. exists m5, OW5, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact G1|]. split; [exact G2|]. split; [exact STF|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
    split; reflexivity.
  Qed.
End Proofs.

End WithRT.
