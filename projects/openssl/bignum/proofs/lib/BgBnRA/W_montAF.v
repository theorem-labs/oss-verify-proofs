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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import W_copyA W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_expandAF W_copyAF W_callsAF W_ctxAF W_ctx_getAF W_ctx_endAF ExpKitAF AFrameKit AFrameEnv.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_MUL_MONT_FIXED_TOP : Z := 0x227550.
Definition BN_MOD_MUL_MONTGOMERY : Z := 0x227508.
Definition BN_TO_MONT_FIXED_TOP : Z := 0x227c1c.
Definition BN_TO_MONTGOMERY : Z := 0x226fb8.
Definition BN_FROM_MONT_FIXED_TOP : Z := 0x227b78.
Definition BN_FROM_MONTGOMERY : Z := 0x227b30.
Definition BN_FROM_MONTGOMERY_WORD : Z := 0x2276b8.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Proofs.

  Variables (CS CSM CMM CFW : Z).
  Hypothesis CSstart : BN_CTX_START_STACK <= CS.
  Hypothesis CSget : BN_CTX_GET_STACK <= CS.
  Hypothesis CSend : BN_CTX_END_STACK <= CS.
  Hypothesis CScopy : BN_COPY_STACK <= CS.
  Hypothesis CSM16 : 16 <= CSM.
  Hypothesis CMM0 : 0 <= CMM.
  Hypothesis CFW0 : 0 <= CFW.
  Definition MONT_MUL2_STACK : Z := 32 + CSM.
  Definition MONT_FROM_STACK : Z := 64 + CS.
  Definition MONT_FROM2_STACK : Z := 32 + (64 + CS).
  Definition MONT_FROM_COST : Z := 3 * MC + CFW.

  Ltac strip2 l := lazymatch l with
    | cons _ (cons _ nil) => constr:(@nil cell)
    | cons ?x ?t => let r := strip2 t in constr:(cons x r)
    end.

  Hypothesis bn_mul_mont_fixed_top_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ rb : bnref) (ar aa ab am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CSM CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MUL_MONT_FIXED_TOP (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> ref_at ls OW PL rb ab -> wref PL rr -> rb <> ROne -> nbuf PL ra_ -> nbuf PL rb ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz ab -> a3 = wz am -> a4 = wz ac ->
    implA (bn_mul_mont_fixed_top (tree_ops bptr) rr ra_ rb ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MUL_MONT_FIXED_TOP) fc None m (seg_rom bgasegs)).

  Hypothesis bn_from_montgomery_word_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rt rx : bnref) (at_ ax am : Z) (qm : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CFW ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_FROM_MONTGOMERY_WORD (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rt at_ -> ref_at ls OW PL rx ax -> wref PL rt -> wref PL rx -> pl_mont PL = Some (am, qm) ->
    a0 = wz at_ -> a1 = wz ax -> a2 = wz am ->
    implA (bn_from_montgomery_word (tree_ops bptr) rt rx ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CFW (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FROM_MONTGOMERY_WORD) fc None m (seg_rom bgasegs)).

  Lemma BN_mod_mul_montgomery_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ rb : bnref) (ar aa ab am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo MONT_MUL2_STACK CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MOD_MUL_MONTGOMERY (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> ref_at ls OW PL rb ab -> wref PL rr -> rb <> ROne -> nbuf PL ra_ -> nbuf PL rb ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz ab -> a3 = wz am -> a4 = wz ac ->
    implA (BN_mod_mul_montgomery (tree_ops bptr) rr ra_ rb ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_MUL_MONTGOMERY) fc None m (seg_rom bgasegs)).
  Proof.
    intros until qc. intros PRE ROOM UW CTX -> HAr HAa HAb WRr NROb NBa NBb HPM HPC -> -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold MONT_MUL2_STACK in LO'.
    pose proof MC0 as MCP.
    unfold BN_MOD_MUL_MONTGOMERY, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    unfold BN_mod_mul_montgomery, bbind. cbn [bind tree_ops tbind fst snd].
    apply implA_from_evt.

    carve_frame 32%nat ST. do 7 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mP OW PL EA _ HEAP LS MU WM FROK WOK) as LS0.
    lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
      assert (EV0 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) CMM Σ ls OW m p 0 Σ ls mP OW) end.
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
    assert (LOFB16 : lo <= bv_unsigned sp + -32 - 16) by (clear - LO' CSM16; lia).

    apply evt_done.
    eapply implA_bind.
    { eapply (bn_mul_mont_fixed_top_walkA) with (lo := lo) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| | | | reflexivity | exact HAr | exact HAa | exact HAb | exact WRr | exact NROb | exact NBa | exact NBb | exact HPM | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV0 | exact LS0 | clear - LO'; lia | clear; lia].
      - eapply cenv_roomA; [exact EV0 | exact ROOM | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV0).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_mul_montgomery_227340 CTX).
    }
    cbv beta. intros [u1 ls1] Σ1 ms1 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) CMM Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV0))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m1 & OW1 & PL1 & -> & CP1 & (EPL1 & ->)).
    subst PL1. specialize (CP1 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) CMM Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV0 CP1) as (EV1 & LS1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
    rewrite (ret_pc_even 2258216) by (clear; lia).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HAr) as HAr1.

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
    step. step. step.
    eapply (ctop_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) CMM Σ ls OW m LOFB16);
      [exact EV1 | exact LS1 | exact HAr1 | exact WRr |].
    intros mC z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 lsC EVC LSC.
    rewrite (ret_pc_even 2258228) by (clear; lia).
    pose proof EVC as (_ & _ & STF & _ & _ & _ & _ & _ & FRF & _ & _). cbn [app] in FRF.
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) CMM Σ ls OW m _ _ _ _ _ _ EVC LSC ltac:(clear; lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    step. do 4 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_postA. do 17 eexists. exists mC, OW1, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact G1|]. split; [exact G2|]. split; [exact STF|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
    split; reflexivity.
  Qed.

  Lemma bn_to_mont_fixed_top_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ : bnref) (ar aa am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CSM CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_TO_MONT_FIXED_TOP (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> wref PL rr -> nbuf PL ra_ ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz am -> a3 = wz ac ->
    implA (bn_to_mont_fixed_top (tree_ops bptr) rr ra_ ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_TO_MONT_FIXED_TOP) fc None m (seg_rom bgasegs)).
  Proof.
    intros until qc. intros PRE ROOM UW CTX -> HAr HAa WRr NBa HPM HPC -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold MONT_MUL2_STACK in LO'.
    pose proof MC0 as MCP.
    unfold BN_TO_MONT_FIXED_TOP, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.

    pose proof (ref_at_montRR ls OW PL am qm HPM) as HARR.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HARR RMontRR_not_one) as (AM0 & AMC & _).
    assert (AMR : am < 2^63) by (clear - AMC C3 SPR; lia). clear AMC.
    pose proof (ref_at_al8A _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HARR RMontRR_not_one) as AM8.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    unfold bn_to_mont_fixed_top.
    apply implA_from_evt.
    carve_frame 16%nat ST. do 8 step. release_frame FR ST (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mX end.
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -16, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -16, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    apply evt_done.
    eapply implA_mono.
    { eapply (bn_mul_mont_fixed_top_walkA ra sp) with (lo := lo) (ras := ras) (rr := rr) (ra_ := ra_) (rb := RMontRR) (ar := ar) (aa := aa) (ab := am) (am := am) (ac := ac) (qm := qm) (qc := qc) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| exact ROOM | | | reflexivity | exact HAr | exact HAa | exact HARR | exact WRr | exact RMontRR_not_one | exact NBa | exact (hpl_nbuf PL RMontRR (hpl_mont PL RMontRR am qm eq_refl HPM)) | exact HPM | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - unfold bn_preA.
        split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
        split; [exact (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mX OW PL EA _ HEAP LS MU WM FROK WOK)|].
        split; [exact FROK|]. split; [exact ST|]. split; [exact CEIL|].
        split; [clear - LO'; lia|].
        split; [unfold USTACK_TOP; lia|]. split; [exact SP16|]. split; [exact MI|]. split; [exact CNT|]. split; [exact CRED|]. split; [exact FAL| exact NOFR].
      - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor].
      - exact (uk_ctx_tail _ _ _ E_bn_to_mont_fixed_top_227a5c CTX). }
    cbv beta. intros [u ls'] Σ' ms' PO. unfold bn_postA in *. cbn [fst snd] in *.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m' & OW' & PL' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    do 17 eexists. exists m', OW', PL'. split; [reflexivity|].
    do 4 (split; [assumption|]). split; [|split; [assumption| split; [assumption| split; [assumption| exact P9]]]].
    eapply ax_pres_trans; [|exact P5]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia)).
  Qed.

  Lemma BN_to_montgomery_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ : bnref) (ar aa am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo MONT_MUL2_STACK CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_TO_MONTGOMERY (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> wref PL rr -> nbuf PL ra_ ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz am -> a3 = wz ac ->
    implA (BN_to_montgomery (tree_ops bptr) rr ra_ ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_TO_MONTGOMERY) fc None m (seg_rom bgasegs)).
  Proof.
    intros until qc. intros PRE ROOM UW CTX -> HAr HAa WRr NBa HPM HPC -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold MONT_MUL2_STACK in LO'.
    pose proof MC0 as MCP.
    unfold BN_TO_MONTGOMERY, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.

    pose proof (ref_at_montRR ls OW PL am qm HPM) as HARR.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HARR RMontRR_not_one) as (AM0 & AMC & _).
    assert (AMR : am < 2^63) by (clear - AMC C3 SPR; lia). clear AMC.
    pose proof (ref_at_al8A _ _ _ _ _ _ _ _ _ HEAP PARTS NOFR HARR RMontRR_not_one) as AM8.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    unfold BN_to_montgomery.
    apply implA_from_evt.
    carve_frame 16%nat ST. do 8 step. release_frame FR ST (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mX end.
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -16, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -16, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    apply evt_done.
    eapply implA_mono.
    { eapply (BN_mod_mul_montgomery_walkA ra sp) with (lo := lo) (ras := ras) (rr := rr) (ra_ := ra_) (rb := RMontRR) (ar := ar) (aa := aa) (ab := am) (am := am) (ac := ac) (qm := qm) (qc := qc) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| exact ROOM | | | reflexivity | exact HAr | exact HAa | exact HARR | exact WRr | exact RMontRR_not_one | exact NBa | exact (hpl_nbuf PL RMontRR (hpl_mont PL RMontRR am qm eq_refl HPM)) | exact HPM | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - unfold bn_preA.
        split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
        split; [exact (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mX OW PL EA _ HEAP LS MU WM FROK WOK)|].
        split; [exact FROK|]. split; [exact ST|]. split; [exact CEIL|].
        split; [unfold MONT_MUL2_STACK; clear - LO'; lia|].
        split; [unfold USTACK_TOP; lia|]. split; [exact SP16|]. split; [exact MI|]. split; [exact CNT|]. split; [exact CRED|]. split; [exact FAL| exact NOFR].
      - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor].
      - exact (uk_ctx_tail _ _ _ E_BN_to_montgomery_226df8 CTX). }
    cbv beta. intros [u ls'] Σ' ms' PO. unfold bn_postA in *. cbn [fst snd] in *.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m' & OW' & PL' & -> & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    do 17 eexists. exists m', OW', PL'. split; [reflexivity|].
    do 4 (split; [assumption|]). split; [|split; [assumption| split; [assumption| split; [assumption| exact P9]]]].
    eapply ax_pres_trans; [|exact P5]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia)).
  Qed.

  Lemma bn_from_mont_fixed_top_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ : bnref) (ar aa am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo MONT_FROM_STACK MONT_FROM_COST ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_FROM_MONT_FIXED_TOP (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> wref PL rr -> ra_ <> ROne ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz am -> a3 = wz ac ->
    implA (bn_from_mont_fixed_top (tree_ops bptr) rr ra_ ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MONT_FROM_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FROM_MONT_FIXED_TOP) fc None m (seg_rom bgasegs)).
  Proof.
    intros until qc. intros PRE UW CTX -> HAr HAa WRr NROa HPM HPC -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold MONT_FROM_STACK in LO'.
    pose proof MC0 as MCP.
    unfold BN_FROM_MONT_FIXED_TOP, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    assert (CS16 : 16 <= CS) by (pose proof CSend as H; unfold BN_CTX_END_STACK in H; clear - H; lia).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    unfold bn_from_mont_fixed_top, bbind. cbn [bind tree_ops tbind fst snd].
    apply implA_from_evt.

    carve_frame 64%nat ST. do 14 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mP OW PL EA _ HEAP LS MU WM FROK WOK) as LS0.
    lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
      assert (EV0 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MONT_FROM_COST Σ ls OW m p 0 Σ ls mP OW) end.
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
      - eapply cenv_preA; [exact EV0 | exact LS0 | clear - LO' CSstart; lia | unfold MONT_FROM_COST; clear - MCP CFW0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV0).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_bn_from_mont_fixed_top_2279cc CTX).
    }
    cbv beta. intros [u1 ls1] Σ1 ms1 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MONT_FROM_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV0))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m1 & OW1 & PL1 & -> & CP1 & (EPL1 & INCL1)).
    subst PL1. specialize (CP1 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MONT_FROM_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV0 CP1) as (EV1 & LS1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
    rewrite (ret_pc_even 2259892) by (clear; lia).

    apply implA_from_evt. step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OW1) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV1 | exact LS1 | clear - LO' CSget; lia | unfold MONT_FROM_COST; clear - MCP CFW0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV1).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_bn_from_mont_fixed_top_2279d4 CTX).
    }
    cbv beta. intros [u2 ls2] Σ2 ms2 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MONT_FROM_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV1))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F2 & fc2 & m2 & OW2 & PL2 & -> & CP2 & (EPL2 & (ti & Et) & (at_ & HAt & ->) & INCL2)).
    subst PL2. specialize (CP2 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MONT_FROM_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV1 CP2) as (EV2 & LS2).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP2) as RS2.
    rewrite (ret_pc_even 2259900) by (clear; lia).
    pose proof (refs_stable_trans _ _ _ _ _ _ RS1 RS2) as RS02.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS02 HAr) as HAr2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS02 HAa) as HAa2.
    pose proof (proj1 (proj2 EV2)) as HEAP2. pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
    assert (NROt : u2 <> ROne) by (rewrite Et; unfold RPool, ROne, NFIX; lia).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROKK HAt NROt) as (At0 & AtC & _).
    assert (AtR : 0 < at_ < 2^64) by (clear - At0 AtC C3; lia). clear AtC.
    unfold MallocRep.wz.
    apply implA_from_evt.

    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
    step. step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_copy_walkA) with (lo := lo) (OW := OW2) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAt | exact HAa2 | rewrite Et; apply wref_pool | exact NROa | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV2 | exact LS2 | clear - LO' CScopy; lia | unfold MONT_FROM_COST; clear - MCP CFW0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV2).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_bn_from_mont_fixed_top_2279e4 CTX).
    }
    cbv beta. intros [u3 ls3] Σ3 ms3 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MONT_FROM_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV2))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & OW3 & PL3 & -> & CP3 & (EPL3 & -> & INCL3)).
    subst PL3. specialize (CP3 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MONT_FROM_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV2 CP3) as (EV3 & LS3).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP3) as RS3.
    rewrite (ret_pc_even 2259916) by (clear; lia).
    pose proof (refs_stable_trans _ _ _ _ _ _ RS02 RS3) as RS03.
    unfold MallocRep.wz.
    apply implA_from_evt.

    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
    step. step. step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_from_montgomery_word_walkA) with (lo := lo) (OW := OW3) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS03 HAr) | exact (ref_at_stable _ _ _ _ PL _ _ RS3 HAt) | exact WRr | rewrite Et; apply wref_pool | exact HPM | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV3 | exact LS3 | clear - LO'; lia | unfold MONT_FROM_COST; clear - MCP CFW0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV3).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_bn_from_mont_fixed_top_2279f8 CTX).
    }
    cbv beta. intros [u4 ls4] Σ4 ms4 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MONT_FROM_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV3))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F4 & fc4 & m4 & OW4 & PL4 & -> & CP4 & (EPL4 & ->)).
    subst PL4. specialize (CP4 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MONT_FROM_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV3 CP4) as (EV4 & LS4).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP4) as RS4.
    rewrite (ret_pc_even 2259936) by (clear; lia).

    apply implA_from_evt. step. step. step. step.
    apply evt_done.
    eapply implA_post_evt.
    { eapply (BN_CTX_end_walkA) with (lo := lo) (OW := OW4) (LB := LB) (PL := PL) (EA := EA);
        [| reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV4 | exact LS4 | clear - LO' CSend; lia | unfold MONT_FROM_COST; clear - MCP CFW0; lia].
    }
    cbv beta. intros [u5 ls5] Σ5 ms5 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) MONT_FROM_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV4))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & EOW5)).
    subst PL5. specialize (CP5 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MONT_FROM_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV4 CP5) as (EV5 & LS5).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5.
    rewrite (ret_pc_even 2259956) by (clear; lia).
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) MONT_FROM_COST Σ ls OW m _ _ _ _ _ _ EV5 LS5 ltac:(unfold MONT_FROM_COST; clear - MCP CFW0; lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof EV5 as (_ & _ & STF & _ & _ & _ & _ & _ & FRF & _ & _). cbn [app] in FRF.
    step. do 7 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_postA. do 17 eexists. exists m5, OW5, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact G1|]. split; [exact G2|]. split; [exact STF|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
    split; reflexivity.
  Qed.

  Lemma BN_from_montgomery_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ : bnref) (ar aa am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo MONT_FROM2_STACK MONT_FROM_COST ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_FROM_MONTGOMERY (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> wref PL rr -> ra_ <> ROne ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz am -> a3 = wz ac ->
    implA (BN_from_montgomery (tree_ops bptr) rr ra_ ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MONT_FROM_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FROM_MONTGOMERY) fc None m (seg_rom bgasegs)).
  Proof.
    intros until qc. intros PRE UW CTX -> HAr HAa WRr NROa HPM HPC -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold MONT_FROM2_STACK in LO'.
    pose proof MC0 as MCP.
    unfold BN_FROM_MONTGOMERY, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    assert (CS16 : 16 <= CS) by (pose proof CSend as H; unfold BN_CTX_END_STACK in H; clear - H; lia).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    unfold BN_from_montgomery, bbind. cbn [bind tree_ops tbind fst snd].
    apply implA_from_evt.

    carve_frame 32%nat ST. do 7 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mP OW PL EA _ HEAP LS MU WM FROK WOK) as LS0.
    lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
      assert (EV0 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) MONT_FROM_COST Σ ls OW m p 0 Σ ls mP OW) end.
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
    assert (LOFB16 : lo <= bv_unsigned sp + -32 - 16) by (clear - LO' CS16; lia).

    apply evt_done.
    eapply implA_bind.
    { eapply (bn_from_mont_fixed_top_walkA) with (lo := lo) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAr | exact HAa | exact WRr | exact NROa | exact HPM | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV0 | exact LS0 | unfold MONT_FROM_STACK; clear - LO'; lia | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV0).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_from_montgomery_227968 CTX).
    }
    cbv beta. intros [u1 ls1] Σ1 ms1 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) MONT_FROM_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV0))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m1 & OW1 & PL1 & -> & CP1 & (EPL1 & ->)).
    subst PL1. specialize (CP1 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) MONT_FROM_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV0 CP1) as (EV1 & LS1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
    rewrite (ret_pc_even 2259792) by (clear; lia).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HAr) as HAr1.

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
    step. step. step.
    eapply (ctop_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) MONT_FROM_COST Σ ls OW m LOFB16);
      [exact EV1 | exact LS1 | exact HAr1 | exact WRr |].
    intros mC z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 lsC EVC LSC.
    rewrite (ret_pc_even 2259804) by (clear; lia).
    pose proof EVC as (_ & _ & STF & _ & _ & _ & _ & _ & FRF & _ & _). cbn [app] in FRF.
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) MONT_FROM_COST Σ ls OW m _ _ _ _ _ _ EVC LSC ltac:(clear; lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    step. do 4 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_postA. do 17 eexists. exists mC, OW1, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact G1|]. split; [exact G2|]. split; [exact STF|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
    split; reflexivity.
  Qed.
End Proofs.

End WithRT.
