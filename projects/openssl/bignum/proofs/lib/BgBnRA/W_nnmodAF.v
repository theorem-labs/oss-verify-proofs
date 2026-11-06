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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgWords BgArith.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_expandAF W_callsAF W_lshiftAF W_div_tailAF W_divAF W_bndivAF W_uaddAF W_addAF W_subAF ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_NNMOD : Z := 0x23233c.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Proofs.
  Definition BN_NNMOD_STACK : Z := 48 + BN_DIV_TOP_STACK.
  Definition BN_NNMOD_COST : Z := BN_DIV_FT_COST + MC.

  Ltac strip2 l := lazymatch l with
    | cons _ (cons _ nil) => constr:(@nil cell)
    | cons ?x ?t => let r := strip2 t in constr:(cons x r)
    end.

  Lemma BN_nnmod_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx rm : bnref) (ar ax am ac : Z) (qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo BN_NNMOD_STACK BN_NNMOD_COST ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_NNMOD (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rx ax -> ref_at ls OW PL rm am -> hpl PL rr -> rx <> ROne -> rm <> ROne -> nbuf PL rx -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz am -> a3 = wz ac ->
    implA (BN_nnmod (tree_ops bptr) rr rx rm ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_NNMOD_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_NNMOD) fc None m (seg_rom bgasegs)).
  Proof.
    intros until qc. intros PRE UW CTX -> HAr HAx HAm HPr NROx NROm NBx HPC -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold BN_NNMOD_STACK, BN_DIV_TOP_STACK, BN_DIV_FT_STACK, BN_LSHIFT_STACK, BN_ADD_STACK, BN_SUB_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
    pose proof MC0 as MCP.
    unfold BN_NNMOD, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (proj1 (hpl_wref _ _ HPr)) as NROr.
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    assert (ArR : 0 < ar < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAr NROr) as (X & Y & _); clear - X Y C3; lia).
    assert (AmR : 0 < am < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAm NROm) as (X & Y & _); clear - X Y C3; lia).
    destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    unfold BN_nnmod, BN_mod, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd].
    apply implA_from_evt.

    carve_frame 48%nat ST. do 7 step. step.
    step. if_cases KE; rewrite ?unsigned_lit in KE by (clear - ArR AmR; lia); zify_cond KE.
    {
      assert (Erm : rr = rm).
      { destruct (Nat.eq_dec rr rm) as [E|NE]; [exact E| exfalso].
        pose proof (struct_disj Σ OW LB m HEAP ls PL EA _ _ PARTS FROK rr rm ar am NE HAr HAm) as D. clear - D KE. lia. }
      replace ((rr =? rm)%nat) with true by (symmetry; apply Nat.eqb_eq; exact Erm).
      apply evt_done. apply implA_unr. }
    assert (NErm : rr <> rm).
    { intros E. pose proof HAm as HAm'. rewrite <- E in HAm'. pose proof (ref_at_fun _ _ _ _ _ _ ND HAr HAm') as EA_. clear - EA_ KE. lia. }
    replace ((rr =? rm)%nat) with false by (symmetry; apply Nat.eqb_neq; exact NErm).

    do 3 step. do 3 step. do 3 step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -48, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mP OW PL EA _ HEAP LS MU WM FROK WOK) as LS0.
    lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
      assert (EV0 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_NNMOD_COST Σ ls OW m p 0 Σ ls mP OW) end.
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
    assert (LOFB16 : lo <= bv_unsigned sp + -48 - 16) by (clear - LO'; lia).
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_div_walkA) with (lo := lo) (dv := None) (rm := Some rr) (adv := 0) (arm := ar) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity | exact HAr | exact HAx | exact HAm | intros d Ed; discriminate Ed | intros r0 Er0; injection Er0 as <-; exact HPr | exact NROx | exact NROm | exact NBx | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV0 | exact LS0 | unfold BN_NNMOD_STACK, BN_DIV_TOP_STACK, BN_DIV_FT_STACK, BN_LSHIFT_STACK, BN_ADD_STACK, BN_SUB_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO'; lia | unfold BN_NNMOD_COST, BN_DIV_FT_COST; clear - MCP; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV0).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_nnmod_2321a0 CTX).
    }
    cbv beta. intros [u1 ls1] Σ1 ms1 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) BN_NNMOD_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV0))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m1 & OW1 & PL1 & -> & CP1 & (EPL1 & ->)).
    subst PL1. specialize (CP1 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_NNMOD_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV0 CP1) as (EV1 & LS1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
    rewrite (ret_pc_even 2302856) by (clear; lia).
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HAr) as HAr1. pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HAm) as HAm1.
    pose proof (proj1 (proj2 EV1)) as HEAP1.
    destruct (open_for_call LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_NNMOD_COST Σ ls OW m LOFB16 _ _ _ _ _ _ _ _ EV1 LS1 HAr1 NROr)
      as (Dr & BNr & _ & _ & _ & _ & SEPr & _ & ACCr & ALr & _ & _ & Ar0).
    destruct (open_for_call LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_NNMOD_COST Σ ls OW m LOFB16 _ _ _ _ _ _ _ _ EV1 LS1 HAm1 NROm)
      as (Dm & BNm & _ & _ & _ & _ & SEPm & _ & ACCm & ALm & _ & _ & Am0).
    unfold BnRepDefs.bn_cells in BNr, BNm.
    destruct (got_add_sub _ _ _ _ _ _ _ LS1 (got_arith_cells_of_heap _ _ _ _ HEAP1)) as (GA & GS). unfold GOT_BN_ADD, GOT_BN_SUB, MallocRep.wz in GA, GS.
    pose proof (munch_refl (@nil (Z * Z)) m1) as MU1.
    apply implA_from_evt. step. if_false.

    do 3 step. shl_with ACCr ALr. chk0.
    step. clear BNr.
    destruct (bn_neg (getbn rr ls1)) eqn:ENr; cbn [Z.b2z negb]; cbv beta.
    2: {
         step. if_true.
         apply evt_done. apply implA_ret_evt.
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_NNMOD_COST Σ ls OW m _ _ _ _ _ _ EV1 LS1 ltac:(unfold BN_NNMOD_COST, BN_DIV_FT_COST; clear - MCP; lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof EV1 as (_ & _ & STF & _ & _ & _ & _ & _ & FRF & _ & _). cbn [app] in FRF.
    step. do 5 step. release_frame FRF STF (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_postA. do 17 eexists. exists m1, OW1, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact G1|]. split; [exact G2|]. split; [exact STF|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
    split; reflexivity.
    }

    step. if_false.
    do 3 step. shl_with ACCm ALm. chk0.
    step. clear BNm.
    pose proof EV1 as (_ & _ & ST1 & _ & _ & _ & _ & _ & FR1 & _ & _). cbn [app] in FR1.
    destruct (bn_neg (getbn rm ls1)) eqn:ENm; cbn [Z.b2z].
    -
      step. if_false.
      step. step. step.
      step. step. step.
      do 5 step. release_frame FR1 ST1 (bv_unsigned sp). step. step.
      apply evt_done.
      destruct (cenv_tailA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_NNMOD_COST Σ ls OW m _ _ _ _ _ _ BN_SUB_STACK MC ras
                  ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = wz 1)
                  EV1 LS1 ST1 ltac:(clear - LO'; unfold BN_SUB_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia)
                  ltac:(unfold BN_NNMOD_COST, BN_DIV_FT_COST; clear - MCP; lia) eq_refl) as (PREX & UWX & POSTX).
      rewrite Z_to_bv_bv_unsigned in PREX, POSTX.
      eapply implA_mono.
      { eapply (BN_sub_walkA ra sp) with (lo := lo) (ras := ras) (rr := rr) (x := rr) (y := rm) (R := ar) (X := ar) (Y := am) (OW := OW1) (LB := LB) (PL := PL) (EA := EA);
          [exact PREX | exact UWX | exact (uk_ctx_tail _ _ _ E_BN_nnmod_232270_BN_sub CTX) | reflexivity | exact HAr1 | exact HPr | exact HAr1 | exact NROr | exact HAm1 | exact NROm
          | reflexivity | reflexivity | reflexivity]. }
      cbv beta. intros r Σ' ms' PO. apply POSTX. exact PO.
    -
      step. if_true.
      step. step.
      step. step. step.
      do 5 step. release_frame FR1 ST1 (bv_unsigned sp). step. step.
      apply evt_done.
      destruct (cenv_tailA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) BN_NNMOD_COST Σ ls OW m _ _ _ _ _ _ BN_ADD_STACK MC ras
                  ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = wz 1)
                  EV1 LS1 ST1 ltac:(clear - LO'; unfold BN_ADD_STACK, BN_UADD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; lia)
                  ltac:(unfold BN_NNMOD_COST, BN_DIV_FT_COST; clear - MCP; lia) eq_refl) as (PREX & UWX & POSTX).
      rewrite Z_to_bv_bv_unsigned in PREX, POSTX.
      eapply implA_mono.
      { eapply (BN_add_walkA ra sp) with (lo := lo) (ras := ras) (rr := rr) (x := rr) (y := rm) (R := ar) (X := ar) (Y := am) (OW := OW1) (LB := LB) (PL := PL) (EA := EA);
          [exact PREX | exact UWX | exact (uk_ctx_tail _ _ _ E_BN_nnmod_232270 CTX) | reflexivity | exact HAr1 | exact HPr | exact HAr1 | exact NROr | exact HAm1 | exact NROm
          | reflexivity | reflexivity | reflexivity]. }
      cbv beta. intros r Σ' ms' PO. apply POSTX. exact PO.
  Qed.
End Proofs.

End WithRT.
