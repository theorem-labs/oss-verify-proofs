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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnDivWords BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_expandAF W_callsAF W_ctxAF W_ctx_getAF W_ctx_endAF W_copyAF W_cmpAF W_usubAF W_lshiftAF W_rshiftAF W_shiftAF W_div_tailAF W_divAF W_bndivAF W_set_bitAF W_mulAF W_mulA2F W_small3A W_calls3AF ExpKitAF ExpBodyKitF W_reciprocalAF W_recp_setAF InvKitAF W_add_wordAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_DIV_RECP : Z := 0x2b1d58.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Proofs.

  Variable CS : Z.
  Hypothesis CSstart : BN_CTX_START_STACK <= CS.
  Hypothesis CSget : BN_CTX_GET_STACK <= CS.
  Hypothesis CSend : BN_CTX_END_STACK <= CS.
  Hypothesis CSnb : BN_NUM_BITS_STACK <= CS.
  Hypothesis CScopy : BN_COPY_STACK <= CS.
  Hypothesis CSucmp : BN_UCMP_STACK <= CS.
  Hypothesis CSusub : BN_USUB_STACK <= CS.
  Hypothesis CSmul : BN_MUL_TOP_STACK <= CS.
  Hypothesis CSrsh : BN_RSHIFT_W_STACK <= CS.
  Hypothesis CSaw : BN_ADD_WORD_STACK <= CS.

  Variable CSR : Z.
  Hypothesis CSRstart : BN_CTX_START_STACK <= CSR.
  Hypothesis CSRget : BN_CTX_GET_STACK <= CSR.
  Hypothesis CSRend : BN_CTX_END_STACK <= CSR.
  Hypothesis CSRsetbit : BN_SET_BIT_STACK <= CSR.
  Hypothesis CSRdiv : BN_DIV_TOP_STACK <= CSR.
  Hypothesis CSrecip : BN_RECIPROCAL_STACK CSR <= CS.
  Definition BN_DIV_RECP_STACK : Z := 128 + CS.

  Definition BN_DIV_RECP_COST : Z := 5 * MC + (3 * MC + BN_DIV_FT_COST) + 2 * MC + 2 * BN_MUL_TOP_COST + MC + 4 * (MC + MC).

  Ltac strip2 l := lazymatch l with
    | cons _ (cons _ nil) => constr:(@nil cell)
    | cons ?x ?t => let r := strip2 t in constr:(cons x r)
    end.

  Ltac relocal EV LS MU WM ST MI FR FSZ EV' LS' :=
    cbn [app cells_size csize Nat.add] in FSZ;
    lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
      destruct (cenv_localA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ EV LS MU WM ltac:(clear; lia) ltac:(clear; lia) ST MI FR
                  ltac:(cbn [cells_size csize Nat.add app]; clear - FSZ; lia)) as (EV' & LS') end.
  Ltac lst := step; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store | |- _ => idtac end.
  Lemma sx32_int : forall z, -2147483648 <= z < 2147483648 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
  Proof.
    intros z Hz. unfold sx32. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    replace (z mod 18446744073709551616) with (z mod 18446744073709551616 + 0) by lia. rewrite bn_swrap32_mod by lia. lia.
  Qed.

  Lemma eqb_int : forall x y, -9223372036854775808 <= x < 9223372036854775808 -> -9223372036854775808 <= y < 9223372036854775808 ->
    bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
  Proof.
    intros x y Hx Hy. rewrite bv_eqb_Z, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    destruct (Z.eqb_spec x y) as [E|NE]; [subst; apply Z.eqb_refl|]. apply Z.eqb_neq. intros E. apply NE. clear NE.
    pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)). pose proof (Z.mod_pos_bound y 18446744073709551616 ltac:(lia)).
    pose proof (Z.div_mod x 18446744073709551616 ltac:(lia)). pose proof (Z.div_mod y 18446744073709551616 ltac:(lia)). lia.
  Qed.

    Lemma xor_b2z : forall a b : bool, Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (Z.b2z a))) (bv_unsigned (Z_to_bv 64 (Z.b2z b)))) = Z_to_bv 64 (Z.b2z (xorb b a)).
  Proof. intros [] []; reflexivity. Qed.

  Lemma BN_div_recp_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rm : bnref) (ar am an ac : Z) (qc : bptr) (q : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo BN_DIV_RECP_STACK BN_DIV_RECP_COST ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_DIV_RECP (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL rm am -> hpl PL rr -> rm <> ROne -> nbuf PL rm -> recp_at PL an -> In (q, an, 64) LB -> an mod 8 = 0 -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz 0 -> a1 = wz ar -> a2 = wz am -> a3 = wz an -> a4 = wz ac ->
    implA (BN_div_recp (tree_ops bptr) None (Some rr) rm ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_DIV_RECP_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_DIV_RECP) fc None m (seg_rom bgasegs)).
  Proof.
    intros until q. intros PRE UW CTX -> HAr HAm HPr NROm NBm HRC INQ AL8 HPC -> -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold BN_DIV_RECP_STACK in LO'.
    pose proof MC0 as MCP.
    unfold BN_DIV_RECP, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (proj1 (hpl_wref _ _ HPr)) as NROr.
    pose proof (recp_at_refN ls OW PL an HRC) as HAN. pose proof (recp_at_refNr ls OW PL an HRC) as HANr.
    pose proof (recp_at_wrefN PL an HRC) as WRN. pose proof (recp_at_wrefNr PL an HRC) as WRNr. pose proof (recp_at_recp PL an HRC) as HRc.
    assert (INB : In (q, an, 64) (OW ++ LB)) by (apply in_or_app; right; exact INQ).
    pose proof (AH_range_gen _ _ _ _ _ HEAP INB) as (An0 & _ & _ & AnC & AnI). cbn [blk_addr blk_size fst snd] in An0, AnC, AnI.
    assert (ArR : 0 < ar < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAr NROr) as (X & Y & _); unfold BnHeapA.ACEIL in *; clear - X Y C1 C2 C3; lia).
    assert (AmR : 0 < am < 2^64) by (pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAm NROm) as (X & Y & _); unfold BnHeapA.ACEIL in *; clear - X Y C1 C2 C3; lia).
    destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
    assert (CS16 : 16 <= CS) by (pose proof CSend as H; unfold BN_CTX_END_STACK in H; clear - H; lia).
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    unfold BN_div_recp, bbind, bret. cbn [bind ret tree_ops tbind fst snd].
    apply implA_from_evt.

    carve_frame 128%nat ST. do 14 step. do 10 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -128, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -128, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m mP OW PL EA _ HEAP LS MU WM FROK WOK) as LS0.
    lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
      assert (EV0 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m p 0 Σ ls mP OW) end.
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
    assert (LOFB16 : lo <= bv_unsigned sp + -128 - 16) by (clear - LO' CS16; lia).
    step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_start_walkA) with (lo := lo) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV0 | exact LS0 | clear - LO' CSstart; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV0).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1bd4 CTX).
    }
    cbv beta. intros [u1 ls1] Σ1 ms1 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV0))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m1 & OW1 & PL1 & -> & CP1 & (EPL1 & INCL1)).
    subst PL1. specialize (CP1 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV0 CP1) as (EV1 & LS1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
    rewrite (ret_pc_even 2825660) by (clear; lia).

    apply implA_from_evt. step. if_true. step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OW1) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV1 | exact LS1 | clear - LO' CSget; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV1).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1d90 CTX).
    }
    cbv beta. intros [u2 ls2] Σ2 ms2 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV1))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F2 & fc2 & m2 & OW2 & PL2 & -> & CP2 & (EPL2 & (di & Ed) & (ad & HAd & ->) & INCL2)).
    subst PL2. specialize (CP2 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV1 CP2) as (EV2 & LS2).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP2) as RS2.
    rewrite (ret_pc_even 2826104) by (clear; lia).
    pose proof (proj1 (proj2 EV2)) as HEAP2. pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
    assert (NROd : u2 <> ROne) by (rewrite Ed; unfold RPool, ROne, NFIX; clear; lia).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROKK HAd NROd) as (Ad0 & AdC & _).
    assert (AdR : 0 < ad < 2^64) by (unfold BnHeapA.ACEIL in *; clear - Ad0 AdC C1 C2 C3; lia). clear AdC HEAP2 PARTS2.
    unfold MallocRep.wz. apply implA_from_evt. step.

    step. if_cases KR; rewrite ?unsigned_lit in KR by (clear - ArR; lia); zify_cond KR; [clear KR| exfalso; clear - KR ArR; lia].
    step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OW2) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV2 | exact LS2 | clear - LO' CSget; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV2).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1be4 CTX).
    }
    cbv beta. intros [u3 ls3] Σ3 ms3 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV2))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & OW3 & PL3 & -> & CP3 & (EPL3 & (ai & Ea) & (aa & HAa & ->) & INCL3)).
    subst PL3. specialize (CP3 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV2 CP3) as (EV3 & LS3).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP3) as RS3.
    rewrite (ret_pc_even 2825676) by (clear; lia).

    unfold MallocRep.wz. apply implA_from_evt. step. step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OW3) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EV3 | exact LS3 | clear - LO' CSget; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV3).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1bf0 CTX).
    }
    cbv beta. intros [u4 ls4] Σ4 ms4 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV3))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F4 & fc4 & m4 & OW4 & PL4 & -> & CP4 & (EPL4 & (bi & Eb) & (ab & HAb & ->) & INCL4)).
    subst PL4. specialize (CP4 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV3 CP4) as (EV4 & LS4).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP4) as RS4.
    rewrite (ret_pc_even 2825688) by (clear; lia).
    pose proof (refs_stable_trans _ _ _ _ _ _ RS1 (refs_stable_trans _ _ _ _ _ _ RS2 (refs_stable_trans _ _ _ _ _ _ RS3 RS4))) as RS04.
    pose proof (refs_stable_trans _ _ _ _ _ _ RS3 RS4) as RS24.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS04 HAr) as HAr4. pose proof (ref_at_stable _ _ _ _ PL _ _ RS04 HAm) as HAm4.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS04 HAN) as HAN4. pose proof (ref_at_stable _ _ _ _ PL _ _ RS04 HANr) as HANr4.
    pose proof (ref_at_stable _ _ _ _ PL _ _ RS24 HAd) as HAd4. pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HAa) as HAa4.
    pose proof (proj1 (proj2 EV4)) as HEAP4. pose proof (lib_state_h_parts _ _ _ _ _ _ LS4) as PARTS4.
    assert (NROa : u3 <> ROne) by (rewrite Ea; unfold RPool, ROne, NFIX; clear; lia).
    assert (NROb : u4 <> ROne) by (rewrite Eb; unfold RPool, ROne, NFIX; clear; lia).
    assert (NRON : RRecpN <> ROne) by (unfold RRecpN, ROne; clear; lia).
    assert (NRONr : RRecpNr <> ROne) by (unfold RRecpNr, ROne; clear; lia).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP4 PARTS4 FROKK HAb NROb) as (Ab0 & AbC & _).
    assert (AbR : 0 < ab < 2^64) by (unfold BnHeapA.ACEIL in *; clear - Ab0 AbC C1 C2 C3; lia). clear AbC.
    unfold MallocRep.wz. apply implA_from_evt.
    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AbR; lia); zify_cond KZ; [exfalso; clear - KZ AbR; lia| clear KZ].

    step. step. step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_ucmp_walkA) with (lo := lo) (OW := OW4) (LB := LB) (PL := PL) (EA := EA);
        [| reflexivity | exact HAm4 | exact HAN4 | exact NROm | exact NRON | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV4 | exact LS4 | clear - LO' CSucmp; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP; lia].
    }
    cbv beta. intros [u5 ls5] Σ5 ms5 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV4))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & ((EPL5 & -> & CR5 & ELS5 & EOW5) & EC5)).
    subst PL5. specialize (CP5 eq_refl).
    destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV4 CP5) as (EV5 & LS5).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5.
    rewrite (ret_pc_even 2825708) by (clear; lia).
    subst ls5 OW5. subst u5. set (c := ucmp_pure (getbn rm ls4) (getbn RRecpN ls4)) in *.
    unfold MallocRep.wz. apply implA_from_evt.
    step. rewrite lts_signed by (clear - CR5; lia).
    destruct (Z.ltb_spec c 0) as [CLT|CGE].
    -
      unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
      step. step.
      eapply (ExpBodyKitF.zero_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m LOFB16) with (r := u2) (ar := ad);
        [exact EV5 | exact LS5 | exact HAd4 | rewrite Ed; apply wref_pool |].
      intros m6 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ls6 EV6 LS6.
      rewrite (ret_pc_even 2826136) by (clear; lia).
      step. step. step.
    apply evt_done.
      eapply implA_bind.
      { eapply (BN_copy_walkA) with (lo := lo) (OW := OW4) (LB := LB) (PL := PL) (EA := EA);
          [| | | reflexivity | apply ref_at_setbn; exact HAr4 | apply ref_at_setbn; exact HAm4 | exact (hpl_wref _ _ HPr) | exact NROm | reflexivity | reflexivity].
        - eapply cenv_preA; [exact EV6 | exact LS6 | clear - LO' CScopy; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP; lia].
        - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV6).
        - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1dbc CTX).
      }
      cbv beta. intros [u7 ls7] Σ7 ms7 PO.
      apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV6))].
      cbn [fst snd] in *.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F7 & fc7 & m7 & OW7 & PL7 & -> & CP7 & (EPL7 & -> & INCL7)).
      subst PL7. specialize (CP7 eq_refl).
      destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV6 CP7) as (EV7 & LS7).
      pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP7) as RS7.
      rewrite (ret_pc_even 2826148) by (clear; lia).
      unfold MallocRep.wz. apply implA_from_evt.
      step. rewrite v_sltu_b2z, !unsigned_lit by (clear - ArR; lia). replace (0 <? ar) with true by (symmetry; apply Z.ltb_lt; clear - ArR; lia). cbn [Z.b2z].
      step. step. step.
    apply evt_done.
      eapply implA_post_evt.
      { eapply (BN_CTX_end_walkA) with (lo := lo) (OW := OW7) (LB := LB) (PL := PL) (EA := EA);
          [| reflexivity | exact HPC | reflexivity].
        - eapply cenv_preA; [exact EV7 | exact LS7 | clear - LO' CSend; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP; lia].
      }
      cbv beta. intros [u8 ls8] Σ8 ms8 PO.
      apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV7))].
      cbn [fst snd] in *.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F8 & fc8 & m8 & OW8 & PL8 & -> & CP8 & (EPL8 & EOW8)).
      subst PL8. specialize (CP8 eq_refl).
      destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV7 CP8) as (EV8 & LS8).
      pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP8) as RS8.
      rewrite (ret_pc_even 2826240) by (clear; lia).
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ EV8 LS8 ltac:(unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP; lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
      pose proof EV8 as (_ & _ & STF & _ & _ & _ & _ & _ & FRF & _ & _). cbn [app] in FRF.
      step. do 13 step. release_frame FRF STF (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_postA. do 17 eexists. exists m8, OW8, PL. split; [reflexivity|]. cbn [fst snd].
      split; [exact G1|]. split; [exact G2|]. split; [exact STF|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
      split; reflexivity.
    -
      unfold BN_num_bits, bgetst, bget, bset, bsetrecp, bbind, bret. cbn [bind ret tree_ops tbind fst snd].
      pose proof (st_wf_ok _ _ (proj1 PARTS4) (ref_at_valid _ _ _ _ _ _ _ _ LS4 HAm4) NROm) as (OKm1 & OKm2 & OKm3 & OKm4).
      set (bm := getbn rm ls4) in *. unfold BG_DMAX in OKm3.
      assert (CTm : Z.land (bn_flags bm) 4 = 0) by (destruct OKm4 as [E|E]; rewrite E; reflexivity).
      step. step.
      eapply (num_bits_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m); [exact EV5 | exact LS5 | exact HAm4 | exact NROm | unfold BN_NUM_BITS_STACK in *; clear - LO' CSnb; lia |].
      intros m9 y0C y1C y2C y4C y5C y6C y7C y8C y9C y10C y11C y12C y13C y14C EV9 LS9.
      rewrite (ret_pc_even 2825720) by (clear; lia).
      pose proof (num_bits_pure_range bm OKm1) as BITS.
      unfold has_flag, BN_FLG_CONSTTIME. fold bm. rewrite CTm. cbn [Z.eqb negb tbind]. cbv beta.
      set (i0 := num_bits_pure bm) in *.
      assert (I0R : 0 <= i0 <= 32768) by (clear - BITS OKm2 OKm3; lia).

      cbn [fst snd].
      destruct (recp_rng ls4) eqn:RNG1; cbn [negb]; [| apply evt_done; unfold bunr; cbn [unreachable tree_ops tbind]; apply implA_unr].
      unfold recp_rng in RNG1. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt in RNG1. destruct RNG1 as (((R1 & R2) & R3) & R4).

      pose proof EV9 as (_ & HEAP9 & ST9 & MI9 & _ & _ & _ & _ & FR9 & FSZ9 & _). cbn [app] in FR9.
      pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)]%Z m9) as MU. pose proof (wmono_refl bgasegs m9) as WM.
      assert (AnT : 0 <= an /\ an + 64 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - An0 AnC C1 C2 C3; lia).
      step. step. lst.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mL1 end.
      relocal EV9 LS9 MU WM ST9 MI9 FR9 FSZ9 EVa LSa. clear MU WM ST9 MI9 FR9 FSZ9 HEAP9.
      pose proof (proj2 (AH_acc _ _ _ _ (q, an, 64) (proj1 (proj2 EVa)) ltac:(apply in_or_app; right; exact INQ))) as ACCa. cbn [blk_addr blk_size fst snd] in ACCa.
      pose proof (munch_refl (@nil (Z * Z)) mL1) as MU0.
      step. shl_with ACCa AL8. chk0. clear MU0 ACCa.
      pose proof EVa as (_ & _ & STa & MIa & _ & _ & _ & _ & FRa & FSZa & _). cbn [app] in FRa.
      pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)]%Z mL1) as MU. pose proof (wmono_refl bgasegs mL1) as WM.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mL2 end.
      relocal EVa LSa MU WM STa MIa FRa FSZa EVb LSb. clear MU WM STa MIa FRa FSZa.
      pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LSb HRc) as RC. unfold recp_cells in RC.
      step. rewrite (sx32_int (st_rbits ls4)) by (clear - R1 R2; lia).
      remember (if i0 <? 2 * st_rbits ls4 then 2 * st_rbits ls4 else i0) as i eqn:Ei.
      assert (IR : 0 <= i < 33554432) by (rewrite Ei; destruct (i0 <? 2 * st_rbits ls4); clear - I0R R1 R2; lia).
      lazymatch goal with |- evt _ ?POSTX _ =>
        assert (CONT : forall (a0' : word),
          evt bgasegs POSTX
            (MS (mkR (Z_to_bv 64 2825720) (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 TP_A) y0C y1C y2C sp (Z_to_bv 64 ac) a0' (Z_to_bv 64 (st_rbits ls4)) y5C (Z_to_bv 64 (an + 48)) y7C y8C y9C y10C
                     (Z_to_bv 64 an) (Z_to_bv 64 am) (Z_to_bv 64 ar) (Z_to_bv 64 ad) (Z_to_bv 64 SHB) (Z_to_bv 64 ab) (Z_to_bv 64 aa) (Z_to_bv 64 i) s10 (Z_to_bv 64 (Z.shiftr (an + 48) 3 + SHB)) y11C y12C y13C y14C)
                F5 (Z_to_bv 64 2825764) fc5 None mL2 (seg_rom bgasegs)))
      end.
      2: { step. rewrite (unsigned_lit (st_rbits ls4)) by (clear - R1 R2; lia). rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 1) with 2.
           rewrite (bn_swrap32_small (st_rbits ls4 * 2)) by (clear - R1 R2; lia). replace (st_rbits ls4 * 2) with (2 * st_rbits ls4) by (clear; lia).
           step. rewrite lts_signed by (clear - I0R R1 R2; lia).
           destruct (Z.ltb_spec i0 (2 * st_rbits ls4)) as [LT|GE]; cbn [negb].
           - rewrite <- Ei. eapply CONT.
           - step. rewrite <- Ei. eapply CONT. }
      intros a0'. clear RC.

      pose proof EVb as (_ & HEAPb & STb & MIb & _ & _ & _ & _ & FRb & FSZb & _). cbn [app] in FRb.
      pose proof (proj2 (AH_acc _ _ _ _ (q, an, 64) HEAPb ltac:(apply in_or_app; right; exact INQ))) as ACCb. cbn [blk_addr blk_size fst snd] in ACCb.
      pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LSb HRc) as RC. unfold recp_cells in RC.
      pose proof (munch_refl (@nil (Z * Z)) mL2) as MU0.
      step. step. step. step. shl_with ACCb AL8. chk0.
      step. rewrite (sx32_int (st_rshift ls4)) by (clear - R3 R4; lia).
      step.
      clear MU0 ACCb.

      lazymatch type of EVb with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?preb _ _ _ _ _ =>
      pose (RCPQ := fun (r : unit * bstate bptr) (Σ' : rts RT) (ms' : machine_state) =>
        exists mJ OWJ usedJ (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (FJ : bvmap 5 word) (fcJ : bv 32),
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 ac) (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 an) (Z_to_bv 64 am) (Z_to_bv 64 ar) (Z_to_bv 64 ad) (Z_to_bv 64 (Z.shiftr (an + 52) 3 + SHB)) (Z_to_bv 64 ab) (Z_to_bv 64 aa) (Z_to_bv 64 i)
                        (Z_to_bv 64 (an + 52)) (Z_to_bv 64 (Z.shiftr (an + 48) 3 + SHB)) t3 t4 t5 t6)
                   FJ (Z_to_bv 64 2825832) fcJ None mJ (seg_rom bgasegs)
          /\ cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m preb usedJ Σ' (snd r) mJ OWJ
          /\ lib_state (snd r) mJ OWJ PL EA /\ refs_stable ls4 OW4 (snd r) OWJ /\ st_rshift (snd r) = i
          /\ usedJ <= 0 + MC + MC + MC + MC + 0 + BN_RECIPROCAL_COST) end.
      step. rewrite eqb_int by (clear - IR R3 R4; lia).
      apply evt_done. eapply implA_bind with (Q1 := RCPQ).
      { destruct (Z.eqb_spec i (st_rshift ls4)) as [ESH|NSH].
        -
          apply implA_ret.
          unfold RCPQ. exists mL2, OW4, (0 + MC + MC + MC + MC + 0). do 17 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact EVb|]. split; [exact LSb|]. split; [apply refs_stable_refl|]. split; [symmetry; exact ESH|].
          unfold BN_RECIPROCAL_COST, BN_DIV_FT_COST. clear - MCP. lia.
        - clear RC.
          pose proof EVb as EV10. pose proof LSb as LS10.
          apply implA_from_evt. step. step. step. step. step.
    apply evt_done.
          eapply implA_bind.
          { eapply (BN_reciprocal_walkA CSR CSRstart CSRget CSRend CSRsetbit CSRdiv) with (lo := lo) (OW := OW4) (LB := LB) (PL := PL) (EA := EA);
              [| | | reflexivity | exact HANr4 | exact HAN4 | exact WRNr | exact NRON | exact HPC | clear - IR; lia | reflexivity | reflexivity | reflexivity | reflexivity].
            - eapply cenv_preA; [exact EV10 | exact LS10 | clear - LO' CSrecip; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP; lia].
            - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV10).
            - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1c74 CTX).
          }
          cbv beta. intros [u11 ls11] Σ11 ms11 PO.
          apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV10))].
          cbn [fst snd] in *.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F11 & fc11 & m11 & OW11 & PL11 & -> & CP11 & (EPL11 & Esh & ->)).
          subst PL11. specialize (CP11 eq_refl).
          destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV10 CP11) as (EV11 & LS11).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP11) as RS11.
          rewrite (ret_pc_even 2825820) by (clear; lia).
          subst u11.
          unfold MallocRep.wz. apply implA_ret_evt.
          pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LS11 HRc) as RC11. unfold recp_cells in RC11.
          pose proof EV11 as (_ & HEAP11 & ST11 & MI11 & _).
          pose proof (proj2 (AH_acc _ _ _ _ (q, an, 64) HEAP11 ltac:(apply in_or_app; right; exact INQ))) as ACC11. cbn [blk_addr blk_size fst snd] in ACC11.
          pose proof (AH_offsh _ _ _ _ (q, an, 64) HEAP11 ltac:(apply in_or_app; right; exact INQ)) as OFFR. cbn [blk_addr blk_size fst snd] in OFFR. unfold SHLO, SHHI in OFFR.
          pose proof (munch_refl [(an + 48, an + 48 + RECP_SC_SZ)]%Z m11) as MUR. pose proof (wmono_refl bgasegs m11) as WMR. unfold RECP_SC_SZ in MUR.
          shl_with ACC11 AL8. chk0.
          step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m12 end.
          destruct (cenv_set_recpA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ m11 m12 _ (an + 48) (q, an, 64) (st_rbits ls11) i EV11 LS11 HRc INQ
                      ltac:(cbn [blk_addr fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; unfold RECP_SC_SZ; clear; lia) MUR WMR ST11 MI11 RC11) as (EV12 & LS12).
          apply evt_done.
          unfold RCPQ. exists m12, OW11, (0 + MC + MC + MC + MC + 0 + BN_RECIPROCAL_COST). do 17 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact EV12|]. split; [exact LS12|]. split; [|split; [reflexivity | clear; lia]].
          eapply refs_stable_trans; [exact RS11|]. intros PL' k a' H. apply ref_at_set_recp. exact H. }
      cbv beta. intros [u20 ls20] Σ20 ms20 (m20 & OW20 & used20 & R).
      destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F20 & fc20 & -> & EV20 & LS20 & RS20 & HSH & U20). cbn [fst snd] in *.
      clear RCPQ.
      unfold BN_RECIPROCAL_COST, BN_DIV_FT_COST in U20.
      pose proof (refs_stable_trans _ _ _ _ _ _ RS04 RS20) as RS020.

      cbn [tbind fst snd].
      destruct (recp_rng ls20) eqn:RNG2; cbn [negb]; [| unfold bunr; cbn [unreachable tree_ops tbind]; apply implA_unr].
      unfold recp_rng in RNG2. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt in RNG2. destruct RNG2 as (((RJ1 & RJ2) & _) & _).
      rewrite HSH. replace (i =? -1) with false by (symmetry; apply Z.eqb_neq; clear - IR; lia).
      pose proof EV20 as (_ & HEAP20 & ST20 & MI20 & _ & _ & _ & _ & FR20 & FSZ20 & _). cbn [app] in FR20.
      pose proof (proj2 (AH_acc _ _ _ _ (q, an, 64) HEAP20 ltac:(apply in_or_app; right; exact INQ))) as ACC20. cbn [blk_addr blk_size fst snd] in ACC20.
      pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LS20 HRc) as RC20. unfold recp_cells in RC20.
      pose proof (munch_refl (@nil (Z * Z)) m20) as MU0.
      apply implA_from_evt.
      step. step. if_cases KM; rewrite ?unsigned_lit in KM by (clear - IR; lia); zify_cond KM; [exfalso; clear - KM IR; lia| clear KM].
      shl_with ACC20 AL8. chk0.
      step.
      step. rewrite (sx32_int (st_rbits ls20)) by (clear - RJ1 RJ2; lia).

      step. step. step.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS20 HAa4) as HAa20. pose proof (ref_at_stable _ _ _ _ PL _ _ RS20 HAb) as HAb20.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS20 HAd4) as HAd20. pose proof (ref_at_stable _ _ _ _ PL _ _ RS020 HAm) as HAm20.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS020 HAr) as HAr20. pose proof (ref_at_stable _ _ _ _ PL _ _ RS020 HAN) as HAN20.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS020 HANr) as HANr20.
      clear ACC20 MU0 RC20 ST20 MI20 FR20 FSZ20 HEAP20.
    apply evt_done.
      eapply implA_bind.
      { eapply (BN_rshift_walkA) with (lo := lo) (OW := OW20) (LB := LB) (PL := PL) (EA := EA);
          [| | | reflexivity | exact HAa20 | rewrite Ea; apply hpl_pool | exact HAm20 | exact NROm | solve_nbuf | reflexivity | reflexivity | reflexivity | clear - RJ1 RJ2; lia].
        - eapply cenv_preA; [exact EV20 | exact LS20 | clear - LO' CSrsh; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP U20; lia].
        - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV20).
        - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1ca4 CTX).
      }
      cbv beta. intros [u21 ls21] Σ21 ms21 PO.
      apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV20))].
      cbn [fst snd] in *.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F21 & fc21 & m21 & OW21 & PL21 & -> & CP21 & (EPL21 & -> & INCL21)).
      subst PL21. specialize (CP21 eq_refl).
      destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV20 CP21) as (EV21 & LS21).
      pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP21) as RS21.
      rewrite (ret_pc_even 2825868) by (clear; lia).
      unfold MallocRep.wz. apply implA_from_evt. step. if_false.

      step. step. step. step. step.
    apply evt_done.
      eapply implA_bind.
      { eapply (BN_mul_walkA) with (lo := lo) (OW := OW21) (LB := LB) (PL := PL) (EA := EA);
          [| | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS21 HAb20) | exact (ref_at_stable _ _ _ _ PL _ _ RS21 HAa20) | exact (ref_at_stable _ _ _ _ PL _ _ RS21 HANr20) | rewrite Eb; apply hpl_pool | exact NROa | exact NRONr | rewrite Ea; apply nbuf_pool | exact (wref_nbuf _ _ WRNr) | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity].
        - eapply cenv_preA; [exact EV21 | exact LS21 | clear - LO' CSmul; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP U20; lia].
        - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV21).
        - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1cbc CTX).
      }
      cbv beta. intros [u22 ls22] Σ22 ms22 PO.
      apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV21))].
      cbn [fst snd] in *.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F22 & fc22 & m22 & OW22 & PL22 & -> & CP22 & (EPL22 & ->)).
      subst PL22. specialize (CP22 eq_refl).
      destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV21 CP22) as (EV22 & LS22).
      pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP22) as RS22.
      rewrite (ret_pc_even 2825892) by (clear; lia).
      pose proof (refs_stable_trans _ _ _ _ _ _ RS21 RS22) as RS2022.
      unfold MallocRep.wz. apply implA_from_evt. step. if_false.

      cbn [tbind fst snd].
      destruct (recp_rng ls22) eqn:RNG3; cbn [negb]; [| apply evt_done; unfold bunr; cbn [unreachable tree_ops tbind]; apply implA_unr].
      unfold recp_rng in RNG3. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt in RNG3. destruct RNG3 as (((RK1 & RK2) & _) & _).
      pose proof EV22 as (_ & HEAP22 & _).
      pose proof (proj2 (AH_acc _ _ _ _ (q, an, 64) HEAP22 ltac:(apply in_or_app; right; exact INQ))) as ACC22. cbn [blk_addr blk_size fst snd] in ACC22.
      pose proof (lib_state_recp_cells _ _ _ _ _ _ _ _ LS22 HRc) as RC22. unfold recp_cells in RC22.
      pose proof (munch_refl (@nil (Z * Z)) m22) as MU0.
      shl_with ACC22 AL8. chk0.
      step. rewrite (sx32_int (st_rbits ls22)) by (clear - RK1 RK2; lia).
      step. rewrite (unsigned_lit i), (unsigned_lit (st_rbits ls22)) by (clear - IR RK1 RK2; lia). rewrite (bn_swrap32_small (i - st_rbits ls22)) by (clear - IR RK1 RK2; lia).
      step. step. step.
      clear ACC22 MU0 RC22 HEAP22.
    apply evt_done.
      eapply implA_bind.
      { eapply (BN_rshift_walkA) with (lo := lo) (OW := OW22) (LB := LB) (PL := PL) (EA := EA);
          [| | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS2022 HAd20) | rewrite Ed; apply hpl_pool | exact (ref_at_stable _ _ _ _ PL _ _ RS2022 HAb20) | exact NROb | solve_nbuf | reflexivity | reflexivity | reflexivity | clear - IR RK1 RK2; lia].
        - eapply cenv_preA; [exact EV22 | exact LS22 | clear - LO' CSrsh; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP U20; lia].
        - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV22).
        - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1cdc CTX).
      }
      cbv beta. intros [u23 ls23] Σ23 ms23 PO.
      apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV22))].
      cbn [fst snd] in *.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F23 & fc23 & m23 & OW23 & PL23 & -> & CP23 & (EPL23 & -> & INCL23)).
      subst PL23. specialize (CP23 eq_refl).
      destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV22 CP23) as (EV23 & LS23).
      pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP23) as RS23.
      rewrite (ret_pc_even 2825924) by (clear; lia).
      pose proof (refs_stable_trans _ _ _ _ _ _ RS2022 RS23) as RS2023.
      unfold MallocRep.wz. apply implA_from_evt. step. if_false.

      pose proof (ref_at_stable _ _ _ _ PL _ _ RS2023 HAd20) as HAd23.
      destruct (cenv_struct_openA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra ras BN_DIV_RECP_COST Σ ls OW m LOFB16 _ _ _ _ _ _ u2 ad EV23 LS23 HAd23 ltac:(rewrite Ed; apply wref_pool))
        as (Dd & BNd & OKd & ACCd & ALd & Ad0' & SEPd & OFSd & STd & MId & CLOSEd).
      unfold BnRepDefs.bn_cells in BNd.
      unfold SHLO, SHHI in OFSd.
      assert (AdT : 0 <= ad /\ ad + 24 <= 140737488355328) by (clear - SEPd SPT Ad0'; lia).
      pose proof EV23 as (_ & _ & _ & _ & _ & _ & _ & _ & FR23 & _). cbn [app] in FR23.
      pose proof (munch_refl [(ad, ad + 24)]%Z m23) as MUd. pose proof (wmono_refl bgasegs m23) as WMd.
      step. step. step. step. shl_with ACCd ALd. chk0.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m24 end.
      set (bd := getbn u2 ls23) in *.
      assert (BNd' : rw_cells bgasegs m24 ad (BnRepDefs.bn_cells Dd (bn_with_neg bd false))) by (unfold BnRepDefs.bn_cells, bn_with_neg; cbn [bn_d bn_top bn_buf bn_neg bn_flags bn_dmax Z.b2z length]; exact BNd).
      assert (OKd' : bg_ok (bn_with_neg bd false)) by (destruct OKd as (O1 & O2 & O3 & O4); unfold bg_ok, bn_with_neg, bn_dmax in *; cbn [bn_buf bn_top bn_flags]; repeat split; assumption).
      destruct (CLOSEd m24 (bn_with_neg bd false) MUd WMd BNd' eq_refl eq_refl OKd' STd MId) as (EV24 & LS24).
      clear CLOSEd BNd BNd' MUd WMd STd MId ACCd FR23.
      unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
      pose proof (refs_stable_trans _ _ _ _ _ _ RS020 RS2023) as RS023.
      pose proof (refs_stable_trans _ _ _ _ _ _ RS20 RS2023) as RS423.

      step. step. step. step. step.
    apply evt_done.
      eapply implA_bind.
      { eapply (BN_mul_walkA) with (lo := lo) (OW := OW23) (LB := LB) (PL := PL) (EA := EA);
          [| | | reflexivity | apply ref_at_setbn; exact (ref_at_stable _ _ _ _ PL _ _ RS423 HAb) | apply ref_at_setbn; exact (ref_at_stable _ _ _ _ PL _ _ RS023 HAN) | apply ref_at_setbn; exact HAd23 | rewrite Eb; apply hpl_pool | exact NRON | exact NROd | exact (wref_nbuf _ _ WRN) | rewrite Ed; apply nbuf_pool | exact HPC | reflexivity | reflexivity | reflexivity | reflexivity].
        - eapply cenv_preA; [exact EV24 | exact LS24 | clear - LO' CSmul; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP U20; lia].
        - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV24).
        - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1d10 CTX).
      }
      cbv beta. intros [u25 ls25] Σ25 ms25 PO.
      apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV24))].
      cbn [fst snd] in *.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F25 & fc25 & m25 & OW25 & PL25 & -> & CP25 & (EPL25 & ->)).
      subst PL25. specialize (CP25 eq_refl).
      destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV24 CP25) as (EV25 & LS25).
      pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP25) as RS25.
      rewrite (ret_pc_even 2825976) by (clear; lia).
      unfold MallocRep.wz. apply implA_from_evt. step. if_false.

      step. step. step. step.
    apply evt_done.
      eapply implA_bind.
      { eapply (BN_usub_walkA) with (lo := lo) (OW := OW25) (LB := LB) (PL := PL) (EA := EA);
          [| | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS25 (proj2 (ref_at_setbn _ _ _ _ _ _ _) (ref_at_stable _ _ _ _ PL _ _ RS023 HAr))) | exact HPr | exact (ref_at_stable _ _ _ _ PL _ _ RS25 (proj2 (ref_at_setbn _ _ _ _ _ _ _) (ref_at_stable _ _ _ _ PL _ _ RS023 HAm))) | exact NROm | exact (ref_at_stable _ _ _ _ PL _ _ RS25 (proj2 (ref_at_setbn _ _ _ _ _ _ _) (ref_at_stable _ _ _ _ PL _ _ RS423 HAb))) | exact NROb | reflexivity | reflexivity | reflexivity].
        - eapply cenv_preA; [exact EV25 | exact LS25 | clear - LO' CSusub; lia | unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP U20; lia].
        - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV25).
        - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1d24 CTX).
      }
      cbv beta. intros [u26 ls26] Σ26 ms26 PO.
      apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV25))].
      cbn [fst snd] in *.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F26 & fc26 & m26 & OW26 & PL26 & -> & CP26 & (EPL26 & -> & INCL26)).
      subst PL26. specialize (CP26 eq_refl).
      destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV25 CP26) as (EV26 & LS26).
      pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP26) as RS26.
      rewrite (ret_pc_even 2825996) by (clear; lia).
      unfold MallocRep.wz. apply implA_from_evt. step. if_false.

      pose proof (refs_stable_trans _ _ _ _ _ _ RS25 RS26) as RS2526.
      assert (HAr26 : ref_at ls26 OW26 PL rr ar) by exact (ref_at_stable _ _ _ _ PL _ _ RS2526 (proj2 (ref_at_setbn _ _ _ _ _ _ _) (ref_at_stable _ _ _ _ PL _ _ RS023 HAr))).
      destruct (cenv_struct_openA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra ras BN_DIV_RECP_COST Σ ls OW m LOFB16 _ _ _ _ _ _ rr ar EV26 LS26 HAr26 (hpl_wref _ _ HPr))
        as (Dr & BNr & OKr & ACCr & ALr & Ar0' & SEPr & OFSr & STr & MIr & CLOSEr).
      unfold BnRepDefs.bn_cells in BNr. unfold SHLO, SHHI in OFSr.
      assert (ArT : 0 <= ar /\ ar + 24 <= 140737488355328) by (clear - SEPr SPT Ar0'; lia).
      pose proof (munch_refl [(ar, ar + 24)]%Z m26) as MUr. pose proof (wmono_refl bgasegs m26) as WMr.
      step. step. step. step. shl_with ACCr ALr. chk0.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m27 end.
      set (br := getbn rr ls26) in *.
      assert (BNr' : rw_cells bgasegs m27 ar (BnRepDefs.bn_cells Dr (bn_with_neg br false))) by (unfold BnRepDefs.bn_cells, bn_with_neg; cbn [bn_d bn_top bn_buf bn_neg bn_flags bn_dmax Z.b2z length]; exact BNr).
      assert (OKr' : bg_ok (bn_with_neg br false)) by (destruct OKr as (O1 & O2 & O3 & O4); unfold bg_ok, bn_with_neg, bn_dmax in *; cbn [bn_buf bn_top bn_flags]; repeat split; assumption).
      destruct (CLOSEr m27 (bn_with_neg br false) MUr WMr BNr' eq_refl eq_refl OKr' STr MIr) as (EV27 & LS27).
      clear CLOSEr BNr BNr' MUr WMr STr MIr ACCr.
      unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].

      assert (HAm26 : ref_at ls26 OW26 PL rm am) by exact (ref_at_stable _ _ _ _ PL _ _ RS2526 (proj2 (ref_at_setbn _ _ _ _ _ _ _) (ref_at_stable _ _ _ _ PL _ _ RS023 HAm))).
      assert (HAd26 : ref_at ls26 OW26 PL u2 ad) by exact (ref_at_stable _ _ _ _ PL _ _ RS2526 (proj2 (ref_at_setbn _ _ _ _ _ _ _) HAd23)).
      set (ls27 := setbn rr (bn_with_neg br false) ls26) in *.
      assert (HAr27 : ref_at ls27 OW26 PL rr ar) by (apply ref_at_setbn; exact HAr26).
      assert (HAm27 : ref_at ls27 OW26 PL rm am) by (apply ref_at_setbn; exact HAm26).
      assert (HAd27 : ref_at ls27 OW26 PL u2 ad) by (apply ref_at_setbn; exact HAd26).
      lazymatch type of EV27 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?preb _ _ _ _ _ => pose (PREB := preb) end.
      pose (LOOPQ := fun (r : unit * bstate bptr) (Σ' : rts RT) (ms' : machine_state) =>
        exists mJ OWJ usedJ (k1 k5 k6 k7 k10 k11 k12 k13 k14 k15 k16 k17 k26 k28 k29 k30 k31 : word) (FJ : bvmap 5 word) (fcJ : bv 32),
          ms' = MS (mkR k1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 TP_A) k5 k6 k7 sp (Z_to_bv 64 ac) k10 k11 k12 k13 k14 k15 k16 k17
                     (Z_to_bv 64 an) (Z_to_bv 64 am) (Z_to_bv 64 ar) (Z_to_bv 64 ad) (Z_to_bv 64 (ad + 16)) (Z_to_bv 64 (ar + 16))
                     (Z_to_bv 64 (Z.shiftr (ad + 16) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (ar + 16) 3 + SHB)) k26 (Z_to_bv 64 (Z.shiftr (an + 48) 3 + SHB)) k28 k29 k30 k31)
                   FJ (Z_to_bv 64 2826156) fcJ None mJ (seg_rom bgasegs)
          /\ cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m PREB usedJ Σ' (snd r) mJ OWJ
          /\ lib_state (snd r) mJ OWJ PL EA /\ refs_stable ls27 OW26 (snd r) OWJ
          /\ usedJ <= BN_DIV_RECP_COST).
      assert (LOOP : forall (fuel : nat) (j used30 : Z) (Σ30 : rts RT) (ls30 : bstate bptr) (m30 : mem) (OW30 : list block)
                       (k1 k5 k6 k7 k10 k11 k12 k13 k14 k15 k16 k17 k28 k29 k30 k31 : word) (F30 : bvmap 5 word) (fc30 : bv 32),
                cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m PREB used30 Σ30 ls30 m30 OW30 -> lib_state ls30 m30 OW30 PL EA -> refs_stable ls27 OW26 ls30 OW30 ->
                0 <= j <= 3 -> 4 - j <= Z.of_nat fuel -> used30 + (4 - j) * (MC + MC) <= BN_DIV_RECP_COST ->
                implA (recp_fix_loop (tree_ops bptr) fuel rr u2 j ls30) Σ30 LOOPQ
                  (MS (mkR k1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 TP_A) k5 k6 k7 sp (Z_to_bv 64 ac) k10 k11 k12 k13 k14 k15 k16 k17
                     (Z_to_bv 64 an) (Z_to_bv 64 am) (Z_to_bv 64 ar) (Z_to_bv 64 ad) (Z_to_bv 64 (ad + 16)) (Z_to_bv 64 (ar + 16))
                     (Z_to_bv 64 (Z.shiftr (ad + 16) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (ar + 16) 3 + SHB)) (Z_to_bv 64 (4 - j)) (Z_to_bv 64 (Z.shiftr (an + 48) 3 + SHB)) k28 k29 k30 k31)
                      F30 (Z_to_bv 64 2826032) fc30 None m30 (seg_rom bgasegs))).
      { clear EV27 LS27.
        induction fuel as [|fuel IH]; intros until fc30; intros EV30 LS30 RS30 J FU U30; [exfalso; clear - J FU; lia|].
        change (recp_fix_loop (tree_ops bptr) (S fuel) rr u2 j ls30) with
          (tbind (BN_ucmp (tree_ops bptr) rr RRecpN ls30)
             (fun p => (if fst p <? 0 then bret (tree_ops bptr) tt
                        else if 2 <? j then bunr (tree_ops bptr)
                        else fun s1 => tbind (BN_usub (tree_ops bptr) rr rr RRecpN s1)
                                         (fun p1 => tbind (BN_add_word (tree_ops bptr) u2 1 (snd p1))
                                                      (fun p2 => recp_fix_loop (tree_ops bptr) fuel rr u2 (j + 1) (snd p2)))) (snd p))).
        assert (JP : 0 <= (4 - j) * (MC + MC)) by (apply Z.mul_nonneg_nonneg; [clear - J; lia | clear - MCP; lia]).
        pose proof (ref_at_stable _ _ _ _ PL _ _ RS30 HAr27) as HAr30.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RS30 HAd27) as HAd30.
        pose proof (recp_at_refN ls30 OW30 PL an HRC) as HAN30.
        apply implA_from_evt. step. step. step.
    apply evt_done.
        eapply implA_bind.
        { eapply (BN_ucmp_walkA) with (lo := lo) (OW := OW30) (LB := LB) (PL := PL) (EA := EA);
            [| reflexivity | exact HAr30 | exact HAN30 | exact NROr | exact NRON | reflexivity | reflexivity].
          - eapply cenv_preA; [exact EV30 | exact LS30 | clear - LO' CSucmp; lia | clear - U30 JP; lia].
        }
        cbv beta. intros [u31 ls31] Σ31 ms31 PO.
        apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV30))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F31 & fc31 & m31 & OW31 & PL31 & -> & CP31 & ((EPL31 & -> & CR31 & ELS31 & EOW31) & EC31)).
        subst PL31. specialize (CP31 eq_refl).
        destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV30 CP31) as (EV31 & LS31).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP31) as RS31.
        rewrite (ret_pc_even 2826044) by (clear; lia).
        subst ls31 OW31. clear EC31.
        unfold MallocRep.wz. apply implA_from_evt.
        step. rewrite lts_signed by (clear - CR31; lia).
        destruct (Z.ltb_spec u31 0) as [CN|CP]; cbn [negb].
        {
          apply evt_done. unfold bret. cbn [ret tree_ops]. apply implA_ret.
          unfold LOOPQ. exists m31, OW30, (used30 + 0). do 19 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact EV31|]. split; [exact LS31|]. split; [exact RS30|]. clear - U30 JP; lia. }
        step. rewrite (unsigned_lit (4 - j)) by (clear - J; lia). rewrite (bn_swrap32_small (4 - j + -1)) by (clear - J; lia).
        step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - J; lia); zify_cond KZ.
        {
          replace (2 <? j) with true by (symmetry; apply Z.ltb_lt; clear - KZ J; lia).
          apply evt_done. unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
        replace (2 <? j) with false by (symmetry; apply Z.ltb_ge; clear - KZ J; lia).
        assert (JM : 0 <= (2 - j) * MC) by (apply Z.mul_nonneg_nonneg; [clear - KZ J; lia | exact MCP]).

        step. step. step. step.
    apply evt_done.
        eapply implA_bind.
        { eapply (BN_usub_walkA) with (lo := lo) (OW := OW30) (LB := LB) (PL := PL) (EA := EA);
            [| | | reflexivity | exact HAr30 | exact HPr | exact HAr30 | exact NROr | exact HAN30 | exact NRON | reflexivity | reflexivity | reflexivity].
          - eapply cenv_preA; [exact EV31 | exact LS31 | clear - LO' CSusub; lia | clear - U30 JM MCP; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV31).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1d70 CTX).
        }
        cbv beta. intros [u32 ls32] Σ32 ms32 PO.
        apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV31))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F32 & fc32 & m32 & OW32 & PL32 & -> & CP32 & (EPL32 & -> & INCL32)).
        subst PL32. specialize (CP32 eq_refl).
        destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV31 CP32) as (EV32 & LS32).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP32) as RS32.
        rewrite (ret_pc_even 2826072) by (clear; lia).
        unfold MallocRep.wz. apply implA_from_evt. step. if_false.

        step. step. step.
    apply evt_done.
        eapply implA_bind.
        { eapply (BN_add_word_walkA) with (lo := lo) (OW := OW32) (LB := LB) (PL := PL) (EA := EA);
            [| | | reflexivity | exact (ref_at_stable _ _ _ _ PL _ _ RS32 HAd30) | rewrite Ed; apply wref_pool | reflexivity | reflexivity | clear; lia].
          - eapply cenv_preA; [exact EV32 | exact LS32 | clear - LO' CSaw; lia | clear - U30 JM MCP; lia].
          - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV32).
          - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_div_recp_2b1d80 CTX).
        }
        cbv beta. intros [u33 ls33] Σ33 ms33 PO.
        apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV32))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F33 & fc33 & m33 & OW33 & PL33 & -> & CP33 & (EPL33 & -> & INCL33)).
        subst PL33. specialize (CP33 eq_refl).
        destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV32 CP33) as (EV33 & LS33).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP33) as RS33.
        rewrite (ret_pc_even 2826088) by (clear; lia).
        unfold MallocRep.wz. apply implA_from_evt. step. if_false. step.
        replace (4 - j + -1) with (4 - (j + 1)) by (clear; lia).
        apply evt_done.
        eapply IH; [exact EV33 | exact LS33 | exact (refs_stable_trans _ _ _ _ _ _ RS30 (refs_stable_trans _ _ _ _ _ _ RS32 RS33)) | clear - J KZ; lia | clear - FU; lia | clear - U30; lia]. }
      step.
      apply evt_done. eapply implA_bind with (Q1 := LOOPQ).
      { eapply (LOOP 5%nat 0); [exact EV27 | exact LS27 | apply refs_stable_refl | clear; lia | clear; lia |].
        unfold BN_DIV_RECP_COST, BN_RECIPROCAL_COST, BN_DIV_FT_COST, BN_MUL_TOP_COST in *; clear - MCP U20; lia. }
      clear LOOP.
      cbv beta. intros [u40 ls40] Σ40 ms40 (m40 & OW40 & used40 & R).
      destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & kc & ? & ? & ? & ? & F40 & fc40 & -> & EV40 & LS40 & RS40 & U40). cbn [fst snd] in *.
      clear LOOPQ.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS40 HAr27) as HAr40. pose proof (ref_at_stable _ _ _ _ PL _ _ RS40 HAm27) as HAm40.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS40 HAd27) as HAd40. pose proof (recp_at_refN ls40 OW40 PL an HRC) as HAN40.

      apply implA_from_evt. step. step.
      eapply (is_zero_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m LOFB16) with (r := rr) (ar := ar);
        [exact EV40 | exact LS40 | exact HAr40 | exact NROr |].
      intros m41 y0D y1D y2D y4D y5D y6D y7D y8D y9D y10D y11D y12D y13D y14D EV41 LS41.
      rewrite (ret_pc_even 2826164) by (clear; lia).
      step. step.
      remember (if is_zero_pure (getbn rr ls40) then false else bn_neg (getbn rm ls40)) as nb eqn:Enb.

      lazymatch goal with |- evt _ ?POSTX _ =>
        assert (TAILR : forall (k12 : word),
          evt bgasegs POSTX
            (MS (mkR (Z_to_bv 64 2826164) (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 TP_A) y0D y1D y2D sp (Z_to_bv 64 ac) (Z_to_bv 64 (am + 16)) (Z_to_bv 64 (Z.b2z nb)) k12 y6D y7D y8D y9D y10D
                     (Z_to_bv 64 an) (Z_to_bv 64 am) (Z_to_bv 64 ar) (Z_to_bv 64 ad) (Z_to_bv 64 (ad + 16)) (Z_to_bv 64 (ar + 16))
                     (Z_to_bv 64 (Z.shiftr (ad + 16) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (ar + 16) 3 + SHB)) kc (Z_to_bv 64 (Z.shiftr (an + 48) 3 + SHB)) y11D y12D y13D y14D)
                F40 (Z_to_bv 64 2826328) fc40 None m41 (seg_rom bgasegs)))
      end.
      { intros k12. clear Enb.
        destruct (cenv_struct_openA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra ras BN_DIV_RECP_COST Σ ls OW m LOFB16 _ _ _ _ _ _ rr ar EV41 LS41 HAr40 (hpl_wref _ _ HPr))
          as (Dr2 & BNr2 & OKr2 & ACCr2 & ALr2 & Ar02 & SEPr2 & OFSr2 & STr2 & MIr2 & CLOSEr2).
        unfold BnRepDefs.bn_cells in BNr2. unfold SHLO, SHHI in OFSr2.
        pose proof (munch_refl [(ar, ar + 24)]%Z m41) as MUr2. pose proof (wmono_refl bgasegs m41) as WMr2.
        shl_with ACCr2 ALr2. chk0.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m42 end.
        set (br2 := getbn rr ls40) in *.
        assert (BNr2' : rw_cells bgasegs m42 ar (BnRepDefs.bn_cells Dr2 (bn_with_neg br2 nb))) by (unfold BnRepDefs.bn_cells, bn_with_neg; cbn [bn_d bn_top bn_buf bn_neg bn_flags bn_dmax length]; exact BNr2).
        assert (OKr2' : bg_ok (bn_with_neg br2 nb)) by (destruct OKr2 as (O1 & O2 & O3 & O4); unfold bg_ok, bn_with_neg, bn_dmax in *; cbn [bn_buf bn_top bn_flags]; repeat split; assumption).
        destruct (CLOSEr2 m42 (bn_with_neg br2 nb) MUr2 WMr2 BNr2' eq_refl eq_refl OKr2' STr2 MIr2) as (EV42 & LS42).
        clear CLOSEr2 BNr2 BNr2' MUr2 WMr2 STr2 MIr2 ACCr2.
        set (ls42 := setbn rr (bn_with_neg br2 nb) ls40) in *.
        assert (HAm42 : ref_at ls42 OW40 PL rm am) by (apply ref_at_setbn; exact HAm40).
        assert (HAd42 : ref_at ls42 OW40 PL u2 ad) by (apply ref_at_setbn; exact HAd40).
        pose proof (recp_at_refN ls42 OW40 PL an HRC) as HAN42.
        destruct (open_for_call LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m LOFB16 _ _ _ _ _ _ rm am EV42 LS42 HAm42 NROm) as (Dm & BNm & _ & _ & _ & _ & SEPm & _ & ACCm & ALm & _ & OFSm & Am0).
        destruct (open_for_call LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m LOFB16 _ _ _ _ _ _ RRecpN an EV42 LS42 HAN42 NRON) as (Dn & BNn & _ & _ & _ & _ & SEPn & _ & ACCn & ALn & _ & OFSn & _).
        destruct (cenv_struct_openA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra ras BN_DIV_RECP_COST Σ ls OW m LOFB16 _ _ _ _ _ _ u2 ad EV42 LS42 HAd42 ltac:(rewrite Ed; apply wref_pool))
          as (Dd2 & BNd2 & OKd2 & ACCd2 & ALd2 & Ad02 & SEPd2 & OFSd2 & STd2 & MId2 & CLOSEd2).
        unfold BnRepDefs.bn_cells, MallocRep.wz in BNm, BNn, BNd2. unfold SHLO, SHHI in OFSm, OFSn, OFSd2.
        assert (AmT : 0 <= am /\ am + 24 <= 140737488355328) by (clear - SEPm SPT Am0; lia).
        pose proof EV42 as (_ & _ & _ & _ & _ & _ & _ & _ & FR42 & _). cbn [app] in FR42. unfold PREB in FR42.
        pose proof (munch_refl [(ad, ad + 24)]%Z m42) as MUd2. pose proof (wmono_refl bgasegs m42) as WMd2.
        pose proof (munch_refl (@nil (Z * Z)) m42) as MU0.
        step. step. step.
        shl_with ACCm ALm. chk0.
        step. step. step.
        shl_with ACCn ALn.
        step. rewrite (sx32_int (Z.b2z (bn_neg (getbn rm ls42)))) by (destruct (bn_neg (getbn rm ls42)); cbn [Z.b2z]; clear; lia).
        chk0.
        clear MU0.
        shl_with ACCd2 ALd2.
        step. rewrite (sx32_int (Z.b2z (bn_neg (getbn RRecpN ls42)))) by (destruct (bn_neg (getbn RRecpN ls42)); cbn [Z.b2z]; clear; lia).
        chk0.
        clear BNm BNn ACCm ACCn.
        step.
        rewrite xor_b2z.
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m43 end.
        set (bd2 := getbn u2 ls42) in *.
        set (nd := xorb (bn_neg (getbn rm ls42)) (bn_neg (getbn RRecpN ls42))) in *.
        assert (BNd2' : rw_cells bgasegs m43 ad (BnRepDefs.bn_cells Dd2 (bn_with_neg bd2 nd))) by (unfold BnRepDefs.bn_cells, bn_with_neg; cbn [bn_d bn_top bn_buf bn_neg bn_flags bn_dmax length]; exact BNd2).
        assert (OKd2' : bg_ok (bn_with_neg bd2 nd)) by (destruct OKd2 as (O1 & O2 & O3 & O4); unfold bg_ok, bn_with_neg, bn_dmax in *; cbn [bn_buf bn_top bn_flags]; repeat split; assumption).
        destruct (CLOSEd2 m43 (bn_with_neg bd2 nd) MUd2 WMd2 BNd2' eq_refl eq_refl OKd2' STd2 MId2) as (EV43 & LS43).
        clear CLOSEd2 BNd2 BNd2' MUd2 WMd2 STd2 MId2 ACCd2 FR42.
        step. step. step. step.
    apply evt_done.
        eapply implA_post_evt.
        { eapply (BN_CTX_end_walkA) with (lo := lo) (OW := OW40) (LB := LB) (PL := PL) (EA := EA);
            [| reflexivity | exact HPC | reflexivity].
          - eapply cenv_preA; [exact EV43 | exact LS43 | clear - LO' CSend; lia | clear - U40; lia].
        }
        cbv beta. intros [u44 ls44] Σ44 ms44 PO.
        apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) BN_DIV_RECP_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 EV43))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F44 & fc44 & m44 & OW44 & PL44 & -> & CP44 & (EPL44 & EOW44)).
        subst PL44. specialize (CP44 eq_refl).
        destruct (cenv_postA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ _ _ _ _ _ EV43 CP44) as (EV44 & LS44).
        pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP44) as RS44.
        rewrite (ret_pc_even 2826240) by (clear; lia).
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m _ _ _ _ _ _ EV44 LS44 ltac:(clear - U40; lia)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
        pose proof EV44 as (_ & _ & STF & _ & _ & _ & _ & _ & FRF & _ & _). unfold PREB in FRF. cbn [app] in FRF.
        step. do 13 step. release_frame FRF STF (bv_unsigned sp). step. step.
        apply evt_done. unfold bn_postA. do 17 eexists. exists m44, OW44, PL. split; [reflexivity|]. cbn [fst snd].
        split; [exact G1|]. split; [exact G2|]. split; [exact STF|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7|].
        split; reflexivity.
      }
      unfold is_zero_pure in Enb. revert Enb.
      destruct (Nat.eqb_spec (bn_top (getbn rr ls40)) 0) as [TZ|TNZ]; intros Enb; cbn [Z.b2z].
      +
        step. if_false. step. step.
        subst nb. exact (TAILR _).
      +
        step. if_true.
        destruct (open_for_call LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -128) s0 ra (Some ras) BN_DIV_RECP_COST Σ ls OW m LOFB16 _ _ _ _ _ _ rm am EV41 LS41 HAm40 NROm) as (Dm & BNm & _ & _ & _ & _ & SEPm & _ & ACCm & ALm & _ & OFSm & Am0).
        unfold BnRepDefs.bn_cells, MallocRep.wz in BNm. unfold SHLO, SHHI in OFSm.
        assert (AmT : 0 <= am /\ am + 24 <= 140737488355328) by (clear - SEPm SPT Am0; lia).
        pose proof EV41 as (_ & _ & _ & _ & _ & _ & _ & _ & FR41 & _). cbn [app] in FR41. unfold PREB in FR41.
        pose proof (munch_refl (@nil (Z * Z)) m41) as MU0.
        step. step. step.
        shl_with ACCm ALm. chk0.
        step. rewrite (sx32_int (Z.b2z (bn_neg (getbn rm ls40)))) by (destruct (bn_neg (getbn rm ls40)); cbn [Z.b2z]; clear; lia).
        subst nb. exact (TAILR _).
  Qed.
End Proofs.

End WithRT.
