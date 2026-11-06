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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA W_topA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF W_expandAF ShiftKitAF W_callsAF W_lshiftAF W_rshiftAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_LSHIFT_W : Z := 0x234344.
Definition BN_LSHIFT_W_STACK : Z := 32 + BN_LSHIFT_STACK.
Definition BN_RSHIFT_W : Z := 0x234700.
Definition BN_RSHIFT_W_STACK : Z := 32 + BN_RSHIFT_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

  Lemma BN_lshift_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax : Z) (n : Z),
    bn_preA Σ ls m OW LB PL EA sp lo BN_LSHIFT_W_STACK MC ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_LSHIFT_W (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> hpl PL rr -> ref_at ls OW PL rx ax -> rx <> ROne -> nbuf PL rx ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz n -> -2^31 <= n < 2^30 ->
    implA (BN_lshift (tree_ops bptr) rr rx n ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC (shift_res rr ls OW PL))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_LSHIFT_W) fc None m (seg_rom bgasegs)).
  Proof.
    intros until n. intros PRE UW CTX -> HAr HP HAx NROx NBx -> -> -> HN.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold BN_LSHIFT_W_STACK, BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
    unfold BN_LSHIFT_W, MallocRep.wz.
    change (2 ^ 31) with 2147483648 in HN. change (2 ^ 30) with 1073741824 in HN.

    unfold BN_lshift.
    destruct (Z.ltb_spec n 0) as [NNEG|NNEG].
    { unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    unfold bbind. cbn [bind tree_ops tbind fst snd].
    apply implA_from_evt.

    carve_frame 32%nat ST. do 6 step.
    step. rewrite lts_signed by lia. destruct (Z.ltb_spec n 0) as [NN|_]; [exfalso; lia|].
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    assert (EV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) MC Σ ls OW m [C8 s2; C8 s1] 0 Σ ls m1 OW).
    { unfold cenvA, cenv_ok.
      split; [split; [exact CEIL|]; split; [lia|]; split; [lia|]; split; [unfold USTACK_TOP; lia|]; split; [exact SP16|];
              split; [clear - SP16; Z.div_mod_to_equations; lia|]; split; [exact CNT|]; split; [exact CRED|]; split; [exact FROK|]; split; [exact FAL| exact NOFR]|].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
      split; [exact ST|]. split; [exact MI|].
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))|].
      split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
      split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
      eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
    pose proof EV as (OK & HEAP1 & _).
    assert (LOFB16 : lo <= bv_unsigned sp + -32 - 16) by (clear - LO'; lia).
    clear HEAP LS ST MI MU WM HWL WOK FR PRE PARTS.

    step.
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_lshift_fixed_top_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (rr := rr) (rx := rx) (ar := ar) (ax := ax) (n := n) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAr | exact HP | exact HAx | exact NROx | solve_nbuf | reflexivity | reflexivity | reflexivity | lia].
      - eapply cenv_preA; [exact EV | exact LS1 | unfold BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO'; lia | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_lshift_234180 : uk_call BN_LSHIFT_W 0x234368 BN_LSHIFT) CTX). }
    cbv beta. intros [u ls1] Σ1 ms1 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) MC Σ ls OW) in PO; [| exact OK | exact HEAP1].
    cbn [fst snd] in *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & CP & (EPL & -> & BST)).
    subst PL2. specialize (CP eq_refl).
    assert (E1 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) MC Σ ls OW m [C8 s2; C8 s1] (0 + MC) Σ1 ls1 m2 OW2 /\ lib_state ls1 m2 OW2 PL EA)
      by (eapply cenv_postA; [exact EV | exact CP]).
    destruct E1 as (EV1 & LS2).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RST2.
    rewrite (ret_pc_even 2311016) by (clear; lia).
    pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAr) as HAr2.

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
    step. step. step.
    eapply (ctop_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) MC Σ ls OW m LOFB16);
      [exact EV1 | exact LS2 | exact HAr2 | exact (hpl_wref PL rr HP) |].
    intros m3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ls3 ENV3 LS3.
    rewrite (ret_pc_even 2311028) by (clear; lia).
    pose proof ENV3 as (_ & _ & ST3 & _ & _ & _ & _ & _ & FR3 & _ & _). cbn [app] in FR3.
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) MC Σ ls OW m _ _ _ _ _ _ ENV3 LS3 ltac:(clear; lia)) as (F1 & F2' & F3 & F4 & F5 & F6 & F7).
    step. step. do 4 step. release_frame FR3 ST3 (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_postA. do 17 eexists. exists m3, OW2, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact F2'|]. split; [exact ST3|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|]. split; [exact F6|]. split; [exact F7|].
    unfold shift_res. split; [reflexivity|]. split; [reflexivity| exact BST].
  Qed.

  Lemma BN_rshift_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr rx : bnref) (ar ax : Z) (n : Z),
    bn_preA Σ ls m OW LB PL EA sp lo BN_RSHIFT_W_STACK MC ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_RSHIFT_W (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> hpl PL rr -> ref_at ls OW PL rx ax -> rx <> ROne -> nbuf PL rx ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz n -> -2^31 <= n < 2^30 ->
    implA (BN_rshift (tree_ops bptr) rr rx n ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC (shift_res rr ls OW PL))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_RSHIFT_W) fc None m (seg_rom bgasegs)).
  Proof.
    intros until n. intros PRE UW CTX -> HAr HP HAx NROx NBx -> -> -> HN.
    pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof LO as LO'. unfold BN_RSHIFT_W_STACK, BN_RSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
    unfold BN_RSHIFT_W, MallocRep.wz.
    change (2 ^ 31) with 2147483648 in HN. change (2 ^ 30) with 1073741824 in HN.

    unfold BN_rshift.
    destruct (Z.ltb_spec n 0) as [NNEG|NNEG].
    { unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    unfold bbind. cbn [bind tree_ops tbind fst snd].
    apply implA_from_evt.

    carve_frame 32%nat ST. do 6 step.
    step. rewrite lts_signed by lia. destruct (Z.ltb_spec n 0) as [NN|_]; [exfalso; lia|].
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
    pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    assert (EV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) MC Σ ls OW m [C8 s2; C8 s1] 0 Σ ls m1 OW).
    { unfold cenvA, cenv_ok.
      split; [split; [exact CEIL|]; split; [lia|]; split; [lia|]; split; [unfold USTACK_TOP; lia|]; split; [exact SP16|];
              split; [clear - SP16; Z.div_mod_to_equations; lia|]; split; [exact CNT|]; split; [exact CRED|]; split; [exact FROK|]; split; [exact FAL| exact NOFR]|].
      split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|].
      split; [exact ST|]. split; [exact MI|].
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia))|].
      split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
      split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
      eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
    pose proof EV as (OK & HEAP1 & _).
    assert (LOFB16 : lo <= bv_unsigned sp + -32 - 16) by (clear - LO'; lia).
    clear HEAP LS ST MI MU WM HWL WOK FR PRE PARTS.

    step.
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_rshift_fixed_top_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (rr := rr) (rx := rx) (ar := ar) (ax := ax) (n := n) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAr | exact HP | exact HAx | exact NROx | solve_nbuf | reflexivity | reflexivity | reflexivity | lia].
      - eapply cenv_preA; [exact EV | exact LS1 | unfold BN_RSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO'; lia | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_rshift_23453c : uk_call BN_RSHIFT_W 0x234724 BN_RSHIFT) CTX). }
    cbv beta. intros [u ls1] Σ1 ms1 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) MC Σ ls OW) in PO; [| exact OK | exact HEAP1].
    cbn [fst snd] in *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & CP & (EPL & -> & BST)).
    subst PL2. specialize (CP eq_refl).
    assert (E1 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) MC Σ ls OW m [C8 s2; C8 s1] (0 + MC) Σ1 ls1 m2 OW2 /\ lib_state ls1 m2 OW2 PL EA)
      by (eapply cenv_postA; [exact EV | exact CP]).
    destruct E1 as (EV1 & LS2).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RST2.
    rewrite (ret_pc_even 2311972) by (clear; lia).
    pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAr) as HAr2.

    unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
    step. step. step.
    eapply (ctop_callA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) MC Σ ls OW m LOFB16);
      [exact EV1 | exact LS2 | exact HAr2 | exact (hpl_wref PL rr HP) |].
    intros m3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ls3 ENV3 LS3.
    rewrite (ret_pc_even 2311984) by (clear; lia).
    pose proof ENV3 as (_ & _ & ST3 & _ & _ & _ & _ & _ & FR3 & _ & _). cbn [app] in FR3.
    destruct (cenv_finalA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -32) s0 ra (Some ras) MC Σ ls OW m _ _ _ _ _ _ ENV3 LS3 ltac:(clear; lia)) as (F1 & F2' & F3 & F4 & F5 & F6 & F7).
    step. step. do 4 step. release_frame FR3 ST3 (bv_unsigned sp). step. step.
    apply evt_done. unfold bn_postA. do 17 eexists. exists m3, OW2, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact F1|]. split; [exact F2'|]. split; [exact ST3|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|]. split; [exact F6|]. split; [exact F7|].
    unfold shift_res. split; [reflexivity|]. split; [reflexivity| exact BST].
  Qed.

End WithRT.
