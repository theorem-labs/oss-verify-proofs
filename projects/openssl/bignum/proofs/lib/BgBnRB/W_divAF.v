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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgArith.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnDivWords BnDivLoop BnSpecs2 BnDivSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require StrFun.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX BnArith.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure DivLoopPure DivTop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2 AW_num_bits_word AW_div_la.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctx_getA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require Import BgLive DivModel.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require W_div.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_expandAF ShiftKitAF W_lshiftAF W_rshiftAF W_copyAF W_ctxAF W_ctx_endAF W_ctx_getAF W_div_tailAF W_div_padAF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import UbStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2313264 => 1
  | 2313268 => 2
  | 2313324 => 2
  | 2313336 => 1
  | 2313344 => 2
  | 2313352 => 1
  | 2313356 => 1
  | 2313360 => 1
  | 2313364 => 2
  | 2313368 => 2
  | 2313372 => 1
  | 2313376 => 2
  | 2313412 => 1
  | 2313416 => 2
  | 2313476 => 2
  | 2313500 => 2
  | 2313528 => 2
  | 2313604 => 1
  | 2313608 => 2
  | 2313612 => 1
  | 2313616 => 1
  | 2313620 => 2
  | 2313688 => 2
  | 2313740 => 1
  | 2313748 => 2
  | 2313752 => 1
  | 2313756 => 1
  | 2313760 => 1
  | 2313764 => 1
  | 2313768 => 2
  | 2313780 => 1
  | 2313784 => 2
  | 2313788 => 1
  | 2313796 => 2
  | 2313840 => 1
  | 2313848 => 2
  | 2313884 => 1
  | 2313892 => 1
  | 2313896 => 2
  | 2313900 => 1
  | 2313904 => 1
  | 2313908 => 1
  | 2313912 => 1
  | 2313916 => 1
  | 2313920 => 1
  | 2313924 => 2
  | 2313932 => 2
  | 2313948 => 1
  | 2313952 => 2
  | 2313956 => 1
  | 2313960 => 1
  | 2313964 => 1
  | 2313968 => 1
  | 2313972 => 1
  | 2313976 => 2
  | 2314000 => 2
  | 2314020 => 1
  | 2314028 => 2
  | 2314032 => 1
  | 2314036 => 1
  | 2314040 => 1
  | 2314044 => 1
  | 2314048 => 2
  | 2314052 => 2
  | 2314056 => 1
  | 2314060 => 2
  | 2314108 => 2
  | 2314120 => 2
  | 2314124 => 1
  | 2314132 => 1
  | 2314136 => 1
  | 2314140 => 2
  | 2314144 => 1
  | 2314148 => 2
  | 2314196 => 1
  | 2314200 => 2
  | 2314204 => 1
  | 2314208 => 1
  | 2314212 => 2
  | 2314240 => 2
  | 2314244 => 1
  | 2314248 => 2
  | 2314252 => 2
  | 2314256 => 1
  | 2314260 => 2
  | 2314376 => 1
  | 2314380 => 1
  | 2314384 => 2
  | 2314388 => 1
  | 2314392 => 1
  | 2314396 => 1
  | 2314400 => 2
  | 2314560 => 2
  | 2314564 => 1
  | 2314568 => 2
  | 2314588 => 1
  | 2314592 => 2
  | 2314648 => 1
  | 2314652 => 2
  | 2314656 => 1
  | 2314660 => 2
  | 2314876 => 1
  | 2314880 => 2
  | 2314948 => 1
  | 2314952 => 1
  | 2314956 => 2
  | 2314960 => 1
  | 2314968 => 1
  | 2314972 => 1
  | 2314976 => 2
  | 2314980 => 2
  | 2314984 => 1
  | 2314988 => 2
  | 2315012 => 1
  | 2315016 => 1
  | 2315020 => 2
  | 2315108 => 2
  | 2315112 => 1
  | 2315116 => 1
  | 2315120 => 2
  | 2315124 => 2
  | 2315160 => 2
  | 2315164 => 1
  | 2315168 => 1
  | 2315172 => 1
  | 2315176 => 2
  | 2315180 => 2
  | 2315184 => 1
  | 2315188 => 1
  | 2315192 => 2
  | 2315288 => 1
  | 2315292 => 2
  | 2315296 => 1
  | 2315300 => 2
  | 2315340 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide (_ \/ _) |- _ => apply hide_elim in H end.
Open Scope Z_scope.

Notation la_run := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_div.la_run.
Notation bbind_get_set := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_div.bbind_get_set.
Notation div_core := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_div.div_core.
Notation div_rest := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_div.div_rest.
Notation bn_div_fixed_top_unfold := OSSVerify.Proofs.openssl.bignum.lib.BgBnR.W_div.bn_div_fixed_top_unfold.
Local Notation ops := (tree_ops bptr).

Lemma shr3_shad : forall X, 0 <= X -> X ≫ 3 + SHB = shad X.
Proof. intros X HX. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.

Definition BN_DIV_FT_COST : Z := 11 * MC.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_dv_start := (E_bn_div_fixed_top_2349fc : uk_call BN_DIV_FIXED_TOP 0x234be4 BN_CTX_START).
Local Notation E_dv_get1 := (E_bn_div_fixed_top_234a08 : uk_call BN_DIV_FIXED_TOP 0x234bf0 BN_CTX_GET).
Local Notation E_dv_get2 := (E_bn_div_fixed_top_234a14 : uk_call BN_DIV_FIXED_TOP 0x234bfc BN_CTX_GET).
Local Notation E_dv_get3 := (E_bn_div_fixed_top_234a20 : uk_call BN_DIV_FIXED_TOP 0x234c08 BN_CTX_GET).
Local Notation E_dv_get4 := (E_bn_div_fixed_top_234a2c : uk_call BN_DIV_FIXED_TOP 0x234c14 BN_CTX_GET).
Local Notation E_dv_copy := (E_bn_div_fixed_top_234a40 : uk_call BN_DIV_FIXED_TOP 0x234c28 BN_COPY).
Local Notation E_dv_lshift := (E_bn_div_fixed_top_234b8c : uk_call BN_DIV_FIXED_TOP 0x234d74 BN_LSHIFT).
Local Notation E_dv_wexp2 := (E_bn_div_fixed_top_234de8 : uk_call BN_DIV_FIXED_TOP 0x234fd0 BN_WEXPAND).
Local Notation E_dv_wexp3 := (E_bn_div_fixed_top_234ed0 : uk_call BN_DIV_FIXED_TOP 0x2350b8 BN_WEXPAND).

Lemma bn_div_fixed_top_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (dv rm : option bnref) (num dvs : bnref) (adv arm anum advs ac : Z) (qc : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo BN_DIV_FT_STACK BN_DIV_FT_COST ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_DIV_FIXED_TOP (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> pl_ctx PL = Some (ac, qc) ->
  oref_at ls OW PL dv adv -> oref_at ls OW PL rm arm -> ref_at ls OW PL num anum -> ref_at ls OW PL dvs advs ->
  (forall d, dv = Some d -> wref PL d) -> (forall r, rm = Some r -> hpl PL r) -> num <> ROne -> dvs <> ROne -> nbuf PL num ->
  a0 = wz adv -> a1 = wz arm -> a2 = wz anum -> a3 = wz advs -> a4 = wz ac ->
  (1 <= bn_top (getbn dvs ls))%nat -> nth (bn_top (getbn dvs ls) - 1) (bn_buf (getbn dvs ls)) 0 <> 0 ->
  implA (bn_div_fixed_top ops dv rm num dvs ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_DIV_FT_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_DIV_FIXED_TOP) fc None m (seg_rom bgbsegs)).
Proof.
  intros until qc. intros PRE UW CTX -> EC HAdv HArm HAnum HAdvs WRdv HPrm NROn NROd NBn -> -> -> -> -> HTOPD HTOPNZ.
  change (not_one num) in NROn. change (not_one dvs) in NROd.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof LO as LO'.
  unfold BN_DIV_FT_STACK, BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO.
  unfold BN_DIV_FIXED_TOP, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.

  rewrite bn_div_fixed_top_unfold, bn_live_run.
  destruct (live_refs (st_ctx ls) (num :: dvs :: opt_refs dv ++ opt_refs rm)) eqn:LIVE; [| apply implA_unr].
  apply live_refs_true_iff in LIVE.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS0 & _).
  destruct (st_wf_get_pre ls WFS0) as (_ & _ & EPU0).
  assert (LVn : (num < NFIX + gx_pused (st_ctx ls))%nat) by (rewrite EPU0; exact (Forall_inv LIVE)).
  assert (LVd : (dvs < NFIX + gx_pused (st_ctx ls))%nat) by (rewrite EPU0; exact (Forall_inv (Forall_inv_tail LIVE))).
  assert (LVv : forall d, dv = Some d -> (d < NFIX + gx_pused (st_ctx ls))%nat).
  { intros d ->. rewrite EPU0. cbn [opt_refs app] in LIVE. exact (Forall_inv (Forall_inv_tail (Forall_inv_tail LIVE))). }
  clear LIVE EPU0 WFS0.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  apply implA_from_evt.
  carve_frame 304%nat ST. do 15 step. do 2 step. do 2 step. do 3 step. do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -304)) = bv_unsigned sp + -304) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -304, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -304, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  lazymatch type of FR with rw_cells _ _ _ (?fr ++ _) => idtac | rw_cells _ _ _ ?fr =>
    let pre := drop2 fr in
    assert (ENV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre 0 Σ ls m1 OW)
  end.
  { unfold cenvA. split.
    { unfold cenv_ok. split; [exact CEIL|]. split; [clear - LO; lia|]. split; [clear; lia|]. split; [unfold USTACK_TOP; clear - SPT; lia|]. split; [exact SP16|].
      split; [clear - SP16; Z.div_mod_to_equations; lia|]. split; [exact CNT|]. split; [exact CRED|]. split; [exact FROK|]. split; [exact FAL| exact NOFR]. }
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|].
    split; [exact ST|]. split; [exact MI|].
    split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(clear - LO; lia))|].
    split; [lia|]. split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|].
    split; [cbn [app]; exact FR|]. split; [cbn; lia|]. unfold uw_opt.
    eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  pose proof ENV as (OK & HEAP1 & _).
  assert (HWLs : forall lsx OWx, Forall (w_lib lsx OWx PL lo (bv_unsigned sp)) [(bv_unsigned sp + -304, bv_unsigned sp)]) by (intros lsx OWx; constructor; [left; cbn; lia| constructor]).
  assert (WOKs : forall OWx lsx, Forall (w_ok OWx LB lsx PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -304, bv_unsigned sp)]).
  { intros OWx lsx; constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  clear HEAP LS ST MI MU WM HWL WOK FR PRE SHB1 SHB2 PARTS.

  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_CTX_start_leaves ls)|].
    eapply (BN_CTX_start_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc); [| | | reflexivity | exact EC | reflexivity].
    - eapply cenv_preA; [exact ENV | exact LS1 | unfold BN_CTX_START_STACK, CRYPTO_MALLOC_ARRAY_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | unfold BN_DIV_FT_COST, MC; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_start CTX). }
  cbv beta. intros [u1 ls2] Σ2 ms2 [PO LEAF2].
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact HEAP1].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F2 & fc2 & m2 & OW2 & PL2 & -> & CP2 & (EPL2 & _)).
  subst PL2. specialize (CP2 eq_refl).
  lazymatch type of ENV with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre _ _ _ _ _ =>
    assert (E2 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (0 + MC) Σ2 ls2 m2 OW2 /\ lib_state ls2 m2 OW2 PL EA)
      by (eapply cenv_postA; [exact ENV | exact CP2]) end.
  destruct E2 as (ENV2 & LS2).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP2) as RS2.
  rewrite (ret_pc_even 0x234be4) by lia. unfold MallocRep.wz.
  clear ENV LS1 CP2 HEAP1 m1.
  destruct LEAF2 as (L2a & L2b & L2c & L2d). cbn [snd] in *.

  lazymatch type of ENV2 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre _ _ _ _ _ =>
  enough (AFTER : forall ΣK lsK mK OWK usedK (FK : bvmap 5 word) (fcK : bv 32) res ares z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31,
     cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre usedK ΣK lsK mK OWK ->
     usedK <= 2 * MC ->
     lib_state lsK mK OWK PL EA ->
     ref_at lsK OWK PL res ares -> wref PL res ->
     oref_at lsK OWK PL rm arm -> ref_at lsK OWK PL num anum -> ref_at lsK OWK PL dvs advs ->
     (res < NFIX + gx_pused (st_ctx lsK))%nat -> (num < NFIX + gx_pused (st_ctx lsK))%nat -> (dvs < NFIX + gx_pused (st_ctx lsK))%nat ->
     (1 <= bn_top (getbn dvs lsK))%nat -> nth (bn_top (getbn dvs lsK) - 1) (bn_buf (getbn dvs lsK)) 0 <> 0 ->
     implA (div_rest res rm num dvs lsK) ΣK
       (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_DIV_FT_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1))
       (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp (Z_to_bv 64 TP_A) z5 z6 z7 sp s1 z10 z11 z12 z13 z14 z15 z16 z17 s2 (Z_to_bv 64 advs) s4 s5 s6 (Z_to_bv 64 ares) (Z_to_bv 64 SHB) s9 s10 (Z_to_bv 64 ac) z28 z29 z30 z31)
           FK (Z_to_bv 64 0x234bf4) fcK None mK (seg_rom bgbsegs)))
  end.
  { pose proof (ref_at_stable _ _ _ _ _ _ _ RS2 HAnum) as HAnum2. pose proof (ref_at_stable _ _ _ _ _ _ _ RS2 HAdvs) as HAdvs2.
    pose proof (oref_at_stable _ _ _ _ _ _ _ RS2 HArm) as HArm2. pose proof (oref_at_stable _ _ _ _ _ _ _ RS2 HAdv) as HAdv2.
    assert (G2 : forall r, getbn r ls2 = getbn r ls) by (intros r; unfold getbn; rewrite L2a; reflexivity).
    destruct dv as [d|].
    -
      cbn [oref_at] in HAdv2. pose proof (WRdv d eq_refl) as WRd.
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
      destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENV2)) PARTS2 NOFR HAdv2 (proj1 WRd)) as (qd & Ad & nd & Hind & Rd1 & Rd2).
      pose proof (AH_range_in _ _ _ _ _ _ _ (proj1 (proj2 ENV2)) Hind) as (DA0 & _ & _ & DAC & _).
      assert (ADV : 0 < adv < 18446744073709551616) by (unfold BnHeapA.ACEIL in *; clear - DA0 Rd1 Rd2 DAC CEIL LO SPR; lia).
      rewrite W_div_tail.bbind_ret.
      apply implA_from_evt.
      zstep. if_cases KD; zify_cond KD. 2:{ exfalso. rewrite ?unsigned_lit in KD by (clear - ADV; lia). clear - KD ADV. lia. }
      clear KD.
      apply evt_done.
      eapply AFTER; [exact ENV2 | unfold MC; clear; lia | exact LS2 | exact HAdv2 | exact WRd | exact HArm2 | exact HAnum2 | exact HAdvs2 | | | | |].
      + rewrite L2b. exact (LVv d eq_refl).
      + rewrite L2b. exact LVn.
      + rewrite L2b. exact LVd.
      + rewrite G2. exact HTOPD.
      + rewrite G2. exact HTOPNZ.
    -
      cbn [oref_at] in HAdv2. subst adv.
      apply implA_from_evt.
      zstep. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. clear - KD. lia. }
      clear KD.
      do 2 zstep.
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as (WFS2 & _).
      destruct (st_wf_get_pre ls2 WFS2) as (GP1 & GP2 & _).
      apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
      eapply implA_bind.
      { eapply implA_leaves; [apply (BN_CTX_get_leaves ls2 GP1 GP2)|].
        eapply (BN_CTX_get_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW2) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc); [| | | reflexivity | exact EC | reflexivity].
        - eapply cenv_preA; [exact ENV2 | exact LS2 | unfold BN_CTX_GET_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | unfold BN_DIV_FT_COST, MC; clear; lia].
        - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV2).
        - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_get1 CTX). }
      cbv beta. intros [res ls3] Σ3 ms3 [PO LEAF3].
      apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENV2))].
      cbn [fst snd] in *.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & OW3 & PL3 & -> & CP3 & (EPL3 & _ & (ares & HAres & ->) & _)).
      subst PL3. specialize (CP3 eq_refl).
      destruct (cenv_postA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ENV2 CP3) as (ENV3 & LS3).
      pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP3) as RS3.
      rewrite (ret_pc_even 0x234bf0) by lia. unfold MallocRep.wz.
      clear CP3.
      destruct LEAF3 as (L3a & L3b & L3c & L3d & _). cbn [fst snd] in *.
      apply implA_from_evt.
      zstep.
      apply evt_done.
      eapply AFTER; [exact ENV3 | unfold MC; clear; lia | exact LS3 | exact HAres | rewrite L3a; apply wref_pool
                    | exact (oref_at_stable _ _ _ _ _ _ _ RS3 HArm2) | exact (ref_at_stable _ _ _ _ _ _ _ RS3 HAnum2) | exact (ref_at_stable _ _ _ _ _ _ _ RS3 HAdvs2) | | | | |].
      + rewrite L3a, L3b. unfold RPool. clear. lia.
      + rewrite L3b, L2b. clear - LVn. lia.
      + rewrite L3b, L2b. clear - LVd. lia.
      + rewrite L3d by (rewrite L2b; unfold RPool; clear - LVd; lia). rewrite G2. exact HTOPD.
      + rewrite L3d by (rewrite L2b; unfold RPool; clear - LVd; lia). rewrite G2. exact HTOPNZ. }

  clear ENV2 LS2 RS2 L2a L2b L2c L2d HAdv HArm HAnum HAdvs HTOPD HTOPNZ LVn LVd LVv WRdv adv m2 OW2 Σ2 ls2 F2 fc2 UW.
  intros ΣK lsK mK OWK usedK FK fcK res ares z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31
         ENVK UKD LSK HAresK WRres HArmK HAnumK HAdvsK LTres LTnum LTdvs HTOPD HTOPNZ.
  pose proof (proj1 WRres : not_one res) as NROr.
  unfold div_rest.

  pose proof (lib_state_h_parts _ _ _ _ _ _ LSK) as (WFSK & _).
  destruct (st_wf_get_pre lsK WFSK) as (GPK1 & GPK2 & _).
  set (p := gx_pused (st_ctx lsK)) in *.
  apply implA_from_evt.
  do 2 zstep.
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_CTX_get_leaves lsK GPK1 GPK2)|].
    eapply (BN_CTX_get_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OWK) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc); [| | | reflexivity | exact EC | reflexivity].
    - eapply cenv_preA; [exact ENVK | exact LSK | unfold BN_CTX_GET_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - UKD; unfold BN_DIV_FT_COST, MC in *; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENVK).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_get2 CTX). }
  cbv beta. intros [tmp ls3] Σ3 ms3 [PO LEAF3].
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENVK))].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & OW3 & PL3 & -> & CP3 & (EPL3 & _ & (atmp & HAtmp & ->) & _)).
  subst PL3. specialize (CP3 eq_refl).
  destruct (cenv_postA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ENVK CP3) as (ENV3 & LS3).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP3) as RS3.
  rewrite (ret_pc_even 0x234bfc) by lia. unfold MallocRep.wz.
  clear CP3 GPK1 GPK2.

  apply implA_from_evt.
  do 3 zstep.

  pose proof (lib_state_h_parts _ _ _ _ _ _ LS3) as (WFS3 & _).
  destruct (st_wf_get_pre ls3 WFS3) as (GP31 & GP32 & _).
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_CTX_get_leaves ls3 GP31 GP32)|].
    eapply (BN_CTX_get_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW3) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc); [| | | reflexivity | exact EC | reflexivity].
    - eapply cenv_preA; [exact ENV3 | exact LS3 | unfold BN_CTX_GET_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - UKD; unfold BN_DIV_FT_COST, MC in *; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV3).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_get3 CTX). }
  cbv beta. intros [snum ls4] Σ4 ms4 [PO LEAF4].
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENV3))].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F4 & fc4 & m4 & OW4 & PL4 & -> & CP4 & (EPL4 & _ & (asnum & HAsnum & ->) & _)).
  subst PL4. specialize (CP4 eq_refl).
  lazymatch type of ENV3 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
    assert (E4 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (u + MC) Σ4 ls4 m4 OW4 /\ lib_state ls4 m4 OW4 PL EA)
      by (eapply cenv_postA; [exact ENV3 | exact CP4]) end.
  destruct E4 as (ENV4 & LS4).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP4) as RS4.
  rewrite (ret_pc_even 0x234c08) by lia. unfold MallocRep.wz.
  clear CP4 GP31 GP32.

  env_openA ENV4. apply implA_from_evt.
  step. do 2 zstep.
  env_closeA HWLs WOKs ENV4 LS4 ENV4' LS4'.

  pose proof (lib_state_h_parts _ _ _ _ _ _ LS4') as (WFS4 & _).
  destruct (st_wf_get_pre ls4 WFS4) as (GP41 & GP42 & _).
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_CTX_get_leaves ls4 GP41 GP42)|].
    eapply (BN_CTX_get_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW4) (LB := LB) (PL := PL) (EA := EA) (ac := ac) (qc := qc); [| | | reflexivity | exact EC | reflexivity].
    - eapply cenv_preA; [exact ENV4' | exact LS4' | unfold BN_CTX_GET_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - UKD; unfold BN_DIV_FT_COST, MC in *; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV4').
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_get4 CTX). }
  cbv beta. intros [sdiv ls5] Σ5 ms5 [PO LEAF5].
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENV4'))].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F5 & fc5 & m5 & OW5 & PL5 & -> & CP5 & (EPL5 & _ & (asdiv & HAsdiv & ->) & _)).
  subst PL5. specialize (CP5 eq_refl).
  lazymatch type of ENV4' with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
    assert (E5 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (u + MC) Σ5 ls5 m5 OW5 /\ lib_state ls5 m5 OW5 PL EA)
      by (eapply cenv_postA; [exact ENV4' | exact CP5]) end.
  destruct E5 as (ENV5 & LS5).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP5) as RS5.
  rewrite (ret_pc_even 0x234c14) by lia. unfold MallocRep.wz.
  clear CP5 GP41 GP42.

  destruct LEAF3 as (L3a & L3b & _ & L3d & _). destruct LEAF4 as (L4a & L4b & _ & L4d & _). destruct LEAF5 as (L5a & L5b & _ & L5d & _).
  cbn [fst snd] in *. fold p in L3a, L3b, L3d.
  rewrite L3b in L4a, L4d. rewrite L4b, L3b in L5a, L5d.
  assert (LOWget : forall r, (r < NFIX + p)%nat -> getbn r ls5 = getbn r lsK).
  { intros r Hr. rewrite L5d by (unfold RPool; clear - Hr; lia). rewrite L4d by (unfold RPool; clear - Hr; lia). apply L3d. unfold RPool. clear - Hr. lia. }
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS5 (ref_at_stable _ _ _ _ _ _ _ RS4 (ref_at_stable _ _ _ _ _ _ _ RS3 HAresK))) as HAdv5.
  pose proof (oref_at_stable _ _ _ _ _ _ _ RS5 (oref_at_stable _ _ _ _ _ _ _ RS4 (oref_at_stable _ _ _ _ _ _ _ RS3 HArmK))) as HArm5.
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS5 (ref_at_stable _ _ _ _ _ _ _ RS4 (ref_at_stable _ _ _ _ _ _ _ RS3 HAnumK))) as HAnum5.
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS5 (ref_at_stable _ _ _ _ _ _ _ RS4 (ref_at_stable _ _ _ _ _ _ _ RS3 HAdvsK))) as HAdvs5.
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS5 (ref_at_stable _ _ _ _ _ _ _ RS4 HAtmp)) as HAtmp5. pose proof (ref_at_stable _ _ _ _ _ _ _ RS5 HAsnum) as HAsnum5.
  assert (NEts : tmp <> snum) by (rewrite L3a, L4a; unfold RPool; clear; lia).
  assert (NEtd : tmp <> sdiv) by (rewrite L3a, L5a; unfold RPool; clear; lia).
  assert (NEsd : snum <> sdiv) by (rewrite L4a, L5a; unfold RPool; clear; lia).
  assert (NEvt : res <> tmp) by (rewrite L3a; unfold RPool; clear - LTres; lia).
  assert (NEvs : res <> snum) by (rewrite L4a; unfold RPool; clear - LTres; lia).
  assert (NEvd : res <> sdiv) by (rewrite L5a; unfold RPool; clear - LTres; lia).
  assert (NEnt : num <> tmp) by (rewrite L3a; unfold RPool; clear - LTnum; lia).
  assert (NEns : num <> snum) by (rewrite L4a; unfold RPool; clear - LTnum; lia).
  assert (NEnd : num <> sdiv) by (rewrite L5a; unfold RPool; clear - LTnum; lia).
  assert (NEdt : dvs <> tmp) by (rewrite L3a; unfold RPool; clear - LTdvs; lia).
  assert (NEds : dvs <> snum) by (rewrite L4a; unfold RPool; clear - LTdvs; lia).
  assert (NEdd : dvs <> sdiv) by (rewrite L5a; unfold RPool; clear - LTdvs; lia).
  assert (HPt : hpl PL tmp) by (rewrite L3a; apply hpl_pool).
  assert (HPs : hpl PL snum) by (rewrite L4a; apply hpl_pool).
  assert (HPd : hpl PL sdiv) by (rewrite L5a; apply hpl_pool).
  pose proof (proj1 HPt : not_one tmp) as NROt. pose proof (proj1 HPs : not_one snum) as NROs. pose proof (proj1 HPd : not_one sdiv) as NROsd.
  assert (HTOPD5 : (1 <= bn_top (getbn dvs ls5))%nat) by (rewrite (LOWget dvs LTdvs); exact HTOPD).
  assert (HTOPNZ5 : nth (bn_top (getbn dvs ls5) - 1) (bn_buf (getbn dvs ls5)) 0 <> 0) by (rewrite (LOWget dvs LTdvs); exact HTOPNZ).
  clear L3a L3b L3d L4a L4b L4d L5a L5b L5d RS3 RS4 RS5 HAtmp HAsnum ENV3 LS3 ENV4 LS4 ENV4' LS4' WFSK WFS3 WFS4.
  clear HAresK HArmK HAnumK HAdvsK ENVK LSK LOWget HTOPD HTOPNZ LTres LTnum LTdvs p.

  repeat match goal with H : _ <> _ |- _ => apply hide_intro in H end.

  pose proof (lib_state_h_parts _ _ _ _ _ _ LS5) as PARTS5; pose proof PARTS5 as (WFS5 & PWF5 & IDS5 & PLB5 & ERRB5).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENV5)) PARTS5 NOFR HAsdiv NROsd) as (qd & Ad & nd & Hind & Rd1 & Rd2).
  pose proof (AH_range_in _ _ _ _ _ _ _ (proj1 (proj2 ENV5)) Hind) as (DA0 & _ & _ & DAC & _).
  env_openA ENV5. apply implA_from_evt.
  step.
  zstep. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. unfold BnHeapA.ACEIL in *. lia. }
  clear KD qd Ad nd Hind Rd1 Rd2 DA0 DAC.
  step. do 2 zstep.
  env_closeA HWLs WOKs ENV5 LS5 ENV5' LS5'.
  clear LS5. rename LS5' into LS5.

  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS5 HAsdiv) as HVsd5. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS5 HAdvs5) as HVdvs5.
  pose proof (st_wf_ok sdiv ls5 WFS5 HVsd5 NROsd) as (_ & OKsd2 & _). pose proof (st_wf_ok dvs ls5 WFS5 HVdvs5 NROd) as (OKdv1 & OKdv2 & OKdv3 & _).
  apply evt_done. unfold div_core. unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply implA_leaves; [apply (BN_copy_leaves sdiv dvs ls5 (not_eq_sym (hide_elim _ NEdd)) HVsd5 OKsd2 OKdv2)|].
    eapply (BN_copy_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW5) (LB := LB) (PL := PL) (EA := EA) (rx := sdiv) (ry := dvs) (ax := asdiv) (ay := advs);
      [| | | reflexivity | exact HAsdiv | exact HAdvs5 | exact (hpl_wref PL sdiv HPd) | exact NROd | reflexivity | reflexivity].
    - eapply cenv_preA; [exact ENV5' | exact LS5 | unfold BN_COPY_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - UKD; unfold BN_DIV_FT_COST, MC in *; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV5').
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_copy CTX). }
  cbv beta. intros [u6 ls6] Σ6 ms6 [PO LEAF6].
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENV5'))].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F6 & fc6 & m6 & OW6 & PL6 & -> & CP6 & (EPL6 & -> & _)).
  subst PL6. specialize (CP6 eq_refl).
  lazymatch type of ENV5' with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
    assert (E6 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (u + MC) Σ6 ls6 m6 OW6 /\ lib_state ls6 m6 OW6 PL EA)
      by (eapply cenv_postA; [exact ENV5' | exact CP6]) end.
  destruct E6 as (ENV6 & LS6).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP6) as RS6.
  rewrite (ret_pc_even 0x234c28) by lia. unfold MallocRep.wz.
  clear CP6.

  destruct LEAF6 as (C6a & C6b & C6c & C6d & C6e & _). cbn [snd] in *.
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS6 HAdv5) as HAdv6. pose proof (oref_at_stable _ _ _ _ _ _ _ RS6 HArm5) as HArm6. pose proof (ref_at_stable _ _ _ _ _ _ _ RS6 HAnum5) as HAnum6. pose proof (ref_at_stable _ _ _ _ _ _ _ RS6 HAdvs5) as HAdvs6.
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS6 HAtmp5) as HAtmp6. pose proof (ref_at_stable _ _ _ _ _ _ _ RS6 HAsnum5) as HAsnum6. pose proof (ref_at_stable _ _ _ _ _ _ _ RS6 HAsdiv) as HAsdiv6.
  set (bd := getbn dvs ls5) in *. set (dn := bn_top bd) in *.
  clear RS6 HAdv5 HArm5 HAnum5 HAdvs5 HAtmp5 HAsnum5 HAsdiv ENV5 ENV5' LS5 PARTS5 WFS5 IDS5 PLB5 ERRB5 HVsd5 HVdvs5 OKsd2 C6a.
  rename PWF5 into PWF.
  pose proof (AH_nodup_l _ _ _ _ (proj1 (proj2 ENV6))) as ND6.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS6) as PARTS6; pose proof PARTS6 as (WFS6 & PWF6 & IDS6 & PLB6 & ERRB6).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS6 HAsdiv6) as HVsd6.
  destruct (lib_state_open [] ls6 m6 OW6 PL EA sdiv asdiv LS6 ND6 HAsdiv6 ltac:(intros []) NROsd) as ((Dsd & BNsd & ARRsd) & (OKs1 & OKs2 & OKs3 & OKs4) & LSH6).
  set (b6 := getbn sdiv ls6) in *.
  destruct (bn_arr_facts_w ls6 OW6 PL EA (bv_unsigned sp) USTACK_TOP Σ6 LB m6 sdiv Dsd (proj1 (proj2 ENV6)) PARTS6 FROK HVsd6 (hpl_wref PL sdiv HPd) ARRsd) as (Usd & LENsd & Dsd0 & DsdC & DsdI & DSEPsd).
  fold b6 in Usd, LENsd, DsdC, DsdI, DSEPsd.
  pose proof (DSEPsd sdiv asdiv HAsdiv6) as SEPsd. clear DSEPsd.
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENV6)) PARTS6 NOFR HAsdiv6 NROsd) as (qsd & Asd & nsd & Hinsd & Rsd1 & Rsd2).
  pose proof (AH_range_in _ _ _ _ _ _ _ (proj1 (proj2 ENV6)) Hinsd) as (SDA0 & _ & _ & SDAC & SDAI).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENV6)) LS6 NOFR HAsdiv6 NROsd) as (ACVA & ALVA & OFVA).
  destruct (arr_shA _ _ _ _ _ _ (proj1 (proj2 ENV6)) (bn_arr_nofr PL sdiv _ _ _ _ PWF NOFR NROsd ARRsd ltac:(solve_nbuf))) as (ACV & ALV & OFV). fold b6 in ACV, OFV.
  assert (HDsd : exists psd, bn_d b6 = Some psd /\ In (psd, Dsd, 8 * Z.of_nat (bn_dmax b6)) OW6).
  { destruct (bn_d b6) as [psd|] eqn:Edsd0; [exists psd; split; [reflexivity|]; unfold bn_arr in ARRsd; rewrite Edsd0 in ARRsd; exact (proj1 ARRsd)|].
    exfalso. destruct (bn_arr_null PL sdiv m6 OW6 Dsd b6 PWF (hpl_wref PL sdiv HPd) Edsd0 ARRsd) as [_ E]. unfold bn_dmax in C6e. rewrite E in C6e. cbn in C6e. fold dn in C6e. clear - C6e HTOPD5. lia. }
  destruct HDsd as (psd & Edsd & Hinpsd).
  pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENV6)) Hinpsd) as (PSD0 & PSD16 & _ & _ & _).
  unfold bn_cells in BNsd. rewrite C6b, C6c in BNsd. fold dn in BNsd. unfold BG_DMAX in OKs3, OKdv3.
  assert (ASD : 0 < asdiv /\ asdiv + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - SDA0 Rsd1 Rsd2 SDAC CEIL LO SPR SPT; lia).
  assert (BDSD : 0 <= Dsd /\ Dsd + 8 * Z.of_nat (bn_dmax b6) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dsd0 DsdC CEIL LO SPR SPT; lia).
  assert (DN1 : (1 <= dn <= bn_dmax b6)%nat) by (unfold bn_dmax in *; clear - HTOPD5 OKs2 C6b; subst dn; lia).
  env_openA ENV6.
  match goal with MUx : munch _ m6 m6 |- _ => clear MUx end. match goal with WMx : wmono _ m6 m6 |- _ => clear WMx end.
  pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]%Z m6) as MU6.
  pose proof (wmono_refl bgbsegs m6) as WM6.
  assert (OFF6 : offshW [(bv_unsigned sp - 320, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFVA OFV C2 CEIL LO. lia. }
  apply hide_intro in OFVA. apply hide_intro in OFV. apply hide_intro in SDAI. apply hide_intro in DsdI. apply hide_intro in SEPsd.
  unfold MallocRep.wz in *. apply implA_from_evt.
  zstep. if_cases KD; zify_cond KD. { exfalso. rewrite ?unsigned_lit in KD by lia. clear - KD ASD. lia. }
  clear KD.
  step.
  hide_ors. ub. unhide.
  do 2 zstep.
  step.
  shl_with ACVA ALVA. chk0.
  do 3 zstep.
  shl_with ACVA ALVA.
  step.
  chk0.
  step. rewrite (sx32_small (Z.of_nat dn)) by lia.
  zstep. rewrite (bk_swrap32_small (Z.of_nat dn + -1)) by lia.
  hide_ors. ub. unhide.
  do 2 zstep.
  replace ((Z.of_nat dn + -1) ≪ 3) with (8 * Z.of_nat dn - 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).

  hide_ors. ub. zstep. ub. zstep. ub. unhide.

  set (dtop := nth (dn - 1) (bn_buf bd) 0) in *.
  assert (Edtop : nth (dn - 1) (bn_buf b6) 0 = dtop).
  { unfold dtop. rewrite <- (firstn_skipn dn (bn_buf b6)), <- (firstn_skipn dn (bn_buf bd)), C6d.
    rewrite !app_nth1 by (rewrite length_firstn; unfold bn_dmax in *; lia). reflexivity. }
  assert (Rdtop : 0 < dtop < 18446744073709551616).
  { assert (L : limb dtop) by (apply limbs_nth; exact OKdv1). unfold limb in L. rewrite BW_lit in L. pose proof (hide_elim _ HTOPNZ5) as NZ. fold bd in NZ. fold dn in NZ. fold dtop in NZ. clear - L NZ. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    destruct (proj1 (limbarr_limbs_at bgbsegs mx Dsd (bn_buf b6)) Usd) as (LAsd & WRsd) end.
  assert (Ntop : nth_error (bn_buf b6) (dn - 1) = Some dtop) by (rewrite <- Edtop; apply nth_error_nth'; unfold bn_dmax in *; lia).
  do 2 zstep.
  shl_with ACV ALV. chk0.
  let ad := cur_mem_addr in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (limbs_at_read_nth bgbsegs mx Dsd (bn_buf b6) (dn - 1) dtop ad LAsd Ntop ltac:(unfold wa; f_equal; lia)) as RD end.
  zstep. clear RD.
  zstep.
  assert (Edt : bv_unsigned (Z_to_bv 64 dtop) = dtop) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
  eapply evt_cut.
  { match goal with STx : stk _ m7 _ _, MIx : mem_inv _ m7 |- _ =>
      eapply BN_num_bits_word_aspec with (lo := lo) (m := m7); [rewrite ESP; exact STx | rewrite ESP; lia | exact MIx] end. }
  intros ms' PO. unfold nbw_post in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & E & MUc & WMc & MIc & STc).
  subst ms'. rewrite ESP, Edt in *.
  rewrite (ret_pc_even 0x234cbc) by lia.
  assert (LAsd8 : limbs_at bgbsegs m8 Dsd (bn_buf b6)).
  { eapply limbs_at_transport; [exact LAsd | exact MUc |]. cbn [disjoint_from]. fold (bn_dmax b6). split; [|exact I]. unfold BnHeapA.ACEIL in *. lia. }
  clear LAsd WRsd.
  match goal with STx : stk _ m7 _ _ |- _ => clear STx end.
  transport_after_call bgbsegs m7 m8 MUc WMc.
  clear MUc WMc. match goal with MIx : mem_inv _ m7 |- _ => clear MIx end. try clear m7.

  set (nb := num_bits_word dtop) in *.
  assert (NB : 1 <= nb <= 64).
  { destruct (num_bits_word_spec dtop ltac:(lia)) as (B1 & _). pose proof (num_bits_word_le dtop 64 ltac:(lia) ltac:(change (2 ^ 64) with 18446744073709551616; lia)). fold nb in B1, H. lia. }
  set (af := firstn dn (bn_buf b6)).
  assert (Laf : length af = dn) by (unfold af; apply firstn_length_le; unfold bn_dmax in *; lia).
  assert (LAaf : limbs_at bgbsegs m8 Dsd af).
  { rewrite <- (firstn_skipn dn (bn_buf b6)) in LAsd8. apply limbs_at_app in LAsd8. exact (proj1 LAsd8). }
  assert (LArest : limbs_at bgbsegs m8 (Dsd + 8 * Z.of_nat dn) (skipn dn (bn_buf b6))).
  { rewrite <- (firstn_skipn dn (bn_buf b6)) in LAsd8. apply limbs_at_app in LAsd8. destruct LAsd8 as [_ X]. fold af in X. rewrite Laf in X. exact X. }
  destruct (proj1 (limbarr_limbs_at bgbsegs m8 Dsd (bn_buf b6)) Usd) as (_ & WRsd8).
  replace (Z_to_bv 64 (Z.of_nat dn)) with (Z_to_bv 64 (Z.of_nat (length af))) by (rewrite Laf; reflexivity).
  pose proof (acc_munch bgbsegs _ m6 m8 _ _ ACV MU6 OFF6 ltac:(clear - BDSD; lia) ltac:(clear - BDSD; lia)) as ACV8.
  lazymatch goal with FRx : rw_cells _ m8 (bv_unsigned sp + -304) ?fr |- _ =>
    eapply la_blockA with (m := m8) (D := Dsd) (SP := bv_unsigned sp) (lo := lo) (a := af) (lb := 64 - nb) (FS := 304) (FB := bv_unsigned sp + -304) (FCELLS := fr) (nb := nb);
    [ reflexivity
    | clear; lia
    | clear - NB; lia
    | rewrite Laf; left; unfold BnHeapA.ACEIL in *; unfold bn_dmax in *; clear - DsdC CEIL LO OKs2 C6b; lia
    | rewrite Laf; eapply acc_sub; [exact ACV8 | clear; lia | unfold bn_dmax in *; clear - OKs2 C6b; lia]
    | exact ALV
    | rewrite Laf; cbn [offshW]; cbn [offshW] in OFF6; unfold bn_dmax in *; clear - OFF6 OKs2 C6b Dsd0; lia
    | exact NB
    | reflexivity
    | rewrite Laf; lia
    | unfold af; apply limbs_firstn; exact OKs1
    | exact LAaf
    | rewrite Laf; apply (wr_at_sub bgbsegs m8 Dsd (8 * Z.of_nat (length (bn_buf b6))) 0 (8 * Z.of_nat dn)) in WRsd8; [rewrite Z.add_0_r in WRsd8; exact WRsd8 | lia | lia | unfold bn_dmax in *; lia]
    | exact FRx
    | exact STc
    | exact MIc
    | ]
  end.
  intros m9 w5 w6 w10 w11 w13 w14 w15 w16 w17 w22 HRES FR9 ST9 MI9 MU9 WM9. rewrite Laf in MU9.
  set (sh := 64 - nb) in *.
  set (resl := fst (lshift_limbs af sh 0)) in *.
  assert (Lres : length resl = dn) by (unfold resl; rewrite lshift_limbs_len; exact Laf).
  assert (DJ9 : forall A k, (A + k <= Dsd \/ Dsd + 8 * Z.of_nat (bn_dmax b6) <= A) -> A + k <= bv_unsigned sp - 304 ->
            disjoint_from [(Dsd, Dsd + 8 * Z.of_nat dn); (bv_unsigned sp - 304, bv_unsigned sp)] A k).
  { intros A k H1 H2. cbn [disjoint_from]. unfold bn_dmax in *. lia. }
  try apply hide_elim in SEPsd.
  eapply (rw_cells_transport bgbsegs _ m8 m9) in BNsd; [| exact MU9 | exact WM9 | apply DJ9; cbn; unfold BnHeapA.ACEIL in *; lia].
  assert (LArest9 : limbs_at bgbsegs m9 (Dsd + 8 * Z.of_nat dn) (skipn dn (bn_buf b6))).
  { eapply limbs_at_transport; [exact LArest | exact MU9 |]. cbn [disjoint_from]. rewrite length_skipn. unfold bn_dmax in *. lia. }
  set (nbuf := splice (bn_buf b6) 0 resl).
  assert (Lnbuf : length nbuf = bn_dmax b6) by (unfold nbuf, bn_dmax in *; rewrite splice_length by lia; reflexivity).
  assert (U9 : u64arr bgbsegs m9 Dsd (wlimbs nbuf)).
  { apply limbarr_limbs_at. split.
    - unfold nbuf, splice. change (firstn 0 (bn_buf b6)) with (@nil Z). change (0 + length resl)%nat with (length resl).
      change ([] ++ resl ++ skipn (length resl) (bn_buf b6)) with (resl ++ skipn (length resl) (bn_buf b6)).
      apply limbs_at_app. split; [exact HRES|]. rewrite Lres. exact LArest9.
    - rewrite Lnbuf. eapply wr_at_transport; [exact WRsd8 | exact WM9]. }
  assert (MU6' : munch [(bv_unsigned sp - 320, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]%Z m6 m9).
  { eapply munch_trans; [exact MU6|]. eapply munch_weaken; [|exact MU9]. unfold sub_fp. intros xx Hxx. cbn [outside] in *. unfold bn_dmax in *. lia. }
  assert (WM6' : wmono bgbsegs m6 m9) by (eapply wmono_trans; eauto).
  assert (LENnb : Z.of_nat (length (wlimbs nbuf)) = Z.of_nat (bn_dmax b6)) by (rewrite wlimbs_len, Lnbuf; reflexivity).
  clear MU6 MU9 WM9 Usd LENsd LAsd8 LAaf LArest LArest9 HRES WRsd8 DJ9 STc MIc ACV8.

  do 3 zstep.
  shl_with ACVA ALVA. chk0.
  zstep.
  step. step.
  step.
  step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m10 end.
  apply evt_done. unfold bbind at 1. cbn [bind tree_ops]. rewrite la_run. cbn [tbind fst snd]. rewrite bbind_get_set.
  fold b6. rewrite C6b. fold dn. rewrite Edtop. fold nb. fold sh. fold af. fold resl. fold nbuf.
  rewrite (getbn_setbn_same sdiv _ ls6 HVsd6), setbn_setbn_same.
  set (sd3 := bn_with_neg (bn_with_buf b6 nbuf) false).
  unfold bbind at 1. cbn [bind tree_ops].
  assert (HWL6 : Forall (w_lib ls6 OW6 PL lo (bv_unsigned sp)) [(bv_unsigned sp - 320, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]).
  { constructor; [left; cbn; lia|]. constructor; [w_lib_ref HAsdiv6 NROsd|].
    constructor; [right; left; exists (psd, Dsd, 8 * Z.of_nat (bn_dmax b6)); cbn; split; [exact Hinpsd| lia]| constructor]. }
  assert (WOK6 : Forall (w_ok OW6 LB ls6 PL EA (bv_unsigned sp) [sdiv]) [(bv_unsigned sp - 320, bv_unsigned sp); (asdiv, asdiv + 24); (Dsd, Dsd + 8 * Z.of_nat (bn_dmax b6))]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [eapply (w_struct OW6 LB ls6 PL EA (bv_unsigned sp) false [sdiv] _ sdiv asdiv); [left; reflexivity| exact HAsdiv6| exact NROsd| cbn; clear; lia| cbn; clear; lia]|].
    constructor; [eapply (w_limbs OW6 LB ls6 PL EA (bv_unsigned sp) false [sdiv] _ sdiv psd Dsd); [left; reflexivity| exact HVsd6| exact Edsd| exact Hinpsd| cbn [fst snd]; fold b6; lia| cbn [fst snd]; fold b6; lia]| constructor]. }
  pose proof (left_align_value af ltac:(unfold af; apply limbs_firstn; exact OKs1) ltac:(rewrite Laf; lia)) as LAV.
  rewrite Laf in LAV.
  assert (Eaft : nth (dn - 1) af 0 = dtop) by (unfold af; rewrite nth_firstn; destruct (Nat.ltb_spec (dn - 1) dn); [exact Edtop | lia]).
  rewrite Eaft in LAV. specialize (LAV ltac:(lia)). cbv zeta in LAV. fold nb in LAV. fold sh in LAV. fold resl in LAV.
  destruct LAV as (SH & LRES & _ & VRES & D0N).
  match goal with HEAPx : @BnHeapA.AHEAP _ Σ6 OW6 LB _, STx : stk _ m10 _ _, MIx : mem_inv _ m10, FRx : rw_cells _ m10 (bv_unsigned sp + -304) _ |- _ =>
    rename HEAPx into HEAP6; rename STx into ST10; rename MIx into MI10; rename FRx into FR10 end.
  assert (LS7 : lib_state (setbn sdiv sd3 ls6) m10 OW6 PL EA).
  { unfold lib_state. eapply (lib_state_close [] ls6 m10 OW6 PL EA sdiv asdiv); [| exact ND6| exact HAsdiv6| exact NROsd| | |].
    - exact (lib_state_frame Σ6 LB (bv_unsigned sp) USTACK_TOP [sdiv] ls6 _ _ OW6 PL EA _ HEAP6 LSH6 MU6' WM6' FROK WOK6).
    - exists Dsd. split.
      + unfold bn_cells, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_top bn_buf bn_neg bn_flags Z.b2z]. rewrite Lnbuf, C6b. fold dn. exact BNsd.
      + unfold bn_arr, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_d bn_buf]. rewrite Edsd, Lnbuf. split; [exact Hinpsd| exact U9].
    - unfold bg_ok, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_buf bn_top bn_flags]. rewrite Lnbuf. unfold BG_DMAX.
      split; [unfold nbuf; apply splice_limbs; [exact OKs1| exact LRES]|]. split; [exact OKs2|]. split; [lia| exact OKs4].
    - apply ids_ok_setbn_same; [exact IDS6| exact HVsd6|]. unfold bn_blocks, sd3, bn_dmax. cbn [bn_with_neg bn_with_buf bn_d bn_buf]. rewrite Lnbuf. reflexivity. }
  lazymatch type of ENV6 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?u _ _ _ _ =>
    lazymatch type of FR10 with rw_cells _ _ _ ?fr' =>
      let pre' := drop2 fr' in
      assert (ENV7 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre' u Σ6 (setbn sdiv sd3 ls6) m10 OW6);
      [ apply cenv_setbnA; [| exact HVsd6 | fold b6; unfold bn_blocks, sd3; cbn [bn_with_neg bn_with_buf bn_d bn_buf bn_dmax bn_top]; rewrite ?Edsd; reflexivity];
        eapply (cenv_silentA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m);
          [exact ENV6 | exact LS6 | exact MU6' | exact WM6' | exact HWL6 | exact ST10 | exact MI10 | cbn [app]; exact FR10 | cbn; lia]
      | ] end end.
  set (ls7 := setbn sdiv sd3 ls6) in *.
  assert (HAsnum7 : ref_at ls7 OW6 PL snum asnum) by (apply ref_at_setbn; exact HAsnum6).
  assert (HAnum7 : ref_at ls7 OW6 PL num anum) by (apply ref_at_setbn; exact HAnum6).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS7) as (WFS7 & _).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS7 HAsnum7) as HVsn7. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS7 HAnum7) as HVnum7.
  pose proof (st_wf_ok snum ls7 WFS7 HVsn7 NROs) as (_ & OKsn2 & _). pose proof (st_wf_ok num ls7 WFS7 HVnum7 NROn) as (OKn1 & OKn2 & OKn3 & _).
  eapply implA_bind.
  { eapply implA_leaves; [apply (bn_lshift_leaves snum num sh ls7 (not_eq_sym (hide_elim _ NEns)) SH HVsn7 OKsn2 OKn2)|].
    eapply (bn_lshift_fixed_top_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW6) (LB := LB) (PL := PL) (EA := EA) (rr := snum) (rx := num) (ar := asnum) (ax := anum) (n := sh);
      [| | | reflexivity | exact HAsnum7 | exact HPs | exact HAnum7 | exact NROn | solve_nbuf | reflexivity | reflexivity | reflexivity | clear - SH; lia].
    - eapply cenv_preA; [exact ENV7 | exact LS7 | unfold BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - UKD; unfold BN_DIV_FT_COST, MC in *; lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV7).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_lshift CTX). }
  cbv beta. intros [u8 ls8] Σ8 ms8 [PO LEAF8].
  apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENV7))].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F8 & fc8 & m11 & OW8 & PL8 & -> & CP8 & (EPL8 & -> & _)).
  subst PL8. specialize (CP8 eq_refl).
  lazymatch type of ENV7 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
    assert (E8 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (u + MC) Σ8 ls8 m11 OW8 /\ lib_state ls8 m11 OW8 PL EA)
      by (eapply cenv_postA; [exact ENV7 | exact CP8]) end.
  destruct E8 as (ENV8 & LS8).
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP8) as RS8.
  rewrite (ret_pc_even 0x234d74) by lia. unfold MallocRep.wz.
  clear CP8.

  destruct LEAF8 as (L8a & L8b & L8c & L8d & L8e & _). cbn [snd] in *.
  set (bnum := getbn num ls7) in *. set (tn := bn_top bnum) in *.
  assert (Esd8 : getbn sdiv ls8 = sd3) by (rewrite L8a by exact NEsd; unfold ls7; apply getbn_setbn_same; exact HVsd6).
  assert (Etmp8 : getbn tmp ls8 = getbn tmp ls6) by (rewrite L8a by (apply not_eq_sym; exact NEts); unfold ls7; apply getbn_setbn_other; apply not_eq_sym; exact NEtd).
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS8 (proj2 (ref_at_setbn ls6 OW6 PL sdiv sd3 _ _) HAdv6)) as HAdv8. pose proof (oref_at_stable _ _ _ _ _ _ _ RS8 (oref_at_setbn ls6 OW6 PL sdiv sd3 _ _ HArm6)) as HArm8.
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS8 HAnum7) as HAnum8. pose proof (ref_at_stable _ _ _ _ _ _ _ RS8 (proj2 (ref_at_setbn ls6 OW6 PL sdiv sd3 _ _) HAdvs6)) as HAdvs8.
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS8 (proj2 (ref_at_setbn ls6 OW6 PL sdiv sd3 _ _) HAtmp6)) as HAtmp8. pose proof (ref_at_stable _ _ _ _ _ _ _ RS8 HAsnum7) as HAsnum8.
  pose proof (ref_at_stable _ _ _ _ _ _ _ RS8 (proj2 (ref_at_setbn ls6 OW6 PL sdiv sd3 _ _) HAsdiv6)) as HAsdiv8.
  clear RS8 HAdv6 HArm6 HAnum6 HAdvs6 HAtmp6 HAsnum6 HAsdiv6 HAsnum7 HAnum7 ENV6 LS6 ENV7 LS7 LSH6 HWL6 WOK6 MU6' WM6' U9 BNsd HVsn7 HVnum7 OKsn2 IDS6 ERRB6 ND6 Hinsd Hinpsd SEPsd DsdI DsdC Dsd0 SDA0 SDAC SDAI Rsd1 Rsd2 ARRsd LENnb HEAP6 ST10 MI10 FR10 ACVA ALVA OFVA ACV ALV OFV OFF6 ASD BDSD PSD0 PSD16.

  pose proof (AH_nodup_l _ _ _ _ (proj1 (proj2 ENV8))) as ND8.
  destruct (lib_state_open [] ls8 m11 OW8 PL EA sdiv asdiv LS8 ND8 HAsdiv8 ltac:(intros []) NROsd) as ((Dsd8 & BNsd8 & _) & _ & _).
  destruct (lib_state_open [] ls8 m11 OW8 PL EA snum asnum LS8 ND8 HAsnum8 ltac:(intros []) NROs) as ((Dsn8 & BNsn8 & _) & (OKsn1 & OKsn2 & OKsn3 & OKsn4) & _).
  rewrite Esd8 in BNsd8. unfold bn_cells in BNsd8, BNsn8. unfold sd3 in BNsd8. cbn [bn_with_neg bn_with_buf bn_top bn_dmax bn_buf bn_neg bn_flags] in BNsd8.
  rewrite C6b in BNsd8. rewrite L8b in BNsn8. unfold BG_DMAX in OKsn3, OKn3.
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENV8)) LS8 NOFR HAsdiv8 NROsd) as (ACVA & ALVA & OFVA).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENV8)) LS8 NOFR HAsnum8 NROs) as (ACSA & ALSA & OFSA).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENV8)) (lib_state_h_parts _ _ _ _ _ _ LS8) NOFR HAsnum8 NROs) as (qs8 & As8 & ns8 & Hins8 & Rs81 & Rs82).
  pose proof (AH_range_in _ _ _ _ _ _ _ (proj1 (proj2 ENV8)) Hins8) as (SA80 & _ & _ & SAC8 & _).
  assert (ASN : 0 < asnum /\ asnum + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - SA80 Rs81 Rs82 SAC8 CEIL LO SPR SPT; lia).
  destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENV8)) (lib_state_h_parts _ _ _ _ _ _ LS8) NOFR HAsdiv8 NROsd) as (qd8 & Ad8 & nd8 & Hind8 & Rd81 & Rd82).
  pose proof (AH_range_in _ _ _ _ _ _ _ (proj1 (proj2 ENV8)) Hind8) as (SD80 & _ & _ & SDC8 & _).
  assert (ASD : 0 < asdiv /\ asdiv + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - SD80 Rd81 Rd82 SDC8 CEIL LO SPR SPT; lia).
  env_openA ENV8.
  assert (OFF8 : offshW [(bv_unsigned sp + -304, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; clear - C2 CEIL LO; lia).
  apply hide_intro in OFVA. apply hide_intro in OFSA.
  unfold MallocRep.wz in *. apply implA_from_evt.
  zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ. lia. }
  clear KZ.
  step.
  shl_with ACVA ALVA. chk0.
  hide_ors. ub. unhide.
  step.
  do 3 zstep.
  step.
  shl_with ACSA ALSA.
  step. rewrite (zx32_small (Z.of_nat dn)) by (unfold bn_dmax in *; lia).
  chk0.
  step.
  step. rewrite (sx32_small (Z.of_nat (tn + 1))) by (unfold bn_dmax in *; lia).
  zstep. rewrite Z.add_0_r, (bk_swrap32_small (Z.of_nat dn)) by (unfold bn_dmax in *; lia).
  do 2 zstep.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m12 end.
  env_closeA HWLs WOKs ENV8 LS8 ENV9 LS9.
  clear LS8. rename LS9 into LS8.
  apply evt_done. rewrite !bbind_get. rewrite Esd8. change (bn_top sd3) with (bn_top b6). rewrite C6b, L8b.
  lazymatch type of ENV9 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?FR8 ?used8 _ _ _ _ =>
   lazymatch goal with |- implA (bbind _ _ ?REST0 _) _ ?Q _ =>
    assert (CONT : forall ΣP lsP mP OWP (nP : nat) (usedP : Z) (FP : bvmap 5 word) (fcP : bv 32) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
               cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m FR8 usedP ΣP lsP mP OWP -> usedP + 3 * MC <= BN_DIV_FT_COST ->
               lib_state lsP mP OWP PL EA ->
               ref_at lsP OWP PL res ares -> oref_at lsP OWP PL rm arm -> ref_at lsP OWP PL num anum -> ref_at lsP OWP PL dvs advs ->
               ref_at lsP OWP PL tmp atmp -> ref_at lsP OWP PL snum asnum -> ref_at lsP OWP PL sdiv asdiv ->
               getbn sdiv lsP = sd3 ->
               bn_top (getbn snum lsP) = nP -> (dn + 1 <= nP)%nat -> (tn + 1 <= nP)%nat -> (nP <= dn + 1 \/ nP = tn + 1)%nat -> bn_neg (getbn snum lsP) = bn_neg bnum ->
               firstn nP (bn_buf (getbn snum lsP)) = lsh_res bnum sh ++ repeat 0%Z (nP - (tn + 1)) ->
               implA (REST0 tt lsP) ΣP Q
                 (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 (Z.of_nat nP))
                          (Z_to_bv 64 (Z.of_nat dn)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (asnum ≫ 3)) (Z_to_bv 64 advs) (Z_to_bv 64 atmp)
                          (Z_to_bv 64 (Z.of_nat (tn + 1))) x22 (Z_to_bv 64 ares) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat dn)) s10 (Z_to_bv 64 ac) x28 x29 x30 x31)
                     FP (Z_to_bv 64 0x234e6c) fcP None mP (seg_rom bgbsegs)))
   end end.
  { intros ΣP lsP mP OWP nP usedP FP fcP q1 q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q22 q28 q29 q30 q31
           ENVP USEDP LSP HAdvP HArmP HAnumP HAdvsP HAtmpP HAsnumP HAsdivP GSP TNP NP1 NP2 NP3 NEGP FNP.
    clear ENV8 HAdv8 HArm8 HAnum8 HAdvs8 HAtmp8 HAsnum8 HAsdiv8 ND8 BNsd8 BNsn8 Dsd8 Dsn8 OKsn1 OKsn2 OKsn3 OKsn4 L8a L8b L8c L8d L8e Esd8 Etmp8 ENV9 LS8 ACVA ALVA OFVA ACSA ALSA OFSA.
    cbv beta. rewrite bbind_get, TNP.

    pose proof (AH_nodup_l _ _ _ _ (proj1 (proj2 ENVP))) as NDP.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LSP) as PARTSP; pose proof PARTSP as (WFSP & PWFP & IDSP & PLBP & ERRBP).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSP HAsdivP) as HVsdP. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSP HAsnumP) as HVsnP.
    destruct (lib_state_open [] lsP mP OWP PL EA sdiv asdiv LSP NDP HAsdivP ltac:(intros []) NROsd) as ((DsdP & BNsdP & ARRsdP) & _ & _).
    destruct (lib_state_open [] lsP mP OWP PL EA snum asnum LSP NDP HAsnumP ltac:(intros []) NROs) as ((DsnP & BNsnP & ARRsnP) & (OKp1 & OKp2 & OKp3 & OKp4) & _).
    destruct (bn_arr_facts_w lsP OWP PL EA (bv_unsigned sp) USTACK_TOP ΣP LB mP sdiv DsdP (proj1 (proj2 ENVP)) PARTSP FROK HVsdP (hpl_wref PL sdiv HPd) ARRsdP) as (UsdP & _ & DsdP0 & DsdPC & _ & _).
    destruct (bn_arr_facts_w lsP OWP PL EA (bv_unsigned sp) USTACK_TOP ΣP LB mP snum DsnP (proj1 (proj2 ENVP)) PARTSP FROK HVsnP (hpl_wref PL snum HPs) ARRsnP) as (UsnP & LENsn & DsnP0 & DsnPC & _ & SEPsnP).
    destruct (arr_shA _ _ _ _ _ _ (proj1 (proj2 ENVP)) (bn_arr_nofr PL sdiv _ _ _ _ PWF NOFR NROsd ARRsdP ltac:(solve_nbuf))) as (ACV & ALV & OFV).
    destruct (arr_shA _ _ _ _ _ _ (proj1 (proj2 ENVP)) (bn_arr_nofr PL snum _ _ _ _ PWF NOFR NROs ARRsnP ltac:(solve_nbuf))) as (ACS & ALS & OFS).
    rewrite GSP in BNsdP, UsdP, DsdPC, ACV, OFV. unfold bn_cells in BNsdP, BNsnP.
    unfold sd3 in BNsdP, UsdP, DsdPC, ACV, OFV. cbn [bn_with_neg bn_with_buf bn_top bn_dmax bn_buf bn_neg bn_flags] in BNsdP, UsdP, DsdPC, ACV, OFV.
    rewrite C6b in BNsdP. rewrite TNP in BNsnP. unfold BG_DMAX in OKp3.
    unfold bn_dmax in DsdPC, ACV, OFV. cbn [bn_buf] in DsdPC, ACV, OFV. rewrite Lnbuf in DsdPC, ACV, OFV.
    assert (LENnbP : Z.of_nat (length (wlimbs nbuf)) = Z.of_nat (bn_dmax b6)) by (rewrite wlimbs_len, Lnbuf; reflexivity).
    set (d0 := nth (dn - 1) nbuf 0).
    set (d1 := if (dn =? 1)%nat then 0 else nth (dn - 2) nbuf 0).
    assert (Lnb2 : (dn <= length nbuf)%nat) by (rewrite Lnbuf; unfold bn_dmax in *; lia).
    assert (LIMnb : limbs nbuf) by (unfold nbuf; apply splice_limbs; [exact OKs1 | exact LRES]).
    assert (Rd0 : 9223372036854775808 <= d0 < 18446744073709551616).
    { assert (L : limb d0) by (apply limbs_nth; exact LIMnb). unfold limb in L. rewrite BW_lit in L. split; [|lia].
      unfold d0, nbuf, splice. change (firstn 0 (bn_buf b6)) with (@nil Z). cbn [app]. rewrite app_nth1 by lia.
      change (2 ^ 63) with 9223372036854775808 in D0N. exact D0N. }
    assert (Rd1 : 0 <= d1 < 18446744073709551616).
    { unfold d1. destruct (dn =? 1)%nat; [lia|]. assert (L : limb (nth (dn - 2) nbuf 0)) by (apply limbs_nth; exact LIMnb). unfold limb in L. rewrite BW_lit in L. lia. }
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) PARTSP NOFR HAsdivP NROsd) as (qsP & AsP & nsP & HinsP & RsP1 & RsP2).
  pose proof (AH_range_in _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) HinsP) as (SP0 & _ & _ & SPC & SPI).
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) PARTSP NOFR HAsnumP NROs) as (qnP & AnP & nnP & HinnP & RnP1 & RnP2).
  pose proof (AH_range_in _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) HinnP) as (NP0 & _ & _ & NPC & NPI).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) LSP NOFR HAsdivP NROsd) as (ACVA & ALVA & OFVA).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) LSP NOFR HAsnumP NROs) as (ACSA & ALSA & OFSA).

    assert (HSN : exists psn, bn_d (getbn snum lsP) = Some psn /\ In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsP))) OWP).
    { destruct (bn_d (getbn snum lsP)) as [psn|] eqn:Edsn0; [exists psn; split; [reflexivity|]; unfold bn_arr in ARRsnP; rewrite Edsn0 in ARRsnP; exact (proj1 ARRsnP)|].
      exfalso. destruct (bn_arr_null PL snum mP OWP DsnP _ PWF (hpl_wref PL snum HPs) Edsn0 ARRsnP) as [_ E]. unfold bn_dmax in OKp2. rewrite E in OKp2. cbn in OKp2. clear - OKp2 TNP NP1. lia. }
    destruct HSN as (psn & Edsn & HinsnP).
    pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) HinsnP) as (PSN0 & PSN16 & _ & _ & _).
    assert (BDSN : 0 < DsnP /\ DsnP + 8 * Z.of_nat (bn_dmax (getbn snum lsP)) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - PSN0 DsnPC CEIL LO SPR SPT; lia).
    assert (HinsdP : In (psd, DsdP, 8 * Z.of_nat (bn_dmax b6)) OWP).
    { unfold bn_arr in ARRsdP. rewrite GSP in ARRsdP. unfold sd3, bn_dmax in ARRsdP. cbn [bn_with_neg bn_with_buf bn_d bn_buf] in ARRsdP.
      rewrite Edsd, Lnbuf in ARRsdP. exact (proj1 ARRsdP). }
    pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENVP)) HinsdP) as (PSDP0 & PSDP16 & _ & _ & _).
    env_openA ENVP.
    assert (OFFP : offshW [(bv_unsigned sp + -304, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; clear - C2 CEIL LO; lia).
    assert (BDQ : 0 <= DsdP /\ DsdP + 8 * Z.of_nat dn + 8 < 18446744073709551616) by (unfold bn_dmax, BnHeapA.ACEIL in *; clear - DsdP0 DsdPC CEIL LO SPR OKs2 C6b; lia).
    assert (NPB : Z.of_nat nP <= Z.of_nat (bn_dmax (getbn snum lsP)) < 8388608) by (clear - OKp2 OKp3 TNP; lia).
    apply hide_intro in OFVA. apply hide_intro in OFSA. apply hide_intro in OFV. apply hide_intro in OFS. apply hide_intro in SPI. apply hide_intro in NPI. apply hide_intro in NP3.
    unfold MallocRep.wz in *. apply implA_from_evt.
    zstep. rewrite (bk_swrap32_small (Z.of_nat nP - Z.of_nat dn)) by lia.
    replace (Z.of_nat nP - Z.of_nat dn) with (Z.of_nat (nP - dn)) by lia.
    set (loop := (nP - dn)%nat) in *.
    hide_ors. ub. unhide.
    step.
    hide_ors. ub. unhide.
    zstep.
    shl_with ACSA ALSA. chk0.
    step.
    step.
    step.
    zstep. replace (Z.of_nat loop ≪ 3) with (8 * Z.of_nat loop) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    hide_ors. ub. unhide.
    step.
    hide_ors. ub. unhide.
    zstep. rewrite (bk_swrap32_small (Z.of_nat nP + -1)) by lia.
    hide_ors. ub. unhide.
    do 2 zstep.
    replace (DsnP + (Z.of_nat nP + -1) ≪ 3) with (DsnP + 8 * Z.of_nat nP - 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    step.
    hide_ors. ub. unhide.
    step.
    shl_with ACVA ALVA. chk0.
    step.
    zstep. rewrite (bk_swrap32_small (Z.of_nat dn + -1)) by lia.
    hide_ors. ub. unhide.
    step.
    step.
    do 2 zstep.
    replace (DsdP + (Z.of_nat dn + -1) ≪ 3) with (DsdP + 8 * Z.of_nat dn - 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mQ end.
    destruct (proj1 (limbarr_limbs_at bgbsegs mQ DsdP nbuf) UsdP) as (LAnb & _).
    hide_ors. ub. zstep. ub. unhide.
    do 2 zstep.
    hide_ors. shl_with ACV ALV. chk0. unhide.
    assert (N0 : nth_error nbuf (dn - 1) = Some d0) by (unfold d0; apply nth_error_nth'; lia).
    let ad := cur_mem_addr in
      pose proof (limbs_at_read_nth bgbsegs mQ DsdP nbuf (dn - 1) d0 ad LAnb N0 ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD.
    zstep.
    step.
    setreg 26%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; rewrite ub_lxor_sign63 by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).

    lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mx _) =>
     lazymatch goal with FRx : rw_cells _ mx (bv_unsigned sp + -304) (CB 16 ?jA :: _) |- _ =>
      assert (JOIN : forall mJ (j1a j1b : list byte) (x10 x11 x12 x13 x14 : word),
        rw_cells bgbsegs mJ (bv_unsigned sp + -304)
          ([CB 16 jA; C8 (Z_to_bv 64 ((asnum + 8) ≫ 3 + SHB)); C8 (Z_to_bv 64 (asnum + 8)); C8 (Z_to_bv 64 sh); C8 (Z_to_bv 64 ac); C8 (Z_to_bv 64 arm);
            CB 32 j1a; C8 (Z_to_bv 64 d1); CB 40 j1b; C8 (Z_to_bv 64 asnum); C8 (Z_to_bv 64 (Z.of_nat loop)); C8 (Z_to_bv 64 (asdiv ≫ 3 + SHB));
            C8 (Z_to_bv 64 (DsnP + 8 * Z.of_nat nP - 8)); C8 (Z_to_bv 64 asdiv); C8 (Z_to_bv 64 anum); C8 (Z_to_bv 64 (Z.of_nat dn)); C8 (Z_to_bv 64 (DsnP + 8 * Z.of_nat loop));
            C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
        stk bgbsegs mJ lo (bv_unsigned sp + -304) -> mem_inv bgbsegs mJ -> munch [(bv_unsigned sp + -304, bv_unsigned sp)] mP mJ -> wmono bgbsegs mP mJ ->
        evt bgbsegs P
          (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 (Z.of_nat nP))
                   x10 x11 x12 x13 x14 q15 q16 q17 (Z_to_bv 64 d0) (Z_to_bv 64 advs) (Z_to_bv 64 atmp) (Z_to_bv 64 DsnP) (Z_to_bv 64 (8 * Z.of_nat loop))
                   (Z_to_bv 64 ares) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat dn)) (Z_to_bv 64 0) (Z_to_bv 64 ac) q28 q29 q30 q31)
              FP (Z_to_bv 64 0x234fc0) fcP None mJ (seg_rom bgbsegs)))
     end end.
    2:{ zstep. if_cases K1; zify_cond K1.
        +
          zstep. rewrite (bk_swrap32_small (Z.of_nat dn + -2)) by lia.
          hide_ors. ub. unhide.
          do 2 zstep.
          replace (DsdP + (Z.of_nat dn + -2) ≪ 3) with (DsdP + 8 * Z.of_nat dn - 16) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
          hide_ors. ub. zstep. ub. unhide.
          do 2 zstep.
          hide_ors. shl_with ACV ALV. chk0. unhide.
          assert (N1 : nth_error nbuf (dn - 2) = Some d1)
            by (unfold d1; replace (dn =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia); apply nth_error_nth'; lia).
          let ad := cur_mem_addr in
            pose proof (limbs_at_read_nth bgbsegs mQ DsdP nbuf (dn - 2) d1 ad LAnb N1 ltac:(unfold wa; f_equal; clear - K1 DN1; lia)) as RD.
          zstep. clear RD.
          step.
          match goal with FRx : rw_cells _ ?mx (bv_unsigned sp + -304) _, STx : stk _ ?mx _ _, MIx : mem_inv _ ?mx, MUx : munch _ mP ?mx, WMx : wmono _ mP ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            eapply JOIN; [exact FRx | exact STx | exact MIx | exact MUx | exact WMx] end.
        +
          step.
          step.
          replace (Z_to_bv 64 d1) with (Z_to_bv 64 0) in JOIN by (unfold d1; replace (dn =? 1)%nat with true by (symmetry; apply Nat.eqb_eq; lia); reflexivity).
          match goal with FRx : rw_cells _ ?mx (bv_unsigned sp + -304) _, STx : stk _ ?mx _ _, MIx : mem_inv _ ?mx, MUx : munch _ mP ?mx, WMx : wmono _ mP ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            eapply JOIN; [exact FRx | exact STx | exact MIx | exact MUx | exact WMx] end. }
    intros mJ j1a j1b r10 r11 r12 r13 r14 FRJ STJ MIJ MUJ WMJ.
    match goal with FRx : rw_cells _ mQ (bv_unsigned sp + -304) _ |- _ => clear FRx | _ => idtac end.
    match goal with STx : stk _ mQ _ _ |- _ => clear STx | _ => idtac end. match goal with MIx : mem_inv _ mQ |- _ => clear MIx | _ => idtac end.
    match goal with MUx : munch _ mP mQ |- _ => clear MUx | _ => idtac end. match goal with WMx : wmono _ mP mQ |- _ => clear WMx | _ => idtac end.
    step.
    zstep.
    step.
    step.

    env_closeA HWLs WOKs ENVP LSP ENVQ LSQ.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSP HAdvP) as HVdvP.
    pose proof (st_wf_ok res lsP WFSP HVdvP NROr) as (_ & OKdvP2 & _).
    apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
    eapply implA_bind.
    { eapply implA_leaves; [apply (bn_wexpand_leaves2 res loop lsP HVdvP OKdvP2)|].
      eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := res) (a := ares) (OW := OWP) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAdvP | exact WRres | reflexivity | reflexivity | unfold bn_dmax in *; lia].
      - eapply cenv_preA; [exact ENVQ | exact LSQ | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - USEDP; unfold MC in *; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENVQ).
      - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_wexp2 CTX). }
    cbv beta. intros [uR lsR] ΣR msR [PO LEAFR].
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENVQ))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FR_ & fcR & mS & OWR & PLR & -> & CPR & (EPLR & -> & HDMR & _ & BLKR)).
    subst PLR. specialize (CPR eq_refl).
    lazymatch type of ENVQ with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
      assert (ER : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (u + MC) ΣR lsR mS OWR /\ lib_state lsR mS OWR PL EA)
        by (eapply cenv_postA; [exact ENVQ | exact CPR]) end.
    destruct ER as (ENVR & LSR).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPR) as RSR.
    rewrite (ret_pc_even 0x234fd0) by lia. unfold MallocRep.wz.
    clear CPR.

    destruct LEAFR as (R1 & R2 & R3 & R4 & R5 & RD & _ & _). cbn [snd] in *.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSR HAdvP) as HAdvR. pose proof (oref_at_stable _ _ _ _ _ _ _ RSR HArmP) as HArmR. pose proof (ref_at_stable _ _ _ _ _ _ _ RSR HAnumP) as HAnumR. pose proof (ref_at_stable _ _ _ _ _ _ _ RSR HAdvsP) as HAdvsR.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSR HAtmpP) as HAtmpR. pose proof (ref_at_stable _ _ _ _ _ _ _ RSR HAsnumP) as HAsnumR. pose proof (ref_at_stable _ _ _ _ _ _ _ RSR HAsdivP) as HAsdivR.
    assert (GSR : getbn sdiv lsR = sd3) by (rewrite R1 by exact NEvd; exact GSP).
    assert (GNR : getbn snum lsR = getbn snum lsP) by (apply R1; exact NEvs).
    assert (HinsnR : In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsP))) OWR).
    { apply BLKR; [exact HinsnP|]. intros E.
      eapply (ids_bn_neq res snum lsP psn psn (ids_m_nodup _ _ _ IDSP) HVdvP HVsnP (hide_elim _ NEvs) E Edsn). reflexivity. }
    clear BLKR RSR HAdvP HArmP HAnumP HAdvsP HAtmpP HAsnumP HAsdivP ENVP LSP ENVQ LSQ NDP IDSP ERRBP HVsdP HVsnP HVdvP OKdvP2 BNsdP BNsnP ARRsdP ARRsnP UsdP UsnP HinsP HinnP HinsnP HinsdP LAnb ACV ALV OFV ACS ALS OFS ACVA ALVA OFVA ACSA ALSA OFSA SEPsnP.
    pose proof (AH_nodup_l _ _ _ _ (proj1 (proj2 ENVR))) as NDR.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LSR) as PARTSR; pose proof PARTSR as (WFSR & PWFR & IDSR & PLBR & ERRBR).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LSR HAdvR) as HVdvR.
    destruct (lib_state_open [] lsR mS OWR PL EA num anum LSR NDR HAnumR ltac:(intros []) NROn) as ((DnumR & BNnumR & _) & _ & _).
    destruct (lib_state_open [] lsR mS OWR PL EA dvs advs LSR NDR HAdvsR ltac:(intros []) NROd) as ((DdvsR & BNdvsR & _) & _ & _).
    destruct (lib_state_open [] lsR mS OWR PL EA res ares LSR NDR HAdvR ltac:(intros []) NROr) as ((Ddv & BNdv & ARRdv) & (OKv1 & OKv2 & OKv3 & OKv4) & LSHR).
    unfold bn_cells in BNnumR, BNdvsR, BNdv.
    set (bv := getbn res lsR) in *. set (bnR := getbn num lsR) in *. set (bdR := getbn dvs lsR) in *.
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) PARTSR NOFR HAdvR NROr) as (qv & Av & nv & Hinv & Rv1 & Rv2).
  pose proof (AH_range_in _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) Hinv) as (V0 & _ & _ & VC & VI).
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) PARTSR NOFR HAnumR NROn) as (qn & An & nn & Hinn & Rn1 & Rn2).
  pose proof (AH_range_in _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) Hinn) as (N0' & _ & _ & NC' & NI').
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) PARTSR NOFR HAdvsR NROd) as (qdR & AdR & ndR & HindR & RdR1 & RdR2).
  pose proof (AH_range_in _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) HindR) as (D0' & _ & _ & DC' & DI').
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) LSR NOFR HAnumR NROn) as (ACNU & ALNU & OFNU).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) LSR NOFR HAdvsR NROd) as (ACDV & ALDV & OFDV).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) LSR NOFR HAdvR NROr) as (ACR & ALR & OFR).
    assert (ANUM : 0 < anum /\ anum + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - N0' Rn1 Rn2 NC' CEIL LO SPR SPT; lia).
    assert (ADVS : 0 < advs /\ advs + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - D0' RdR1 RdR2 DC' CEIL LO SPR SPT; lia).
    assert (ADV : 0 < ares /\ ares + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - V0 Rv1 Rv2 VC CEIL LO SPR SPT; lia).

    assert (HDV : exists pv, bn_d bv = Some pv /\ In (pv, Ddv, 8 * Z.of_nat (bn_dmax bv)) OWR).
    { destruct (bn_d bv) as [pv|] eqn:Edv0; [exists pv; split; [reflexivity|]; unfold bn_arr in ARRdv; rewrite Edv0 in ARRdv; exact (proj1 ARRdv)|].
      exfalso. destruct (bn_arr_null PL res mS OWR Ddv bv PWF WRres Edv0 ARRdv) as [_ E]. unfold bn_dmax in RD. rewrite E in RD. cbn in RD. clear - RD NP1. unfold loop in *. lia. }
    destruct HDV as (pv & Edv & Hinpv).
    pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENVR)) Hinpv) as (PV0 & PV16 & _ & PVC & _).
    assert (BDV : 0 < Ddv /\ Ddv + 8 * Z.of_nat (bn_dmax bv) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - PV0 PVC CEIL LO SPR SPT; lia).
    assert (LOOPB : Z.of_nat loop <= Z.of_nat (bn_dmax bv) < 8388608) by (unfold BG_DMAX in OKv3; clear - RD OKv3; lia).
    env_openA ENVR.
    match goal with MUx : munch _ mS mS |- _ => clear MUx end.
    pose proof (munch_refl [(bv_unsigned sp + -304, bv_unsigned sp); (ares, ares + 24)]%Z mS) as MUR.
    assert (OFFR : offshW [(bv_unsigned sp + -304, bv_unsigned sp); (ares, ares + 24)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; clear - OFR C2 CEIL LO; lia).
    apply hide_intro in OFNU. apply hide_intro in OFDV. apply hide_intro in OFR. apply hide_intro in VI. apply hide_intro in NI'. apply hide_intro in DI'.
    unfold MallocRep.wz in *. apply implA_from_evt.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ ADV. lia. }
    clear KZ.
    hide_ors. ub. unhide.
    step.
    do 3 zstep.
    shl_with ACNU ALNU. chk0.
    hide_ors. ub. unhide.
    do 3 zstep.
    shl_with ACDV ALDV.
    step. rewrite (sx32_small (Z.b2z (bn_neg bnR))) by (destruct (bn_neg bnR); cbn; lia).
    chk0.
    do 3 zstep.
    shl_with ACR ALR.
    step. rewrite (sx32_small (Z.b2z (bn_neg bdR))) by (destruct (bn_neg bdR); cbn; lia).
    chk0.
    zstep.
    setreg 11%Z (Z_to_bv 64 (Z.b2z (xorb (bn_neg bnR) (bn_neg bdR)))) ltac:(f_equal; destruct (bn_neg bnR), (bn_neg bdR); reflexivity).
    clear BNnumR BNdvsR Rn1 Rn2 RdR1 RdR2 N0' NC' D0' DC' DnumR DdvsR.
    zstep.
    zstep.
    do 2 zstep.
    shl_with ACR ALR. chk0.
    step.
    zstep.
    do 2 zstep.
    shl_with ACR ALR. chk0.
    step.
    step.
    zstep.
    setreg 19%Z (Z_to_bv 64 (Ddv + 8 * Z.of_nat loop)) ltac:(f_equal; lia).
    hide_ors. ub. unhide.
    step.
    zstep. rewrite (bk_swrap32_small (Z.of_nat dn + 1)) by (unfold bn_dmax in *; lia).
    do 2 zstep.
    step.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT end.
    apply evt_done. rewrite !bbind_get. fold bnR bdR. rewrite bbind_get_set. fold bv.
    set (q2 := mkBN (bn_d bv) (bn_buf bv) loop (xorb (bn_neg bnR) (bn_neg bdR)) (bn_flags bv)).
    assert (WOKR : Forall (w_ok OWR LB lsR PL EA (bv_unsigned sp) [res]) [(bv_unsigned sp + -304, bv_unsigned sp); (ares, ares + 24)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia|]. constructor; [eapply (w_struct OWR LB lsR PL EA (bv_unsigned sp) false [res] _ res ares); [left; reflexivity| exact HAdvR| exact NROr| cbn; clear; lia| cbn; clear; lia]| constructor]. }
    assert (HWLR : Forall (w_lib lsR OWR PL lo (bv_unsigned sp)) [(bv_unsigned sp + -304, bv_unsigned sp); (ares, ares + 24)]).
    { constructor; [left; cbn; lia|]. constructor; [w_lib_ref HAdvR NROr| constructor]. }
    match goal with HEAPx : @BnHeapA.AHEAP _ ΣR OWR LB mS, STx : stk _ mT _ _, MIx : mem_inv _ mT, FRx : rw_cells _ mT (bv_unsigned sp + -304) _, WMx : wmono _ mS mT |- _ =>
      rename HEAPx into HEAPR; rename STx into STT; rename MIx into MIT; rename FRx into FRT; rename WMx into WMT end.
    assert (LST : lib_state (setbn res q2 lsR) mT OWR PL EA).
    { unfold lib_state. eapply (lib_state_close [] lsR mT OWR PL EA res ares); [| exact NDR| exact HAdvR| exact NROr| | |].
      - exact (lib_state_frame ΣR LB (bv_unsigned sp) USTACK_TOP [res] lsR mS mT OWR PL EA _ HEAPR LSHR MUR WMT FROK WOKR).
      - exists Ddv. split.
        + unfold bn_cells, q2, bn_dmax. cbn [bn_top bn_buf bn_neg bn_flags]. exact BNdv.
        + unfold bn_arr, q2 in *. cbn [bn_d bn_buf bn_dmax] in *. rewrite Edv in ARRdv |- *.
          destruct ARRdv as [Hin Uarr]. split; [exact Hin|].
          eapply u64arr_transport; [exact Uarr | exact MUR | exact WMT |].
          pose proof (struct_limbs_disj ΣR OWR LB mS HEAPR lsR PL EA (bv_unsigned sp) USTACK_TOP PARTSR FROK res res ares pv Ddv _ HAdvR HVdvR Edv Hin) as SLD.
          cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax bv). clear - SLD PVC CEIL LO SPR. unfold BnHeapA.ACEIL in *. lia.
      - unfold bg_ok, q2, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OKv1|]. split; [exact RD|]. split; [exact OKv3| exact OKv4].
      - apply ids_ok_setbn_same; [exact IDSR| exact HVdvR| reflexivity]. }
    lazymatch type of ENVR with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?u _ _ _ _ =>
      lazymatch type of FRT with rw_cells _ _ _ ?fr' =>
        let pre' := drop2 fr' in
        assert (ENVT : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre' u ΣR (setbn res q2 lsR) mT OWR);
        [ apply cenv_setbnA; [| exact HVdvR | reflexivity];
          eapply (cenv_silentA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m);
            [exact ENVR | exact LSR | exact MUR | exact WMT | exact HWLR | exact STT | exact MIT | cbn [app]; exact FRT | cbn; lia]
        | ] end end.
    set (lsT := setbn res q2 lsR) in *.
    assert (HAtmpT : ref_at lsT OWR PL tmp atmp) by (apply ref_at_setbn; exact HAtmpR).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LST) as (WFST & PWFT & IDST & _).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LST HAtmpT) as HVtT.
    pose proof (st_wf_ok tmp lsT WFST HVtT NROt) as (_ & OKtT2 & _).
    unfold bbind at 1. cbn [bind tree_ops].
    eapply implA_bind.
    { eapply implA_leaves; [apply (bn_wexpand_leaves2 tmp (dn + 1) lsT HVtT OKtT2)|].
      eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := tmp) (a := atmp) (OW := OWR) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAtmpT | exact (hpl_wref PL tmp HPt) | reflexivity | f_equal; f_equal; lia | unfold bn_dmax in *; lia].
      - eapply cenv_preA; [exact ENVT | exact LST | unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | clear - USEDP; unfold MC in *; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENVT).
      - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_wexp3 CTX). }
    cbv beta. intros [uU lsU] ΣU msU [PO LEAFU].
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -304) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact (proj1 (proj2 ENVT))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FU & fcU & mU & OWU & PLU & -> & CPU & (EPLU & -> & HDMU & _ & BLKU)).
    subst PLU. specialize (CPU eq_refl).
    lazymatch type of ENVT with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre ?u _ _ _ _ =>
      assert (EU : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -304) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (u + MC) ΣU lsU mU OWU /\ lib_state lsU mU OWU PL EA)
        by (eapply cenv_postA; [exact ENVT | exact CPU]) end.
    destruct EU as (ENVU & LSU).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPU) as RSU.
    rewrite (ret_pc_even 0x2350b8) by lia. unfold MallocRep.wz.
    clear CPU.

    destruct LEAFU as (U1 & U2 & U3 & U4 & U5 & UD & _ & _). cbn [snd] in *.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSU (proj2 (ref_at_setbn lsR OWR PL res q2 _ _) HAdvR)) as HAdvU. pose proof (oref_at_stable _ _ _ _ _ _ _ RSU (oref_at_setbn lsR OWR PL res q2 _ _ HArmR)) as HArmU.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSU HAtmpT) as HAtmpU. pose proof (ref_at_stable _ _ _ _ _ _ _ RSU (proj2 (ref_at_setbn lsR OWR PL res q2 _ _) HAsnumR)) as HAsnumU.
    pose proof (ref_at_stable _ _ _ _ _ _ _ RSU (proj2 (ref_at_setbn lsR OWR PL res q2 _ _) HAsdivR)) as HAsdivU.
    assert (GSU : getbn sdiv lsU = sd3) by (rewrite U1 by exact NEtd; unfold lsT; rewrite getbn_setbn_other by exact NEvd; exact GSR).
    assert (GNU : getbn snum lsU = getbn snum lsP) by (rewrite U1 by exact NEts; unfold lsT; rewrite getbn_setbn_other by exact NEvs; exact GNR).
    assert (GVU : getbn res lsU = q2) by (rewrite U1 by (apply not_eq_sym; exact NEvt); unfold lsT; apply getbn_setbn_same; exact HVdvR).
    assert (HinsnU : In (psn, DsnP, 8 * Z.of_nat (bn_dmax (getbn snum lsP))) OWU).
    { apply BLKU; [exact HinsnR|]. intros E.
      assert (HVsT : vref snum lsT) by (apply vref_setbn; apply (ref_at_valid _ _ _ _ _ _ _ _ LSR HAsnumR)).
      eapply (ids_bn_neq tmp snum lsT psn psn (ids_m_nodup _ _ _ IDST) HVtT HVsT (hide_elim _ NEts) E); [|reflexivity].
      unfold lsT. rewrite getbn_setbn_other by exact NEvs. rewrite GNR. exact Edsn. }
    assert (HinpvU : In (pv, Ddv, 8 * Z.of_nat (bn_dmax bv)) OWU).
    { apply BLKU; [exact Hinpv|]. intros E.
      assert (HVvT : vref res lsT) by (apply vref_setbn; exact HVdvR).
      eapply (ids_bn_neq tmp res lsT pv pv (ids_m_nodup _ _ _ IDST) HVtT HVvT (not_eq_sym (hide_elim _ NEvt)) E); [|reflexivity].
      unfold lsT. rewrite getbn_setbn_same by exact HVdvR. exact Edv. }
    set (bsn := getbn snum lsP) in *.
    clear BLKU RSU HAdvR HArmR HAnumR HAdvsR HAtmpR HAsnumR HAsdivR HAtmpT ENVR LSR ENVT LST LSHR NDR IDSR ERRBR IDST HVtT OKtT2 HVdvR HinsnR Hinpv Hinv WOKR HWLR MUR BNdv ARRdv GSR GNR R1 R2 R3 R4 R5 V0 VC VI Rv1 Rv2 HEAPR STT MIT FRT WMT ACNU ALNU OFNU ACDV ALDV OFDV ACR ALR OFR OFFR.
    assert (LOOP1 : (1 <= loop)%nat) by (unfold loop; lia).
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVU)) (lib_state_h_parts _ _ _ _ _ _ LSU) NOFR HAtmpU NROt) as (qt & At & nt & Hint & Rt1 & Rt2).
    pose proof (AH_range_in _ _ _ _ _ _ _ (proj1 (proj2 ENVU)) Hint) as (T0' & _ & _ & TC' & _).
    assert (ATMP : 0 < atmp /\ atmp + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - T0' Rt1 Rt2 TC' CEIL LO SPR SPT; lia).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj2 ENVU)) LSU NOFR HAtmpU NROt) as (_ & ALTA & _).
    assert (RDN : 0 <= Z.of_nat dn < 4294967296) by (unfold bn_dmax in *; lia).
    env_openA ENVU.
    unfold MallocRep.wz in *. apply implA_from_evt.
    step.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by lia. clear - KZ ATMP. lia. }
    clear KZ.
    step.
    zstep.
    step.
    do 2 zstep.
    step.
    zstep.
    setreg 12%Z (Z_to_bv 64 1) ltac:(f_equal; symmetry; replace (0 <? atmp) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    zstep.
    setreg 13%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7; exact ALTA).
    step.
    zstep. replace (Z.of_nat dn ≪ 3) with (8 * Z.of_nat dn) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    step.
    zstep.
    setreg 9%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7; clear - PV16; Z.div_mod_to_equations; lia).
    step.
    zstep.
    setreg 15%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; apply land7; clear - PSN16; Z.div_mod_to_equations; lia).
    step.
    zstep. replace (Z.of_nat dn ≪ 3) with (8 * Z.of_nat dn) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    zstep.
    setreg 14%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; rewrite ub_lxor_sign63 by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
    step.
    zstep.
    remember (Z_to_bv 64 4294967295) as mask32 eqn:Emask.
    step. subst mask32.
    zstep.
    step.
    zstep.
    zstep.
    setreg 21%Z (Z_to_bv 64 (shad atmp)) ltac:(f_equal; symmetry; apply shr3_shad; lia).
    zstep.
    setreg 10%Z (Z_to_bv 64 1) ltac:(reflexivity).
    step.
    step.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mL end.
    match goal with FRx : rw_cells _ mL (bv_unsigned sp + -304) _ |- _ => rename FRx into FRL end.
    replace (Z.land d1 4294967295) with (d1 mod 4294967296) in FRL by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; reflexivity).
    rewrite (shr3_shad (asnum + 8)) in FRL by lia. rewrite (shr3_shad asdiv) in FRL by lia.
    env_closeA HWLs WOKs ENVU LSU ENVV LSV.
    apply evt_done.
    eapply (div_tailA) with (res := res) (rm := rm) (tmp := tmp) (snum := snum) (sdiv := sdiv) (adv := ares) (arm := arm) (atmp := atmp) (asnum := asnum) (asdiv := asdiv) (ac := ac) (qc := qc)
                            (psn := psn) (pv := pv) (sdbuf := nbuf) (negn := bn_neg bnR) (dn := dn) (loop := loop) (nP := nP) (d0 := d0) (d1 := d1) (sh := sh)
                            (DsnP := DsnP) (Ddv := Ddv) (ras := ras).
    { exact LO'. }
    { exact EC. }
    { exact ENVV. }
    { clear - USEDP. unfold MC in *. lia. }
    { exact CTX. }
    { exact LSV. }
    { exact HAdvU. }
    { exact HArmU. }
    { exact HAtmpU. }
    { exact HAsnumU. }
    { exact HAsdivU. }
    { exact WRres. }
    { exact HPrm. }
    { exact HPt. }
    { exact HPs. }
    { exact HPd. }
    { exact NEts. }
    { exact NEtd. }
    { exact NEsd. }
    { exact NEvt. }
    { exact NEvs. }
    { exact NEvd. }
    { rewrite GSU. reflexivity. }
    { rewrite GSU. exact C6b. }
    { exact HTOPD5. }
    { reflexivity. }
    { reflexivity. }
    { exact (proj1 Rd0). }
    { rewrite GNU. exact TNP. }
    { unfold loop. lia. }
    { exact LOOP1. }
    { rewrite GNU. exact Edsn. }
    { rewrite GNU. exact HinsnU. }
    { rewrite GNU.
      apply (div_top_init (bn_buf bsn) (firstn tn (bn_buf bnum)) (firstn dn nbuf) sh dn tn nP).
      - exact OKp1.
      - rewrite <- TNP. exact OKp2.
      - exact HTOPD5.
      - exact NP1.
      - exact NP2.
      - exact SH.
      - apply limbs_firstn. exact OKn1.
      - apply firstn_length_le. exact OKn2.
      - exact FNP.
      - apply limbs_firstn. exact LIMnb.
      - apply firstn_length_le. exact Lnb2.
      - rewrite nth_firstn. destruct (Nat.ltb_spec (dn - 1) dn); [exact (proj1 Rd0) | lia]. }
    { rewrite GVU. exact Edv. }
    { rewrite GVU. exact HinpvU. }
    { rewrite GVU. reflexivity. }
    { rewrite GVU. exact RD. }
    { exact UD. }
    { exact SH. } }
  apply implA_from_evt.
  zstep. rewrite lts_signed by (unfold bn_dmax in *; lia). if_cases KB; zify_cond KB.
  -
    apply evt_done.
    replace (tn + 1 <=? dn)%nat with false by (symmetry; apply Nat.leb_gt; lia).
    unfold bbind at 1. unfold bret at 1. cbn [bind ret tree_ops tbind fst snd].
    eapply (CONT Σ8 ls8 m12 OW8 (tn + 1)%nat); [exact ENV9 | clear - UKD; unfold BN_DIV_FT_COST, MC in *; lia | exact LS8 | exact HAdv8 | exact HArm8 | exact HAnum8 | exact HAdvs8 | exact HAtmp8 | exact HAsnum8 | exact HAsdiv8
      | exact Esd8 | exact L8b | lia | lia | right; reflexivity | exact L8c | ].
    rewrite Nat.sub_diag. cbn [repeat]. rewrite app_nil_r. exact L8d.
  -
    apply evt_done.
    replace (tn + 1 <=? dn)%nat with true by (symmetry; apply Nat.leb_le; lia).
    lazymatch goal with |- implA (bbind _ _ ?REST0 _) _ ?Q _ =>
      eapply (div_padA REST0 Q) with (snum := snum) (asnum := asnum) (dn := dn) (tnp := (tn + 1)%nat) (lo := lo) (LB := LB) (PL := PL) (EA := EA) (ras := ras)
    end.
    { exact LO'. }
    { exact ENV9. }
    { clear - UKD. unfold BN_DIV_FT_COST, MC in *. lia. }
    { exact CTX. }
    { exact LS8. }
    { exact HAsnum8. }
    { exact HPs. }
    { exact L8b. }
    { lia. }
    { unfold bn_dmax in *. lia. }
    intros ΣP lsP mP OWP FP' fcP' q1 q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 ENVP LSP RSP OTH TOPP NEGP FNP CTXP.
    eapply (CONT ΣP lsP mP OWP (dn + 1)%nat); [exact ENVP | clear - UKD; unfold BN_DIV_FT_COST, MC in *; lia | exact LSP | exact (ref_at_stable _ _ _ _ _ _ _ RSP HAdv8)
      | exact (oref_at_stable _ _ _ _ _ _ _ RSP HArm8) | exact (ref_at_stable _ _ _ _ _ _ _ RSP HAnum8)
      | exact (ref_at_stable _ _ _ _ _ _ _ RSP HAdvs8) | exact (ref_at_stable _ _ _ _ _ _ _ RSP HAtmp8) | exact (ref_at_stable _ _ _ _ _ _ _ RSP HAsnum8)
      | exact (ref_at_stable _ _ _ _ _ _ _ RSP HAsdiv8) | | exact TOPP | lia | lia | left; lia | | ].
    + rewrite OTH by (intros E; apply (hide_elim _ NEsd); symmetry; exact E). exact Esd8.
    + rewrite NEGP. exact L8c.
    + rewrite FNP, L8d. reflexivity.
Qed.

End WithRT.
