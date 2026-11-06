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
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgPlace.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitA BnCallA W_expandA PlaceKitA.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2238528 => 1
  | 2238532 => 2
  | 2257364 => 1
  | 2257368 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Definition BN_NEW : Z := 0x222808.
Definition BN_NEW_STACK : Z := 32 + CRYPTO_ZALLOC_STACK.
Definition BN_CTX_NEW : Z := 0x227300.
Definition BN_CTX_NEW_EX : Z := 0x22718c.
Definition BN_CTX_NEW_STACK : Z := 48 + CRYPTO_ZALLOC_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma BN_new_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (r : bnref),
  bn_preA Σ ls m OW LB PL EA sp lo BN_NEW_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_NEW (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> stored_ref r -> pl_bn PL r = None ->
  implA (BN_new (tree_ops bptr) r ls) Σ
    (bn_postA_p ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
                (fun p ls' OW' PL' a0' => exists a, PL' = pl_set PL r (Some (PHeap a p 0)) /\ a0' = wz a /\ 0 < a < 2^63
                                          /\ OW' = (p, a, 24) :: OW /\ ls' = setbn r (bn_nil BN_FLG_MALLOCED) ls))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_NEW) fc None m (seg_rom bgbsegs)).
Proof.
  intros until r. intros PRE UW CTX -> SR E.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof LO as LO'. unfold BN_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_NEW, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  unfold BN_new, bbind, bmalloc, bset, bret. cbn [bind ret unreachable lib_malloc tree_ops tbind fst snd].
  apply implA_from_evt.
  carve_frame 32%nat ST.
  do 5 step. do 3 step. do 4 step. step.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (jfr := j) in *; clearbody jfr end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -32, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia)) as HEAP1.
  pose proof (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia)) as AXP1.
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -32) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m1 _ (bv_unsigned sp) 32 [CB 8 jfr; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  apply evt_done.
  eapply (CRYPTO_zalloc_walkA) with (n := 24) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
  - exact HEAP1.
  - rewrite ESP. exact ST.
  - exact CEIL.
  - rewrite ESP. unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK. clear - LO'. lia.
  - rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
  - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
  - exact MI.
  - exact (proj1 LS1).
  - clear. lia.
  - pose proof (cnt_ok_live ls OW LB OW 0 WFS CNT ltac:(lia) ltac:(lia)) as HL. rewrite length_map in HL. exact HL.
  - exact CRED.
  - rewrite ESP. exact UW1.
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_new_222654 : uk_call BN_NEW 0x22283c CRYPTO_ZALLOC) CTX).
  - intros p Σ1 ms1 FRESH PO.
    unfold calloc_postA in PO. rewrite ?ESP in PO.
    destruct PO as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & F1 & fc1 & m3 & An & -> & MI3 & ST3 & AG3 & CR3 & BR & HEAP3 & ACCN & BLK).
    rewrite (ret_pc_even 2238524) by (clear; lia).
    apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; clear - Hx SPT; lia].
    assert (LS3 : lib_state ls m3 OW PL EA).
    { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp) USTACK_TOP); [exact LS1| exact FROK| clear; lia| clear; lia| exact AG3|]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
    assert (AXP3 : ax_pres LB (bv_unsigned sp) (XW PL) m m3).
    { eapply ax_pres_trans; [exact AXP1|]. eapply agree_on_mono; [exact AG3|]. intros x [_ [Hx|[Hx|(b0 & Hb0 & Hr)]]];
        [left; clear - Hx; lia | right; left; exact Hx | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]]. }
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    assert (ND3 : List.NoDup (map blk_id (((p, An, 24) :: OW) ++ LB))) by (exact (AH_nodup _ _ _ _ HEAP3)).
    assert (FRESHA : ~ In p (all_ids ls PL EA)).
    { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
    set (OW1 := (p, An, 24) :: OW) in *.
    assert (LS3' : lib_state ls m3 OW1 PL EA) by (eapply lib_state_h_ow; [exact LS3|]; intros q A0 n0 _ Hq; right; exact Hq).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS3') as PARTS3.
    apply zero_bn_cellsA in BLK. unfold bn_cells, BnRepDefs.bn_cells, bn_nil, MallocRep.wz in BLK. cbn [bn_top bn_buf bn_neg bn_flags bn_d length Z.b2z] in BLK.
    assert (ALN : An mod 8 = 0) by (clear - BA16; Z.div_mod_to_equations; lia).
    assert (INN : In (p, An, 24) (OW1 ++ LB)) by (left; reflexivity).
    pose proof (AH_offsh _ _ _ _ (p, An, 24) HEAP3 INN) as OFN. cbn [blk_addr blk_size fst snd] in OFN. unfold SHLO, SHHI in OFN.
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (An, An + 24)]%Z m3) as MU3. pose proof (wmono_refl bgbsegs m3) as WM3.
    assert (OFF3 : offshW [(bv_unsigned sp + -32, bv_unsigned sp); (An, An + 24)]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFN SPR LO' CEIL C1 C2 C3. lia. }
    assert (EAn : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - BA0 BAC C1 C2 C3; lia).
    clear MU WM HEAP LS HEAP1 LS1 LS3 ST MI SHB1 SHB2 HWL WOK AG3 PARTS.
    destruct (AH_shb _ _ _ _ HEAP3) as (SHB1 & SHB2).
    apply implA_from_evt.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EAn in KA; clear - KA BA0; lia|]. clear KA.
    ub.
    do 3 step. shl_with ACCN ALN. chk0.
    step. step.
    do 3 step. release_frame FR ST3 (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    apply evt_done. apply implA_ret.
    assert (HWL3 : Forall (w_lib ls OW1 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -32, bv_unsigned sp); (An, An + 24)]).
    { constructor; [left; cbn; clear - LO'; lia|]. constructor; [|constructor].
      right; left. exists (p, An, 24). cbn [blk_addr blk_size fst snd]. split; [left; reflexivity | clear; lia]. }
    assert (WOK3 : Forall (w_ok OW1 LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -32, bv_unsigned sp); (An, An + 24)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia|]. constructor; [|constructor].
      eapply (w_foreign OW1 LB ls PL EA (bv_unsigned sp) false [] _ p An 24); [exact INN | exact FRESHA | cbn; clear; lia | cbn; clear; lia]. }
    unfold bn_postA_p. do 17 eexists. exists mF, OW1, (pl_set PL r (Some (PHeap An p 0))). split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP3 PARTS3 FROK MU3 WM3 HWL3 CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|].
    split.
    { eapply (lib_state_place_bn false [] ls mF OW1 PL EA r An p 24); [| exact SR| exact E| left; reflexivity| unfold BN_STRUCT_SZ; clear; lia| exact FRESHA|].
      - eapply (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP); [exact HEAP3| exact LS3'| exact MU3| exact WM3| exact FROK| exact WOK3].
      - unfold bn_cells, BnRepDefs.bn_cells, bn_nil, BN_FLG_MALLOCED, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags bn_d length Z.b2z]. exact BLK. }
    split; [exact ST3|]. split; [assumption|].
    split. { eapply ax_pres_trans; [exact AXP3|]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP3 PARTS3 FROK MU3 HWL3 CEIL ltac:(clear - LO'; lia)). }
    split; [unfold MC in *; clear - CR3; lia|].
    exists An. split; [reflexivity|]. split; [reflexivity|]. split; [unfold BnHeapA.ACEIL in *; clear - BA0 BAC C1 C2 C3; lia|]. split; reflexivity.
Qed.

Lemma BN_CTX_new_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_CTX_NEW_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_CTX_NEW (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> pl_ctx PL = None ->
  implA (BN_CTX_new (tree_ops bptr) ls) Σ
    (bn_postA_p ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
                (fun p ls' OW' PL' a0' => exists a, PL' = pl_set_ctx PL (Some (a, p)) /\ a0' = wz a /\ 0 < a < 2^63
                                          /\ OW' = (p, a, 72) :: OW /\ ls' = set_ctx gx_nil ls))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_CTX_NEW) fc None m (seg_rom bgbsegs)).
Proof.
  intros until ras. intros PRE UW CTX -> E.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof LO as LO'. unfold BN_CTX_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_CTX_NEW, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  unfold BN_CTX_new, bbind, bmalloc, bsetctx, bret. cbn [bind ret unreachable lib_malloc tree_ops tbind fst snd].
  apply implA_from_evt.

  carve_frame 16%nat ST.
  do 4 step. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.

  carve_frame 48%nat ST.
  do 7 step. do 3 step. step. do 4 step. step.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (jfr := j) in *; clearbody jfr end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -48, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia)) as HEAP1.
  pose proof (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia)) as AXP1.
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -48) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m1 _ (bv_unsigned sp) 48 [CB 8 jfr; C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  apply evt_done.
  eapply (CRYPTO_zalloc_walkA) with (n := 72) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
  - exact HEAP1.
  - rewrite ESP. exact ST.
  - exact CEIL.
  - rewrite ESP. unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK. clear - LO'. lia.
  - rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
  - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
  - exact MI.
  - exact (proj1 LS1).
  - clear. lia.
  - pose proof (cnt_ok_live ls OW LB OW 0 WFS CNT ltac:(lia) ltac:(lia)) as HL. rewrite length_map in HL. exact HL.
  - exact CRED.
  - rewrite ESP. exact UW1.
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_CTX_new_ex_226fe4 : uk_call BN_CTX_NEW_EX 0x2271cc CRYPTO_ZALLOC) (uk_ctx_tail _ _ _ (E_BN_CTX_new_22713c : uk_tail BN_CTX_NEW BN_CTX_NEW_EX) CTX)).
  - intros p Σ1 ms1 FRESH PO.
    unfold calloc_postA in PO. rewrite ?ESP in PO.
    destruct PO as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & F1 & fc1 & m3 & An & -> & MI3 & ST3 & AG3 & CR3 & BR & HEAP3 & ACCN & BLK).
    rewrite (ret_pc_even 2257356) by (clear; lia).
    apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; clear - Hx SPT; lia].
    assert (LS3 : lib_state ls m3 OW PL EA).
    { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ (bv_unsigned sp + -48) (bv_unsigned sp) USTACK_TOP); [exact LS1| exact FROK| clear; lia| clear; lia| exact AG3|]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
    assert (AXP3 : ax_pres LB (bv_unsigned sp) (XW PL) m m3).
    { eapply ax_pres_trans; [exact AXP1|]. eapply agree_on_mono; [exact AG3|]. intros x [_ [Hx|[Hx|(b0 & Hb0 & Hr)]]];
        [left; clear - Hx; lia | right; left; exact Hx | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]]. }
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    assert (FRESHA : ~ In p (all_ids ls PL EA)).
    { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
    set (OW1 := (p, An, 72) :: OW) in *.
    assert (LS3' : lib_state ls m3 OW1 PL EA) by (eapply lib_state_h_ow; [exact LS3|]; intros q A0 n0 _ Hq; right; exact Hq).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS3') as PARTS3.
    assert (ALN : An mod 8 = 0) by (clear - BA16; Z.div_mod_to_equations; lia).
    assert (INN : In (p, An, 72) (OW1 ++ LB)) by (left; reflexivity).
    assert (INO : In (p, An, 72) OW1) by (left; reflexivity).
    pose proof (AH_offsh _ _ _ _ (p, An, 72) HEAP3 INN) as OFN. cbn [blk_addr blk_size fst snd] in OFN. unfold SHLO, SHHI in OFN.
    assert (EAn : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - BA0 BAC C1 C2 C3; lia).

    apply (rw_cells_split_CB bgbsegs _ _ [] 72 _ [] [16; 8; 4; 4; 8; 4; 4; 16; 8]%nat) in BLK; [| reflexivity]. cbn [mk_CB_cells app firstn skipn repeat] in BLK.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (An, An + 72)]%Z m3) as MU3. pose proof (wmono_refl bgbsegs m3) as WM3.
    assert (OFF3 : offshW [(bv_unsigned sp + -48, bv_unsigned sp); (An, An + 72)]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFN SPR LO' CEIL C1 C2 C3. lia. }
    clear MU WM HEAP LS HEAP1 LS1 LS3 ST MI SHB1 SHB2 HWL WOK AG3 PARTS.
    destruct (AH_shb _ _ _ _ HEAP3) as (SHB1 & SHB2).
    apply implA_from_evt.
    step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EAn in KA; clear - KA BA0; lia|]. clear KA.
    ub.
    do 3 step. shl_with ACCN ALN. chk0.
    step. try change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). try store_done.
    do 3 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HWL4 : Forall (w_lib ls OW1 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp); (An, An + 72)]).
    { constructor; [left; cbn; clear - LO'; lia|]. constructor; [|constructor].
      right; left. exists (p, An, 72). cbn [blk_addr blk_size fst snd]. split; [left; reflexivity | clear; lia]. }
    assert (WOK4 : Forall (w_ok OW1 LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -48, bv_unsigned sp); (An, An + 72)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia|]. constructor; [|constructor].
      eapply (w_foreign OW1 LB ls PL EA (bv_unsigned sp) false [] _ p An 72); [exact INN | exact FRESHA | cbn; clear; lia | cbn; clear; lia]. }
    pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP3 PARTS3 FROK MU3 WM3 HWL4 CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia)) as HEAP4.
    pose proof (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP [] ls m3 m4 OW1 PL EA _ HEAP3 LS3' MU3 WM3 FROK WOK4) as LS4.
    assert (AXP4 : ax_pres LB (bv_unsigned sp) (XW PL) m m4).
    { eapply ax_pres_trans; [exact AXP3|]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP3 PARTS3 FROK MU3 HWL4 CEIL ltac:(clear - LO'; lia)). }
    lazymatch goal with B : rw_cells bgbsegs m4 An (_ :: _) |- _ => rename B into BLK4 end.
    apply (proj1 (bk_rw_cells_app bgbsegs m4 An [_] _)) in BLK4. destruct BLK4 as [_ BLK2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BLK2.
    apply evt_done.
    eapply implA_step_same.
    { eapply (asan_memset_cpsA) with (d := An) (n := 16) (c := Z_to_bv 8 0) (bd := (p, An, 72)) (lo := lo) (OW := OW1) (LB := LB); try reflexivity.
      - exact HEAP4.
      - rewrite ESP. assumption.
      - exact CEIL.
      - rewrite ESP. unfold RT_STACK. clear - LO'. lia.
      - rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
      - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
      - assumption.
      - exact INN.
      - cbn [blk_addr blk_size fst snd]. clear. lia.
      - clear. lia. }
    intros msM PO. unfold icall_post in PO. rewrite ?ESP in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & mM & -> & MIM & STM & HEAPM & WMM & AGM & BZ & WRM).
    rewrite (ret_pc_even 2257408) by (clear; lia). unfold MallocRep.wz.
    apply (rw_cells_agree _ _ _ _ _ AGM) in FR.
    2:{ intros x Hx. cbn in Hx. split; [left; unfold USTACK_TOP; clear - Hx SPT; lia| unfold BnHeapA.ACEIL in *; clear - Hx BAC CEIL LO'; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGM) in BLK2.
    2:{ intros x Hx. cbn in Hx. split; [right; right; exists (p, An, 72); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hx; lia]| clear - Hx; lia]. }
    assert (PZ : rw_cells bgbsegs mM An [CB 16 (repeat (Z_to_bv 8 0) 16)]).
    { change (Z.to_nat 16) with 16%nat in BZ.
      split; [split; [cbn [cells_wf cell_wf]; rewrite repeat_length; clear; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BZ]|].
      cbn [cells_size csize Nat.add]. exact WRM. }
    assert (LSM : lib_state ls mM OW1 PL EA).
    { eapply (lib_state_h_icall Σ1 LB [] ls m4 mM OW1 PL EA (bv_unsigned sp + -48) (bv_unsigned sp) An 16 HEAP4 LS4 FROK ltac:(clear; lia) AGM).
      eapply (w_foreign OW1 LB ls PL EA (bv_unsigned sp) false [] _ p An 72); [exact INN | exact FRESHA | cbn; clear; lia | cbn; clear; lia]. }
    assert (AXPM : ax_pres LB (bv_unsigned sp) (XW PL) m mM).
    { eapply ax_pres_trans; [exact AXP4|]. eapply (ax_pres_weaken LB (bv_unsigned sp + -48)); [|clear; lia].
      eapply (ax_pres_of_icall Σ1 OW1 LB m4 mM (bv_unsigned sp + -48) (XW PL) An 16 (p, An, 72) HEAP4 INO);
        [cbn [blk_addr blk_size fst snd]; clear; lia| cbn [blk_addr blk_size fst snd]; clear; lia| clear - CEIL LO'; lia| exact AGM]. }
    lazymatch type of BLK2 with rw_cells _ _ _ ?cs => assert (BLKM : rw_cells bgbsegs mM An ([CB 16 (repeat (Z_to_bv 8 0) 16)] ++ cs)) end.
    { apply (proj2 (bk_rw_cells_app bgbsegs mM An [_] _)). split; [exact PZ|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact BLK2. }
    cbn [app] in BLKM.
    destruct (AH_acc _ _ _ _ (p, An, 72) HEAPM INN) as [_ ACCM]. cbn [blk_addr blk_size fst snd] in ACCM.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (An, An + 72)]%Z mM) as MU5. pose proof (wmono_refl bgbsegs mM) as WM5.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LSM) as PARTSM.
    clear BLK2 PZ BZ WRM AGM MU3 WM3 ACCN HEAP3 LS3' ST3 MI3 PARTS3 AXP3 WMM HEAP4 LS4 AXP4 SHB1 SHB2.
    destruct (AH_shb _ _ _ _ HEAPM) as (SHB1 & SHB2).
    apply implA_from_evt.
    do 3 step. shl_with ACCM ALN. chk0. step.
    do 3 step. shl_with ACCM ALN. chk0. step.
    do 3 step. shl_with ACCM ALN. chk0. step. try change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). try store_done.
    do 3 step. shl_with ACCM ALN. chk0. step.
    do 3 step. shl_with ACCM ALN. chk0. step.
    do 3 step. shl_with ACCM ALN. chk0. step. try change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). try store_done.
    step.
    do 5 step. release_frame FR STM (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    apply evt_done. apply implA_ret.
    unfold bn_postA_p. do 17 eexists. exists mF, OW1, (pl_set_ctx PL (Some (An, p))). split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAPM PARTSM FROK MU5 WM5 HWL4 CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|].
    split.
    { eapply (lib_state_place_ctx [] ls mF OW1 PL EA An p); [| exact E| left; reflexivity| exact FRESHA|].
      - eapply (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP); [exact HEAPM| exact LSM| exact MU5| exact WM5| exact FROK| exact WOK4].
      - eapply bk_rw_cells_recast; [eassumption| cbn; repeat split| reflexivity| reflexivity]. }
    split; [exact STM|]. split; [assumption|].
    split. { eapply ax_pres_trans; [exact AXPM|]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAPM PARTSM FROK MU5 HWL4 CEIL ltac:(clear - LO'; lia)). }
    split; [unfold MC in *; clear - CR3; lia|].
    exists An. split; [reflexivity|]. split; [reflexivity|]. split; [unfold BnHeapA.ACEIL in *; clear - BA0 BAC C1 C2 C3; lia|]. split; reflexivity.
Qed.

End WithRT.
