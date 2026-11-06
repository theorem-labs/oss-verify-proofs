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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgPlace.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctx_getA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_expandAF PlaceKitA PlaceMont ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2254296 => 1
  | 2254300 => 2
  | 2254404 => 2
  | 2254412 => 1
  | 2254416 => 2
  | 2254484 => 1
  | 2254488 => 2
  | 2254664 => 1
  | 2254668 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Definition BN_MONT_CTX_NEW : Z := 0x226590.
Definition BN_MONT_CTX_INIT : Z := 0x22662c.
Definition BN_MONT_CTX_FREE : Z := 0x226728.
Definition BN_MONT_CTX_NEW_STACK : Z := 32 + CRYPTO_MALLOC_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Ltac strip2 l := lazymatch l with
  | cons _ (cons _ nil) => constr:(@nil cell)
  | cons ?x ?t => let r := strip2 t in constr:(cons x r)
  end.

Lemma BN_MONT_CTX_new_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_MONT_CTX_NEW_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_MONT_CTX_NEW (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> pl_mont PL = None ->
  implA (BN_MONT_CTX_new (tree_ops bptr) ls) Σ
    (bn_postA_p ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
                (fun p ls' OW' PL' a0' => exists a, PL' = pl_set_mont PL (Some (a, p)) /\ a0' = wz a /\ 0 < a < 2^63
                                          /\ OW' = (p, a, 96) :: OW /\ ls' = st_mont_init ls))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_MONT_CTX_NEW) fc None m (seg_rom bgbsegs)).
Proof.
  intros until ras. intros PRE UW CTX -> E.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof LO as LO'. unfold BN_MONT_CTX_NEW_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_MONT_CTX_NEW, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  unfold BN_MONT_CTX_new, bbind, bmalloc, bsetmont, bset, bret. cbn [bind ret unreachable lib_malloc tree_ops tbind fst snd].
  apply implA_from_evt.
  carve_frame 32%nat ST.
  do 6 step. do 3 step. do 4 step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (ESPI : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -32, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia)) as HEAP1.
  pose proof (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU HWL CEIL ltac:(lia)) as AXP1.
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -32) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
      apply (uw_push_frame m1 _ (bv_unsigned sp) 32 p (bv_unsigned ra) (bv_unsigned s0) ras) end;
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  rename FR into FRN.
  apply evt_done.
  eapply (CRYPTO_malloc_walkA) with (n := 96) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
  - exact HEAP1.
  - rewrite ESP. exact ST.
  - exact CEIL.
  - rewrite ESP. unfold CRYPTO_MALLOC_STACK, RT_STACK. clear - LO'. lia.
  - rewrite ESP. unfold USTACK_TOP. clear - SPT. lia.
  - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
  - exact MI.
  - exact (proj1 LS1).
  - clear. lia.
  - pose proof (cnt_ok_live ls OW LB OW 0 WFS CNT ltac:(lia) ltac:(lia)) as HL. rewrite length_map in HL. exact HL.
  - exact CRED.
  - rewrite ESP. exact UW1.
  - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_MONT_CTX_new_2263e0 CTX).
  - intros p Σ1 ms1 FRESH PO.
    unfold calloc_postA in PO. rewrite ?ESP in PO.
    destruct PO as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & F1 & fc1 & m3 & An & -> & MI3 & ST3 & AG3 & CR3 & BR & HEAP3 & ACCN & (jb & BLK)).
    rewrite (ret_pc_even 2254280) by (clear; lia).
    apply (rw_cells_agree _ _ _ _ _ AG3) in FRN; [| intros x Hx; left; cbn in Hx; unfold USTACK_TOP; clear - Hx SPT; lia].
    assert (LS3 : lib_state ls m3 OW PL EA).
    { eapply (lib_state_h_heap_pres _ _ _ _ _ _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp) USTACK_TOP); [exact LS1| exact FROK| clear; lia| clear; lia| exact AG3| | lb_in_heap]. intros b0 Hb0. apply in_or_app. left. exact Hb0. }
    assert (AXP3 : ax_pres LB (bv_unsigned sp) (XW PL) m m3).
    { eapply ax_pres_trans; [exact AXP1|]. eapply agree_on_mono; [exact AG3|]. intros x [_ [Hx|[Hx|(b0 & Hb0 & Hr)]]];
        [left; clear - Hx; lia | right; left; exact Hx | right; right; exists b0; split; [apply in_or_app; right; exact Hb0 | exact Hr]]. }
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI).
    assert (FRESHA : ~ In p (all_ids ls PL EA)).
    { intros Hin. apply FRESH. rewrite map_app. apply in_or_app. left. eapply all_ids_owned; eauto. }
    set (OW1 := (p, An, 96) :: OW) in *.
    assert (LS3' : lib_state ls m3 OW1 PL EA) by (eapply lib_state_h_ow; [exact LS3|]; intros q A0 n0 _ Hq; right; exact Hq).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS3') as PARTS3.
    assert (ALN : An mod 8 = 0) by (clear - BA16; Z.div_mod_to_equations; lia).
    assert (INN : In (p, An, 96) (OW1 ++ LB)) by (left; reflexivity).
    assert (INO : In (p, An, 96) OW1) by (left; reflexivity).
    pose proof (AH_offsh _ _ _ _ (p, An, 96) HEAP3 INN) as OFN. cbn [blk_addr blk_size fst snd] in OFN. unfold SHLO, SHHI in OFN.
    assert (EAn : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - BA0 BAC C1 C2 C3; lia).

    change (Z.to_nat 96) with 96%nat in BLK.
    apply (rw_cells_split_CB bgbsegs _ _ [] 96 _ [] [24; 24; 24; 16; 4; 4]%nat) in BLK; [| reflexivity]. cbn [mk_CB_cells app firstn skipn] in BLK.
    apply (proj1 (bk_rw_cells_app bgbsegs m3 An [_] _)) in BLK. destruct BLK as [B0 BLK]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BLK.
    apply (proj1 (bk_rw_cells_app bgbsegs m3 _ [_] _)) in BLK. destruct BLK as [B1 BLK]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BLK.
    apply (proj1 (bk_rw_cells_app bgbsegs m3 _ [_] _)) in BLK. destruct BLK as [B2 BLK]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BLK.
    apply (proj1 (bk_rw_cells_app bgbsegs m3 _ [_] _)) in BLK. destruct BLK as [B3 BLK]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BLK.
    apply (proj1 (bk_rw_cells_app bgbsegs m3 _ [_] _)) in BLK. destruct BLK as [B4 B5]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B5.
    change (Z.of_nat 24) with 24 in *.
    replace (An + 24 + 24) with (An + 48) in * by (clear; lia). replace (An + 48 + 24) with (An + 72) in * by (clear; lia).
    replace (An + 72 + 16) with (An + 88) in * by (clear; lia). replace (An + 88 + 4) with (An + 92) in * by (clear; lia).
    clear MU WM HEAP LS HEAP1 LS1 LS3 ST MI SHB1 SHB2 HWL WOK AG3 PARTS.
    destruct (AH_shb _ _ _ _ HEAP3) as (SHB1 & SHB2).
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp + -32); (An, An + 96)]%Z m3) as MU3. pose proof (wmono_refl bgbsegs m3) as WM3.
    assert (OFF3 : offshW [(bv_unsigned sp + -64, bv_unsigned sp + -32); (An, An + 96)]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFN SPR LO' CEIL C1 C2 C3. lia. }
    unfold MallocRep.wz.
    apply implA_from_evt.
    step.
    step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EAn in KA; clear - KA BA0; lia|]. clear KA.
    step. step.

    remember (Z_to_bv 64 2254296) as raI eqn:EraI.

    carve_frame 32%nat ST3.
    do 6 step. hide_ors. ub. unhide. step. hide_ors. ub. unhide. do 3 step.
    do 3 step. shl_with ACCN ALN. chk0.
    step. try change (Z_to_le_bytes 4 (bv_unsigned (low32 (Z_to_bv 64 0)))) with (le4 (Z_to_bv 64 0)). try store_done.
    step. step.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HWL3 : Forall (w_lib ls OW1 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -64, bv_unsigned sp + -32); (An, An + 96)]).
    { constructor; [left; cbn; clear - LO'; lia|]. constructor; [|constructor].
      right; left. exists (p, An, 96). cbn [blk_addr blk_size fst snd]. split; [left; reflexivity | clear; lia]. }
    assert (WOK3 : Forall (w_ok OW1 LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -64, bv_unsigned sp + -32); (An, An + 96)]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia|]. constructor; [|constructor].
      eapply (w_foreign OW1 LB ls PL EA (bv_unsigned sp) false [] _ p An 96); [first [eassumption | left; reflexivity | right; eassumption] | exact FRESHA | cbn; clear; lia | cbn; clear; lia]. }
    pose proof (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP3 PARTS3 FROK MU3 WM3 HWL3 CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia)) as HEAP4.
    pose proof (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP [] ls m3 m4 OW1 PL EA _ HEAP3 LS3' MU3 WM3 FROK WOK3) as LS4.
    assert (AXP4 : ax_pres LB (bv_unsigned sp) (XW PL) m m4).
    { eapply ax_pres_trans; [exact AXP3|]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP3 PARTS3 FROK MU3 HWL3 CEIL ltac:(clear - LO'; lia)). }
    clear HEAP3 LS3' AXP3 MU3 WM3 OFF3 ACCN SHB1 SHB2 PARTS3. rename MI3 into MIc. rename ST3 into STc.

    apply evt_done.
    eapply implA_step_same.
    { eapply (bn_init_cpsA) with (A := An) (bd := (p, An, 96)) (lo := lo) (OW := OW1) (LB := LB); try reflexivity;
        [exact HEAP4 | rewrite ESPI; exact STc | exact CEIL | rewrite ESPI; unfold BN_INIT_STACK, RT_STACK; clear - LO'; lia
        | rewrite ESPI; unfold USTACK_TOP; clear - SPT; lia | rewrite ESPI; clear - SP16; Z.div_mod_to_equations; lia | exact MIc | exact INN
        | cbn [blk_addr blk_size fst snd]; clear; lia ..]. }
    intros msK PO. unfold icall_post in PO. rewrite ?ESPI in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & -> & MIk & STk & HEAP5 & WMk & AGk & BN0).
    rewrite (ret_pc_even 2254464) by (clear; lia). unfold MallocRep.wz.
    apply (rw_cells_agree _ _ _ _ _ AGk) in FRN.
    2:{ intros xq Hxq. cbn in Hxq. split; [left; unfold USTACK_TOP; clear - Hxq SPT; lia| unfold BnHeapA.ACEIL in *; clear - Hxq BAC CEIL LO'; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in FR.
    2:{ intros xq Hxq. cbn in Hxq. split; [left; unfold USTACK_TOP; clear - Hxq SPT; lia| unfold BnHeapA.ACEIL in *; clear - Hxq BAC CEIL LO'; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B1.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B2.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B3.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B4.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B5.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    assert (LS5 : lib_state ls m5 OW1 PL EA).
    { eapply (lib_state_h_icall Σ1 LB [] ls m4 m5 OW1 PL EA (bv_unsigned sp + -64) (bv_unsigned sp) An 24 HEAP4 LS4 FROK ltac:(clear; lia) AGk).
      eapply (w_foreign OW1 LB ls PL EA (bv_unsigned sp) false [] _ p An 96); [first [eassumption | left; reflexivity | right; eassumption] | exact FRESHA | cbn; clear; lia | cbn; clear; lia]. }
    assert (AXP5 : ax_pres LB (bv_unsigned sp) (XW PL) m m5).
    { eapply ax_pres_trans; [exact AXP4|]. eapply (ax_pres_weaken LB (bv_unsigned sp + -64)); [|clear; lia].
      eapply (ax_pres_of_icall Σ1 OW1 LB m4 m5 (bv_unsigned sp + -64) (XW PL) An 24 (p, An, 96) HEAP4 INO);
        [cbn [blk_addr blk_size fst snd]; clear; lia| cbn [blk_addr blk_size fst snd]; clear; lia| clear - CEIL LO'; lia| exact AGk]. }
    clear HEAP4 LS4 AXP4 AGk WMk. clear MIc STc. rename MIk into MIc. rename STk into STc.
    clear B0. rename BN0 into B0. unfold BnRepDefs.bn_cells, bn_nil, MallocRep.wz in B0. cbn [bn_top bn_buf bn_neg bn_flags bn_d length Z.b2z Z.of_nat] in B0.

    apply implA_from_evt. step. step.
    apply evt_done.
    eapply implA_step_same.
    { eapply (bn_init_cpsA) with (A := An + 24) (bd := (p, An, 96)) (lo := lo) (OW := OW1) (LB := LB); try reflexivity;
        [exact HEAP5 | rewrite ESPI; exact STc | exact CEIL | rewrite ESPI; unfold BN_INIT_STACK, RT_STACK; clear - LO'; lia
        | rewrite ESPI; unfold USTACK_TOP; clear - SPT; lia | rewrite ESPI; clear - SP16; Z.div_mod_to_equations; lia | exact MIc | exact INN
        | cbn [blk_addr blk_size fst snd]; clear; lia ..]. }
    intros msK PO. unfold icall_post in PO. rewrite ?ESPI in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & -> & MIk & STk & HEAP6 & WMk & AGk & BN1).
    rewrite (ret_pc_even 2254472) by (clear; lia). unfold MallocRep.wz.
    apply (rw_cells_agree _ _ _ _ _ AGk) in FRN.
    2:{ intros xq Hxq. cbn in Hxq. split; [left; unfold USTACK_TOP; clear - Hxq SPT; lia| unfold BnHeapA.ACEIL in *; clear - Hxq BAC CEIL LO'; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in FR.
    2:{ intros xq Hxq. cbn in Hxq. split; [left; unfold USTACK_TOP; clear - Hxq SPT; lia| unfold BnHeapA.ACEIL in *; clear - Hxq BAC CEIL LO'; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B0.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B2.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B3.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B4.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B5.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    assert (LS6 : lib_state ls m6 OW1 PL EA).
    { eapply (lib_state_h_icall Σ1 LB [] ls m5 m6 OW1 PL EA (bv_unsigned sp + -64) (bv_unsigned sp) (An + 24) 24 HEAP5 LS5 FROK ltac:(clear; lia) AGk).
      eapply (w_foreign OW1 LB ls PL EA (bv_unsigned sp) false [] _ p An 96); [first [eassumption | left; reflexivity | right; eassumption] | exact FRESHA | cbn; clear; lia | cbn; clear; lia]. }
    assert (AXP6 : ax_pres LB (bv_unsigned sp) (XW PL) m m6).
    { eapply ax_pres_trans; [exact AXP5|]. eapply (ax_pres_weaken LB (bv_unsigned sp + -64)); [|clear; lia].
      eapply (ax_pres_of_icall Σ1 OW1 LB m5 m6 (bv_unsigned sp + -64) (XW PL) (An + 24) 24 (p, An, 96) HEAP5 INO);
        [cbn [blk_addr blk_size fst snd]; clear; lia| cbn [blk_addr blk_size fst snd]; clear; lia| clear - CEIL LO'; lia| exact AGk]. }
    clear HEAP5 LS5 AXP5 AGk WMk. clear MIc STc. rename MIk into MIc. rename STk into STc.
    clear B1. rename BN1 into B1. unfold BnRepDefs.bn_cells, bn_nil, MallocRep.wz in B1. cbn [bn_top bn_buf bn_neg bn_flags bn_d length Z.b2z Z.of_nat] in B1.

    apply implA_from_evt. step. step.
    apply evt_done.
    eapply implA_step_same.
    { eapply (bn_init_cpsA) with (A := An + 48) (bd := (p, An, 96)) (lo := lo) (OW := OW1) (LB := LB); try reflexivity;
        [exact HEAP6 | rewrite ESPI; exact STc | exact CEIL | rewrite ESPI; unfold BN_INIT_STACK, RT_STACK; clear - LO'; lia
        | rewrite ESPI; unfold USTACK_TOP; clear - SPT; lia | rewrite ESPI; clear - SP16; Z.div_mod_to_equations; lia | exact MIc | exact INN
        | cbn [blk_addr blk_size fst snd]; clear; lia ..]. }
    intros msK PO. unfold icall_post in PO. rewrite ?ESPI in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & -> & MIk & STk & HEAP7 & WMk & AGk & BN2).
    rewrite (ret_pc_even 2254480) by (clear; lia). unfold MallocRep.wz.
    apply (rw_cells_agree _ _ _ _ _ AGk) in FRN.
    2:{ intros xq Hxq. cbn in Hxq. split; [left; unfold USTACK_TOP; clear - Hxq SPT; lia| unfold BnHeapA.ACEIL in *; clear - Hxq BAC CEIL LO'; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in FR.
    2:{ intros xq Hxq. cbn in Hxq. split; [left; unfold USTACK_TOP; clear - Hxq SPT; lia| unfold BnHeapA.ACEIL in *; clear - Hxq BAC CEIL LO'; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B0.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B1.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B3.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B4.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGk) in B5.
    2:{ intros xq Hxq. cbn in Hxq. split; [right; right; exists (p, An, 96); split; [exact INN| cbn [blk_addr blk_size fst snd]; clear - Hxq; lia]| clear - Hxq; lia]. }
    assert (LS7 : lib_state ls m7 OW1 PL EA).
    { eapply (lib_state_h_icall Σ1 LB [] ls m6 m7 OW1 PL EA (bv_unsigned sp + -64) (bv_unsigned sp) (An + 48) 24 HEAP6 LS6 FROK ltac:(clear; lia) AGk).
      eapply (w_foreign OW1 LB ls PL EA (bv_unsigned sp) false [] _ p An 96); [first [eassumption | left; reflexivity | right; eassumption] | exact FRESHA | cbn; clear; lia | cbn; clear; lia]. }
    assert (AXP7 : ax_pres LB (bv_unsigned sp) (XW PL) m m7).
    { eapply ax_pres_trans; [exact AXP6|]. eapply (ax_pres_weaken LB (bv_unsigned sp + -64)); [|clear; lia].
      eapply (ax_pres_of_icall Σ1 OW1 LB m6 m7 (bv_unsigned sp + -64) (XW PL) (An + 48) 24 (p, An, 96) HEAP6 INO);
        [cbn [blk_addr blk_size fst snd]; clear; lia| cbn [blk_addr blk_size fst snd]; clear; lia| clear - CEIL LO'; lia| exact AGk]. }
    clear HEAP6 LS6 AXP6 AGk WMk. clear MIc STc. rename MIk into MIc. rename STk into STc.
    clear B2. rename BN2 into B2. unfold BnRepDefs.bn_cells, bn_nil, MallocRep.wz in B2. cbn [bn_top bn_buf bn_neg bn_flags bn_d length Z.b2z Z.of_nat] in B2.

    destruct (AH_acc _ _ _ _ (p, An, 96) HEAP7 INN) as [_ ACC7]. cbn [blk_addr blk_size fst snd] in ACC7.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS7) as PARTS7.
    pose proof (munch_refl [(An, An + 96)]%Z m7) as MU7. pose proof (wmono_refl bgbsegs m7) as WM7.
    assert (OFF7 : offshW [(An, An + 96)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; clear - OFN; lia).
    apply (rw_cells_split_CB bgbsegs _ _ [] 16 _ [] [8; 8]%nat) in B3; [| reflexivity]. cbn [mk_CB_cells app firstn skipn] in B3.
    apply (proj1 (bk_rw_cells_app bgbsegs m7 _ [_] _)) in B3. destruct B3 as [B3a B3b]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B3b.
    replace (An + 72 + 8) with (An + 80) in B3b by (clear; lia).
    assert (ANR : An + 96 < 2^47) by (unfold BnHeapA.ACEIL in *; clear - BAC C1 C2 C3; lia).
    apply implA_from_evt.
    step. hide_ors. ub. unhide.
    do 3 step. shl_with ACC7 ALN. chk0.
    step. try change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). try store_done.
    do 2 step. shl_with ACC7 ALN. chk0.
    step. try change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). try store_done.
    do 3 step. shl_with ACC7 ALN. chk0.
    step. try change (Z_to_le_bytes 4 (bv_unsigned (low32 (Z_to_bv 64 0)))) with (le4 (Z_to_bv 64 0)). try store_done.
    do 4 step. release_frame FR STc (bv_unsigned sp + -32). step. subst raI. step.
    hide_ors. ub. unhide.
    do 3 step. shl_with ACC7 ALN. chk0.
    step.
    step. try change (Z_to_le_bytes 4 (bv_unsigned (low32 (Z_to_bv 64 1)))) with (le4 (Z_to_bv 64 1)). try store_done.
    step.
    do 4 step. release_frame FRN STc (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    apply evt_done. apply implA_ret.
    assert (HWL9 : Forall (w_lib ls OW1 PL lo (bv_unsigned sp)) [(An, An + 96)]).
    { constructor; [|constructor]. right; left. exists (p, An, 96). cbn [blk_addr blk_size fst snd]. split; [left; reflexivity | clear; lia]. }
    assert (WOK9 : Forall (w_ok OW1 LB ls PL EA (bv_unsigned sp) []) [(An, An + 96)]).
    { constructor; [|constructor]. eapply (w_foreign OW1 LB ls PL EA (bv_unsigned sp) false [] _ p An 96); [first [eassumption | left; reflexivity | right; eassumption] | exact FRESHA | cbn; clear; lia | cbn; clear; lia]. }
    unfold bn_postA_p. do 17 eexists. exists mF, OW1, (pl_set_mont PL (Some (An, p))). split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP7 PARTS7 FROK MU7 WM7 HWL9 CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|].
    split.
    { eapply (lib_state_place_mont false [] ls mF OW1 PL EA An p); [| exact E| left; reflexivity| exact FRESHA| exact B0| exact B1| exact B2|].
      - eapply (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP); [exact HEAP7| exact LS7| exact MU7| exact WM7| exact FROK| exact WOK9].
      - assert (B345 : rw_cells bgbsegs mF (An + 72) ([C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 1)])).
        { apply (proj2 (bk_rw_cells_app bgbsegs mF (An + 72) [_] _)). split; [exact B3a|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
          replace (An + 72 + 8) with (An + 80) by (clear; lia).
          apply (proj2 (bk_rw_cells_app bgbsegs mF (An + 80) [_] _)). split; [exact B3b|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
          replace (An + 80 + 8) with (An + 88) by (clear; lia).
          apply (proj2 (bk_rw_cells_app bgbsegs mF (An + 88) [_] _)). split; [exact B4|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
          replace (An + 88 + 4) with (An + 92) by (clear; lia). exact B5. }
        eapply bk_rw_cells_recast; [exact B345 | cbn; repeat split | reflexivity | reflexivity]. }
    split; [exact STc|]. split; [assumption|].
    split. { eapply ax_pres_trans; [exact AXP7|]. exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP7 PARTS7 FROK MU7 HWL9 CEIL ltac:(clear - LO'; lia)). }
    split; [unfold MC in *; clear - CR3; lia|].
    exists An. split; [reflexivity|]. split; [reflexivity|]. split; [unfold BnHeapA.ACEIL in *; clear - BA0 BAC C1 C2 C3; lia|]. split; reflexivity.
Qed.

End WithRT.
