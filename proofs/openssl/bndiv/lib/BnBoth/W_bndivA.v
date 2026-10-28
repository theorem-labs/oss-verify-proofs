(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnTacX BnArith.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA ImplAX BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA W_expandA W_smallA W_topA BnAKitA BnCallA W_callsA AsStruct2 W_lshiftA W_fuzzA W_div_tailA W_divA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit UbStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2434404 => 2
  | 2434408 => 1
  | 2434412 => 2
  | 2434444 => 2
  | 2434476 => 1
  | 2434484 => 2
  | 2434492 => 1
  | 2434496 => 1
  | 2434500 => 1
  | 2434504 => 2
  | 2434508 => 2
  | 2434512 => 1
  | 2434516 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Open Scope Z_scope.


Definition BN_DIV_TOP_STACK : Z := 64 + BN_DIV_FT_STACK.
Definition BN_DIV_TOP_COST : Z := BN_DIV_FT_COST.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_dv_ft := (E_BN_div_24f1b0 : uk_call BN_DIV 0x252608 BN_DIV_FIXED_TOP).

Section Calls.
  Variables (LB : list block) (AD : bn_addrs) (EA : err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z).
  Variables (Σ0 : rts RT) (ls0 : lstate bptr) (OW0 : list block) (m0 : mem).
  Notation CENV := (cenvA LB AD lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0).
  Hypothesis LOFB16 : lo <= FB - 16.

  (* [comment removed for export] *)
  Lemma ctop_callA : forall (POST : machine_state -> Prop) pre used Σ (ls : lstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    CENV pre used Σ ls m OW -> lib_state ls m OW AD EA -> ref_at ls OW AD r ar ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        CENV pre used Σ (setbn r (bn_correct_top_pure (getbn r ls)) ls) m' OW ->
        lib_state (setbn r (bn_correct_top_pure (getbn r ls)) ls) m' OW AD EA ->
        evt bsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                            F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    evt bsegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                        F (Z_to_bv 64 BN_CORRECT_TOP) fc None m (seg_rom bsegs)).
  Proof using LOFB16.
    intros until fc. intros ENV LS HA K.
    pose proof ENV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW).
    pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
    pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] ls m OW AD EA r ar LS ND HA ltac:(intros [])) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    set (b := getbn r ls) in *.
    destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB r D HV ARR) as (U & _ & D0 & DC & DI & SEP). fold b in U, DC, DI, SEP.
    pose proof (SEP r ar HA) as SEPr. clear SEP.
    destruct (ref_at_inb _ _ _ _ _ ADB HA) as (q & A & n & _ & Hin & R1 & R2).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (A0 & _ & _ & AC & AI).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HA) as (ACC & AL & OFR).
    destruct (arr_shA _ _ _ _ _ _ HEAP ARR) as (ACD & ALD & OFD). fold b in ACD, OFD.
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (unfold BnHeapA.ACEIL in *; apply unsigned_lit; lia).
    unfold BN_WORDS_MAX in OK3.
    assert (OK2Z : Z.of_nat (bn_top b) <= Z.of_nat (bn_dmax b)) by (clear - OK2; lia).
    assert (AR0 : 0 < ar) by (clear - A0 R1 R2; lia).
    eapply evt_cut.
    { eapply bn_correct_top_specA with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | exact U | exact OK1 | exact OK2 | lia | rewrite ESP; exact ST | rewrite ESP; lia | exact MI
        | rewrite ESP; left; unfold BnHeapA.ACEIL in *; lia | rewrite ESP; left; unfold BnHeapA.ACEIL in *; lia | exact SEPr
        | exact (AH_shb _ _ _ _ HEAP) | exact ACC | exact AL | exact ACD | exact ALD | unfold SHHI; lia | exact OFR | reflexivity
        | exact AR0 | exact (arr_ub_okA _ _ _ _ _ _ _ HEAP ARR OK2Z)]. }
    intros ms' PO. unfold bn_small_postA in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESP in *.
    assert (U' : u64arr bsegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [left; unfold BnHeapA.ACEIL in *; lia|]. split; [lia| exact I]. }
    eapply (rw_cells_transport bsegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; split; [right; lia|]; split; [right; unfold BnHeapA.ACEIL in *; lia| exact I]].
    assert (WOK : Forall (w_ok OW LB ls AD EA [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst]; lia|].
      constructor; [eapply (w_struct OW LB ls AD EA false [r] _ r ar); [left; reflexivity| exact HA| cbn; lia| cbn; lia]| constructor]. }
    assert (HWL : Forall (w_lib OW lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; lia|]. constructor; [right; exists (q, A, n); cbn; auto| constructor]. }
    assert (LS' : lib_state (setbn r (bn_correct_top_pure b) ls) m' OW AD EA).
    { unfold lib_state. eapply (lib_state_close [] ls m' OW AD EA r ar); [| exact ND | exact HA | | |].
      - exact (lib_state_frame Σ LB [r] ls m m' OW AD EA _ HEAP LSH MUc WMc WOK).
      - exists D. split; [exact RES|]. unfold bn_arr in *. unfold bn_correct_top_pure, bn_dmax in *. cbn [bn_d bn_buf].
        destruct (bn_d b) as [p|]; [split; [exact (proj1 ARR)| exact U'] | exact ARR].
      - destruct (strip_top_spec (bn_buf b) (bn_top b) OK2) as (S1 & _ & _).
        unfold bn_okm, bn_correct_top_pure, bn_dmax, BN_WORDS_MAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [lia|]. split; [exact OK3| exact OK4].
      - apply ids_ok_setbn_same; [exact IDS | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply cenv_setbnA; [| exact HV | reflexivity].
    eapply (cenv_silentA LB AD lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre pre);
      [exact ENV | exact MUc | exact WMc | exact HWL | exact STc | exact MIc | exact FR | exact FSZ].
  Qed.
End Calls.

Lemma BN_div_walkA : BN_div_walkA_stmt BN_DIV_TOP_STACK BN_DIV_TOP_COST.
Proof.
  unfold BN_div_walkA_stmt.
  intros until advs. intros PRE UW CTX -> HAdv HArm HAnum HAdvs -> -> -> -> -> NPdv NPrm NPnum NPdvs NEdn NEdd.
  pose proof PRE as (HEAP & LS & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED).
  pose proof LO as LO'.
  unfold BN_DIV_TOP_STACK, BN_DIV_FT_STACK, BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO.
  unfold BN_DIV_TOP_COST in *. unfold BN_DIV, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, SPT.
  unfold BN_div. rewrite bbind_get.
  set (bd := getbn dvs ls) in *.
  (* [comment removed for export] *)
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (IDS & ADB & ERRB & SOK).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAdvs) as HVdvs.
  destruct (lib_state_open [] ls m OW AD EA dvs advs LS ND HAdvs ltac:(intros [])) as ((Dd & BNd & ARRd) & (OKd1 & OKd2 & OKd3 & OKd4) & _).
  fold bd in BNd, ARRd, OKd1, OKd2, OKd3, OKd4.
  destruct (bn_arr_facts Σ OW LB m HEAP ls AD EA IDS ADB dvs Dd HVdvs ARRd) as (Ud & _ & Dd0 & DdC & DdI & DSEPd).
  fold bd in Ud, DdC, DdI, DSEPd. pose proof (DSEPd dvs advs HAdvs) as SEPd. clear DSEPd.
  destruct (ref_at_inb _ _ _ _ _ ADB HAdvs) as (qd & Ad & nd & _ & Hind & Rd1 & Rd2).
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hind) as (DA0 & _ & _ & DAC & DAI).
  destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP LS HAdvs) as (ACDV & ALDV & OFDV).
  destruct (arr_shA _ _ _ _ _ _ HEAP ARRd) as (ACV & ALV & OFV). fold bd in ACV, OFV.
  destruct (proj1 (limbarr_limbs_at bsegs m Dd (bn_buf bd)) Ud) as (LAd & _).
  unfold BN_WORDS_MAX in OKd3. unfold bn_cells in BNd. unfold MallocRep.wz in BNd. clear Ud.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 80, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  assert (ASD : 0 < advs /\ advs + 24 <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - DA0 Rd1 Rd2 DAC CEIL LO SPR SPT; lia).
  assert (BDD : 0 <= Dd /\ Dd + 8 * Z.of_nat (bn_dmax bd) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dd0 DdC CEIL LO SPR SPT; lia).
  apply implA_from_evt.
  carve_frame 64%nat ST. do 10 (ub; step). do 4 (ub; step). do 3 (ub; step). do 3 (ub; step).
  (* [comment removed for export] *)
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  eapply evt_cut.
  { match goal with STx : stk _ m1 _ _, MIx : mem_inv _ m1 |- _ =>
      eapply BN_is_zero_specA with (lo := lo) (A := advs) (D := Dd) (b := bd);
        [exact BNd | unfold bn_dmax in *; lia | rewrite ESP; exact STx | rewrite ESP; lia | exact MIx | rewrite ESP; left; unfold BnHeapA.ACEIL in *; lia
        | exact (conj SHB1 SHB2) | exact (acc_munch bsegs _ m m1 _ _ ACDV MU OFF ltac:(lia) ltac:(lia)) | exact ALDV | unfold SHHI; lia | exact OFDV | reflexivity
        | exact (proj1 ASD)] end. }
  intros ms' PO. unfold bn_small_postA in PO.
  destruct PO as (? & ? & ? & a0z & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & E & MUc & WMc & MIc & STc & ->).
  subst ms'. rewrite ESP in *.
  fix_ret.
  assert (LAd2 : limbs_at bsegs m2 Dd (bn_buf bd)).
  { eapply limbs_at_transport; [eapply limbs_at_transport; [exact LAd | exact MU |] | exact MUc |];
      cbn [disjoint_from]; fold (bn_dmax bd); (split; [left; unfold BnHeapA.ACEIL in *; lia| exact I]). }
  match goal with STx : stk _ m1 _ _, MIx : mem_inv _ m1 |- _ => clear STx MIx end.
  transport_after_call bsegs m1 m2 MUc WMc. clear MUc WMc.
  apply hide_intro in OFDV. apply hide_intro in OFV. apply hide_intro in DAI. apply hide_intro in DdI. apply hide_intro in SEPd.
  ub; zstep. if_cases KZ; zify_cond KZ.
  2:{ (* [comment removed for export] *)
      apply evt_done.
      replace (bn_top bd =? 0)%nat with true by (destruct (bn_top bd =? 0)%nat; [reflexivity| exfalso; cbn in KZ; rewrite ?unsigned_lit in KZ by lia; lia]).
      unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
  apply Nat.eqb_neq in KZ.
  (* [comment removed for export] *)
  assert (TOPR : 1 <= Z.of_nat (bn_top bd) <= Z.of_nat (bn_dmax bd) /\ Z.of_nat (bn_dmax bd) <= 8388607) by (unfold bn_dmax in *; clear - KZ OKd2 OKd3; lia).
  destruct (arr_ubA Σ OW LB m Dd bd HEAP ARRd ltac:(unfold bn_dmax in *; lia)) as (DPOS & PD16x).
  assert (PD16 : Dd mod 8 = 0) by (clear - PD16x; Z.div_mod_to_equations; lia).
  ub.                                                       (* [comment removed for export] *)
  do 3 (ub; zstep).                                         (* [comment removed for export] *)
  shl_with ACDV ALDV. ub; chk0.                             (* [comment removed for export] *)
  ub; step. rewrite (sx32_small (Z.of_nat (bn_top bd))) by (clear - TOPR; lia).   (* [comment removed for export] *)
  ub; zstep. rewrite (bn_swrap32_small (Z.of_nat (bn_top bd) + -1)) by (clear - TOPR; lia).
  ub.                                                       (* [comment removed for export] *)
  do 2 (ub; zstep).                                         (* [comment removed for export] *)
  shl_with ACDV ALDV. ub; chk0.                             (* [comment removed for export] *)
  ub; step.
  ub; zstep. replace ((Z.of_nat (bn_top bd) + -1) ≪ 3) with (8 * (Z.of_nat (bn_top bd) + -1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  ub; zstep.
  set (dtop := nth (bn_top bd - 1) (bn_buf bd) 0) in *.
  assert (Ntop : nth_error (bn_buf bd) (bn_top bd - 1) = Some dtop) by (apply nth_error_nth'; unfold bn_dmax in *; lia).
  assert (Rdtop : 0 <= dtop < 18446744073709551616).
  { assert (L : limb dtop) by (apply limbs_nth; exact OKd1). unfold limb in L. rewrite BW_lit in L. lia. }

  ub. ub; zstep. ub. ub; zstep. ub.
  do 2 (ub; zstep).                                               (* [comment removed for export] *)
  shl_with ACV ALV. ub; chk0.                                   (* [comment removed for export] *)
  let ad := cur_mem_addr in
    pose proof (limbs_at_read_nth bsegs m2 Dd (bn_buf bd) (bn_top bd - 1) dtop ad LAd2 Ntop ltac:(unfold wa; f_equal; lia)) as RD.
  ub; zstep. clear RD.
  ub; zstep. if_cases KT; zify_cond KT.
  { (* [comment removed for export] *)
    apply evt_done.
    replace (bn_top bd =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact KZ).
    replace (dtop =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite ?unsigned_lit in KT by lia; lia).
    unfold bunr. cbn [unreachable tree_ops]. apply implA_unr. }
  do 5 (ub; zstep). ub; step.
  (* [comment removed for export] *)
  assert (HWL : Forall (w_lib OW lo (bv_unsigned sp)) [(bv_unsigned sp - 80, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls AD EA []) [(bv_unsigned sp - 80, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]).
  pose proof (lib_state_frame Σ LB [] ls m m2 OW AD EA _ HEAP LS MU WM WOK) as LS1.
  match goal with FRx : rw_cells _ m2 (bv_unsigned sp + -64) ?fr, STx : stk _ m2 _ _, MIx : mem_inv _ m2 |- _ =>
    let pre := drop2 fr in
    assert (ENV : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre 0 Σ ls m2 OW);
    [ unfold cenvA, cenv_ok; split; [repeat split; try assumption; try (unfold USTACK_TOP; lia); clear - SP16; Z.div_mod_to_equations; lia|];
      split; [exact (seg_heap _ _ _ _ _ _ _ _ HEAP MU WM HWL CEIL ltac:(unfold USTACK_TOP; lia))|];
      split; [exact STx|]; split; [exact MIx|];
      split; [exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ HEAP MU HWL CEIL ltac:(lia))|];
      split; [lia|]; split; [apply cnt_eq_refl|]; split; [apply refs_stable_refl|];
      split; [cbn [app]; exact FRx|]; split; [cbn; lia|]; unfold uw_opt;
      eapply uw_chain_munch_nw; [exact UW | exact MU |]; constructor; [cbn; lia | constructor]
    | ] end.
  pose proof ENV as (OK & HEAP1 & _).
  apply evt_done.
  replace (bn_top bd =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact KZ).
  replace (dtop =? 0) with false by (symmetry; apply Z.eqb_neq; exact KT).
  unfold bbind at 1. cbn [bind tree_ops].
  eapply implA_bind.
  { eapply (bn_div_fixed_top_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB) (AD := AD) (EA := EA)
             (dv := dv) (rm := rm) (num := num) (dvs := dvs) (adv := adv) (arm := arm) (anum := anum) (advs := advs);
      [| | | reflexivity | exact HAdv | exact HArm | exact HAnum | exact HAdvs | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | exact NPdv | exact NPrm | exact NPnum | exact NPdvs | exact NEdn | exact NEdd | fold bd; lia | fold bd; exact KT].
    - eapply cenv_preA; [exact ENV | exact LS1 | unfold BN_DIV_FT_STACK, BN_LSHIFT_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia | lia].
    - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV).
    - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_dv_ft CTX). }
  cbv beta. intros [u1 ls1] Σ1 ms1 PO.
  apply (bn_postA_cpost LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -64) BN_DIV_FT_COST Σ ls OW) in PO; [| exact OK | exact HEAP1].
  cbn [fst snd] in *.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F1 & fc1 & m3 & OW1 & -> & CP1 & ->).
  lazymatch type of ENV with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre _ _ _ _ _ =>
    assert (E1 : cenvA LB AD lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m pre (0 + BN_DIV_FT_COST) Σ1 ls1 m3 OW1 /\ lib_state ls1 m3 OW1 AD EA)
      by (eapply cenv_postA; [exact ENV | exact CP1]) end.
  destruct E1 as (ENV1 & LS1').
  pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP1) as RS1.
  fix_ret. unfold MallocRep.wz.
  clear CP1.
  (* [comment removed for export] *)
  pose proof (RS1 _ _ HAdv) as HAdv1. pose proof (RS1 _ _ HArm) as HArm1.
  destruct (lib_state_h_parts _ _ _ _ _ _ LS1') as (_ & ADB1 & _ & _).
  destruct (ref_at_inb _ _ _ _ _ ADB1 HAdv1) as (qv & Av & nv & _ & Hinv & Rv1 & Rv2).
  pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENV1)) Hinv) as (VA0 & _ & _ & VAC & _).
  destruct (ref_at_inb _ _ _ _ _ ADB1 HArm1) as (qr & Ar & nr & _ & Hinr & Rr1 & Rr2).
  pose proof (AH_range _ _ _ _ _ _ _ (proj1 (proj2 ENV1)) Hinr) as (RA0 & _ & _ & RAC & _).
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd]. apply implA_ret_evt.
  unfold MallocRep.wz.
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  clear K1.
  zstep. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. unfold BnHeapA.ACEIL in *. lia. }
  clear K2.
  zstep. step.
  eapply (ctop_callA LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m ltac:(clear - LO; lia) _ _ _ Σ1 ls1 m3 OW1 dv adv);
    [exact ENV1 | exact LS1' | exact HAdv1 |].
  intros m4 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 ENV2 LS2.
  fix_ret.
  set (lsa := setbn dv (bn_correct_top_pure (getbn dv ls1)) ls1) in *.
  zstep.
  zstep. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. unfold BnHeapA.ACEIL in *. lia. }
  clear K3.
  zstep. step.
  eapply (ctop_callA LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m ltac:(clear - LO; lia) _ _ _ Σ1 lsa m4 OW1 rm arm);
    [exact ENV2 | exact LS2 | apply ref_at_setbn; exact HArm1 |].
  intros m5 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 ENV3 LS3.
  fix_ret.
  (* [comment removed for export] *)
  pose proof (cenv_finalA LB AD EA lo (bv_unsigned sp) (bv_unsigned sp + -64) s0 ra (Some ras) BN_DIV_FT_COST Σ ls OW m _ _ _ _ _ _ ENV3 LS3 ltac:(lia))
    as (F1' & F2 & F3 & F4 & F5 & F6 & F7).
  env_openA ENV3.
  step.                                                     (* [comment removed for export] *)
  ub; zstep. do 8 (ub; step).
  release_frame FRe STe (bv_unsigned sp). ub; step. ub; step.
  apply evt_done. unfold bn_postA. do 17 eexists. exists m5, OW1. split; [reflexivity|]. cbn [fst snd].
  split; [exact F1'|]. split; [exact F2|]. split; [exact STe|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
  split; [exact F6|]. split; [exact F7|]. reflexivity.
Qed.

End WithRT.
