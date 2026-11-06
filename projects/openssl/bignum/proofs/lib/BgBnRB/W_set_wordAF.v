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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require W_rshift.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR2 Require W_set_word.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_expandAF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import UbStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2240740 => 2
  | 2240748 => 1
  | 2240752 => 2
  | 2240860 => 2
  | 2240864 => 1
  | 2240868 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Definition BN_SET_WORD : Z := 0x2230c8.
Definition BN_SET_WORD_STACK : Z := 48 + BN_EXPAND2_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Local Notation set_word_bn := OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_word.set_word_bn.

Lemma BN_set_word_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rx : bnref) (ax w : Z),
  bn_preA Σ ls m OW LB PL EA sp lo BN_SET_WORD_STACK MC ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_SET_WORD (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rx ax -> wref PL rx -> a0 = wz ax -> a1 = wz w -> 0 <= w < 2^64 ->
  implA (BN_set_word (tree_ops bptr) rx w ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
              (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = wz 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_SET_WORD) fc None m (seg_rom bgbsegs)).
Proof.
  intros until w. intros PRE UW CTX -> HAx WRx -> -> HW.
  pose proof (proj1 WRx : not_one rx) as NROx.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof LO as LO'. unfold BN_SET_WORD_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_SET_WORD, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  change (2 ^ 64) with 18446744073709551616 in HW.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  destruct (open_ro_sh Σ OW LB m ls PL EA _ rx ax HEAP LS FROK NOFR HAx NROx) as (Dx & BNx & (OKx1 & OKx2 & OKx3 & OKx4) & _ & X0 & XC & _ & _ & ACX & ALX & _ & _).
  set (bx := getbn rx ls) in *.
  unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNx. unfold BN_WORDS_MAX, BG_DMAX in OKx3.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 48, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
  unfold BN_set_word, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
  apply implA_from_evt.
  carve_frame 48%nat ST.
  do 7 step. ub. step. ub. step. do 3 step. do 3 step. shl_with ACX ALX. chk0.
  step. rewrite (sx32_small (Z.of_nat (bn_dmax bx))) by (unfold bn_dmax in *; lia).
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (jfr := j) in *; clearbody jfr end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -48, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  assert (EV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) MC Σ ls OW m [CB 8 jfr; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
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

  assert (FIN : forall (Σ1 : rts RT) (ls1 : bstate bptr) (m2 : mem) (OW2 : list block) (used : Z) (FT : bvmap 5 word) (fcT : bv 32)
                       (q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
      cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) MC Σ ls OW m [CB 8 jfr; C8 s3; C8 s2; C8 s1] used Σ1 ls1 m2 OW2 ->
      lib_state ls1 m2 OW2 PL EA -> used <= MC ->
      (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW2) ->
      ref_at ls1 OW2 PL rx ax -> (1 <= bn_dmax (getbn rx ls1))%nat ->
      implA (TRet (tt, setbn rx (set_word_bn (getbn rx ls1) w) ls1)) Σ1
        (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA MC
                  (fun _ _ OW' PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1 /\ (forall q A n, In (q, A, n) OW -> bn_d (getbn rx ls) <> Some q -> In (q, A, n) OW')))
        (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 TP_A) q5 q6 q7 sp (Z_to_bv 64 w) q10 q11 q12 q13 q14 q15 q16 q17
                 (Z_to_bv 64 ax) (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
            FT (Z_to_bv 64 0x223130) fcT None m2 (seg_rom bgbsegs))).
  { intros Σ1 ls1 m2 OW2 used FT fcT q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 EV1 LS2 USED BST HAx2 HDM.
    clear BNx MU WM ST MI FR HWL WOK LS1 HEAP1 EV OK ACX OFF SHB1 SHB2 Dx HEAP LS PARTS PRE UW ND HVx C1 C2 C3 OKx1 OKx2 OKx3 OKx4.
    pose proof EV1 as (OK1 & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
    cbn [app] in FR2.
    pose proof (AH_nodup_l _ _ _ _ HEAP2) as ND2.
    pose proof (AH_ceil _ _ _ _ HEAP2) as (C1' & C2' & C3'). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2; pose proof PARTS2 as (WFS2 & PWF2 & IDS2 & PLB2 & ERRB2).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.
    destruct (lib_state_open [] ls1 m2 OW2 PL EA rx ax LS2 ND2 HAx2 ltac:(intros []) NROx) as ((Dr & BNr & ARRr) & (OKq1 & OKq2 & OKq3 & OKq4) & LSH).
    destruct (bn_arr_facts_w ls1 OW2 PL EA (bv_unsigned sp) USTACK_TOP Σ1 LB m2 rx Dr HEAP2 PARTS2 FROK HVx2 WRx ARRr) as (Ur & LENr & Dr0 & DrC & DrI & DSEPr).
    set (br := getbn rx ls1) in *.
    pose proof (DSEPr rx ax HAx2) as SEPrr. fold br in SEPrr.
    destruct (ref_at_inbA _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 NOFR HAx2 NROx) as (qr2 & Ar2 & nr2 & Hinr2 & Rr21 & Rr22).
    pose proof (AH_range_in _ _ _ _ _ _ _ HEAP2 Hinr2) as (SA0 & _ & _ & SAC & _).
    destruct (ref_shA _ _ _ _ _ _ _ _ _ _ _ HEAP2 LS2 NOFR HAx2 NROx) as (ACR & ALR & OFR).
    pose proof ARRr as ARRo. apply (fun ARRnb__ => bn_arr_nofr PL rx m2 OW2 Dr _ PWF2 NOFR NROx ARRnb__ ltac:(solve_nbuf)) in ARRo.
    destruct (arr_shA _ _ _ _ _ _ HEAP2 ARRo) as (ACDR & ALDR & OFDR). fold br in ACDR, OFDR.
    unfold bn_cells, BnRepDefs.bn_cells in BNr. unfold BG_DMAX in OKq3. unfold MallocRep.wz in *. unfold SHLO, SHHI in *.
    apply implA_ret_evt.

    assert (HDr : exists pr, bn_d br = Some pr /\ In (pr, Dr, 8 * Z.of_nat (bn_dmax br)) OW2).
    { unfold BnRepDefs.bn_arr in ARRo. fold br in ARRo. destruct (bn_d br) as [pr|]; [exists pr; split; [reflexivity| exact (proj1 ARRo)]|].
      exfalso. destruct ARRo as [_ E]. unfold bn_dmax in HDM. fold br in HDM. rewrite E in HDM. cbn in HDM. clear - HDM. lia. }
    destruct HDr as (pr & Edr & Hinpr).
    assert (LBR : length (bn_buf br) = bn_dmax br) by reflexivity.
    fold br in HDM.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]%Z m2) as MU3.
    pose proof (wmono_refl bgbsegs m2) as WM3.
    assert (OFF3 : offshW [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFR OFDR SPR LO' CEIL C1' C2' C3'. lia. }
    assert (BDR : 0 <= Dr /\ Dr + 8 * Z.of_nat (bn_dmax br) <= 140737488355328) by (unfold BnHeapA.ACEIL in *; clear - Dr0 DrC C1' C2' C3'; lia).
    assert (HDMZ : 1 <= Z.of_nat (bn_dmax br)) by (clear - HDM; lia).
    assert (LENW : Z.of_nat (length (wlimbs (bn_buf br))) = Z.of_nat (bn_dmax br)) by (rewrite wlimbs_len; reflexivity).
    clear DSEPr DrI OFR OFDR.

    do 3 step. shl_with ACR ALR. chk0.
    step.

    do 2 step. shl_with ACR ALR. chk0.
    step.
    assert (PR0 : 0 < Dr) by (pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinpr) as (P0 & _); exact P0).
    hide_ors. ub. unhide.
    do 2 step. shl_limb ACDR ALDR BDR 0. chk0.
    assert (IDX : 0 <= 0 < Z.of_nat (length (wlimbs (bn_buf br)))) by (rewrite wlimbs_len, LBR; clear - HDM; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u64arr_store_ok bgbsegs mx Dr _ 0 (wa (Dr + 8 * 0)) ltac:(eassumption) IDX eq_refl) as SOKW;
      pose proof (u64arr_write bgbsegs mx Dr _ 0 (Z_to_bv 64 w) ltac:(eassumption) IDX) as U2 end.
    replace (Dr + 8 * 0) with Dr in SOKW, U2 by (clear; lia). change (Z.to_nat 0) with 0%nat in U2.
    clear Ur. step. store_done.

    do 3 step. shl_with ACR ALR. chk0.
    step. step.
    rewrite v_sltu_b2z, !unsigned_lit in BNr by (clear - HW; lia).
    assert (ETOP : Z.b2z (0 <? w) = Z.of_nat (if w =? 0 then 0%nat else 1%nat)).
    { destruct (Z.ltb_spec 0 w); destruct (Z.eqb_spec w 0); cbn; lia. }
    rewrite ETOP in BNr.
    step. do 5 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mG end.
    apply evt_done.
    set (nb := upd (bn_buf br) 0 w).
    assert (Lnb : length nb = bn_dmax br) by (subst nb; rewrite upd_length by (clear - HDM LBR; lia); exact LBR).
    assert (LMnb : limbs nb) by (subst nb; apply upd_limbs; [exact OKq1| unfold limb, BW; exact HW]).
    assert (UF : u64arr bgbsegs mG Dr (wlimbs nb)).
    { subst nb. lazymatch goal with U : u64arr bgbsegs mG Dr ?l |- _ => replace (wlimbs (upd (bn_buf br) 0 w)) with l; [exact U|] end.
      unfold upd, splice, wlimbs. cbn [firstn app length Nat.add]. destruct (bn_buf br) as [|b0 bt] eqn:Ebuf; [cbn in LBR; clear - LBR HDM; lia|].
      cbn [skipn map Arr.upd Z.to_nat]. reflexivity. }
    assert (HWL3 : Forall (w_lib ls1 OW2 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
    { constructor; [left; cbn; clear - LO'; lia|]. constructor; [w_lib_ref HAx2 NROx|].
      constructor; [right; left; exists (pr, Dr, 8 * Z.of_nat (bn_dmax br)); cbn [blk_addr blk_size fst snd]; split; [exact Hinpr| clear; lia]| constructor]. }
    assert (WOK3 : Forall (w_ok OW2 LB ls1 PL EA (bv_unsigned sp) [rx]) [(bv_unsigned sp + -48, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax br))]).
    { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; clear - LO' CEIL; lia|].
      constructor; [eapply (w_struct OW2 LB ls1 PL EA (bv_unsigned sp) false [rx] _ rx ax); [left; reflexivity| exact HAx2| exact NROx| cbn; clear; lia| cbn; clear; lia]|].
      constructor; [eapply (w_limbs OW2 LB ls1 PL EA (bv_unsigned sp) false [rx] _ rx pr Dr); [left; reflexivity| exact HVx2| exact Edr| exact Hinpr| cbn [fst snd]; clear; lia| cbn [fst snd]; fold br; clear; lia]| constructor]. }
    unfold bn_postA. do 17 eexists. exists mG, OW2, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK MU3 WM3 HWL3 CEIL ltac:(unfold USTACK_TOP; clear - SPT; lia))|].
    split.
    { unfold lib_state. eapply (lib_state_close [] ls1 mG OW2 PL EA rx ax); [| exact ND2| exact HAx2| exact NROx| | |].
      - eapply (lib_state_frame Σ1 LB (bv_unsigned sp) USTACK_TOP); [exact HEAP2| exact LSH| exact MU3| exact WM3| exact FROK| exact WOK3].
      - exists Dr. split.
        + unfold bn_cells, BnRepDefs.bn_cells, bn_dmax, set_word_bn, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_word.set_word_bn, MallocRep.wz. cbn [bn_top bn_buf bn_neg bn_flags bn_d Z.b2z]. fold br nb. rewrite Lnb. exact BNr.
        + apply (fun ARRnb__ => bn_arr_of_nofr PL rx mG OW2 Dr _ PWF2 NOFR NROx ARRnb__ ltac:(solve_nbuf)). unfold BnRepDefs.bn_arr, bn_dmax, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_word.set_word_bn. cbn [bn_d bn_buf]. fold br nb. rewrite Edr, Lnb. split; [exact Hinpr| exact UF].
      - unfold bg_ok, bn_dmax, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_word.set_word_bn. cbn [bn_buf bn_top bn_flags]. fold br nb. rewrite Lnb. unfold BG_DMAX in *.
        split; [exact LMnb|]. split; [destruct (w =? 0); clear - HDM; lia|]. split; [clear - OKq3; unfold bn_dmax in *; lia| exact OKq4].
      - apply ids_ok_setbn_same; [exact IDS2| exact HVx2|]. unfold bn_blocks, bn_dmax, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_word.set_word_bn. cbn [bn_d bn_buf]. fold br nb. rewrite Lnb. reflexivity. }
    split; [exact ST2|]. split; [assumption|].
    split; [eapply ax_pres_trans; [exact AXP2|]; exact (seg_ax_pres' _ _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK MU3 HWL3 CEIL ltac:(clear - LO'; lia))|].
    split; [clear - CR2 USED; lia|].
    split. { unfold cnt_eq in *. rewrite (cnt_bal_setbn rx _ ls1 OW2 OW2 HVx2). fold br. rewrite CNT2.
             unfold bn_blocks, bn_dmax, OSSVerify.Proofs.openssl.bignum.lib.BgBnR2.W_set_word.set_word_bn. cbn [bn_d bn_buf]. fold nb. rewrite Edr, Lnb. cbn [length]. clear. lia. }
    split. { eapply refs_stable_trans; [exact RS2| apply refs_stable_setbn]. }
    split; [reflexivity|]. split; [reflexivity| exact BST]. }
  zstep. if_cases KD; zify_cond KD.
  -
    assert (HD1 : (1 <= bn_dmax bx)%nat) by (clear - KD0; lia).
    apply evt_done. unfold bn_wexpand, bbind, bget, bret, bset. cbn [bind ret tree_ops tbind fst snd]. fold bx.
    replace (1 <=? bn_dmax bx)%nat with true by (symmetry; apply Nat.leb_le; exact HD1).
    cbn [tbind fst snd].
    eapply (FIN Σ ls m1 OW 0 F fc);
      [ exact EV | exact LS1 | unfold MC; clear; lia | intros q0 A0 n0 Hq0 _; exact Hq0 | exact HAx | fold bx; exact HD1 ].
  -
    do 3 step.
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_expand2_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rx) (a := ax) (words := 1%nat) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAx | exact WRx | reflexivity | reflexivity | cbn; clear; lia].
      - eapply cenv_preA; [exact EV | exact LS1 | unfold BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO'; lia | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_BN_set_word_222f44 : uk_call BN_SET_WORD 0x22312c BN_EXPAND2) CTX). }
    cbv beta. intros [u ls1] Σ1 ms1 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -48) MC Σ ls OW) in PO; [| exact OK | exact HEAP1].
    cbn [fst snd] in *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F2 & fc2 & m2 & OW2 & PL2 & -> & CP & (EPL & -> & HDM & WRES & BST)).
    subst PL2. specialize (CP eq_refl).
    assert (E1 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -48) s0 ra (Some ras) MC Σ ls OW m [CB 8 jfr; C8 s3; C8 s2; C8 s1] (0 + MC) Σ1 ls1 m2 OW2 /\ lib_state ls1 m2 OW2 PL EA)
      by (eapply cenv_postA; [exact EV | exact CP]).
    destruct E1 as (EV1 & LS2).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RST2.
    rewrite (ret_pc_even 2240812) by (clear; lia).
    pose proof (ref_at_stable _ _ _ _ _ _ _ RST2 HAx) as HAx2.
    apply implA_from_evt.
    zstep. if_cases KZ; zify_cond KZ. { exfalso. rewrite ?unsigned_lit in KZ by (clear - X0 XC C1 C2 C3; unfold BnHeapA.ACEIL in *; lia). clear - KZ X0. lia. }
    clear KZ.
    apply evt_done. cbn [ret tree_ops].
    eapply (FIN Σ1 ls1 m2 OW2 (0 + MC) F2 fc2);
      [ exact EV1 | exact LS2 | clear; lia | exact BST | exact HAx2 | exact HDM ].
Qed.

End WithRT.
