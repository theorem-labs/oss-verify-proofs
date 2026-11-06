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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require AsLeaf.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require AW_sub_words.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW2 Require W_from_mont_loops.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_callsAF W_expandAF ExpKitAF InvKitAF HoleKitAF FromMontKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require AFromMontArr AFrameComp ExpBodyKitF.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import UbStructF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2252644 => 2
  | 2252652 => 1
  | 2252656 => 2
  | 2252700 => 1
  | 2252704 => 1
  | 2252708 => 2
  | 2252740 => 1
  | 2252748 => 2
  | 2252932 => 2
  | 2252936 => 1
  | 2252940 => 1
  | 2252944 => 2
  | 2252948 => 2
  | 2253064 => 1
  | 2253076 => 2
  | 2253080 => 2
  | 2253120 => 2
  | 2253164 => 2
  | 2253236 => 2
  | 2253240 => 1
  | 2253244 => 1
  | 2253248 => 2
  | 2253360 => 2
  | 2253372 => 2
  | 2253376 => 1
  | 2253380 => 1
  | 2253384 => 1
  | 2253388 => 1
  | 2253392 => 2
  | 2253444 => 1
  | 2253448 => 1
  | 2253452 => 1
  | 2253456 => 1
  | 2253464 => 1
  | 2253468 => 1
  | 2253472 => 2
  | 2253476 => 2
  | 2253504 => 2
  | 2253508 => 1
  | 2253512 => 1
  | 2253516 => 2
  | 2253520 => 2
  | 2253588 => 1
  | 2253592 => 2
  | 2253596 => 1
  | 2253600 => 1
  | 2253604 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Local Ltac ub_unfold ::= unfold BnHeapA.ACEIL in *.
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.

Definition BN_FROM_MONTGOMERY_WORD : Z := 0x225f20.
Definition BN_FROM_MONT_WORD_STACK : Z := 160 + BN_WEXPAND_STACK.
Definition BN_FROM_MONT_WORD_COST : Z := 2 * MC.

Local Notation mixl := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.mixl.
Local Notation clear_top := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.clear_top.
Local Notation clear_top_length := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.clear_top_length.
Local Notation clear_top_limbs := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.clear_top_limbs.
Local Notation select_words_length := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.select_words_length.
Local Notation select_words_limbs := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.select_words_limbs.
Local Notation sel_res := OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.sel_res.
Local Notation fm_clearA := OSSVerify.Proofs.openssl.bignum.lib.BgBnRB.AFromMontArr.fm_clearA.
Local Notation fm_selectA := OSSVerify.Proofs.openssl.bignum.lib.BgBnRB.AFromMontArr.fm_selectA.
Local Notation fm_reduceA := OSSVerify.Proofs.openssl.bignum.lib.BgBnRB.AFromMontArr.fm_reduceA.
Local Notation RBA := OSSVerify.Proofs.openssl.bignum.lib.BgBnRB.AFromMontArr.RBA.
Local Notation RBA_init := OSSVerify.Proofs.openssl.bignum.lib.BgBnRB.AFromMontArr.RBA_init.

Lemma lxor_b2z : forall x y, Z.lxor (Z.b2z x) (Z.b2z y) = Z.b2z (xorb x y).
Proof. intros [|] [|]; reflexivity. Qed.
Lemma b2z_31 : forall x, 0 <= Z.b2z x < 2^31.
Proof. intros [|]; cbn; lia. Qed.
Lemma b2z_64 : forall x, 0 <= Z.b2z x < 2^64.
Proof. intros [|]; cbn; lia. Qed.

Lemma to_bv_mod64 : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 18446744073709551616).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64).
  assert (L : Z.land x (Z.lxor x (Z.ones 64)) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z.ltb_spec n 64) as [Hlt|Hge].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
    - rewrite (Z.bits_above_log2 x n); [reflexivity| lia|].
      destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). lia. }
  pose proof (Z.add_nocarry_lxor _ _ L) as E.
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in E. lia.
Qed.

Lemma mont_final_sel : forall L ap np carry (nl : nat),
  length ap = nl -> length np = nl -> (nl <= length L)%nat ->
  splice L 0 (mont_final ap np carry)
  = sel_res (subw carry (snd (sub_words ap np))) (fst (sub_words ap np) ++ skipn nl L) ap nl.
Proof.
  intros L ap np carry nl Ha Hn HL. unfold mont_final.
  pose proof (sub_words_length ap np) as LR. destruct (sub_words ap np) as [res bw]. cbn [fst snd] in *.
  rewrite Ha, Hn, Nat.min_id in LR.
  set (sw := select_words (subw carry bw) ap res).
  assert (LS : length sw = nl) by (subst sw; rewrite select_words_length, Ha, LR; apply Nat.min_id).
  unfold OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.sel_res, splice. cbn [firstn app Nat.add]. rewrite LS.
  rewrite (firstn_app nl res), LR, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r, (firstn_all2 res) by lia.
  rewrite (skipn_app nl res), LR, Nat.sub_diag, (skipn_all2 res) by lia. cbn [skipn app]. reflexivity.
Qed.

Lemma splice_zero_parts : forall (L : list Z) nl, (2 * nl <= length L)%nat ->
  splice L nl (repeat 0 nl) = firstn nl L ++ repeat 0 nl ++ skipn (2 * nl) L.
Proof. intros L nl H. unfold splice. rewrite repeat_length. replace (nl + nl)%nat with (2 * nl)%nat by lia. reflexivity. Qed.

Lemma three_parts : forall (L : list Z) nl, (2 * nl <= length L)%nat -> L = firstn nl L ++ slice L nl nl ++ skipn (2 * nl) L.
Proof.
  intros L nl H. unfold slice. rewrite <- (firstn_skipn nl L) at 1. f_equal.
  rewrite <- (firstn_skipn nl (skipn nl L)) at 1. f_equal. rewrite skipn_skipn. f_equal. lia.
Qed.

Definition fm_ret (rt rx : bnref) (nl : nat) (np : list Z) (carry : Z) (bs : bstate bptr) : bignum bptr :=
  mkBN (bn_d (getbn rt bs)) (splice (bn_buf (getbn rt bs)) 0 (mont_final (slice (bn_buf (getbn rx bs)) nl nl) np carry)) nl
       (bn_neg (getbn rx bs)) (bn_flags (getbn rt bs)).
Definition fm_final (rt rx : bnref) (nl : nat) (np : list Z) (carry : Z) (bs : bstate bptr) : bstate bptr :=
  setbn rx (bn_with_buf (getbn rx (setbn rt (fm_ret rt rx nl np carry bs) bs))
                        (splice (bn_buf (getbn rx (setbn rt (fm_ret rt rx nl np carry bs) bs))) nl (repeat 0 nl)))
        (setbn rt (fm_ret rt rx nl np carry bs) bs).

Section TailB.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma fm_tailA : forall
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo : Z) (ras : list Z)
    (rt rx : bnref) (at_ ax am : Z) (qm : bptr)
    (Σ5 : rts RT) (ls5 : bstate bptr) (m5 : mem) (OW5 : list block) (used : Z) (F5 : bvmap 5 word) (fc5 : bv 32)
    (nl : nat) (np : list Z) (Dn2 : Z) (pn : bptr) (carry : Z)
    (w1 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w18 w19 w21 w22 w23 w25 w26 w27 w28 w29 w30 w31 : word),
  cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra (Some ras) BN_FROM_MONT_WORD_COST Σ ls OW m
        [C8 (Z_to_bv 64 ((ax + 16) ≫ 3 + SHB)); C8 (Z_to_bv 64 (ax ≫ 3 + SHB)); C8 (Z_to_bv 64 (ax + 16)); C8 (Z_to_bv 64 ax); C8 (Z_to_bv 64 at_);
         C8 (Z_to_bv 64 Dn2); C8 (Z_to_bv 64 (Z.of_nat nl));
         C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] used Σ5 ls5 m5 OW5 ->
  lib_state ls5 m5 OW5 PL EA -> used <= BN_FROM_MONT_WORD_COST ->
  lo <= bv_unsigned sp + -160 - 128 ->
  ref_at ls5 OW5 PL rt at_ -> ref_at ls5 OW5 PL rx ax -> wref PL rt -> wref PL rx -> pl_mont PL = Some (am, qm) ->
  rt <> rx -> rt <> RMontN -> rx <> RMontN ->
  nl = bn_top (getbn RMontN ls5) -> np = firstn nl (bn_buf (getbn RMontN ls5)) -> nl <> 0%nat ->
  bn_d (getbn RMontN ls5) = Some pn -> In (pn, Dn2, 8 * Z.of_nat (bn_dmax (getbn RMontN ls5))) OW5 ->
  (nl <= bn_dmax (getbn rt ls5))%nat -> (2 * nl <= bn_dmax (getbn rx ls5))%nat ->
  0 <= carry <= 1 ->
  (forall (Σ1 : rts RT) (ls1 : bstate bptr) (m2 : mem) (OW2 : list block) (used : Z) (FT : bvmap 5 word) (fcT : bv 32) (jj : list byte)
          (q1 q5 q6 q7 q8 q9 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 : word),
      cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra (Some ras) BN_FROM_MONT_WORD_COST Σ ls OW m
            [CB 56 jj; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] used Σ1 ls1 m2 OW2 ->
      lib_state ls1 m2 OW2 PL EA -> used <= BN_FROM_MONT_WORD_COST ->
      implA (TRet (tt, ls1)) Σ1
        (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_FROM_MONT_WORD_COST
                  (fun _ _ _ PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1))
        (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp (Z_to_bv 64 TP_A) q5 q6 q7 q8 q9 (Z_to_bv 64 1) q11 q12 q13 q14 q15 q16 q17
                 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31)
            FT (Z_to_bv 64 0x226348) fcT None m2 (seg_rom bgbsegs))) ->
  implA (TRet (tt, fm_final rt rx nl np carry ls5)) Σ5
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_FROM_MONT_WORD_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1))
    (MS (mkR w1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp (Z_to_bv 64 TP_A) w5 w6 w7 sp (Z_to_bv 64 at_) (Z_to_bv 64 at_) w11 w12 w13 w14 w15 w16 w17
             w18 w19 (Z_to_bv 64 SHB) w21 w22 w23 (Z_to_bv 64 carry) w25 w26 w27 w28 w29 w30 w31)
        F5 (Z_to_bv 64 0x2261ac) fc5 None m5 (seg_rom bgbsegs)).
Proof.
  intros until w31. intros EV5 LS5 USED LO' HAt5 HAx5 WRt WRx HPM NEtx NEtn NExn Enl Enp NT0 Edn Hinn5 HDM3 HDMx0 HC EPI.
  pose proof (proj1 WRt : not_one rt) as NROt. pose proof (proj1 WRx : not_one rx) as NROx.
  assert (WRn : wref PL RMontN) by (apply hpl_wref; eapply hpl_mont; [reflexivity| exact HPM]).
  pose proof (ref_at_montN ls5 OW5 PL am qm HPM) as HAn5.
  subst np. subst nl.
  set (bn := getbn RMontN ls5) in *. set (nl := bn_top bn) in *. set (np := firstn nl (bn_buf bn)) in *.
  assert (NT : bn_top bn <> 0%nat) by exact NT0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof EV5 as (OK5' & HEAP5' & _). pose proof OK5' as (CEIL & _ & _ & SPT & SP16 & _ & _ & _ & FROK & _ & NOFR).
  pose proof (AH_ceil _ _ _ _ HEAP5') as (C1' & C2' & C3'). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  clear OK5' HEAP5'.
  assert (LOF16 : lo <= bv_unsigned sp + -160 - 16) by (clear - LO'; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = bv_unsigned sp + -160) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - LO' CEIL C1' SPR; lia).
  pose proof (st_wf_ok RMontN ls5 (proj1 (lib_state_h_parts _ _ _ _ _ _ LS5)) (ref_at_valid _ _ _ _ _ _ _ _ LS5 HAn5) RMontN_not_one) as (OKn1 & OKn2 & OKn3 & _).
  fold bn in OKn1, OKn2, OKn3. fold nl in OKn2. unfold BG_DMAX in OKn3.
  assert (NL31 : Z.of_nat nl <= 512) by (clear - OKn2 OKn3; lia).
  assert (LBn : length (bn_buf bn) = bn_dmax bn) by reflexivity.
  unfold fm_final, fm_ret. fold bn. fold nl. fold np.

    pose proof EV5 as (OK5 & HEAP5 & _).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS5) as PARTS5.
    pose proof (AH_nodup_l _ _ _ _ HEAP5) as ND5.
    set (bt := getbn rt ls5) in *.
    assert (HDt : (0 < bn_dmax bt)%nat) by (clear - HDM3 NT; fold nl in NT; lia).
    assert (HDx : (0 < bn_dmax (getbn rx ls5))%nat) by (clear - HDMx0 NT; fold nl in NT; lia).
    assert (HDn5 : (0 < bn_dmax (getbn RMontN ls5))%nat) by (fold bn; clear - OKn2 NT; fold nl in OKn2, NT; lia).
    destruct (cenv_hole1A LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra ras BN_FROM_MONT_WORD_COST Σ ls OW m LOF16 _ _ _ _ _ _ rt at_ EV5 LS5 HAt5 WRt HDt)
      as (Dt & pt & Edt & Hint & BNt & Ut & (OKt1 & OKt2 & OKt3 & OKt4) & (ACT & ALT & At0 & AtS & OFT) & (ACDT & ALDT & Dt0 & DtS & OFDT) & SEPt & SEPAt & ST5 & MI5 & _).
    destruct (cenv_hole1A LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra ras BN_FROM_MONT_WORD_COST Σ ls OW m LOF16 _ _ _ _ _ _ rx ax EV5 LS5 HAx5 WRx HDx)
      as (Dx & px & Edx & Hinx & BNx & Ux & (OKx1 & OKx2 & OKx3 & OKx4) & (ACX & ALX & Ax0 & AxS & OFX) & (ACDX & ALDX & Dx0 & DxS & OFDX) & SEPx & SEPAx & _ & _ & _).
    destruct (cenv_hole1A LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra ras BN_FROM_MONT_WORD_COST Σ ls OW m LOF16 _ _ _ _ _ _ RMontN (am + 24) EV5 LS5 HAn5 WRn HDn5)
      as (Dn5 & pn5 & Edn5 & Hinn5' & _ & Un & _ & _ & (ACDN & ALDN & Dn0 & DnS & OFDN) & SEPn & SEPAn & _ & _ & _).
    fold bt in Edt, Hint, BNt, Ut, OKt1, OKt2, OKt3, OKt4, ACDT, DtS, OFDT, SEPt, SEPAt.
    fold bn in Edn5, Hinn5', Un, ACDN, DnS, OFDN, SEPn, SEPAn.
    set (bx := getbn rx ls5) in *.
    assert (EDn : Dn5 = Dn2).
    { rewrite Edn in Edn5. injection Edn5 as <-. exact (proj1 (AH_addr_unique OW5 pn Dn5 _ Dn2 _ ND5 Hinn5' Hinn5)). }
    subst Dn5. clear Edn5 Hinn5' pn5.
    assert (LBt : length (bn_buf bt) = bn_dmax bt) by reflexivity.
    assert (LBx : length (bn_buf bx) = bn_dmax bx) by reflexivity.
    assert (HDMx : (2 * nl <= bn_dmax bx)%nat) by exact HDMx0.
    assert (ARRt : bn_arr m5 OW5 (pl_of PL rt) Dt bt) by (unfold bn_arr; rewrite Edt; split; [exact Hint| exact Ut]).
    assert (ARRx : bn_arr m5 OW5 (pl_of PL rx) Dx bx) by (unfold bn_arr; rewrite Edx; split; [exact Hinx| exact Ux]).

    pose proof (SEPt rt at_ HAt5) as S_tt. pose proof (SEPx rt at_ HAt5) as S_tx. pose proof (SEPn rt at_ HAt5) as S_tn.
    pose proof (SEPt rx ax HAx5) as S_xt. pose proof (SEPx rx ax HAx5) as S_xx. pose proof (SEPn rx ax HAx5) as S_xn.
    pose proof (SEPAt rx ax Dx NEtx HAx5 NROx ARRx) as D_tx. fold bx in D_tx.
    pose proof (SEPAn rt at_ Dt ltac:(intros E; apply NEtn; symmetry; exact E) HAt5 NROt ARRt) as D_tn. fold bt in D_tn.
    pose proof (SEPAn rx ax Dx ltac:(intros E; apply NExn; symmetry; exact E) HAx5 NROx ARRx) as D_xn. fold bx in D_xn.
    pose proof (struct_disj Σ5 OW5 LB m5 HEAP5 ls5 PL EA _ _ PARTS5 FROK rt rx at_ ax NEtx HAt5 HAx5) as S_ax.
    clear SEPt SEPx SEPn SEPAt SEPAx SEPAn ARRt ARRx.

    assert (DtL : Dt + 8 * Z.of_nat (bn_dmax bt) <= lo)
      by (pose proof (AH_range _ _ _ _ _ _ _ HEAP5 Hint) as (_ & _ & _ & X & _); unfold BnHeapA.ACEIL in *; clear - X CEIL; lia).
    assert (DxL : Dx + 8 * Z.of_nat (bn_dmax bx) <= lo)
      by (pose proof (AH_range _ _ _ _ _ _ _ HEAP5 Hinx) as (_ & _ & _ & X & _); unfold BnHeapA.ACEIL in *; clear - X CEIL; lia).
    assert (DnL : Dn2 + 8 * Z.of_nat (bn_dmax bn) <= lo)
      by (pose proof (AH_range _ _ _ _ _ _ _ HEAP5 Hinn5) as (_ & _ & _ & X & _); unfold BnHeapA.ACEIL in *; clear - X CEIL; lia).
    assert (AtL : at_ + 24 <= lo)
      by (destruct (ref_at_rangeF ls5 OW5 PL EA (bv_unsigned sp) USTACK_TOP Σ5 LB m5 rt at_ HEAP5 PARTS5 FROK HAt5 NROt) as (_ & X & _); unfold BnHeapA.ACEIL in *; clear - X CEIL; lia).
    assert (AxL : ax + 24 <= lo)
      by (destruct (ref_at_rangeF ls5 OW5 PL EA (bv_unsigned sp) USTACK_TOP Σ5 LB m5 rx ax HEAP5 PARTS5 FROK HAx5 NROx) as (_ & X & _); unfold BnHeapA.ACEIL in *; clear - X CEIL; lia).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP5 Hint) as (_ & _ & _ & _ & TLO).
    destruct (cenv_hole2F LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra ras BN_FROM_MONT_WORD_COST Σ ls OW m LOF16 _ _ _ _ _ _ rt at_ Dt pt rx ax Dx px 128
                EV5 LS5 NEtx HAt5 NROt Edt Hint HAx5 NROx Edx Hinx ltac:(clear; lia) ltac:(clear - LO'; lia)) as (FRAMEH2 & CLOSE2).
    fold bt bx in FRAMEH2, CLOSE2.
    pose proof EV5 as (_ & _ & _ & _ & _ & _ & _ & _ & FR5 & FSZ5 & _). cbn [app] in FR5.
    unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNt, BNx. unfold BG_DMAX in OKt3, OKx3.

    assert (NL1 : (1 <= nl)%nat) by (clear - NT; fold nl in NT; lia).
    assert (HDMt : (nl <= bn_dmax bt)%nat) by exact HDM3.
    assert (AtR : 0 < at_ < 2^64) by (clear - At0 AtS SPR; lia).

    pose proof Ux as Ux3. rewrite (three_parts (bn_buf bx) nl) in Ux3 by (rewrite LBx; exact HDMx).
    apply limbarr_app in Ux3. destruct Ux3 as [Ux1 Ux3]. apply limbarr_app in Ux3. destruct Ux3 as [Uap Ux3].
    rewrite length_firstn, Nat.min_l in Uap, Ux3 by (clear - HDMx LBx; lia).
    rewrite slice_length in Ux3 by (clear - HDMx LBx; lia).
    replace (Dx + 8 * Z.of_nat nl + 8 * Z.of_nat nl) with (Dx + 8 * Z.of_nat (2 * nl)) in Ux3 by (clear; lia).
    set (ap := slice (bn_buf bx) nl nl) in *.
    assert (Lap : length ap = nl) by (subst ap; apply slice_length; clear - HDMx LBx; lia).
    assert (LMap : limbs ap) by (subst ap; apply slice_limbs; exact OKx1).
    assert (Lnp : length np = nl) by (subst np; apply firstn_length_le; clear - OKn2 LBn; fold nl in OKn2; lia).
    assert (LMnp : limbs np) by (subst np; apply limbs_firstn; exact OKn1).
    pose proof Ut as Ut2. apply (limbarr_split bgbsegs _ Dt (bn_buf bt) nl) in Ut2; [| clear - HDMt LBt; lia]. destruct Ut2 as [Ut1 Ut2].
    pose proof Un as Unp. apply (limbarr_split bgbsegs _ Dn2 (bn_buf bn) nl) in Unp; [| clear - OKn2 LBn; fold nl in OKn2; lia]. apply proj1 in Unp. fold np in Unp.
    clear Ux Ut Un.

    pose proof (munch_refl [(bv_unsigned sp + -160 - 128, bv_unsigned sp + -160); (at_, at_ + 24); (Dt, Dt + 8 * Z.of_nat nl);
                            (Dx + 8 * Z.of_nat nl, Dx + 8 * Z.of_nat nl + 8 * Z.of_nat nl)]%Z m5) as MU.
    pose proof (munch_refl [(bv_unsigned sp + -160 - 128, bv_unsigned sp + -160); (at_, at_ + 24); (Dt, Dt + 8 * Z.of_nat nl)]%Z m5) as MUa.
    pose proof (wmono_refl bgbsegs m5) as WM.
    assert (OFF : offshW [(bv_unsigned sp + -160 - 128, bv_unsigned sp + -160); (at_, at_ + 24); (Dt, Dt + 8 * Z.of_nat nl);
                          (Dx + 8 * Z.of_nat nl, Dx + 8 * Z.of_nat nl + 8 * Z.of_nat nl)]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFT OFDT OFX OFDX HDMt HDMx SPR LO' CEIL C1' C2' C3'. lia. }
    assert (MUK : forall mq, munch [(bv_unsigned sp + -160 - 128, bv_unsigned sp + -160); (at_, at_ + 24); (Dt, Dt + 8 * Z.of_nat nl);
                                     (Dx + 8 * Z.of_nat nl, Dx + 8 * Z.of_nat nl + 8 * Z.of_nat nl)]%Z m5 mq ->
                         munch (fpF2 (bv_unsigned sp) (bv_unsigned sp + -160) 128 at_ Dt (bn_dmax bt) ax Dx (bn_dmax bx)) m5 mq).
    { intros mq MUq. eapply munch_weaken; [| exact MUq]. unfold sub_fp, fpF2. cbn [outside]. intros x Hx. clear - Hx HDMt HDMx. lia. }
    assert (OFFa : offshW [(bv_unsigned sp + -160 - 128, bv_unsigned sp + -160); (at_, at_ + 24); (Dt, Dt + 8 * Z.of_nat nl)]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFT OFDT HDMt SPR LO' CEIL C1' C2' C3'. lia. }
    assert (LUt1 : Z.of_nat (length (wlimbs (firstn nl (bn_buf bt)))) = Z.of_nat nl)
      by (rewrite wlimbs_len, firstn_length_le by (clear - HDMt LBt; lia); reflexivity).
    assert (BDT : 0 <= Dt /\ Dt + 8 * Z.of_nat (bn_dmax bt) <= 140737488355328) by (clear - Dt0 DtS SPT; lia).
    assert (BDX : 0 <= Dx /\ Dx + 8 * Z.of_nat (bn_dmax bx) <= 140737488355328) by (clear - Dx0 DxS SPT; lia).
    assert (BDN5 : 0 <= Dn2 /\ Dn2 + 8 * Z.of_nat (bn_dmax bn) <= 140737488355328) by (clear - Dn0 DnS SPT; lia).
    assert (TOPT : Z.of_nat (bn_dmax bt) <= 512 /\ Z.of_nat (bn_dmax bx) <= 512) by (clear - OKt3 OKx3; lia).
    set (b1 := mkBN (bn_d bt) (splice (bn_buf bt) 0 (mont_final ap np carry)) nl (bn_neg bx) (bn_flags bt)).
    assert (G2 : getbn rx (setbn rt b1 ls5) = bx) by (apply getbn_setbn_other; exact NEtx).
    rewrite G2.
    set (b2f := bn_with_buf bx (splice (bn_buf bx) nl (repeat 0 nl))).
    apply implA_from_evt. unfold MallocRep.wz.

    apply hide_intro in Ux1. apply hide_intro in Uap. apply hide_intro in Ux3. apply hide_intro in Ut2. apply hide_intro in Unp.
    apply hide_intro in OKt4. apply hide_intro in OKx4. apply hide_intro in OFT. apply hide_intro in OFDT. apply hide_intro in OFX. apply hide_intro in OFDX.
    apply hide_intro in OFDN. apply hide_intro in S_tx. apply hide_intro in S_tn. apply hide_intro in S_xt. apply hide_intro in S_xx. apply hide_intro in S_xn.
    apply hide_intro in D_tx. apply hide_intro in D_tn. apply hide_intro in D_xn. apply hide_intro in TLO.
    apply hide_intro in FRAMEH2. apply hide_intro in CLOSE2. apply hide_intro in EPI. apply hide_intro in MUK.

    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
    step.

    ub.
    step.
    do 3 step. shl_with ACT ALT. chk0.
    step.

    step. shl_with ACX ALX. step. chk0.
    do 3 step. shl_with ACT ALT. step. chk0.
    rewrite (sx32_small (Z.b2z _)) by (apply b2z_31).
    step.

    do 2 step. shl_with ACT ALT. step. chk0.
    step. shl_with ACX ALX. chk0.
    step.

    assert (PDx : 0 < Dx) by (pose proof (AH_range _ _ _ _ _ _ _ HEAP5 Hinx) as (X & _); clear - X; lia).
    assert (PDt : 0 < Dt) by (pose proof (AH_range _ _ _ _ _ _ _ HEAP5 Hint) as (X & _); clear - X; lia).
    assert (PDn : 0 < Dn2) by (pose proof (AH_range _ _ _ _ _ _ _ HEAP5 Hinn5) as (X & _); clear - X; lia).
    assert (BDXa : Dx + 8 * Z.of_nat (bn_dmax bx) <= 140737488355328) by (clear - BDX; lia).
    ub.
    step.
    setreg 21%Z (Z_to_bv 64 (8 * Z.of_nat nl))
      ltac:(f_equal; rewrite unsigned_lit by (clear - NL31; fold nl in NL31; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
    step.
    rewrite ?(unsigned_lit Dx), ?(unsigned_lit (8 * Z.of_nat nl)) by (clear - PDx BDXa NL31; fold nl in NL31; lia).
    assert (PAP : 0 < Dx + 8 * Z.of_nat nl /\ Dx + 8 * Z.of_nat nl < 140737488355328 /\ Dx <= Dx + 8 * Z.of_nat nl) by (clear - PDx BDXa HDMx NL1; lia).

    ub.
    do 7 step.

    apply hide_elim in S_tx. apply hide_elim in S_tn. apply hide_elim in D_tx. apply hide_elim in D_tn. apply hide_elim in OFDT. apply hide_elim in FRAMEH2.
    apply hide_elim in MUK.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      assert (HAP : limbs_at bgbsegs mq (Dx + 8 * Z.of_nat nl) ap);
      [ apply limbs_at_of_u64arr; apply hide_elim in Uap; eapply u64arr_transport; [exact Uap| exact MUa| exact WM|];
        cbn [disjoint_from]; rewrite wlimbs_len, Lap; clear - DxL S_tx D_tx HDMx HDMt LO'; lia |];
      assert (HNP : limbs_at bgbsegs mq Dn2 np);
      [ apply limbs_at_of_u64arr; apply hide_elim in Unp; eapply u64arr_transport; [exact Unp| exact MUa| exact WM|];
        cbn [disjoint_from]; rewrite wlimbs_len, Lnp; clear - DnL S_tn D_tn OKn2 HDMt LO'; fold nl in OKn2; lia |];
      pose proof (acc_munch bgbsegs _ m5 mq Dt _ ACDT MU OFF (proj1 BDT) (proj2 BDT)) as ACTc;
      pose proof (acc_munch bgbsegs _ m5 mq Dx _ ACDX MU OFF (proj1 BDX) (proj2 BDX)) as ACXc;
      pose proof (acc_munch bgbsegs _ m5 mq Dn2 _ ACDN MU OFF (proj1 BDN5) (proj2 BDN5)) as ACNc;
      pose proof (AH_shb _ _ _ _ (proj1 (FRAMEH2 mq (MUK mq MU) WM))) as SHBc
    end.
    pose proof (proj2 (proj1 (limbarr_limbs_at bgbsegs _ _ _) Ut1)) as WRT.
    rewrite firstn_length_le in WRT by (clear - HDMt LBt; lia).
    assert (EDt : bv_unsigned (Z_to_bv 64 Dt) = Dt) by (apply unsigned_lit; clear - BDT; lia).
    assert (EAP : bv_unsigned (Z_to_bv 64 (Dx + 8 * Z.of_nat nl)) = Dx + 8 * Z.of_nat nl) by (apply unsigned_lit; clear - BDX HDMx; lia).
    assert (EDn : bv_unsigned (Z_to_bv 64 Dn2) = Dn2) by (apply unsigned_lit; clear - BDN5; lia).
    assert (ENL : bv_unsigned (Z_to_bv 64 (Z.of_nat nl)) = Z.of_nat nl) by (apply unsigned_lit; clear - NL31; fold nl in NL31; lia).
    apply hide_intro in FRAMEH2. apply hide_intro in MUK.

    eapply evt_cut.
    { eapply OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth.AW_sub_words.bn_sub_words_aspec with (a := ap) (b := np) (lo := lo);
        rewrite ?EDt, ?EAP, ?EDn, ?ENL, ?ESP, ?Lap;
        [ exact LMap | exact LMnp | rewrite Lnp; reflexivity | clear - NL31; fold nl in NL31; lia | reflexivity | exact HAP | exact HNP | exact WRT
        | right; clear - D_tx HDMx HDMt; lia | right; clear - D_tn OKn2 HDMt; fold nl in OKn2; lia
        | exact ST5 | clear - LO'; lia | left; clear - DtL HDMt LO'; lia | left; clear - DxL HDMx LO'; lia | left; clear - DnL OKn2 LO'; fold nl in OKn2; lia
        | assumption
        | exact SHBc
        | eapply acc_sub; [exact ACTc | clear; lia | clear - HDMt; lia]
        | eapply acc_sub; [exact ACXc | clear; lia | clear - HDMx; lia]
        | eapply acc_sub; [exact ACNc | clear; lia | clear - OKn2; fold nl in OKn2; lia]
        | unfold aptrs3; split; [exact ALDT|]; split; [clear - ALDX; Z.div_mod_to_equations; lia|]; split; [exact ALDN|];
          split; [unfold SHLO, SHHI in *; clear - OFDT HDMt; lia | unfold SHHI, BnHeapA.ACEIL in *; clear - C2' CEIL; lia]
        | intros _; split; [exact PDt | exact ALDT]
        | intros _; split; [clear - PAP; lia | clear - ALDX; Z.div_mod_to_equations; lia]
        | intros _; split; [exact PDn | exact ALDN] ]. }
    clear Ut1 LUt1 ST5 HAP HNP ACTc ACXc ACNc SHBc.
    intros ms' PO. unfold OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth.AW_sub_words.sw_apost, OSSVerify.Proofs.openssl.bignum.lib.BnW.BnLoop.wl_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5' & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m6 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite EDt, Lap, ESP in MUc. rewrite EDt in HR. rewrite ESP in STc.
    destruct (sub_words ap np) as [res bw] eqn:ESW. cbn [fst snd] in *.
    pose proof (sub_words_spec ap np LMap LMnp ltac:(rewrite Lap, Lnp; reflexivity)) as SWS. rewrite ESW in SWS.
    destruct SWS as (LMres & Lres & BW01 & _). rewrite Lap in Lres.
    apply hide_elim in S_xt. apply hide_intro in S_tx. apply hide_intro in S_tn. apply hide_intro in D_tx. apply hide_intro in D_tn. apply hide_intro in OFDT.
    apply hide_intro in S_ax. apply hide_intro in BW01.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bgbsegs mm m6 MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv bgbsegs mm |- _ => clear H end; try clear mm end.
    rewrite (ret_pc_even 2253424) by (clear; lia).

    step. step.
    step. rewrite (lts_signed 0 (Z.of_nat nl)) by (clear - NL31; fold nl in NL31; lia).
    if_cases KB; zify_cond KB; [exfalso; clear - KB NL1; lia|]. clear KB.
    step. step.

    ub.
    step.
    ub1 ub_kind. ub1 ub_kind.

    apply hide_elim in BW01.
    set (mk := subw carry bw).
    assert (MK : 0 <= mk < 18446744073709551616) by (subst mk; unfold subw; rewrite BW_lit; apply Z.mod_pos_bound; clear; lia).
    assert (EL1 : Z.land bw 18446744073709551615 = bw)
      by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); apply Z.mod_small; clear - BW01; lia).
    assert (EL2 : Z.land (carry + - bw) 18446744073709551615 = mk)
      by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by (clear; lia); subst mk; unfold subw; rewrite BW_lit; reflexivity).
    rewrite EL1, EL2.
    assert (EA1 : Z_to_bv 64 (carry + - bw) = Z_to_bv 64 mk) by (subst mk; unfold subw; rewrite BW_lit; rewrite (to_bv_mod64 (carry + - bw)); reflexivity).

    rewrite EA1. rewrite (lxor_ones64 mk) by (clear - MK; lia).
    replace (18446744073709551615 - mk) with (18446744073709551616 - 1 - mk) by (clear; lia).
    rewrite (lxor_ones64 (Dx + 8 * Z.of_nat nl)) by (clear - PAP; lia).
    rewrite (land7 Dx ALDX), (land7 Dt ALDT).
    replace (0 <? Dt) with true by (symmetry; apply Z.ltb_lt; exact PDt).
    change (Z.land (Z.b2z (0 <? 1)) (Z.b2z true)) with 1. change (Z.b2z true) with 1.
    setreg 13%Z (Z_to_bv 64 (8 * Z.of_nat 0)) ltac:(reflexivity).

    apply hide_elim in Ut2. apply hide_elim in Uap. apply hide_elim in S_tx. apply hide_elim in D_tx.
    assert (UR : u64arr bgbsegs m6 Dt (wlimbs (res ++ skipn nl (bn_buf bt)))).
    { apply limbarr_app. split.
      - apply u64arr_of_limbs_at; [exact HR| rewrite Lres; exact WRT].
      - rewrite Lres. eapply u64arr_transport; [exact Ut2| exact MUa| exact WM|].
        cbn [disjoint_from]. rewrite wlimbs_len, length_skipn, LBt. clear - DtL S_tt HDMt LO'. lia. }
    assert (UP : u64arr bgbsegs m6 (Dx + 8 * Z.of_nat nl) (wlimbs ap)).
    { eapply u64arr_transport; [exact Uap| exact MUa| exact WM|]. cbn [disjoint_from]. rewrite wlimbs_len, Lap. clear - DxL S_tx D_tx HDMx HDMt LO'. lia. }
    clear MUa OFFa HR WRT Ut2 Uap.
    assert (LR : length (res ++ skipn nl (bn_buf bt)) = bn_dmax bt) by (rewrite length_app, Lres, length_skipn, LBt; clear - HDMt; lia).
    pose proof (acc_munch bgbsegs _ m5 m6 Dt _ ACDT MU OFF (proj1 BDT) (proj2 BDT)) as ACTc.
    pose proof (acc_munch bgbsegs _ m5 m6 Dx _ ACDX MU OFF (proj1 BDX) (proj2 BDX)) as ACXc.
    assert (EK : exists K3, nl = S K3) by (exists (nl - 1)%nat; clear - NL1; lia). destruct EK as (K3 & EK3).
    apply hide_elim in OFDT. apply hide_elim in OFDX.

    pose proof (munch_refl [(Dt, Dt + 8 * Z.of_nat nl); (Dx + 8 * Z.of_nat nl, Dx + 8 * Z.of_nat nl + 8 * Z.of_nat nl)]%Z m6) as MUL. pose proof (wmono_refl bgbsegs m6) as WML.
    eapply (fm_selectA _ F5 fc5) with (RPr := Dt) (AP := Dx + 8 * Z.of_nat nl) (mk := mk) (R := res ++ skipn nl (bn_buf bt)) (P := ap) (nl := nl)
                                       (m0 := m6) (K := K3) (j := 0%nat) (m1 := m6);
      [ apply limbs_app; [exact LMres| apply limbs_skipn; exact OKt1] | exact LMap | exact Lap | rewrite LR; exact HDMt | rewrite LR; clear - TOPT; lia | exact MK
      | rewrite LR; clear - D_tx HDMx; lia
      | eapply acc_sub; [exact ACTc | clear; lia | clear - HDMt; lia] | exact ALDT | clear - BDT HDMt; lia | exact PDt
      | eapply acc_sub; [exact ACXc | clear; lia | clear - HDMx; lia] | clear - ALDX; Z.div_mod_to_equations; lia | clear - BDX HDMx; lia | clear - PAP; lia
      | cbn [offshW]; unfold SHLO, SHHI in *; clear - OFDT OFDX HDMt HDMx; lia
      | clear - EK3; lia | exact MUL | exact WML | exact UR | exact UP | assumption | ].
    intros m7 u7 u11 u12 u28 u29 URf UPf MU7 WM7 MI7. clear MUL WML UR UP ACTc ACXc.
    apply hide_intro in OFDT. apply hide_intro in OFDX. apply hide_intro in D_tx. apply hide_elim in S_xx.
    lazymatch type of MU7 with munch _ ?mm _ => transport_after_call bgbsegs mm m7 MU7 WM7; clear MU7 WM7;
      try match goal with H : mem_inv bgbsegs mm |- _ => clear H end; try clear mm end.

    apply hide_elim in Ux1. apply hide_elim in Ux3. apply hide_elim in OKt4. apply hide_elim in OKx4. apply hide_elim in CLOSE2. apply hide_elim in EPI.
    apply hide_elim in MUK. try (apply hide_elim in S_tx). try (apply hide_elim in D_tx).
    assert (Eb1 : bn_buf b1 = sel_res mk (res ++ skipn nl (bn_buf bt)) ap nl).
    { subst b1. cbn [bn_buf]. rewrite (mont_final_sel (bn_buf bt) ap np carry nl Lap Lnp ltac:(rewrite LBt; exact HDMt)). rewrite ESW. reflexivity. }
    assert (Lb1 : length (bn_buf b1) = bn_dmax bt).
    { rewrite Eb1. unfold OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.sel_res.
      rewrite length_app, select_words_length, length_firstn, length_skipn, length_app, Lres, length_skipn, Lap, LBt. clear - HDMt. lia. }
    assert (Lb2 : length (bn_buf b2f) = bn_dmax bx).
    { subst b2f. cbn [bn_with_buf bn_buf]. rewrite splice_length by (rewrite repeat_length, LBx; clear - HDMx; lia). exact LBx. }

    pose proof (rw_cells_merge bgbsegs m7 (bv_unsigned sp + -160) []
                  [C8 (Z_to_bv 64 ((ax + 16) ≫ 3 + SHB)); C8 (Z_to_bv 64 (ax ≫ 3 + SHB)); C8 (Z_to_bv 64 (ax + 16)); C8 (Z_to_bv 64 ax); C8 (Z_to_bv 64 at_);
                   C8 (Z_to_bv 64 Dn2); C8 (Z_to_bv 64 (Z.of_nat nl))]
                  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR5) as FRM.
    cbn [app cells_size csize Nat.add] in FRM.
    lazymatch type of FRM with rw_cells _ _ _ (CB 56 ?jj :: _) => set (jm := jj) in * end.
    destruct (CLOSE2 m7 b1 b2f [CB 56 jm; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (MUK m7 MU) WM) as (ENVF & LSF).
    { unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz. change (bn_dmax b1) with (length (bn_buf b1)). cbn [b1 bn_top bn_neg bn_flags]. rewrite Lb1. exact BNt. }
    { rewrite Eb1. exact URf. }
    { reflexivity. }
    { rewrite Lb1, LBt. reflexivity. }
    { unfold bg_ok. change (bn_dmax b1) with (length (bn_buf b1)). rewrite Lb1. change (bn_top b1) with nl. change (bn_flags b1) with (bn_flags bt).
      split. { rewrite Eb1. unfold OSSVerify.Proofs.openssl.bignum.lib.BgBnW2.W_from_mont_loops.sel_res.
               apply limbs_app; [apply select_words_limbs; [rewrite BW_lit; exact MK| exact LMap|]| apply limbs_skipn].
               - apply limbs_firstn. apply limbs_app; [exact LMres| apply limbs_skipn; exact OKt1].
               - apply limbs_app; [exact LMres| apply limbs_skipn; exact OKt1]. }
      split; [exact HDMt|]. split; [unfold BG_DMAX; exact OKt3| exact OKt4]. }
    { unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz. change (bn_dmax b2f) with (length (bn_buf b2f)). cbn [b2f bn_with_buf bn_top bn_neg bn_flags]. rewrite Lb2. exact BNx. }
    { subst b2f. cbn [bn_with_buf bn_buf]. rewrite splice_zero_parts by (rewrite LBx; exact HDMx).
      apply limbarr_app. split.
      + eapply u64arr_transport; [exact Ux1| exact MU| exact WM|]. cbn [disjoint_from].
        rewrite wlimbs_len, firstn_length_le by (rewrite LBx; clear - HDMx; lia). clear - DxL S_tx D_tx HDMt HDMx LO'. lia.
      + rewrite firstn_length_le by (rewrite LBx; clear - HDMx; lia). apply limbarr_app. split; [exact UPf|].
        rewrite repeat_length. replace (Dx + 8 * Z.of_nat nl + 8 * Z.of_nat nl) with (Dx + 8 * Z.of_nat (2 * nl)) by (clear; lia).
        eapply u64arr_transport; [exact Ux3| exact MU| exact WM|]. cbn [disjoint_from].
        rewrite wlimbs_len, length_skipn, LBx. clear - DxL S_tx D_tx HDMt HDMx LO'. lia. }
    { reflexivity. }
    { rewrite Lb2, LBx. reflexivity. }
    { unfold bg_ok. change (bn_dmax b2f) with (length (bn_buf b2f)). rewrite Lb2. change (bn_top b2f) with (bn_top bx). change (bn_flags b2f) with (bn_flags bx).
      split. { subst b2f. cbn [bn_with_buf bn_buf]. apply splice_limbs; [exact OKx1| apply limbs_repeat; unfold limb, BW; clear; lia]. }
      split; [exact OKx2|]. split; [unfold BG_DMAX; exact OKx3| exact OKx4]. }
    { assumption. }
    { assumption. }
    { cbn [app]. exact FRM. }
    { cbn [cells_size csize Nat.add]. clear. lia. }
    apply evt_done.
    eapply (EPI Σ5 _ m7 OW5 used); [exact ENVF | exact LSF | exact USED].
Qed.
End TailB.
Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma bn_from_montgomery_word_walkA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
    (lo : Z) (ras : list Z) (rt rx : bnref) (at_ ax am : Z) (qm : bptr),
  bn_preA Σ ls m OW LB PL EA sp lo BN_FROM_MONT_WORD_STACK BN_FROM_MONT_WORD_COST ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BN_FROM_MONTGOMERY_WORD (bv_unsigned ra :: ras) ->
  tp = wz TP_A -> ref_at ls OW PL rt at_ -> ref_at ls OW PL rx ax -> wref PL rt -> wref PL rx -> pl_mont PL = Some (am, qm) ->
  a0 = wz at_ -> a1 = wz ax -> a2 = wz am ->
  implA (bn_from_montgomery_word (tree_ops bptr) rt rx ls) Σ
    (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_FROM_MONT_WORD_COST (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_FROM_MONTGOMERY_WORD) fc None m (seg_rom bgbsegs)).
Proof.
  intros until qm. intros PRE UW CTX -> HAt HAx WRt WRx HPM -> -> ->.
  pose proof (proj1 WRt : not_one rt) as NROt. pose proof (proj1 WRx : not_one rx) as NROx.
  pose proof PRE as (HEAP & LS & FROK & ST & CEIL & LO & SPT & SP16 & MI & CNT & CRED & FAL & NOFR).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  pose proof LO as LO'. unfold BN_FROM_MONT_WORD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK in LO'.
  unfold BN_FROM_MONTGOMERY_WORD, MallocRep.wz.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1' & C2' & C3'). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct (AH_shb _ _ _ _ HEAP) as (SHB1 & SHB2).
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 160, bv_unsigned sp)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; lia).
  pose proof (ref_at_montN ls OW PL am qm HPM) as HAn.

  unfold bn_from_montgomery_word.
  destruct ((rt =? rx)%nat || (rt =? RMontN)%nat || (rx =? RMontN)%nat) eqn:G1;
    [unfold bunr; cbn [unreachable tree_ops]; apply implA_unr|].
  apply orb_false_iff in G1. destruct G1 as [G1 NExn]. apply orb_false_iff in G1. destruct G1 as [NEtx NEtn].
  apply Nat.eqb_neq in NEtx, NEtn, NExn.
  apply implA_from_evt.

  carve_frame 160%nat ST.
  do 15 step.

  step. step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = bv_unsigned sp + -160) by (apply unsigned_lit; lia).
  assert (HWL : Forall (w_lib ls OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -160, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
  assert (WOK : Forall (w_ok OW LB ls PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -160, bv_unsigned sp)]).
  { constructor; [apply w_stack; cbn; unfold BnHeapA.ACEIL in *; lia| constructor]. }
  pose proof (lib_state_frame Σ LB (bv_unsigned sp) USTACK_TOP [] ls m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
  lazymatch type of FR with rw_cells _ _ _ (CB 24 ?j1 :: _ :: _ :: CB 16 ?j2 :: _) => set (jf1 := j1) in *; set (jf2 := j2) in * end.
  assert (EV : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra (Some ras) BN_FROM_MONT_WORD_COST Σ ls OW m
                 [CB 24 jf1; C8 (Z_to_bv 64 ax); C8 (Z_to_bv 64 at_); CB 16 jf2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ ls m1 OW).
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

  assert (EPI : forall (Σ1 : rts RT) (ls1 : bstate bptr) (m2 : mem) (OW2 : list block) (used : Z) (FT : bvmap 5 word) (fcT : bv 32) (jj : list byte)
                       (q1 q5 q6 q7 q8 q9 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 : word),
      cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra (Some ras) BN_FROM_MONT_WORD_COST Σ ls OW m
            [CB 56 jj; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] used Σ1 ls1 m2 OW2 ->
      lib_state ls1 m2 OW2 PL EA -> used <= BN_FROM_MONT_WORD_COST ->
      implA (TRet (tt, ls1)) Σ1
        (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA BN_FROM_MONT_WORD_COST
                  (fun _ _ _ PL' a0' => PL' = PL /\ a0' = Z_to_bv 64 1))
        (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp (Z_to_bv 64 TP_A) q5 q6 q7 q8 q9 (Z_to_bv 64 1) q11 q12 q13 q14 q15 q16 q17
                 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31)
            FT (Z_to_bv 64 0x226348) fcT None m2 (seg_rom bgbsegs))).
  { intros Σ1 ls1 m2 OW2 used FT fcT jj q1 q5 q6 q7 q8 q9 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 EV1 LS2 USED.
    clear MU WM ST MI FR HWL WOK LS1 HEAP1 EV OK OFF SHB1 SHB2 HEAP LS PARTS PRE UW.
    pose proof EV1 as (OK1 & HEAP2 & ST2 & MI2 & AXP2 & CR2 & CNT2 & RS2 & FR2 & FSZ2 & UW2).
    cbn [app] in FR2.
    apply implA_ret_evt.
    do 13 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
    apply evt_done.
    unfold bn_postA. do 17 eexists. exists m2, OW2, PL. split; [reflexivity|]. cbn [fst snd].
    split; [exact HEAP2|]. split; [exact LS2|]. split; [exact ST2|]. split; [exact MI2|]. split; [exact AXP2|].
    split; [clear - CR2 USED; lia|]. split; [exact CNT2|]. split; [exact RS2|].
    split; reflexivity. }

  assert (LOF16 : lo <= bv_unsigned sp + -160 - 16) by (clear - LO'; lia).
  assert (WRn : wref PL RMontN) by (apply hpl_wref; eapply hpl_mont; [reflexivity| exact HPM]).

  destruct (cenv_read_roA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra ras BN_FROM_MONT_WORD_COST Σ ls OW m LOF16 _ _ _ _ _ _ RMontN (am + 24) EV LS1 HAn RMontN_not_one)
    as (Dn & BNn & Un & (OKn1 & OKn2 & OKn3 & OKn4) & (ACN & ALN & An0 & AnS) & (ACDN & ALDN & Dn0 & DnS) & SEPn & LLn).
  set (bn := getbn RMontN ls) in *.
  unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNn. unfold BG_DMAX in OKn3.
  assert (NL31 : Z.of_nat (bn_top bn) <= 512) by (clear - OKn2 OKn3; lia).

  assert (AMF : 0 < am /\ am mod 8 = 0).
  { pose proof PARTS as (_ & _ & _ & (_ & _ & PM0) & _). rewrite HPM in PM0. unfold MONT_CTX_SZ in PM0.
    pose proof (AH_range _ _ _ _ _ _ _ HEAP PM0) as (M0a & M16a & _). clear - M0a M16a. split; [lia| Z.div_mod_to_equations; lia]. }
  destruct AMF as (AM0 & ALM0).

  hide_ors. ub1 ub_kind. step. ub1 ub_kind. ub1 ub_kind. unhide.
  do 3 step.

  clear MU WM OFF. pose proof (munch_refl (@nil (Z * Z)) m1) as MU1. assert (OFF1 : offshW (@nil (Z * Z))) by exact I.
  do 3 step. shl_with ACN ALN. chk0.
  step. rewrite (sx32_small (Z.of_nat (bn_top bn))) by (clear - NL31; lia).
  step. if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by (clear - NL31; lia).

  -
    assert (ET : bn_top bn = 0%nat) by (clear - KT; lia).
    unfold bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd]. fold bn.
    replace (bn_top bn =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; exact ET).
    destruct (cenv_struct_openA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra ras BN_FROM_MONT_WORD_COST Σ ls OW m LOF16 _ _ _ _ _ _ rt at_ EV LS1 HAt WRt)
      as (Dt & BNt & (OKt1 & OKt2 & OKt3 & OKt4) & ACT & ALT & At0 & AtS & OFT & ST1 & MI1 & CLOSE).
    set (bt := getbn rt ls) in *. unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNt.
    clear BNn Un MU1 OFF1. pose proof (munch_refl [(at_, at_ + 24)]%Z m1) as MU. pose proof (wmono_refl bgbsegs m1) as WM.
    assert (OFF : offshW [(at_, at_ + 24)]) by (cbn [offshW]; unfold SHLO, SHHI in *; clear - OFT; lia).
    hide_ors. ub. unhide.
    do 4 step. shl_with ACT ALT. chk0.
    step.

    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
    assert (OK' : bg_ok (bn_with_top bt 0)).
    { unfold bg_ok, bn_with_top, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OKt1|]. split; [clear; lia|]. split; [exact OKt3| exact OKt4]. }
    destruct (CLOSE m2 (bn_with_top bt 0) MU WM) as (ENVF & LSF); [exact BNt | reflexivity | reflexivity | exact OK' | assumption | assumption |].

    pose proof (ExpBodyKitF.cenv_pre_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ENVF) as WFF.
    assert (ENVG : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra (Some ras) BN_FROM_MONT_WORD_COST Σ ls OW m
                     [CB 56 (cells_bytes [CB 24 jf1; C8 (Z_to_bv 64 ax); C8 (Z_to_bv 64 at_); CB 16 jf2]);
                      C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] 0 Σ (setbn rt (bn_with_top bt 0) ls) m2 OW).
    { eapply ExpBodyKitF.cenv_recastA; [exact ENVF | | |].
      - cbn [cells_wf cell_wf app] in WFF |- *. destruct WFF as (LJ1 & _ & _ & LJ2 & _).
        split; [| repeat split].
        rewrite (cells_bytes_length [CB 24 jf1; C8 (Z_to_bv 64 ax); C8 (Z_to_bv 64 at_); CB 16 jf2]) by (cbn [cells_wf cell_wf]; repeat split; assumption).
        reflexivity.
      - cbn [cells_bytes cbytes app]. rewrite <- !app_assoc. reflexivity.
      - reflexivity. }
    apply evt_done.
    eapply (EPI Σ (setbn rt (bn_with_top bt 0) ls) m2 OW 0); [exact ENVG | exact LSF | unfold BN_FROM_MONT_WORD_COST, MC; clear; lia].
  -
    assert (NT : bn_top bn <> 0%nat) by (clear - KT; lia).
    unfold bbind at 1. unfold bget at 1. cbn [bind ret tree_ops tbind fst snd]. fold bn.
    replace (bn_top bn =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact NT).
    set (nl := bn_top bn) in *.
    assert (LOF : lo <= bv_unsigned sp + -160 - BN_WEXPAND_STACK)
      by (unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK, CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO'; lia).

    hide_ors. ub. unhide.
    clear MU1 OFF1. pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp + -104)]%Z m1) as MU. pose proof (wmono_refl bgbsegs m1) as WM.
    assert (OFF : offshW [(bv_unsigned sp + -160, bv_unsigned sp + -104)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; clear - SPR LO' CEIL C1' C2' C3'; lia).
    step.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m1s end.
    lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: _ :: CB 8 ?j2 :: _) => set (jf3 := j2) in * end.
    destruct (ExpBodyKitF.cenv_localA LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra (Some ras) BN_FROM_MONT_WORD_COST Σ ls OW m _
                [CB 24 jf1; C8 (Z_to_bv 64 ax); C8 (Z_to_bv 64 at_); CB 8 jf3; C8 (Z_to_bv 64 (Z.of_nat nl));
                 C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _ _ _ _ _ _ _ _
                EV LS1 MU WM ltac:(clear; lia) ltac:(clear; lia) ST MI FR ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as (EVs & LSs).
    clear EV LS1 OK HEAP1 MU WM OFF. rename EVs into EV. rename LSs into LS1. pose proof EV as (OK & HEAP1 & _).
    step. setreg 24%Z (Z_to_bv 64 (Z.of_nat (2 * nl))) ltac:(f_equal; rewrite unsigned_lit by (clear - NL31; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia);
                                                              rewrite bn_swrap32_small by (clear - NL31; lia); clear; lia).
    step. step. step. step.

    clear BNn SHB1 SHB2 ST MI FR HWL WOK. try clear Un.
    apply evt_done. unfold bbind at 1. cbn [bind tree_ops].
    eapply implA_bind.
    { eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rx) (a := ax) (words := (2 * nl)%nat) (OW := OW) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAx | exact WRx | reflexivity | reflexivity | clear - NL31; lia].
      - eapply cenv_preA; [exact EV | exact LS1 | exact LOF | unfold BN_FROM_MONT_WORD_COST, MC; clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_bn_from_montgomery_word_225dd8 : uk_call BN_FROM_MONTGOMERY_WORD 0x225fc0 BN_WEXPAND) CTX). }
    cbv beta. intros [u1 ls2] Σ2 ms2 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -160) BN_FROM_MONT_WORD_COST Σ ls OW) in PO; [| exact OK | exact HEAP1].
    cbn [fst snd] in *.
    destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & F2 & fc2 & m2 & OW2 & PL2 & -> & CP & (EPL & -> & HDM1 & WXR1 & BST1)).
    subst PL2. specialize (CP eq_refl).
    assert (E2 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra (Some ras) BN_FROM_MONT_WORD_COST Σ ls OW m
                   [CB 24 jf1; C8 (Z_to_bv 64 ax); C8 (Z_to_bv 64 at_); CB 8 jf3; C8 (Z_to_bv 64 (Z.of_nat nl));
                    C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] (0 + MC) Σ2 ls2 m2 OW2 /\ lib_state ls2 m2 OW2 PL EA)
      by (eapply cenv_postA; [exact EV | exact CP]).
    destruct E2 as (EV2 & LS2).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS2.
    rewrite (ret_pc_even 2252736) by (clear; lia).
    clear CP EV LS1 HEAP1 ACN ALN An0 AnS ACDN ALDN Dn0 DnS SEPn LLn Dn OKn4 HEAP LS PARTS PRE UW CNT CRED.

    pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAx) as HAx2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAt) as HAt2.
    pose proof (ref_at_montN ls2 OW2 PL am qm HPM) as HAn2.
    assert (EN1 : getbn RMontN ls2 = bn).
    { destruct WXR1 as [[_ ->]|[_ (pn & ->)]]; [reflexivity| apply getbn_setbn_other; exact NExn]. }
    assert (EN0 : st_n0 ls2 = st_n0 ls) by (destruct WXR1 as [[_ ->]|[_ (pn & ->)]]; reflexivity).
    set (rb := getbn rx ls2) in *.
    assert (HDr : (0 < bn_dmax rb)%nat) by (clear - HDM1 NT; lia).
    assert (HDn : (0 < bn_dmax (getbn RMontN ls2))%nat) by (rewrite EN1; clear - OKn2 NT; fold nl in OKn2; lia).
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.
    pose proof EV2 as (OK2 & HEAP2 & _).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.

    pose proof PARTS2 as (_ & _ & _ & (_ & _ & PM) & _). rewrite HPM in PM. unfold MONT_CTX_SZ in PM.
    pose proof (AH_range _ _ _ _ _ _ _ HEAP2 PM) as (M0 & M16 & _ & MCe & _).
    destruct (AH_acc _ _ _ _ (qm, am, 96) HEAP2 ltac:(apply in_or_app; left; exact PM)) as (_ & ACM). cbn [blk_addr blk_size fst snd] in ACM.
    assert (ALM : am mod 8 = 0) by (clear - M16; Z.div_mod_to_equations; lia).
    clear PM M16.
    destruct (cenv_hole1F LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra ras BN_FROM_MONT_WORD_COST Σ ls OW m LOF16 _ _ _ _ _ _ rx ax 128
                EV2 LS2 HAx2 WRx HDr ltac:(clear; lia) ltac:(clear - LO'; lia))
      as (Dr & pr & Edr & Hinr & BNr & Ur & (OKr1 & OKr2 & OKr3 & OKr4) & (ACX & ALX & Ax0 & AxS & OFX) & (ACDX & ALDX & Dr0 & DrS & OFDX) & SEPr & FRAMEH & CLOSE).
    destruct (cenv_hole1A LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra ras BN_FROM_MONT_WORD_COST Σ ls OW m LOF16 _ _ _ _ _ _ RMontN (am + 24)
                EV2 LS2 HAn2 WRn HDn)
      as (Dn2 & pn & Edn & Hinn & BNn2 & Un2 & _ & (ACN2 & ALN2 & An20 & An2S & OFN2) & (ACDN2 & ALDN2 & Dn20 & Dn2S & OFDN2) & SEPn2 & SEPAn & ST2 & MI2 & _).
    fold rb in Edr, Hinr, BNr, Ur, OKr1, OKr2, OKr3, OKr4, ACDX, DrS, OFDX, SEPr, FRAMEH, CLOSE.
    rewrite EN1 in Edn, Hinn, BNn2, Un2, ACDN2, Dn2S, OFDN2, SEPn2, SEPAn.
    assert (ARRr : bn_arr m2 OW2 (pl_of PL rx) Dr rb) by (unfold bn_arr; rewrite Edr; split; [exact Hinr| exact Ur]).

    assert (DrL : Dr + 8 * Z.of_nat (bn_dmax rb) <= lo)
      by (pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinr) as (_ & _ & _ & X & _); unfold BnHeapA.ACEIL in *; clear - X CEIL; lia).
    assert (DnL : Dn2 + 8 * Z.of_nat (bn_dmax bn) <= lo)
      by (pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinn) as (_ & _ & _ & X & _); unfold BnHeapA.ACEIL in *; clear - X CEIL; lia).
    assert (AxL : ax + 24 <= lo)
      by (destruct (ref_at_rangeF ls2 OW2 PL EA (bv_unsigned sp) USTACK_TOP Σ2 LB m2 rx ax HEAP2 PARTS2 FROK HAx2 NROx) as (_ & X & _); unfold BnHeapA.ACEIL in *; clear - X CEIL; lia).
    assert (AmL : am + 96 <= lo) by (unfold BnHeapA.ACEIL in *; clear - MCe CEIL; lia).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinr) as (DrP & _ & _ & _ & RLO).
    pose proof (AH_range _ _ _ _ _ _ _ HEAP2 Hinn) as (DnP & _).
    pose proof (SEPn2 rx ax HAx2) as SXN. pose proof (SEPr RMontN (am + 24) HAn2) as SNR. pose proof (SEPr rx ax HAx2) as SXR.
    pose proof (SEPAn rx ax Dr ltac:(intros E; apply NExn; symmetry; exact E) HAx2 NROx ARRr) as DND. fold rb in DND.
    pose proof (struct_disj Σ2 OW2 LB m2 HEAP2 ls2 PL EA _ _ PARTS2 FROK rx RMontN ax (am + 24) NExn HAx2 HAn2) as SXA.
    clear SEPr SEPn2 SEPAn ARRr.
    pose proof EV2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2 & FSZ2 & _). cbn [app] in FR2.
    unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz in BNr, BNn2. unfold BG_DMAX in OKr3.
    pose proof (munch_refl (fpF1 (bv_unsigned sp) (bv_unsigned sp + -160) 128 ax Dr (bn_dmax rb)) m2) as MU. pose proof (wmono_refl bgbsegs m2) as WM.
    unfold fpF1 in MU.
    assert (OFF : offshW [(bv_unsigned sp + -160 - 128, bv_unsigned sp); (ax, ax + 24); (Dr, Dr + 8 * Z.of_nat (bn_dmax rb))]).
    { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. clear - OFX OFDX SPR LO' CEIL C1' C2' C3'. lia. }
    assert (AxR : 0 < ax < 2^64) by (clear - Ax0 AxS SPR; lia).
    assert (LUr : Z.of_nat (length (wlimbs (bn_buf rb))) = Z.of_nat (bn_dmax rb)) by (rewrite wlimbs_len; reflexivity).
    assert (LUn : Z.of_nat (length (wlimbs (bn_buf bn))) = Z.of_nat (bn_dmax bn)) by (rewrite wlimbs_len; reflexivity).

    unfold bbind, bget, bgetst, bset, bret. cbn [bind ret tree_ops tbind fst snd]. fold rb. rewrite EN1.
    destruct ((0 <=? st_n0 ls2) && (st_n0 ls2 <? 18446744073709551616)) eqn:GN0; cbn [negb];
      [| unfold bunr; cbn [unreachable tree_ops]; apply implA_unr].
    apply andb_true_iff in GN0. destruct GN0 as [GN1 GN2]. apply Z.leb_le in GN1. apply Z.ltb_lt in GN2.
    set (n0 := st_n0 ls2) in *. set (np := firstn nl (bn_buf bn)) in *.
    change (splice (bn_buf rb) (bn_top rb) (repeat 0 (2 * nl - bn_top rb))) with (clear_top (bn_buf rb) (bn_top rb) (2 * nl)).
    destruct (mont_reduce_loop np n0 nl nl 0 (clear_top (bn_buf rb) (bn_top rb) (2 * nl)) 0) as [buf carry] eqn:EMR.
    cbv beta iota.
    apply implA_from_evt. unfold MallocRep.wz.

    apply hide_intro in RLO. apply hide_intro in SXN. apply hide_intro in SNR. apply hide_intro in DND. apply hide_intro in OFX. apply hide_intro in OFDX.
    apply hide_intro in OFN2. apply hide_intro in OFDN2. apply hide_intro in OKr4. apply hide_intro in Un2. apply hide_intro in HDM1.
    apply hide_intro in WXR1. apply hide_intro in BST1. apply hide_intro in FRAMEH. apply hide_intro in CLOSE.

    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AxR; lia); zify_cond KZ; [exfalso; clear - KZ AxR; lia| clear KZ].

    ub1 ub_kind. step. ub1 ub_kind.

    do 3 step. shl_with ACN2 ALN2. chk0.
    do 4 step. shl_with ACX ALX. step. chk0.

    step. step. rewrite !(sx32_small (Z.b2z _)) by (apply b2z_31).
    step. rewrite !(unsigned_lit (Z.b2z _)) by (apply b2z_64). rewrite lxor_b2z.
    step. step.
    apply hide_intro in SXR. apply hide_intro in SXA.

    step. shl_with ACN2 ALN2. chk0.
    do 2 step. shl_with ACX ALX. chk0.
    step. step. step.
    step. step.

    do 3 step. shl_with ACX ALX. step. chk0.
    step.

    setreg 26%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite ?unsigned_lit by (clear - Dr0 DrS SPT; lia); symmetry; apply land7; exact ALDX).

    step. rewrite (lts_signed 0 (Z.of_nat (2 * nl))) by (clear - NL31; lia).
    if_cases KB; zify_cond KB; [exfalso; clear - KB NT; lia|]. clear KB.
    step. rewrite (sx32_small (Z.of_nat (bn_top rb))) by (clear - OKr2 OKr3; lia).
    do 7 step.

    assert (LBr : length (bn_buf rb) = bn_dmax rb) by reflexivity.
    assert (BDR : 0 <= Dr /\ Dr + 8 * Z.of_nat (bn_dmax rb) <= 140737488355328) by (clear - Dr0 DrS SPT; lia).
    assert (TOPR : 0 <= Z.of_nat (bn_top rb) <= Z.of_nat (bn_dmax rb) /\ Z.of_nat (bn_dmax rb) <= 512) by (clear - OKr2 OKr3; lia).

    setreg 13%Z (Z_to_bv 64 1)
      ltac:(rewrite v_sltu_b2z, !unsigned_lit by (clear - BDR; lia); replace (0 <? Dr) with true by (symmetry; apply Z.ltb_lt; exact DrP); reflexivity).
    lazymatch goal with |- context [Z_to_bv 64 (Z.land (bv_unsigned (v_sltiu (Z_to_bv 64 0) 1)) (bv_unsigned (Z_to_bv 64 1)))] =>
      change (Z_to_bv 64 (Z.land (bv_unsigned (v_sltiu (Z_to_bv 64 0) 1)) (bv_unsigned (Z_to_bv 64 1)))) with (Z_to_bv 64 1) end.
    setreg 15%Z (Z_to_bv 64 (Z.of_nat 0 - Z.of_nat (bn_top rb)))
      ltac:(f_equal; rewrite unsigned_lit by (clear - TOPR; lia); rewrite bn_swrap32_small by (clear - TOPR; lia); reflexivity).
    assert (EK : exists K2, (2 * nl)%nat = S K2) by (exists (2 * nl - 1)%nat; clear - NT; lia). destruct EK as (K2 & EK2).
    setreg 16%Z (Z_to_bv 64 (Z.of_nat (S K2))) ltac:(f_equal; rewrite EK2; reflexivity).

    lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mq _) =>
      pose proof (acc_munch bgbsegs _ m2 mq Dr _ ACDX MU OFF (proj1 BDR) (proj2 BDR)) as ACDc;
      pose proof (munch_refl [(Dr, Dr + 8 * Z.of_nat (length (bn_buf rb)))]%Z mq) as MUL; pose proof (wmono_refl bgbsegs mq) as WML;
      epose proof (fm_clearA Q F2 fc2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dr (bn_buf rb) (bn_top rb) (2 * nl)%nat mq K2 0%nat mq _ _) as XL1;
      replace (Dr + 8 * Z.of_nat 0) with Dr in XL1 by (clear; lia);
      eapply XL1; clear XL1;
        [ exact OKr1 | apply hide_elim in HDM1; exact HDM1 | rewrite LBr; clear - TOPR; lia | clear - TOPR; lia | exact OKr2
        | exact ACDc | exact ALDX | exact BDR | exact DrP | cbn [offshW]; apply hide_elim in OFDX; unfold SHLO, SHHI in *; rewrite LBr; clear - OFDX; lia
        | clear - EK2; lia | exact MUL | exact WML | exact Ur | assumption | ]
    end.
    intros m3 y5 y6 y15 U3 MU3 WM3 MI3. clear MUL WML ACDc Ur.
    rewrite LBr in MU3. apply hide_elim in SXR. apply hide_elim in SNR.
    lazymatch type of MU3 with munch _ ?mm _ => transport_after_call bgbsegs mm m3 MU3 WM3; clear MU3 WM3;
      try match goal with H : mem_inv bgbsegs mm |- _ => clear H end; try clear mm end.
    apply hide_intro in SNR.
    set (B1 := clear_top (bn_buf rb) (bn_top rb) (2 * nl)) in *.
    assert (LB1 : length B1 = bn_dmax rb) by (subst B1; rewrite clear_top_length by (apply hide_elim in HDM1; rewrite LBr; exact HDM1); exact LBr).
    assert (LM1 : limbs B1) by (subst B1; apply clear_top_limbs; exact OKr1).
    clear LUr. assert (LUr : Z.of_nat (length (wlimbs B1)) = Z.of_nat (bn_dmax rb)) by (rewrite wlimbs_len, LB1; reflexivity).

    setreg 24%Z (Z_to_bv 64 (Z.of_nat (2 * nl))) ltac:(f_equal; rewrite EK2; reflexivity). clear K2 EK2.

    shl_with ACX ALX. chk0.
    apply hide_elim in SXA.
    step.
    apply hide_intro in SXR. apply hide_intro in SXA.

    do 3 step. shl_with ACM ALM. chk0.
    step.
    step. rewrite (lts_signed 0 (Z.of_nat nl)) by (clear - NL31; lia).
    if_cases KB; zify_cond KB; [exfalso; clear - KB NT; lia|]. clear KB.
    apply hide_elim in FRAMEH.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (FRAMEH mq MU WM) as (HEAPc & LSHc);
      pose proof (lib_state_mont_cells _ _ _ _ _ _ _ am qm LSHc HPM) as MCc end.
    unfold mont_cells, MallocRep.wz in MCc. fold n0 in MCc.
    step. clear MCc LSHc.
    do 4 step.
    ub1 ub_kind.
    do 2 step.

    setreg 19%Z (Z_to_bv 64 (8 * Z.of_nat nl))
      ltac:(f_equal; rewrite ?unsigned_lit by (clear - NL31; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
    setreg 25%Z (Z_to_bv 64 (shad (Dr + 8 * Z.of_nat 0)))
      ltac:(f_equal; unfold shad; rewrite ?unsigned_lit by (clear - BDR; lia); rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8;
            replace (Dr + 8 * Z.of_nat 0) with Dr by (clear; lia); clear; lia).
    setreg 21%Z (Z_to_bv 64 (18446744073709551615 - Dr - 8 * Z.of_nat 0))
      ltac:(f_equal; rewrite ?unsigned_lit by (clear - BDR; lia); rewrite (lxor_ones64 Dr) by (clear - BDR; lia); clear; lia).
    setreg 23%Z (Z_to_bv 64 (Dr + 8 * Z.of_nat 0)) ltac:(f_equal; clear; lia).

    apply hide_elim in Un2. apply hide_elim in DND. apply hide_elim in SXN. apply hide_elim in HDM1. apply hide_elim in OFDX. apply hide_elim in OFDN2.
    assert (LBn : length (bn_buf bn) = bn_dmax bn) by reflexivity.
    assert (NLD : (nl <= bn_dmax bn)%nat) by (exact OKn2).
    assert (BDN : 0 <= Dn2 /\ Dn2 + 8 * Z.of_nat (bn_dmax bn) <= 140737488355328) by (clear - Dn20 Dn2S SPT; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      assert (HNP : limbs_at bgbsegs mq Dn2 np);
      [ apply limbs_at_of_u64arr; subst np;
        assert (Unc : u64arr bgbsegs mq Dn2 (wlimbs (bn_buf bn)));
        [ eapply u64arr_transport; [exact Un2| exact MU| exact WM|]; cbn [disjoint_from]; rewrite wlimbs_len, LBn; clear - DnL SXN DND LO'; lia |];
        apply (limbarr_split bgbsegs _ Dn2 (bn_buf bn) nl) in Unc; [exact (proj1 Unc)| rewrite LBn; exact NLD] |];
      pose proof (acc_munch bgbsegs _ m2 mq Dr _ ACDX MU OFF (proj1 BDR) (proj2 BDR)) as ACRc;
      pose proof (acc_munch bgbsegs _ m2 mq Dn2 _ ACDN2 MU OFF (proj1 BDN) (proj2 BDN)) as ACNc;
      pose proof (AH_shb _ _ _ _ HEAPc) as SHBc;
      pose proof (OSSVerify.Proofs.openssl.bignum.lib.BgBnRB.AFrameComp.rw_cells_app_l mq (bv_unsigned sp + -160)
                    [C8 (Z_to_bv 64 ((ax + 16) ≫ 3 + SHB)); C8 (Z_to_bv 64 (ax ≫ 3 + SHB)); C8 (Z_to_bv 64 (ax + 16)); C8 (Z_to_bv 64 ax); C8 (Z_to_bv 64 at_);
                     C8 (Z_to_bv 64 Dn2); C8 (Z_to_bv 64 (Z.of_nat nl))] _ FR2) as FRP;
      assert (I0 : RBA sp mq lo Dr Dn2 np nl (bn_dmax rb) (Z_to_bv 64 ((ax + 16) ≫ 3 + SHB)) (Z_to_bv 64 (ax ≫ 3 + SHB)) (Z_to_bv 64 (ax + 16)) (Z_to_bv 64 ax) (Z_to_bv 64 at_) mq B1)
        by (apply RBA_init; [exact LM1 | exact LB1 | exact U3 | exact HNP | exact ST2 | assumption | exact FRP])
    end.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply (fm_reduceA sp gp (Z_to_bv 64 TP_A) F2 fc2 mq lo Dr Dn2 n0 np nl (bn_dmax rb)
                (Z_to_bv 64 ((ax + 16) ≫ 3 + SHB)) (Z_to_bv 64 (ax ≫ 3 + SHB)) (Z_to_bv 64 (ax + 16)) (Z_to_bv 64 ax) (Z_to_bv 64 at_))
        with (K := (nl - 1)%nat) (i := 0%nat) (m1 := mq) (B := B1) (C := 0) (cnt := Z.of_nat nl);
        [ subst np; apply limbs_firstn; exact OKn1
        | subst np; apply firstn_length_le; rewrite LBn; exact NLD
        | clear - NT; lia | exact HDM1 | clear - TOPR; lia | split; [exact GN1| exact GN2]
        | clear - DND NLD HDM1; lia
        | clear - LO'; lia
        | unfold SHHI, BnHeapA.ACEIL in *; clear - C2' CEIL; lia
        | clear - DrL LO'; lia
        | clear - DnL NLD LO'; lia
        | exact ACRc | exact ALDX | exact BDR
        | eapply acc_sub; [exact ACNc | clear; lia | clear - NLD; lia]
        | exact ALDN2 | clear - BDN NLD; lia
        | exact DrP | exact DnP
        | unfold SHLO, SHHI in *; exact OFDX
        | intros mz MUz; eapply AsLeaf.shb_cells_munch; [exact SHBc | exact MUz | |];
          cbn [disjoint_from]; unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, BnHeapA.ACEIL in *;
          apply hide_elim in RLO; clear - RLO HDM1 LO' CEIL C1'; lia
        | clear - SPT; lia
        | clear - NT; lia | f_equal; clear - NT; lia | exact I0 | clear; lia | ]
    end.
    intros m4 Bn Cn v1 v5 v6 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 EML I4 HC.
    replace (S (nl - 1)) with nl in EML by (clear - NT; lia). rewrite EMR in EML. injection EML as <- <-.
    destruct I4 as (LMB & LENB & HRB & HNB & WRB & STc & MIc & MUc & WMc & FRc).
    clear I0 HNP ACRc ACNc SHBc FRP U3 ST2 HEAPc. apply hide_elim in SNR. apply hide_elim in SXR.
    apply hide_intro in DND. apply hide_intro in SXN. apply hide_intro in OFDX. apply hide_intro in OFDN2. apply hide_intro in Un2.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bgbsegs mm m4 MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv bgbsegs mm |- _ => clear H end; try clear mm end.

    apply hide_intro in SNR. apply hide_intro in SXR.

    set (b2 := mkBN (bn_d rb) buf (2 * nl) (xorb (bn_neg rb) (bn_neg bn)) (bn_flags rb)) in *.
    apply hide_elim in OKr4. apply hide_elim in CLOSE.
    assert (OK2b : bg_ok b2).
    { unfold bg_ok, BG_DMAX. change (bn_dmax b2) with (length buf). cbn [b2 bn_buf bn_top bn_flags]. rewrite LENB.
      split; [exact LMB|]. split; [exact HDM1|]. split; [exact OKr3| exact OKr4]. }
    destruct (CLOSE m4 b2 [C8 (Z_to_bv 64 ((ax + 16) ≫ 3 + SHB)); C8 (Z_to_bv 64 (ax ≫ 3 + SHB)); C8 (Z_to_bv 64 (ax + 16)); C8 (Z_to_bv 64 ax); C8 (Z_to_bv 64 at_);
                           C8 (Z_to_bv 64 Dn2); C8 (Z_to_bv 64 (Z.of_nat nl));
                           C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] MU WM) as (ENV3 & LS3).
    { unfold bn_cells, BnRepDefs.bn_cells, MallocRep.wz. change (bn_dmax b2) with (length buf). cbn [b2 bn_buf bn_top bn_neg bn_flags]. rewrite LENB. exact BNr. }
    { apply u64arr_of_limbs_at; [exact HRB| change (bn_buf b2) with buf; rewrite LENB; exact WRB]. }
    { reflexivity. } { change (bn_buf b2) with buf. rewrite LENB. reflexivity. } { exact OK2b. } { exact STc. } { exact MIc. }
    { cbn [app]. exact FR2. } { cbn [cells_size csize Nat.add]. clear. lia. }

    pose proof (ref_at_setbn ls2 OW2 PL rx b2 rt at_) as HAt3. apply proj2 in HAt3. specialize (HAt3 HAt2).
    pose proof (ref_at_setbn ls2 OW2 PL rx b2 rx ax) as HAx3. apply proj2 in HAx3. specialize (HAx3 HAx2).
    pose proof ENV3 as (OK3 & HEAP3 & _).
    clear CLOSE FRAMEH BNr BNn2 HRB WRB HNB FRc.

    do 4 step.
    clear MU WM FR2 STc MIc.
    repeat match goal with H : acc bgbsegs _ _ _ |- _ => clear H end.
    repeat match goal with H : mem_inv bgbsegs _ |- _ => clear H end.
    clear LUr LUn OFF Un2 EV2 LS2.
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_wexpand_walkA) with (lo := lo) (ras := bv_unsigned ra :: ras) (r := rt) (a := at_) (words := nl) (OW := OW2) (LB := LB) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAt3 | exact WRt | reflexivity | reflexivity | clear - NL31; lia].
      - eapply cenv_preA; [exact ENV3 | exact LS3 | exact LOF | unfold BN_FROM_MONT_WORD_COST, MC; clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl ENV3).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ (E_bn_from_montgomery_word_225fc4 : uk_call BN_FROM_MONTGOMERY_WORD 0x2261ac BN_WEXPAND) CTX). }
    cbv beta. intros [u5 ls5] Σ5 ms5 PO.
    apply (bn_postA_cpost LB PL EA lo (bv_unsigned sp) (bv_unsigned sp + -160) BN_FROM_MONT_WORD_COST Σ ls OW) in PO; [| exact OK3 | exact HEAP3].
    cbn [fst snd] in *.
    destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & F5 & fc5 & m5 & OW5 & PL5 & -> & CP & (EPL & -> & HDM3 & WXR3 & BST3)).
    subst PL5. specialize (CP eq_refl).
    lazymatch type of ENV3 with cenvA _ _ _ _ _ _ _ _ _ _ _ _ _ ?pre3 _ _ _ _ _ =>
      assert (E5 : cenvA LB PL lo (bv_unsigned sp) (bv_unsigned sp + -160) s0 ra (Some ras) BN_FROM_MONT_WORD_COST Σ ls OW m
                     pre3 (0 + MC + MC) Σ5 ls5 m5 OW5 /\ lib_state ls5 m5 OW5 PL EA)
        by (eapply cenv_postA; [exact ENV3 | exact CP])
    end.
    destruct E5 as (EV5 & LS5).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CP) as RS5.
    rewrite (ret_pc_even 2253228) by (clear; lia).
    clear CP.

    pose proof (ref_at_stable _ _ _ _ PL _ _ RS5 HAt3) as HAt5. pose proof (ref_at_stable _ _ _ _ PL _ _ RS5 HAx3) as HAx5.
    pose proof (ref_at_montN ls5 OW5 PL am qm HPM) as HAn5.
    set (bs2 := setbn rx b2 ls2) in *.
    assert (HVt3 : vref rt bs2) by (eapply ref_at_valid; [exact LS3| exact HAt3]).
    assert (HVn3 : vref RMontN bs2) by (eapply ref_at_valid; [exact LS3| exact (ref_at_montN bs2 OW2 PL am qm HPM)]).
    assert (EX2 : getbn rx bs2 = b2) by (subst bs2; apply getbn_setbn_same; exact HVx2).
    assert (EN2 : getbn RMontN bs2 = bn) by (subst bs2; rewrite getbn_setbn_other by exact NExn; exact EN1).
    assert (ET2 : getbn rt bs2 = getbn rt ls2) by (subst bs2; apply getbn_setbn_other; intros E; apply NEtx; symmetry; exact E).
    apply hide_elim in WXR3 || idtac.
    assert (EX3 : getbn rx ls5 = b2).
    { destruct WXR3 as [[_ ->]|[_ (p3 & ->)]]; [exact EX2| rewrite getbn_setbn_other by exact NEtx; exact EX2]. }
    assert (EN3 : getbn RMontN ls5 = bn).
    { destruct WXR3 as [[_ ->]|[_ (p3 & ->)]]; [exact EN2| rewrite getbn_setbn_other by exact NEtn; exact EN2]. }
    assert (Hinn5 : In (pn, Dn2, 8 * Z.of_nat (bn_dmax bn)) OW5).
    { apply BST3; [exact Hinn|]. rewrite ET2. intros E.
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS3) as (_ & _ & IDS3 & _).
      refine (ids_bn_neq rt RMontN bs2 pn pn (ids_m_nodup _ _ _ IDS3) HVt3 HVn3 NEtn _ _ eq_refl).
      - rewrite ET2. exact E.
      - rewrite EN2. exact Edn. }

    unfold MallocRep.wz.
    eapply (fm_tailA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m Σ ls OW LB PL EA lo ras rt rx at_ ax am qm Σ5 ls5 m5 OW5 (0 + MC + MC) F5 fc5 nl np Dn2 pn carry);
      [ exact EV5 | exact LS5 | unfold BN_FROM_MONT_WORD_COST, MC; clear; lia | clear - LO'; lia | exact HAt5 | exact HAx5 | exact WRt | exact WRx | exact HPM
      | exact NEtx | exact NEtn | exact NExn | rewrite EN3; reflexivity | rewrite EN3; reflexivity | exact NT | rewrite EN3; exact Edn | rewrite EN3; exact Hinn5
      | exact HDM3 | rewrite EX3; change (bn_dmax b2) with (length buf); rewrite LENB; try (apply hide_elim in HDM1); exact HDM1 | exact HC | exact EPI ].
Qed.

End WithRT.
