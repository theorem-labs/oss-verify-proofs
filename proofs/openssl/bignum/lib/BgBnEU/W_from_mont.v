(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnBridge BgState BgInv BgWords BgLib BgArith BgMont.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX BnLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_sub_words.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU2 Require Import WU_from_mont_loops.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import W_expand.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit ExpKitArr W_mont.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition fm_kind (pc : Z) : Z :=
  match pc with
  | 1048652 => 2 | 1048664 => 1 | 1048668 => 2 | 1048680 => 1 | 1048684 => 1 | 1048688 => 2 | 1048716 => 1 | 1048720 => 2
  | 1048792 => 2 | 1048796 => 1 | 1048800 => 1 | 1048804 => 2 | 1048808 => 2 | 1048880 => 2 | 1048884 => 2 | 1048912 => 2
  | 1048936 => 2 | 1048992 => 2 | 1048996 => 1 | 1049000 => 2 | 1049020 => 2 | 1049032 => 2 | 1049036 => 1 | 1049040 => 1
  | 1049044 => 1 | 1049048 => 1 | 1049052 => 2 | 1049128 => 2 | 1049132 => 2 | 1049136 => 1 | 1049140 => 2 | 1049144 => 1
  | 1049148 => 1 | 1049152 => 2 | 1049156 => 2 | 1049204 => 2 | 1049208 => 1 | 1049212 => 2
  | _ => 0
  end.
Ltac ub := repeat (ub1 fm_kind).
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.

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
  unfold sel_res, splice. cbn [firstn app Nat.add]. rewrite LS.
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

Lemma fm_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (Printf_lib.bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Printf_lib.Z_to_le_bytes_to_Z.
Qed.

Lemma fm_cb8_c8 : forall m A bs post, rw_cells bgusegs m A (CB 8 bs :: post) -> rw_cells bgusegs m A (C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A bs post H.
  change (CB 8 bs :: post) with ([] ++ CB 8 bs :: post) in H.
  change (C8 (le_bytes_to_word bs) :: post) with ([] ++ C8 (le_bytes_to_word bs) :: post).
  destruct H as [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite fm_le8_of_bytes by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.

Lemma fm_slot : forall m A w rest, rw_cells bgusegs m A (C8 (Z_to_bv 64 w) :: rest) -> limbs_at bgusegs m A [w].
Proof.
  intros m A w rest [[_ H] _]. cbn [cells_bytes cbytes] in H. apply bytes_at_app in H.
  unfold limbs_at. rewrite lbytes_cons, lbytes_nil, app_nil_r. exact (proj1 H).
Qed.

Definition fm_ret (rt rx : bnref) (nl : nat) (np : list Z) (carry : Z) (bs : bstate bptr) : bignum bptr :=
  mkBN (bn_d (getbn rt bs)) (splice (bn_buf (getbn rt bs)) 0 (mont_final (slice (bn_buf (getbn rx bs)) nl nl) np carry)) nl
       (bn_neg (getbn rx bs)) (bn_flags (getbn rt bs)).
Definition fm_final (rt rx : bnref) (nl : nat) (np : list Z) (carry : Z) (bs : bstate bptr) : bstate bptr :=
  setbn rx (bn_with_buf (getbn rx (setbn rt (fm_ret rt rx nl np carry bs) bs))
                        (splice (bn_buf (getbn rx (setbn rt (fm_ret rt rx nl np carry bs) bs))) nl (repeat 0 nl)))
        (setbn rt (fm_ret rt rx nl np carry bs) bs).

Lemma fm_flag_nz_al : forall D, 0 < D < 2^64 -> D mod 8 = 0 ->
  Z_to_bv 64 (Z.land (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 D)) 7)) 1)) (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 D)))) = Z_to_bv 64 1.
Proof.
  intros D H1 H2.
  rewrite (unsigned_lit D) by lia.
  replace (Z.land D 7) with 0 by (change 7 with (2^3 - 1); rewrite zb_land_mask by lia; change (2^3) with 8; lia).
  rewrite v_sltiu_b2z, v_sltu_b2z. rewrite (unsigned_lit D) by lia.
  replace (bv_unsigned (Z_to_bv 64 0) <? D) with true by (symmetry; apply Z.ltb_lt; rewrite unsigned_lit by lia; lia).
  vm_compute. reflexivity.
Qed.

Lemma fm_sltu_nz : forall D, 0 < D < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 D) = Z_to_bv 64 1.
Proof.
  intros D H1. rewrite v_sltu_b2z. rewrite (unsigned_lit D) by lia.
  replace (bv_unsigned (Z_to_bv 64 0) <? D) with true by (symmetry; apply Z.ltb_lt; rewrite unsigned_lit by lia; lia).
  reflexivity.
Qed.

Lemma fm_land7 : forall D, 0 <= D < 2^64 -> D mod 8 = 0 -> Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 D)) 7) = Z_to_bv 64 0.
Proof. intros D H1 H2. rewrite (unsigned_lit D) by lia. f_equal. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. lia. Qed.

Lemma fm_lxor_mk : forall k, 0 <= k < 2^64 -> Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 k)) 18446744073709551615) = Z_to_bv 64 (18446744073709551616 - 1 - k).
Proof. intros k H. rewrite (unsigned_lit k) by lia. f_equal. rewrite zb_lxor_ones by lia. lia. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_FROM_MONT_WORD_STACK : Z := 112 + BN_WEXPAND_STACK.

Section Final.
  Variables (LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B SPv FB : Z).
  Variables (se : PState) (bse : bstate bptr) (OWe : list block) (me : mem).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOFB : lo <= FB.
  Hypothesis FBSP : FB <= SPv.
  Hypothesis SPB : SPv <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis SPR : SPv < 2^64.
  Hypothesis FROK : frames_ok PL SPv B.
  Hypothesis FB112 : FB = SPv - 112.
  Hypothesis LOF80 : lo <= FB - 80.

  Lemma L_final : forall (Q : bstate bptr -> PState -> machine_state -> Prop) (frr : list cell) (gp : word) (F : bvmap 5 word) (fc : bv 32)
      (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) (rt rx : bnref) (at_ ax am : Z) (qm : bptr)
      (Dn : Z) (pn : bptr) (carry : Z)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    kenv LB PL lo B SPv FB se bse OWe me (C8 (Z_to_bv 64 Dn) :: frr) st bs m OW -> lib_state bs m OW PL EA ->
    ref_at bs OW PL rt at_ -> ref_at bs OW PL rx ax -> wref PL rt -> wref PL rx -> pl_mont PL = Some (am, qm) ->
    rt <> rx -> rt <> RMontN -> rx <> RMontN ->
    0 < at_ -> at_ mod 8 = 0 -> at_ < 2^63 -> 0 < ax -> ax mod 8 = 0 -> ax < 2^63 ->
    (1 <= bn_top (getbn RMontN bs))%nat ->
    bn_d (getbn RMontN bs) = Some pn -> In (pn, Dn, 8 * Z.of_nat (bn_dmax (getbn RMontN bs))) OW ->
    0 < Dn -> Dn mod 8 = 0 ->
    (bn_top (getbn RMontN bs) <= bn_dmax (getbn rt bs))%nat -> (2 * bn_top (getbn RMontN bs) <= bn_dmax (getbn rx bs))%nat ->
    0 <= carry <= 1 ->
    (forall (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block)
            (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
        kenv LB PL lo B SPv FB se bse OWe me (C8 (Z_to_bv 64 Dn) :: frr) st1 bs1 m2 OW2 -> lib_state bs1 m2 OW2 PL EA ->
        evt bgusegs (Q bs1 st1)
          (MS (mkR x1 (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
                   x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              F (Z_to_bv 64 0x100288) fc None m2 (seg_rom bgusegs))) ->
    evt bgusegs (Q (fm_final rt rx (bn_top (getbn RMontN bs)) (firstn (bn_top (getbn RMontN bs)) (bn_buf (getbn RMontN bs))) carry bs) st)
      (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 SPv) (Z_to_bv 64 at_) (Z_to_bv 64 at_) a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 ax) (Z_to_bv 64 (Z.of_nat (bn_top (getbn RMontN bs)))) s5 s6 (Z_to_bv 64 carry) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x10019c) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK FB112 LOF80.
    intros until t6. intros ENV LS HAt HAx WRt WRx HPM NEtx NEtn NExn PAt0 AT8 PAt63 PAx0 PAx8 PAx63 NL1 Edn Hinn PDn0 PDn8 HDMt HDMx HC EPIQ.
    pose proof (proj1 WRt) as NROt. pose proof (proj1 WRx) as NROx.
    assert (WRn : wref PL RMontN) by (apply hpl_wref; eapply hpl_mont; [reflexivity| exact HPM]).
    pose proof (ref_at_montN bs OW PL am qm HPM) as HAn.
    pose proof ENV as (HEAP & _). pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. clear HEAP.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAt) as HVt. pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HAx) as HVx.
    set (bn := getbn RMontN bs) in *. set (nl := bn_top bn) in *. set (np := firstn nl (bn_buf bn)).
    set (bt := getbn rt bs) in *. set (bx := getbn rx bs) in *.
    pose proof (kenv_read LB PL EA lo B SPv FB se bse OWe me CEIL FROK) as KREAD.
    destruct (KREAD _ _ _ _ _ rt at_ ENV LS HAt WRt ltac:(fold bt; clear - HDMt NL1; lia))
      as (Dt & pt & Edt & Hint & BNt & Ut & (OKt1 & OKt2 & OKt3 & OKt4) & (At0 & AtS & At63 & AtI) & (Dt0 & DtS & DtI) & SEPt & LLt).
    destruct (KREAD _ _ _ _ _ rx ax ENV LS HAx WRx ltac:(fold bx; clear - HDMx NL1; lia))
      as (Dx & px & Edx & Hinx & BNx & Ux & (OKx1 & OKx2 & OKx3 & OKx4) & (Ax0 & AxS & Ax63 & AxI) & (Dx0 & DxS & DxI) & SEPx & LLx).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (st_wf_ok RMontN bs (proj1 PARTS) (ref_at_valid _ _ _ _ _ _ _ _ LS HAn) RMontN_not_one) as (OKn1 & OKn2 & OKn3 & _).
    fold bn in OKn1, OKn2, OKn3. fold nl in OKn2. unfold BG_DMAX in OKn3, OKt3, OKx3.
    destruct (KREAD _ _ _ _ _ RMontN (am + 24) ENV LS HAn WRn ltac:(fold bn; clear - OKn2 NL1; lia))
      as (Dn' & pn' & Edn' & Hinn' & _ & Un & _ & _ & (Dn0 & DnS & DnI) & SEPn & LLn).
    fold bt in Edt, Hint, BNt, Ut, OKt1, OKt2, OKt3, OKt4, DtS, DtI, SEPt, LLt.
    fold bx in Edx, Hinx, BNx, Ux, OKx1, OKx2, OKx3, OKx4, DxS, DxI, SEPx, LLx.
    fold bn in Edn', Hinn', Un, DnS, DnI, SEPn, LLn.
    assert (EDn : Dn' = Dn).
    { rewrite Edn in Edn'. injection Edn' as <-. exact (proj1 (RH_addr_unique OW pn Dn' _ Dn _ ND Hinn' Hinn)). }
    subst Dn'. clear Edn' Hinn' pn'.

    pose proof (SEPt rt at_ HAt) as S_tt. pose proof (SEPx rt at_ HAt) as S_tx. pose proof (SEPn rt at_ HAt) as S_tn.
    pose proof (SEPt rx ax HAx) as S_xt. pose proof (SEPx rx ax HAx) as S_xx.
    pose proof (LLx rt pt Dt NEtx HVt Edt Hint) as D_tx. fold bt in D_tx.
    pose proof (LLn rt pt Dt NEtn HVt Edt Hint) as D_tn. fold bt in D_tn.
    pose proof (LLn rx px Dx NExn HVx Edx Hinx) as D_xn. fold bx in D_xn.
    pose proof ENV as (HEAP & _).
    pose proof (struct_disj st OW LB m HEAP bs PL EA _ _ PARTS FROK rt rx at_ ax NEtx HAt HAx) as S_ax. clear HEAP.
    clear SEPt SEPx SEPn LLt LLx LLn.
    destruct (kenv_hole2 LB PL EA lo B SPv FB se bse OWe me CEIL GLO LOFB FBSP SPB B63 SPR FROK _ _ _ _ _ rt at_ Dt pt rx ax Dx px 80
                ENV LS NEtx HAt NROt Edt Hint HAx NROx Edx Hinx ltac:(lia) LOF80) as (_ & CLOSE).
    fold bt bx in CLOSE.
    pose proof (kenv_final LB PL lo B SPv FB se bse OWe me _ _ _ _ _ ENV) as (_ & _ & ST & (errv & ERR) & MI & _ & _ & _ & _ & FR).
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    unfold bn_cells in BNt, BNx.
    assert (LBt : length (bn_buf bt) = bn_dmax bt) by reflexivity.
    assert (LBx : length (bn_buf bx) = bn_dmax bx) by reflexivity.
    assert (LBn : length (bn_buf bn) = bn_dmax bn) by reflexivity.
    assert (NL31 : Z.of_nat nl <= 512) by (clear - OKn2 OKn3; lia).
    assert (DXR : 0 < Dx + 8 * Z.of_nat nl < 2^64) by (clear - Dx0 DxS HDMx LOFB FBSP SPR; unfold bn_dmax in *; lia).
    assert (AtR : 0 < at_ < 2^64) by (clear - At0 At63; lia).
    assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; clear - SPR FBSP LOFB CEIL; lia).

    pose proof Ux as Ux3. rewrite (three_parts (bn_buf bx) nl) in Ux3 by (rewrite LBx; exact HDMx).
    apply limbarr_app in Ux3. destruct Ux3 as [Ux1 Ux3]. apply limbarr_app in Ux3. destruct Ux3 as [Uap Ux3].
    rewrite length_firstn, Nat.min_l in Uap, Ux3 by (clear - HDMx LBx; lia).
    rewrite slice_length in Ux3 by (clear - HDMx LBx; lia).
    replace (Dx + 8 * Z.of_nat nl + 8 * Z.of_nat nl) with (Dx + 8 * Z.of_nat (2 * nl)) in Ux3 by lia.
    set (ap := slice (bn_buf bx) nl nl) in *.
    assert (Lap : length ap = nl) by (subst ap; apply slice_length; clear - HDMx LBx; lia).
    assert (LMap : limbs ap) by (subst ap; apply slice_limbs; exact OKx1).
    assert (Lnp : length np = nl) by (subst np; apply firstn_length_le; clear - OKn2 LBn; lia).
    assert (LMnp : limbs np) by (subst np; apply limbs_firstn; exact OKn1).
    pose proof Ut as Ut2. apply (limbarr_split bgusegs _ Dt (bn_buf bt) nl) in Ut2; [| clear - HDMt LBt; lia]. destruct Ut2 as [Ut1 Ut2].
    pose proof Un as Unp. apply (limbarr_split bgusegs _ Dn (bn_buf bn) nl) in Unp; [| clear - OKn2 LBn; lia]. apply proj1 in Unp. fold np in Unp.
    clear Ux Ut Un.

    pose proof (munch_refl [(FB - 80, FB); (at_, at_ + 24); (Dt, Dt + 8 * Z.of_nat nl); (Dx + 8 * Z.of_nat nl, Dx + 8 * Z.of_nat nl + 8 * Z.of_nat nl)] m) as MU.
    pose proof (munch_refl [(FB - 80, FB); (at_, at_ + 24); (Dt, Dt + 8 * Z.of_nat nl)] m) as MUa.
    pose proof (wmono_refl bgusegs m) as WM.
    assert (LUt1 : Z.of_nat (length (wlimbs (firstn nl (bn_buf bt)))) = Z.of_nat nl)
      by (rewrite wlimbs_len, firstn_length_le by (clear - HDMt LBt; lia); reflexivity).

    step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AtR; lia); zify_cond KZ; [exfalso; clear - KZ AtR; lia| clear KZ].
    step. if_cases K0; rewrite ?unsigned_lit in K0 by (clear - AtR; lia); zify_cond K0; [exfalso; clear - K0 AtR; lia| clear K0].
    step.
    step. if_cases K1; rewrite ?unsigned_lit in K1 by (clear - AtR; lia); zify_cond K1.
    { exfalso. change 7 with (2^3 - 1) in K1. rewrite zb_land_mask in K1 by lia. clear - K1 AT8. lia. }
    clear K1.
    apply hide_intro in Ux1. apply hide_intro in Uap. apply hide_intro in Ux3. apply hide_intro in Ut2.
    apply hide_intro in Unp. apply hide_intro in FR. apply hide_intro in ERR.
    apply hide_intro in OKt4. apply hide_intro in OKx4. apply hide_intro in AtI. apply hide_intro in AxS. apply hide_intro in AxI.
    apply hide_intro in DtI. apply hide_intro in DxI. apply hide_intro in DnI.
    pose proof BNx as BNx0. apply hide_intro in BNx0.
    step. step. step.
    clear BNx. rename BNx0 into BNx. apply hide_intro in S_tx. apply hide_intro in S_tn.
    apply hide_intro in S_xt. apply hide_intro in S_xx. apply hide_intro in D_tx. apply hide_intro in D_tn. apply hide_intro in D_xn.
    apply hide_intro in S_ax.
    unfold MallocRep.wz. rewrite (sx32_small (Z.b2z _)) by (apply b2z_31).
    step. ub. step. step.
    replace (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat nl))) 3) with (8 * Z.of_nat nl)
      by (rewrite unsigned_lit by (clear - NL31; lia); rewrite Z.shiftl_mul_pow2 by lia; lia).
    ub. step. step. step.
    pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FSZ0).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (FRc : rw_cells bgusegs mx FB (C8 (Z_to_bv 64 Dn) :: frr));
      [ eapply rw_cells_transport; [exact (hide_elim _ FR)| exact MU| exact WM|]; cbn [disjoint_from]; rewrite FSZ0;
        apply hide_elim in AtI; apply hide_elim in DtI; clear - AtS DtS DxS HDMt HDMx LOFB FBSP; lia |]
    end.
    replace FB with (SPv + -112) in FRc by (rewrite FB112; lia).
    step. clear FRc FSZ0. step. step.
    unfold MallocRep.wz.
    apply hide_elim in S_tx. apply hide_elim in S_tn. apply hide_elim in D_tx. apply hide_elim in D_tn.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HAP : limbs_at bgusegs mx (Dx + 8 * Z.of_nat nl) ap);
      [ apply limbs_at_of_u64arr; apply hide_elim in Uap; eapply u64arr_transport; [exact Uap| exact MUa| exact WM|];
        cbn [disjoint_from]; rewrite wlimbs_len, Lap; clear - DxS S_tx D_tx HDMx LOF80; lia |];
      assert (HNP : limbs_at bgusegs mx Dn np);
      [ apply limbs_at_of_u64arr; apply hide_elim in Unp; eapply u64arr_transport; [exact Unp| exact MUa| exact WM|];
        cbn [disjoint_from]; rewrite wlimbs_len, Lnp; clear - DnS S_tn D_tn OKn2 HDMt LOF80; lia |]
    end.
    pose proof (proj2 (proj1 (limbarr_limbs_at bgusegs _ _ _) Ut1)) as WRT.
    rewrite firstn_length_le in WRT by (clear - HDMt LBt; lia).
    assert (EDt : bv_unsigned (Z_to_bv 64 Dt) = Dt) by (apply unsigned_lit; clear - Dt0 DtS SPR FBSP LOFB; lia).
    assert (EAP : bv_unsigned (Z_to_bv 64 (Dx + 8 * Z.of_nat nl)) = Dx + 8 * Z.of_nat nl) by (apply unsigned_lit; clear - Dx0 DxS HDMx SPR FBSP LOFB; lia).
    assert (EDn : bv_unsigned (Z_to_bv 64 Dn) = Dn) by (apply unsigned_lit; clear - Dn0 DnS SPR FBSP LOFB; lia).
    assert (ENL : bv_unsigned (Z_to_bv 64 (Z.of_nat nl)) = Z.of_nat nl) by (apply unsigned_lit; clear - NL31; lia).
    assert (DT8 : Dt mod 8 = 0 /\ Dx mod 8 = 0).
    { pose proof ENV as (HEAP0 & _). split; [exact (proj2 (block_ualign _ _ _ _ _ _ _ HEAP0 Hint)) | exact (proj2 (block_ualign _ _ _ _ _ _ _ HEAP0 Hinx))]. }
    eapply evt_cut.
    { eapply bn_sub_words_uspec with (a := ap) (b := np) (lo := lo); rewrite ?EDt, ?EAP, ?EDn, ?ENL, ?ESP, ?Lap;
        [ exact LMap | exact LMnp | rewrite Lnp; reflexivity | clear - NL31; lia | reflexivity | exact HAP | exact HNP | exact WRT
        | right; clear - D_tx HDMx HDMt; lia | right; clear - D_tn OKn2 HDMt; lia
        | exact ST | clear - LOF80; lia | left; clear - DtS HDMt LOF80; lia | left; clear - DxS HDMx LOF80; lia | left; clear - DnS OKn2 LOF80; lia
        | exact MI
        | intros _; split; [clear - Dt0; lia | clear - DT8; tauto]
        | intros _; split; [clear - Dx0; lia | clear - DT8; destruct DT8 as [_ X]; Z.div_mod_to_equations; lia]
        | intros _; split; [exact PDn0 | exact PDn8] ]. }
    clear Ut1 LUt1 ST HAP HNP.
    intros ms' PO. unfold sw_upost, wl_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m3 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite EDt, Lap, ESP in MUc. rewrite EDt in HR. rewrite ESP in STc.
    destruct (sub_words ap np) as [res bw] eqn:ESW. cbn [fst snd] in *.
    pose proof (sub_words_spec ap np LMap LMnp ltac:(rewrite Lap, Lnp; reflexivity)) as SWS. rewrite ESW in SWS.
    destruct SWS as (LMres & Lres & BW01 & _). rewrite Lap in Lres.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bgusegs mm m3 MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv bgusegs mm |- _ => clear H end; try clear mm end.
    rewrite (ret_pc_even 1049080) by lia.

    step. step.
    step. if_cases KB; zify_cond KB; [exfalso; clear - KB NL1 NL31; rewrite andb_false_iff, !Z.ltb_ge in KB; lia| try clear KB].
    step. step. step.
    set (mk := subw carry bw).
    assert (MK : 0 <= mk < 18446744073709551616) by (subst mk; unfold subw; rewrite BW_lit; apply Z.mod_pos_bound; lia).
    assert (EA1 : Z_to_bv 64 (carry + - bv_unsigned (Z_to_bv 64 bw)) = Z_to_bv 64 mk).
    { rewrite unsigned_lit by (clear - BW01; lia). subst mk. unfold subw. rewrite BW_lit. rewrite (to_bv_mod64 (carry + - bw)). reflexivity. }
    rewrite ?EA1.
    setreg 13%Z (Z_to_bv 64 (18446744073709551616 - 1 - (Dx + 8 * Z.of_nat nl))) ltac:(f_equal; rewrite EAP; rewrite zb_lxor_ones by (clear - DXR; lia); lia).
    step. step. step. step. step. step.
    assert (DtR : 0 < Dt < 2^64) by (clear - Dt0 DtS HDMt LOFB FBSP SPR; unfold bn_dmax in *; lia).
    rewrite (fm_flag_nz_al Dt DtR ltac:(clear - DT8; tauto)).
    rewrite (fm_sltu_nz Dt DtR), (fm_land7 Dx ltac:(clear - DXR Dx0; lia) ltac:(clear - DT8; tauto)), (fm_lxor_mk mk ltac:(clear - MK; lia)).
    replace (18446744073709551615 - (Dx + 8 * Z.of_nat nl)) with (18446744073709551616 - 1 - (Dx + 8 * Z.of_nat nl)) by lia.

    apply hide_elim in Ut2. apply hide_elim in Uap.
    assert (UR : u64arr bgusegs m3 Dt (wlimbs (res ++ skipn nl (bn_buf bt)))).
    { apply limbarr_app. split.
      - apply u64arr_of_limbs_at; [exact HR| rewrite Lres; exact WRT].
      - rewrite Lres. eapply u64arr_transport; [exact Ut2| exact MUa| exact WM|].
        cbn [disjoint_from]. rewrite wlimbs_len, length_skipn, LBt. clear - DtS S_tt HDMt LOF80. lia. }
    assert (UP : u64arr bgusegs m3 (Dx + 8 * Z.of_nat nl) (wlimbs ap)).
    { eapply u64arr_transport; [exact Uap| exact MUa| exact WM|]. cbn [disjoint_from]. rewrite wlimbs_len, Lap. clear - DxS S_tx D_tx HDMx HDMt LOF80. lia. }
    clear MUa HR WRT Ut2 Uap.
    assert (LR : length (res ++ skipn nl (bn_buf bt)) = bn_dmax bt) by (rewrite length_app, Lres, length_skipn, LBt; clear - HDMt; lia).
    eapply evt_cut.
    { eapply select_loop_walk with (lo := lo) (RPr := Dt) (AP := Dx + 8 * Z.of_nat nl) (mk := mk) (R := res ++ skipn nl (bn_buf bt)) (P := ap) (nl := nl);
        [ apply limbs_app; [exact LMres| apply limbs_skipn; exact OKt1] | exact LMap | exact NL1 | exact Lap | rewrite LR; exact HDMt | exact MK
        | rewrite LR; clear - D_tx HDMx; lia | intros _; split; [clear - Dt0; lia | clear - DT8; tauto]
        | exact UR | exact UP | the_mi | rewrite ESP; exact STc ]. }
    clear UR UP STc.
    intros ms' PO. unfold sl_post in PO.
    destruct PO as (z5 & z6 & z7 & z12 & z28 & m4 & E & MUc & WMc & MIf & URf & UPf & STf).
    subst ms'. rewrite ESP in STf.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call bgusegs mm m4 MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv bgusegs mm |- _ => clear H end; try clear mm end.

    apply hide_elim in BNx. apply hide_elim in Ux1. apply hide_elim in Ux3. apply hide_elim in FR. apply hide_elim in ERR.
    apply hide_elim in OKt4. apply hide_elim in OKx4. apply hide_elim in AtI. apply hide_elim in AxS. apply hide_elim in AxI.
    apply hide_elim in DtI. apply hide_elim in DxI. apply hide_elim in S_xt. apply hide_elim in S_xx. apply hide_elim in S_ax.
    pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FSZ).
    unfold fm_final. fold bn. fold nl. fold np.
    set (b1 := fm_ret rt rx nl np carry bs).
    assert (G2 : getbn rx (setbn rt b1 bs) = bx) by (apply getbn_setbn_other; exact NEtx).
    rewrite G2.
    set (b2 := bn_with_buf bx (splice (bn_buf bx) nl (repeat 0 nl))).
    assert (Eb1 : bn_buf b1 = sel_res mk (res ++ skipn nl (bn_buf bt)) ap nl).
    { subst b1. unfold fm_ret. cbn [bn_buf]. fold bt bx ap.
      rewrite (mont_final_sel (bn_buf bt) ap np carry nl Lap Lnp ltac:(rewrite LBt; exact HDMt)). rewrite ESW. reflexivity. }
    assert (Lb1 : length (bn_buf b1) = bn_dmax bt).
    { rewrite Eb1. unfold sel_res. rewrite length_app, select_words_length, length_firstn, length_skipn, length_app, Lres, length_skipn, Lap, LBt.
      clear - HDMt. lia. }
    assert (Lb2 : length (bn_buf b2) = bn_dmax bx).
    { subst b2. cbn [bn_with_buf bn_buf]. rewrite splice_length by (rewrite repeat_length, LBx; clear - HDMx; lia). exact LBx. }
    assert (MUk : munch (fpw2 FB 80 at_ Dt (bn_dmax bt) ax Dx (bn_dmax bx)) m m4).
    { eapply munch_weaken; [| exact MU]. unfold sub_fp, fpw2. cbn [outside]. intros x Hx. clear - Hx HDMt HDMx. lia. }
    destruct (CLOSE m4 b1 b2 errv MUk WM) as (ENVF & LSF).
    - change (bn_cells Dt b1) with [C8 (wz Dt); C4 (wz (Z.of_nat nl)); C4 (wz (Z.of_nat (length (bn_buf b1))));
                                    C4 (wz (Z.b2z (bn_neg bx))); C4 (wz (bn_flags bt))].
      rewrite Lb1. exact BNt.
    - rewrite Eb1. exact URf.
    - reflexivity.
    - rewrite Lb1, LBt. reflexivity.
    - unfold bg_ok. change (bn_dmax b1) with (length (bn_buf b1)). rewrite Lb1. change (bn_top b1) with nl. change (bn_flags b1) with (bn_flags bt).
      split. { rewrite Eb1. unfold sel_res. apply limbs_app; [apply select_words_limbs; [rewrite BW_lit; exact MK| exact LMap|]| apply limbs_skipn].
               - apply limbs_firstn. apply limbs_app; [exact LMres| apply limbs_skipn; exact OKt1].
               - apply limbs_app; [exact LMres| apply limbs_skipn; exact OKt1]. }
      split; [exact HDMt|]. split; [unfold BG_DMAX; exact OKt3| exact OKt4].
    - change (bn_cells Dx b2) with [C8 (wz Dx); C4 (wz (Z.of_nat (bn_top bx))); C4 (wz (Z.of_nat (length (bn_buf b2))));
                                    C4 (wz (Z.b2z (bn_neg bx))); C4 (wz (bn_flags bx))].
      rewrite Lb2. eapply rw_cells_transport; [exact BNx| exact MU| exact WM|].
      cbn [disjoint_from cells_size csize Nat.add]. clear - AxS S_ax S_xt S_xx HDMt HDMx LOFB FBSP LOF80. lia.
    - subst b2. cbn [bn_with_buf bn_buf]. rewrite splice_zero_parts by (rewrite LBx; exact HDMx).
      apply limbarr_app. split.
      + eapply u64arr_transport; [exact Ux1| exact MU| exact WM|]. cbn [disjoint_from].
        rewrite wlimbs_len, firstn_length_le by (rewrite LBx; clear - HDMx; lia). clear - DxS S_tx D_tx HDMt HDMx LOF80. lia.
      + rewrite firstn_length_le by (rewrite LBx; clear - HDMx; lia). apply limbarr_app. split; [exact UPf|].
        rewrite repeat_length. replace (Dx + 8 * Z.of_nat nl + 8 * Z.of_nat nl) with (Dx + 8 * Z.of_nat (2 * nl)) by lia.
        eapply u64arr_transport; [exact Ux3| exact MU| exact WM|]. cbn [disjoint_from].
        rewrite wlimbs_len, length_skipn, LBx. clear - DxS S_tx D_tx HDMt HDMx LOF80. lia.
    - reflexivity.
    - rewrite Lb2, LBx. reflexivity.
    - unfold bg_ok. change (bn_dmax b2) with (length (bn_buf b2)). rewrite Lb2. change (bn_top b2) with (bn_top bx). change (bn_flags b2) with (bn_flags bx).
      split. { subst b2. cbn [bn_with_buf bn_buf]. apply splice_limbs; [exact OKx1| apply limbs_repeat; unfold limb, BW; lia]. }
      split; [exact OKx2|]. split; [unfold BG_DMAX; exact OKx3| exact OKx4].
    - exact STf.
    - exact MIf.
    - eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn [disjoint_from]. rewrite FSZ.
      clear - AtS DtS DxS HDMt HDMx LOFB FBSP. lia.
    - unfold LX_ERRNO, RATP. change (3346328 - 164) with 3346164.
      eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add].
      unfold GLOBALS_TOP in GLO. clear - GLO LOF80 AtI At0 DtI Dt0 DxI Dx0 HDMt HDMx. lia.
    - step. eapply EPIQ; [exact ENVF| exact LSF].
  Qed.
End Final.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma bn_from_montgomery_word_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
      (lo B : Z) (errv : word) (rt rx : bnref) (at_ ax am : Z) (qm : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_FROM_MONT_WORD_STACK -> tp = wz RATP ->
    ref_at bs OW PL rt at_ -> ref_at bs OW PL rx ax -> wref PL rt -> wref PL rx -> pl_mont PL = Some (am, qm) ->
    a0 = wz at_ -> a1 = wz ax -> a2 = wz am ->
    implM bgusegs (interp (embed (bn_from_montgomery_word (tree_ops bptr) rt rx bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_FROM_MONTGOMERY_WORD) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qm. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> HAt HAx WRt WRx HPM -> -> ->.
    pose proof (proj1 WRt) as NROt. pose proof (proj1 WRx) as NROx.
    unfold BN_FROM_MONT_WORD_STACK, BN_WEXPAND_STACK, BN_EXPAND2_STACK, BN_FROM_MONTGOMERY_WORD, GLOBALS_TOP, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_montN bs OW PL am qm HPM) as HAn.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO.

    unfold bn_from_montgomery_word.
    destruct ((rt =? rx)%nat || (rt =? RMontN)%nat || (rx =? RMontN)%nat) eqn:G1;
      [unfold bunr; cbn [unreachable tree_ops embed interp fst snd]; apply implM_interp_unr|].
    apply orb_false_iff in G1. destruct G1 as [G1 NExn]. apply orb_false_iff in G1. destruct G1 as [NEtx NEtn].
    apply Nat.eqb_neq in NEtx, NEtn, NExn.
    unfold implM. iprefix.

    carve_frame 112%nat ST. do 14 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    apply fm_cb8_c8 in FR.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -112, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK) as LS1.
    lazymatch type of FR with rw_cells _ _ _ ?fr =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m fr s bs m1 OW)
    end.
    { unfold kenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL CEIL); lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FR| cbn; lia]. }
    assert (FBlo : lo <= bv_unsigned sp + -112) by lia.
    assert (FBsp : bv_unsigned sp + -112 <= bv_unsigned sp) by lia.
    assert (SPR2 : bv_unsigned sp < 2 ^ 64) by lia.
    pose proof (kenv_pre LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KPRE.
    pose proof (kenv_post LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp FROK) as KPOST.
    pose proof (fun A => @bn_post_kpost _ _ LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) CEIL FBlo FBsp SPR2 A) as BPK.
    pose proof (kenv_open LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL FROK) as KOPEN.
    pose proof (kenv_struct_store LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KSTORE.
    pose proof (kenv_read LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL FROK) as KREAD.
    pose proof (kenv_hole1 LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KHOLE1.
    pose proof (kenv_hole2 LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK) as KHOLE2.
    pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m) as KFINAL.
    assert (WRn : wref PL RMontN) by (apply hpl_wref; eapply hpl_mont; [reflexivity| exact HPM]).
    assert (LOF : lo <= bv_unsigned sp + -112 - BN_WEXPAND_STACK) by (unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK; lia).
    destruct (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS (ref_at_montRR bs OW PL am qm HPM) RMontRR_not_one) as (Am0 & Am8).
    assert (AmR : am < 2^63)
      by (destruct (ref_at_range_any _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK (ref_at_montRR bs OW PL am qm HPM)) as (_ & [X|X]); clear - X B63 SPB; lia).
    destruct (ref_at_ualign_any _ _ _ _ _ _ _ _ _ HEAP PARTS HAt) as (At0' & At8).
    assert (AtR' : at_ < 2^63) by (destruct (ref_at_range_any _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAt) as (_ & [X|X]); clear - X B63 SPB; lia).
    destruct (ref_at_ualign_any _ _ _ _ _ _ _ _ _ HEAP PARTS HAx) as (Ax0' & Ax8).
    assert (AxR' : ax < 2^63) by (destruct (ref_at_range_any _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HAx) as (_ & [X|X]); clear - X B63 SPB; lia).
    step. ub.
    step. step. ub.
    destruct (KOPEN _ _ _ _ _ RMontN (am + 24) ENV LS1 HAn RMontN_not_one) as (Dn & BNn & Un & (OKn1 & OKn2 & OKn3 & OKn4) & An0 & AnS & DnS & SEPn).
    set (bn := getbn RMontN bs) in *.
    unfold bn_cells in BNn. unfold BG_DMAX in OKn3.
    assert (NL31 : Z.of_nat (bn_top bn) <= 512) by (clear - OKn2 OKn3; lia).

    lazymatch type of FR with rw_cells _ _ _ (C8 _ :: ?frr) =>
    assert (EPI : forall (w0 : word) (st1 : PState) (bs1 : bstate bptr) (m2 : mem) (OW2 : list block)
                         (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m (C8 w0 :: frr) st1 bs1 m2 OW2 -> lib_state bs1 m2 OW2 PL EA ->
      evt bgusegs (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                     (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = Z_to_bv 64 1) (tt, bs1) st1)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 1049224) fc None m2 (seg_rom bgusegs)))
    end.
    { intros w0 st1 bs1 m2 OW2 x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ENVF LSF.
      clear - ENVF LSF SPR FBlo FBsp CEIL GLO' SPB B63.
      pose proof (kenv_final LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m _ _ _ _ _ ENVF) as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
      clear ENVF.
      do 13 step. release_frame FRF STF (bv_unsigned sp). step. step.
      apply evt_done. unfold bn_post. do 15 eexists. exists m2, OW2, PL, errvF. split; [reflexivity|]. cbn [fst snd].
      split; [exact F1|]. split; [exact LSF|]. split; [exact F2|]. split; [exact STF|]. split; [exact F4|]. split; [exact F5|].
      split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; reflexivity. }
    step. unfold MallocRep.wz. rewrite (sx32_small (Z.of_nat (bn_top bn))) by (clear - NL31; lia).
    step. if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by (clear - NL31; lia).
    -
      assert (ET : bn_top bn = 0%nat) by (clear - KT; lia).
      unfold bbind, bget, bset, bret. cbn [bind ret tree_ops tbind fst snd]. fold bn.
      replace (bn_top bn =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; exact ET).
      destruct (KSTORE _ _ _ _ _ rt at_ ENV LS1 HAt NROt) as (Dt & BNt & (OKt1 & OKt2 & OKt3 & OKt4) & At0 & AtS & At63 & AtI & CLOSE).
      set (bt := getbn rt bs) in *. unfold bn_cells in BNt.
      clear MU WM BNn Un. pose proof (munch_refl [(at_, at_ + 24)]%Z m1) as MU. pose proof (wmono_refl bgusegs m1) as WM.
      ub. step. step.
      ihere. to_implM. cbn [embed interp]. apply implM_ret.
      assert (OK' : bg_ok (bn_with_top bt 0)).
      { unfold bg_ok, bn_with_top, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. split; [exact OKt1|]. split; [clear; lia|]. split; [exact OKt3| exact OKt4]. }
      destruct (CLOSE _ (bn_with_top bt 0) MU WM BNt eq_refl eq_refl OK' ST MI) as (ENVF & LSF).
      eapply EPI; [exact ENVF| exact LSF].
    -
      assert (NT : bn_top bn <> 0%nat) by (clear - KT; lia).
      unfold bbind at 1. unfold bget at 1. cbn [bind ret tree_ops tbind fst snd]. fold bn.
      replace (bn_top bn =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact NT).
      set (nl := bn_top bn) in *.
      ub. do 5 step.
      setreg 11%Z (Z_to_bv 64 (Z.of_nat (2 * nl))) ltac:(f_equal; rewrite unsigned_lit by (clear - NL31; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia);
                                                        rewrite bn_swrap32_small by (clear - NL31; lia); clear - NL31; lia).

      destruct (KPRE _ _ _ _ _ BN_WEXPAND_STACK ENV LS1 LOF) as (errv1 & PRE1).
      clear MU WM BNn Un HEAP AUX ST ERR MI HWL WOK FR.
      ihere. to_implM. unfold bbind at 1. cbn [bind tree_ops].
      eapply implM_embed_bind.
      { eapply (bn_wexpand_walk HM HF); [exact PRE1| reflexivity| exact HAx| exact WRx| reflexivity| reflexivity| clear - NL31; lia]. }
      cbv beta. intros [u1 bs1] st1 ms1 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & OW2 & -> & KP & (_ & -> & HDM1 & WXR1 & BST1)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV KP) as (ENV2 & LS2). pose proof KP as RS2; apply kpost_refs in RS2.
      cbn [fst snd] in *. clear PRE1 KP ENV LS1.
      replace (ret_pc (Z_to_bv 64 1048712)) with (Z_to_bv 64 1048712) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).

      pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAx) as HAx2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS2 HAt) as HAt2.
      pose proof (ref_at_montN bs1 OW2 PL am qm HPM) as HAn2.
      assert (EN1 : getbn RMontN bs1 = bn).
      { destruct WXR1 as [[_ ->]|[_ (pn & ->)]]; [reflexivity| apply getbn_setbn_other; exact NExn]. }
      assert (EN0 : st_n0 bs1 = st_n0 bs) by (destruct WXR1 as [[_ ->]|[_ (pn & ->)]]; reflexivity).
      set (rb := getbn rx bs1) in *.
      assert (HDr : (0 < bn_dmax rb)%nat) by (clear - HDM1 NT; lia).
      assert (HDn : (0 < bn_dmax (getbn RMontN bs1))%nat) by (rewrite EN1; clear - OKn2 NT; fold nl in OKn2; lia).
      pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS2 HAx2) as HVx2.
      destruct (KREAD _ _ _ _ _ rx ax ENV2 LS2 HAx2 WRx HDr) as (Dr & pr & Edr & Hinr & BNr & Ur & (OKr1 & OKr2 & OKr3 & OKr4) & (Ar0 & ArS & Ar63 & ArI) & (Dr0 & DrS & DrI) & SEPr & _).
      destruct (KREAD _ _ _ _ _ RMontN (am + 24) ENV2 LS2 HAn2 WRn HDn) as (Dn2 & pn & Edn & Hinn & BNn2 & Un2 & _ & _ & (Dn0 & DnS2 & DnI) & SEPn2 & LLn).
      fold rb in Edr, Hinr, BNr, Ur, OKr1, OKr2, OKr3, OKr4, DrS, DrI, SEPr. rewrite EN1 in Edn, Hinn, BNn2, Un2, DnS2, DnI, SEPn2, LLn.
      pose proof (SEPn2 rx ax HAx2) as SXN. pose proof (SEPr RMontN (am + 24) HAn2) as SNR. pose proof (SEPr rx ax HAx2) as SXR.
      pose proof (LLn rx pr Dr NExn HVx2 Edr Hinr) as DND. fold rb in DND.
      clear SEPr SEPn2 LLn.
      unfold bn_cells in BNr, BNn2. unfold BG_DMAX in OKr3.
      assert (AxR : 0 < ax < 2^64) by (clear - Ar0 Ar63; lia).

      unfold bbind, bget, bgetst, bset, bret. cbn [bind ret tree_ops tbind fst snd]. fold rb. rewrite EN1.
      destruct ((0 <=? st_n0 bs1) && (st_n0 bs1 <? 18446744073709551616)) eqn:GN0; cbn [negb];
        [| unfold bunr; cbn [unreachable tree_ops embed interp fst snd]; apply implM_interp_unr].
      apply andb_true_iff in GN0. destruct GN0 as [GN1 GN2]. apply Z.leb_le in GN1. apply Z.ltb_lt in GN2.
      set (n0 := st_n0 bs1) in *. set (np := firstn nl (bn_buf bn)) in *.
      change (splice (bn_buf rb) (bn_top rb) (repeat 0 (2 * nl - bn_top rb))) with (clear_top (bn_buf rb) (bn_top rb) (2 * nl)).
      destruct (mont_reduce_loop np n0 nl nl 0 (clear_top (bn_buf rb) (bn_top rb) (2 * nl)) 0) as [buf carry] eqn:EMR.
      cbv beta iota.
      unfold implM. iprefix.
      unfold MallocRep.wz.
      step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AxR; lia); zify_cond KZ; [exfalso; clear - KZ AxR; lia| clear KZ].
      hide_ors. ub. unhide.
      do 4 step.

      pose proof (KFINAL _ _ _ _ _ ENV2) as (_ & _ & ST & (errv2 & ERR) & MI & _ & _ & _ & _ & FR).
      lazymatch type of FR with rw_cells _ _ _ (C8 ?w0 :: ?rest) =>
        change (C8 w0 :: rest) with ([C8 w0] ++ rest) in FR end.
      apply bk_rw_cells_app in FR. destruct FR as [F0 FS]. cbn [cells_size csize] in FS.
      pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp + -112 + 8)]%Z m2) as MUs. pose proof (wmono_refl bgusegs m2) as WMs.
      apply hide_intro in ERR. apply hide_intro in FS. apply hide_intro in BNr. apply hide_intro in BNn2. apply hide_intro in Ur. apply hide_intro in Un2.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2s end.
      apply hide_elim in ERR. apply hide_elim in FS. apply hide_elim in BNr. apply hide_elim in BNn2. apply hide_elim in Ur. apply hide_elim in Un2.
      eapply (rw_cells_transport bgusegs _ m2 m2s) in ERR;
        [| exact MUs | exact WMs | cbn [disjoint_from cells_size csize Nat.add]; split; [left; clear - GLO' FBlo; unfold GLOBALS_TOP, LX_ERRNO, RATP in *; lia| exact I]].
      eapply (rw_cells_transport bgusegs _ m2 m2s) in FS; [| exact MUs | exact WMs | cbn [disjoint_from]; split; [right; clear; lia| exact I]].
      eapply (rw_cells_transport bgusegs _ m2 m2s) in BNr;
        [| exact MUs | exact WMs | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - ArS FBlo; lia| exact I]].
      eapply (u64arr_transport bgusegs _ m2 m2s) in Ur;
        [| exact MUs | exact WMs | cbn [disjoint_from]; rewrite wlimbs_len; change (length (bn_buf rb)) with (bn_dmax rb); split; [clear - DrS FBlo; lia| exact I]].
      eapply (u64arr_transport bgusegs _ m2 m2s) in Un2;
        [| exact MUs | exact WMs | cbn [disjoint_from]; rewrite wlimbs_len; change (length (bn_buf bn)) with (bn_dmax bn); split; [clear - DnS2 FBlo; lia| exact I]].
      clear BNn2.
      lazymatch type of FS with rw_cells _ _ _ ?rest =>
        assert (FR2 : rw_cells bgusegs m2s (bv_unsigned sp + -112) (C8 (wz Dn2) :: rest))
          by (change (C8 (wz Dn2) :: rest) with ([C8 (wz Dn2)] ++ rest); apply bk_rw_cells_app; split; [exact F0| exact FS])
      end.
      assert (HWLs : Forall (w_lib bs1 OW2 PL lo (bv_unsigned sp)) [(bv_unsigned sp + -112, bv_unsigned sp + -112 + 8)])
        by (constructor; [left; cbn; clear - FBlo; lia| constructor]).
      pose proof (kenv_silent LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB FROK _ _ st1 bs1 m2 m2s OW2 _ errv2
                    ENV2 (lib_state_h_parts _ _ _ _ _ _ LS2) MUs WMs HWLs ST ERR ltac:(the_mi) FR2 ltac:(cbn; clear; lia)) as ENV2s.
      assert (WOKs : Forall (w_ok OW2 LB bs1 PL EA (bv_unsigned sp) []) [(bv_unsigned sp + -112, bv_unsigned sp + -112 + 8)])
        by (constructor; [apply w_stack; cbn; clear - CEIL FBlo; lia| constructor]).
      pose proof (lib_state_frame st1 LB _ _ [] bs1 m2 m2s OW2 PL EA _ (proj1 ENV2) LS2 MUs WMs FROK WOKs) as LS2s.
      clear ENV2 LS2 MUs WMs HWLs WOKs F0 FS FR2 ST ERR MI.
      destruct (KHOLE1 _ _ _ _ _ rx ax Dr pr 112 ENV2s LS2s HAx2 NROx Edr Hinr ltac:(clear; lia) ltac:(clear - LOF; unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK in LOF; lia)) as (FRAMEH & CLOSE).
      fold rb in FRAMEH, CLOSE.
      pose proof (KFINAL _ _ _ _ _ ENV2s) as (_ & _ & ST & (errv2s & ERR) & MI & _ & _ & _ & _ & FR).
      unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
      pose proof (munch_refl (fpw1 (bv_unsigned sp + -112) 112 ax Dr (bn_dmax rb)) m2s) as MU. pose proof (wmono_refl bgusegs m2s) as WM.
      unfold fpw1 in MU.
      step.
      unfold MallocRep.wz. rewrite !(sx32_small (Z.b2z _)) by (apply b2z_31).
      rewrite !(unsigned_lit (Z.b2z _)) by (apply b2z_64). rewrite lxor_b2z.
      clear OKn4 An0 AnS DnS SEPn Dn SNR HDn KT DnI KSTORE KOPEN.
      apply hide_intro in OKr4. apply hide_intro in DND. apply hide_intro in SXN. apply hide_intro in Un2.
      assert (LUr : Z.of_nat (length (wlimbs (bn_buf rb))) = Z.of_nat (bn_dmax rb)) by (rewrite wlimbs_len; reflexivity).
      step. step.
      step. rewrite (lts_signed 0 (Z.of_nat (2 * nl))) by (clear - NL31; lia).
      rewrite (proj2 (Z.ltb_lt 0 (Z.of_nat (2 * nl)))) by (clear - NT; lia). cbv iota beta delta [negb].
      do 8 step.
      destruct (block_ualign _ _ _ _ _ _ _ (proj1 ENV2s) Hinr) as (_ & Dr8).
      assert (DrR : 0 <= Dr < 2^64) by (clear - Dr0 DrS FBlo SPR2; lia).
      assert (EQa0 : v_sltu (Z_to_bv 64 0) (Z_to_bv 64 Dr) = Z_to_bv 64 1)
        by (rewrite v_sltu_b2z, !unsigned_lit by (clear - DrR; lia); replace (0 <? Dr) with true by (symmetry; apply Z.ltb_lt; exact Dr0); reflexivity).
      assert (EQd7 : Z.land (bv_unsigned (Z_to_bv 64 Dr)) 7 = 0)
        by (rewrite unsigned_lit by (clear - DrR; lia); change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact Dr8).
      rewrite EQa0, EQd7.
      lazymatch goal with |- context [Z_to_bv 64 (Z.land (bv_unsigned (v_sltiu (Z_to_bv 64 0) 1)) (bv_unsigned (Z_to_bv 64 1)))] =>
        change (Z_to_bv 64 (Z.land (bv_unsigned (v_sltiu (Z_to_bv 64 0) 1)) (bv_unsigned (Z_to_bv 64 1)))) with (Z_to_bv 64 1) end.
      unfold MallocRep.wz. rewrite (sx32_small (Z.of_nat (bn_top rb))) by (clear - OKr2 OKr3; lia).
      setreg 12%Z (Z_to_bv 64 (0 - Z.of_nat (bn_top rb)))
        ltac:(f_equal; rewrite unsigned_lit by (clear - OKr2 OKr3; lia); rewrite bn_swrap32_small by (clear - OKr2 OKr3; lia); reflexivity).
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; clear - SPR2 FBlo CEIL; lia).
      assert (LBr : length (bn_buf rb) = bn_dmax rb) by reflexivity.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply clear_loop_walk with (lo := lo) (RP := Dr) (B := bn_buf rb) (rtop := bn_top rb) (mx := (2 * nl)%nat);
          [exact OKr1| clear - HDM1 NT LBr; lia| clear - NL31; lia| clear - OKr2 OKr3; lia| clear - OKr2 LBr; lia
          | unfold ub_ptr_ok; intros _; split; [exact Dr0| exact Dr8] | exact Ur| exact MI| rewrite ESP; exact ST]
        | clear Ur; post_call bgusegs mm ] end.
      clear POST. rename PC into Ur.
      set (B1 := clear_top (bn_buf rb) (bn_top rb) (2 * nl)) in *.
      assert (LB1 : length B1 = bn_dmax rb) by (subst B1; rewrite clear_top_length by (clear - HDM1 LBr; lia); exact LBr).
      assert (LM1 : limbs B1) by (subst B1; apply clear_top_limbs; exact OKr1).
      clear LUr. assert (LUr : Z.of_nat (length (wlimbs B1)) = Z.of_nat (bn_dmax rb)) by (rewrite wlimbs_len, LB1; reflexivity).
      step. step. step.
      rewrite (lts_signed 0 (Z.of_nat nl)) by (clear - NL31; lia).
      rewrite (proj2 (Z.ltb_lt 0 (Z.of_nat nl))) by (clear - NT; lia). cbv iota beta delta [negb].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (lib_state_mont_cells _ _ _ _ _ _ _ am qm (proj2 (FRAMEH mx MU WM)) HPM) as MC end.
      unfold mont_cells in MC.
      step. clear MC.
      do 4 step. unfold MallocRep.wz. fold n0.
      setreg 25%Z (Z_to_bv 64 (8 * Z.of_nat nl))
        ltac:(f_equal; rewrite unsigned_lit by (clear - NL31; lia); rewrite Z.shiftl_mul_pow2 by lia; lia).
      setreg 26%Z (Z_to_bv 64 (18446744073709551615 - Dr))
        ltac:(f_equal; rewrite unsigned_lit by (clear - DrR; lia); rewrite lxor_ones64 by (clear - DrR; lia); reflexivity).
      setreg 27%Z (Z_to_bv 64 18446744073709551607) ltac:(apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity).

      apply hide_elim in Un2. apply hide_elim in DND. apply hide_elim in SXN.
      assert (LBn : length (bn_buf bn) = bn_dmax bn) by reflexivity.
      assert (LOF112 : lo <= bv_unsigned sp + -112 - 112) by (clear - LOF; unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK in LOF; lia).
      destruct (block_ualign _ _ _ _ _ _ _ (proj1 ENV2s) Hinn) as (_ & Dn8).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (HNP : limbs_at bgusegs mx Dn2 np);
        [ apply limbs_at_of_u64arr; subst np;
          eapply u64arr_transport in Un2; [| exact MU| exact WM|];
          [ apply (limbarr_split bgusegs _ Dn2 (bn_buf bn) nl) in Un2; [exact (proj1 Un2)| clear - OKn2 LBn; lia]
          | cbn [disjoint_from]; rewrite wlimbs_len, LBn; clear - DnS2 SXN DND LOF112; lia ]
        | ]
      end.
      pose proof (fm_slot _ _ Dn2 _ FR) as SLOT. clear Un2.

      eapply evt_cut.
      { eapply reduce_loop_walk with (lo := lo) (RP := Dr) (NP := Dn2) (n0 := n0) (np := np) (nl := nl) (LB := bn_dmax rb) (B := B1);
          [ subst np; apply limbs_firstn; exact OKn1
          | subst np; apply firstn_length_le; clear - OKn2 LBn; lia
          | clear - NT; lia | clear - NL31; lia | exact HDM1 | split; [exact GN1| exact GN2]
          | clear - DND OKn2 HDM1; lia
          | rewrite ESP; exact LOF112
          | rewrite ESP; left; clear - DrS LOF112; lia
          | rewrite ESP; left; clear - DnS2 OKn2 LOF112; lia
          | unfold ub_ptr_ok; intros _; split; [exact Dr0| exact Dr8]
          | unfold ub_ptr_ok; intros _; split; [exact Dn0| exact Dn8]
          | rewrite ESP; clear; lia
          | rewrite ESP; exact SLOT
          | exact LM1 | exact LB1 | exact Ur | exact HNP | rewrite ESP; exact ST | the_mi ]. }
      clear Ur HNP ST DND SXN DnS2 LBn SLOT. subst B1.
      intros ms' PO. rewrite EMR in PO. unfold mr_post in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & m4 & E & MUc & WMc & MIc & HRB & WRB & HNB & STc & LMB & LENB & HC).
      subst ms'. rewrite ESP in MUc, STc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call bgusegs mm m4 MUc WMc; clear MUc WMc;
        try match goal with H : mem_inv bgusegs mm |- _ => clear H end; try clear mm end.

      set (b2 := mkBN (bn_d rb) buf (2 * nl) (xorb (bn_neg rb) (bn_neg bn)) (bn_flags rb)) in *.
      apply hide_elim in OKr4.
      assert (OK2 : bg_ok b2).
      { unfold bg_ok, BG_DMAX. change (bn_dmax b2) with (length buf). cbn [b2 bn_buf bn_top bn_flags]. rewrite LENB.
        split; [exact LMB|]. split; [exact HDM1|]. split; [exact OKr3| exact OKr4]. }
      destruct (CLOSE m4 b2 errv2s MU WM) as (ENV3 & LS3).
      { change (bn_cells Dr b2) with [C8 (wz Dr); C4 (wz (Z.of_nat (2 * nl))); C4 (wz (Z.of_nat (length buf)));
                                      C4 (wz (Z.b2z (xorb (bn_neg rb) (bn_neg bn)))); C4 (wz (bn_flags rb))].
        rewrite LENB. exact BNr. }
      { apply u64arr_of_limbs_at; [exact HRB| change (bn_buf b2) with buf; rewrite LENB; exact WRB]. }
      { reflexivity. } { change (bn_buf b2) with buf. rewrite LENB. reflexivity. } { exact OK2. } { exact STc. } { exact MIc. } { exact FR. }
      { exact ERR. }
      pose proof (proj2 (ref_at_setbn bs1 OW2 PL rx b2 rt at_) HAt2) as HAt3. pose proof (proj2 (ref_at_setbn bs1 OW2 PL rx b2 rx ax) HAx2) as HAx3.
      clear CLOSE FRAMEH MU WM BNr HRB WRB HNB FR ERR STc MIc LUr ArS ArI SXR DrI DrS Ar0 Ar63 LOF112 ENV2s LS2s.
      step. step. step.
      destruct (KPRE _ _ _ _ _ BN_WEXPAND_STACK ENV3 LS3 LOF) as (errv3 & PRE3).
      ihere. to_implM.
      eapply implM_embed_bind.
      { eapply (bn_wexpand_walk HM HF); [exact PRE3| reflexivity| exact HAt3| exact WRt| reflexivity| reflexivity| clear - NL31; lia]. }
      cbv beta. intros [u3 bs3] st3 ms3 PO. apply BPK in PO; [|intros v b o p a [E _]; exact E].
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & OW5 & -> & KP & (_ & -> & HDM3 & WXR3 & BST3)).
      destruct (KPOST _ _ _ _ _ _ _ _ _ ENV3 KP) as (ENV5 & LS5). pose proof KP as RS5; apply kpost_refs in RS5.
      cbn [fst snd] in *. clear PRE3 KP.
      lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.

      set (bs2 := setbn rx b2 bs1) in *.
      assert (HVt3 : vref rt bs2) by (eapply ref_at_valid; [exact LS3| exact HAt3]).
      assert (HVn3 : vref RMontN bs2) by (eapply ref_at_valid; [exact LS3| exact (ref_at_montN bs2 OW2 PL am qm HPM)]).
      assert (EX2 : getbn rx bs2 = b2) by (subst bs2; apply getbn_setbn_same; exact HVx2).
      assert (EN2 : getbn RMontN bs2 = bn) by (subst bs2; rewrite getbn_setbn_other by exact NExn; exact EN1).
      assert (ET2 : getbn rt bs2 = getbn rt bs1) by (subst bs2; apply getbn_setbn_other; intros E; apply NEtx; symmetry; exact E).
      assert (EX3 : getbn rx bs3 = b2).
      { destruct WXR3 as [[_ ->]|[_ (p3 & ->)]]; [exact EX2| rewrite getbn_setbn_other by exact NEtx; exact EX2]. }
      assert (EN3 : getbn RMontN bs3 = bn).
      { destruct WXR3 as [[_ ->]|[_ (p3 & ->)]]; [exact EN2| rewrite getbn_setbn_other by exact NEtn; exact EN2]. }
      assert (Hinn5 : In (pn, Dn2, 8 * Z.of_nat (bn_dmax bn)) OW5).
      { apply BST3; [exact Hinn|]. rewrite ET2. intros E.
        pose proof (lib_state_h_parts _ _ _ _ _ _ LS3) as (_ & _ & IDS3 & _).
        refine (ids_bn_neq rt RMontN bs2 pn pn (ids_m_nodup _ _ _ IDS3) HVt3 HVn3 NEtn _ _ eq_refl).
        - rewrite ET2. exact E.
        - rewrite EN2. exact Edn. }
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS5 HAt3) as HAt5. pose proof (ref_at_stable _ _ _ _ PL _ _ RS5 HAx3) as HAx5.
      cbn [embed interp]. apply implM_ret. unfold MallocRep.wz.
      lazymatch type of ENV5 with kenv _ _ _ _ _ _ _ _ _ _ (C8 _ :: ?frr) _ _ _ _ =>
        pose proof (L_final LB PL EA lo B (bv_unsigned sp) (bv_unsigned sp + -112) s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK
                      ltac:(clear; lia)
                      ltac:(clear - LOF; unfold BN_WEXPAND_STACK, BN_EXPAND2_STACK in LOF; lia)
                      (fun bsF stF => bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
                                        (fun (_ : unit) (_ : bstate bptr) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = Z_to_bv 64 1) (tt, bsF) stF)
                      frr gp F fc st3 bs3 m5 OW5 rt rx at_ ax am qm Dn2 pn carry) as LF
      end.
      rewrite EN3 in LF. fold nl in LF. fold np in LF. unfold fm_final, fm_ret in LF. rewrite (Z_to_bv_bv_unsigned sp) in LF.
      eapply LF; [exact ENV5| exact LS5| exact HAt5| exact HAx5| exact WRt| exact WRx| exact HPM| exact NEtx| exact NEtn| exact NExn
                 | exact At0'| exact At8| exact AtR'| exact Ax0'| exact Ax8| exact AxR'
                 | clear - NT; lia| exact Edn| exact Hinn5| exact Dn0| exact Dn8
                 | exact HDM3| rewrite EX3; change (bn_dmax b2) with (length buf); rewrite LENB; exact HDM1
                 | exact HC| exact (EPI (Z_to_bv 64 Dn2))].
  Qed.
End Proofs.
End WithCeiling0.
