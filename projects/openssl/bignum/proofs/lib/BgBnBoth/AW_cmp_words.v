(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnCmp.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require W_cmp_words.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2247552 => 2
  | 2247564 => 1
  | 2247568 => 1
  | 2247572 => 2
  | 2247576 => 1
  | 2247580 => 1
  | 2247584 => 1
  | 2247588 => 1
  | 2247592 => 2
  | 2247596 => 2
  | 2247600 => 1
  | 2247604 => 2
  | 2247640 => 1
  | 2247644 => 1
  | 2247648 => 2
  | 2247652 => 1
  | 2247656 => 1
  | 2247660 => 1
  | 2247664 => 2
  | 2247668 => 2
  | 2247672 => 1
  | 2247676 => 2
  | 2247740 => 2
  | 2247748 => 1
  | 2247752 => 1
  | 2247764 => 2
  | 2247768 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Definition bn_cmp_words_aentry := 0x224b68%Z.

Notation ro_post := W_cmp_words.ro_post.

Lemma lxor_ones64' : forall x, (0 <= x < 18446744073709551616 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x)%Z.
Proof.
  intros x Hx. change 18446744073709551615%Z with (Z.ones 64) at 1.
  assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases i 64) as [H|H].
    - rewrite Z.ones_spec_low by lia. rewrite andb_true_r, xorb_true_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite andb_false_r, xorb_false_r.
      destruct (Z.eq_dec x 0) as [->|Nx]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. assert (Z.log2 x < 64)%Z by (apply Z.log2_lt_pow2; lia). lia. }
  rewrite E, Z.land_ones by lia. unfold Z.lnot, Z.pred. change (2 ^ 64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. lia.
Qed.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z).
  Notation ap := (bv_unsigned a0).
  Notation bp := (bv_unsigned a1).
  Notation n := (Z.of_nat (length a)).
  Notation SP := (bv_unsigned sp).
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
  Hypothesis LEN : length b = length a.
  Hypothesis N31 : (n < 2^31)%Z.
  Hypothesis A2 : bv_unsigned a2 = n.
  Hypothesis RA : limbs_at bgbsegs m ap a.
  Hypothesis RB : limbs_at bgbsegs m bp b.
  Hypothesis STK : stk bgbsegs m lo SP.
  Hypothesis LO : (lo <= SP - 16)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 16 \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * n <= SP - 16 \/ SP <= bp)%Z.
  Hypothesis MI0 : mem_inv bgbsegs m.

  Hypothesis SHBC : shb_cells bgbsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACA : acc bgbsegs m ap (8 * n).
  Hypothesis ACB : acc bgbsegs m bp (8 * n).
  Hypothesis AL8A : (ap mod 8 = 0)%Z.
  Hypothesis AL8B : (bp mod 8 = 0)%Z.
  Hypothesis SHLO_LO : (SHHI <= lo)%Z.

  Hypothesis UBA : ub_ptr_ok n ap.
  Hypothesis UBB : ub_ptr_ok n bp.

  Notation POST := (ro_post bgbsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 16%Z (cmp_words a b) lo m).

  Notation ST pc mm x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgbsegs)).
  Notation FW := [(SP + -16, SP)]%Z.

  Definition CINV (m1 : word -> option byte) : Prop :=
    limbs_at bgbsegs m1 ap a /\ limbs_at bgbsegs m1 bp b /\
    rw_cells bgbsegs m1 (SP + -16) [C8 s0; C8 ra] /\ stk bgbsegs m1 lo (SP + -16) /\
    mem_inv bgbsegs m1 /\ munch FW m m1 /\ wmono bgbsegs m m1.

  Definition cpure : Prop :=
    (0 < ap /\ ap mod 8 = 0 /\ ap + 8 * n <= 140737488355328)%Z /\ (0 < bp /\ bp mod 8 = 0 /\ bp + 8 * n <= 140737488355328)%Z /\ offshW FW.

  Lemma cpure_intro : (0 < n)%Z -> cpure.
  Proof using RA RB MI0 LEN LO SHLO_LO UBA UBB AL8A AL8B.
    intros Hn. unfold cpure.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA. pose proof (limbs_at_bound _ _ _ _ RB) as BB.
    assert (NE : forall l : list Z, (0 < Z.of_nat (length l))%Z -> lbytes l <> []).
    { intros l Hl E. pose proof (lbytes_lengthZ l) as L. rewrite E in L. cbn [length] in L. lia. }
    pose proof (bytes_at_below bgbsegs m ap _ MI0 RA (NE a Hn)) as TA. rewrite lbytes_lengthZ in TA. unfold UTOP in TA.
    pose proof (bytes_at_below bgbsegs m bp _ MI0 RB (NE b ltac:(rewrite LEN; exact Hn))) as TB. rewrite lbytes_lengthZ, LEN in TB. unfold UTOP in TB.
    destruct (UBA Hn) as [PA _]. destruct (UBB Hn) as [PB _].
    split; [lia|]. split; [lia|]. cbn [offshW]. split; [right; lia | exact I].
  Qed.

  Lemma shA : forall m1 (k : nat) ad, cpure -> CINV m1 -> (k < length a)%nat -> ad = wa (shad (ap + 8 * Z.of_nat k)) ->
    ov_read_bytes bgbsegs m1 ad 1 = Some [z8].
  Proof using ACA AL8A LEN.
    intros m1 k ad ((PA & _ & BA) & _ & OFF) (_ & _ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bgbsegs FW m m1 ap n 0 (Z.of_nat k) _ ACA MU OFF AL8A (conj (Z.lt_le_incl _ _ PA) BA)); [reflexivity | lia | lia | lia |].
    rewrite Z.add_0_r. reflexivity.
  Qed.
  Lemma shB : forall m1 (k : nat) ad, cpure -> CINV m1 -> (k < length a)%nat -> ad = wa (shad (bp + 8 * Z.of_nat k)) ->
    ov_read_bytes bgbsegs m1 ad 1 = Some [z8].
  Proof using ACB AL8B LEN.
    intros m1 k ad (_ & (PB & _ & BB) & OFF) (_ & _ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bgbsegs FW m m1 bp n 0 (Z.of_nat k) _ ACB MU OFF AL8B (conj (Z.lt_le_incl _ _ PB) BB)); [reflexivity | lia | lia | lia |].
    rewrite Z.add_0_r. reflexivity.
  Qed.

  Lemma cw_ret : forall m1 res x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17, CINV m1 -> res = cmp_words a b ->
    evt bgbsegs POST (ST 0x224c28 m1 x5 x6 x7 x8 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 res x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 (HA & HB & FR & ST & MI & MU & WM) ->.
    do 4 zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  Lemma cw_differ : forall m1 x y x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17, CINV m1 ->
    (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z -> x <> y -> cmp1 x y = cmp_words a b ->
    evt bgbsegs POST (ST 0x224c20 m1 x5 x6 x7 x8 (Z_to_bv 64 (Z.b2z (y <? x)%Z)) x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x y x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 I Rx Ry NE E.
    do 2 zstep.
    setreg 10%Z (Z_to_bv 64 (cmp1 x y))
      ltac:(unfold cmp1; destruct (Z.eqb_spec x y) as [|_]; [contradiction|]; destruct (y <? x)%Z; apply Z_to_bv_eqm; vm_compute; reflexivity).
    eapply cw_ret; [exact I | exact E].
  Qed.

  Lemma cw_zero : forall m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17, CINV m1 -> cmp_words a b = 0%Z ->
    evt bgbsegs POST (ST 0x224c94 m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 I E.
    do 2 zstep.
    eapply cw_ret; [exact I | symmetry; exact E].
  Qed.

  Lemma cw_loop : forall (k : nat) m1 x5 x6 x7 x8 x12 x13, cpure -> CINV m1 -> (1 <= k <= length a)%nat ->
    cmp_words a b = cmp_words (firstn k a) (firstn k b) ->
    evt bgbsegs POST (ST 0x224c4c m1 x5 x6 x7 x8 a0 a1 x12 x13 (Z_to_bv 64 (18446744073709551615 - ap)) (Z_to_bv 64 (Z.of_nat k))
                       (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - bp))).
  Proof.
    induction k as [|k IH]; intros m1 x5 x6 x7 x8 x12 x13 P I Hk E; [exfalso; lia|].
    pose proof I as (HA & HB & _). pose proof P as ((PA & AA & BA) & (PB & AB & BB) & _).
    assert (Hka : (k < length a)%nat) by lia. assert (Hkb : (k < length b)%nat) by lia.
    destruct (nth_error a k) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    destruct (nth_error b k) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
    pose proof (limbs_nth_error_lit a k x LA Ex) as Rx. pose proof (limbs_nth_error_lit b k y LB Ey) as Ry.
    assert (Hkz : (0 <= Z.of_nat k /\ 8 * Z.of_nat k + 8 <= 8 * n)%Z) by (clear - Hka; lia).
    zstep.
    rewrite (bn_swrap32_small (Z.of_nat (S k) + -1)) by (clear - Hk N31; lia).
    replace (Z.of_nat (S k) + -1)%Z with (Z.of_nat k) by (clear; lia).
    zstep.
    replace (Z.of_nat k ≪ 3)%Z with (8 * Z.of_nat k)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    ub. zstep.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shA m1 k ad P I Hka ltac:(sh_addr)) as RD); zstep; clear RD.
    chk0.
    zstep.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shB m1 k ad P I Hka ltac:(sh_addr)) as RD); zstep; clear RD.
    chk0.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgbsegs m1 ap a k x ad HA Ex ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgbsegs m1 bp b k y ad HB Ey ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    pose proof (cmp_words_top a b k x y (eq_sym LEN) Ex Ey) as T.
    zstep. if_cases K1; zify_cond K1.
    -
      do 2 zstep.
      eapply cw_differ; [exact I | exact Rx | exact Ry | exact K1 |].
      rewrite E, T. destruct (Z.eqb_spec x y) as [|_]; [contradiction | reflexivity].
    - assert (E' : cmp_words a b = cmp_words (firstn k a) (firstn k b)).
      { rewrite E, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
      zstep. if_cases K2; zify_cond K2.
      + eapply IH; [exact P | exact I | clear - K0 Hk; lia | exact E'].
      + assert (k = 0%nat).
        { apply andb_false_iff in K2. destruct K2 as [K2|K2]; apply Z.ltb_ge in K2; clear - K2 Hk N31; lia. }
        subst k.
        eapply cw_zero; [exact I | rewrite E'; reflexivity].
  Qed.

  Lemma bn_cmp_words_aspec :
    evt bgbsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x224b68) fc None m (seg_rom bgbsegs)).
  Proof.
    pose proof (munch_refl [(SP - 16, SP)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
    assert (LOHI : (17594333495296 <= lo)%Z) by (clear - SHLO_LO; unfold SHHI in SHLO_LO; exact SHLO_LO).
    assert (Ph : hide ((0 < n)%Z -> cpure)) by (apply hide_intro; exact cpure_intro).
    destruct SHBC as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    carve_frame 16%nat STK.
    do 4 zstep.
    assert (I : CINV m1).
    { unfold CINV. split; [|split].
      - eapply limbs_at_transport; [exact RA | exact MU | cbn [disjoint_from]; lia].
      - eapply limbs_at_transport; [exact RB | exact MU | cbn [disjoint_from]; rewrite LEN; lia].
      - split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM]. }
    zstep. if_cases K; zify_cond K.
    {
      assert (E0 : cmp_words a b = 0%Z) by (clear - K A2; destruct a; [reflexivity | exfalso; cbn [length] in *; lia]).
      eapply cw_zero; [exact I | exact E0]. }
    assert (Hn : (1 <= length a)%nat) by (clear - K A2; lia).
    set (k := (length a - 1)%nat).
    assert (Ek : (Z.of_nat k = n - 1)%Z) by (subst k; clear - Hn; lia).
    assert (Hka : (k < length a)%nat) by (subst k; clear - Hn; lia).
    destruct (nth_error a k) as [x|] eqn:Ex; [|apply nth_error_None in Ex; subst k; lia].
    destruct (nth_error b k) as [y|] eqn:Ey; [|apply nth_error_None in Ey; subst k; lia].
    pose proof (limbs_nth_error_lit a k x LA Ex) as Rx. pose proof (limbs_nth_error_lit b k y LB Ey) as Ry.
    pose proof I as (HA & HB & _).
    pose proof (hide_elim _ Ph ltac:(lia)) as P. clear Ph. pose proof P as ((PA & AA & BA) & (PB & AB & BB) & _).
    assert (Ea2 : a2 = Z_to_bv 64 n) by (rewrite <- A2; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Hkz : (0 <= Z.of_nat k /\ 8 * Z.of_nat k + 8 <= 8 * n)%Z) by (clear - Hka; lia).
    zstep. rewrite A2. rewrite (bn_swrap32_small (n + -1)) by (clear - Hn N31; lia).
    replace (n + -1)%Z with (Z.of_nat k) by (clear - Ek; lia). rewrite Ea2.
    ub. zstep.
    replace (Z.of_nat k ≪ 3)%Z with (8 * Z.of_nat k)%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    zstep.
    ub. do 3 zstep.
    do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shA m1 k ad P I Hka ltac:(sh_addr)) as RD); zstep; clear RD.
    chk0.
    zstep.
    ub. do 2 zstep.
    (let ad := cur_mem_addr in pose proof (shB m1 k ad P I Hka ltac:(sh_addr)) as RD); zstep; clear RD.
    chk0.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgbsegs m1 ap a k x ad HA Ex ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgbsegs m1 bp b k y ad HB Ey ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    pose proof (cmp_words_top a b k x y (eq_sym LEN) Ex Ey) as T.
    assert (EF : cmp_words a b = cmp_words (firstn (S k) a) (firstn (S k) b)).
    { replace (S k) with (length a) by (subst k; clear - Hn; lia). rewrite firstn_all. rewrite <- LEN, firstn_all. reflexivity. }
    clear RA RB FR STK MI0 MU WM G1 G2.
    zstep. if_cases K1; zify_cond K1.
    -
      assert (E' : cmp_words a b = cmp_words (firstn k a) (firstn k b)).
      { rewrite EF, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
      zstep. rewrite (bn_swrap32_small (n + -2)) by (clear - Hn N31; lia).
      ub. zstep. rewrite lts_signed by (clear - Hn N31; lia).
      if_cases K2; zify_cond K2.
      +
        assert (H0 : k = 0%nat) by (subst k; clear - K2 Hn; lia).
        eapply cw_zero; [exact I | rewrite E', H0; reflexivity].
      + do 2 zstep. rewrite !lxor_ones64' by (clear - PA BA PB BB Hn; lia).
        eapply evt_eq; [ | eapply (cw_loop k m1); [exact P | exact I | subst k; clear - K2 Hn; lia | exact E'] ].
        reflexivity.
    -
      zstep.
      eapply cw_differ; [exact I | exact Rx | exact Ry | exact K1 |].
      rewrite EF, T. destruct (Z.eqb_spec x y) as [|_]; [contradiction | reflexivity].
  Qed.
End Proofs.
