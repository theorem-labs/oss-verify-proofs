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
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnCmp.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require W_cmp_words.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_cmp_words_aentry := 0x226504%Z.

Notation ro_post := W_cmp_words.ro_post.

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
  Hypothesis RA : limbs_at bgasegs m ap a.
  Hypothesis RB : limbs_at bgasegs m bp b.
  Hypothesis STK : stk bgasegs m lo SP.
  Hypothesis LO : (lo <= SP - 16)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 16 \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * n <= SP - 16 \/ SP <= bp)%Z.
  Hypothesis MI0 : mem_inv bgasegs m.

  Hypothesis SHBC : shb_cells bgasegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACA : acc bgasegs m ap (8 * n).
  Hypothesis ACB : acc bgasegs m bp (8 * n).
  Hypothesis AL8A : (ap mod 8 = 0)%Z.
  Hypothesis AL8B : (bp mod 8 = 0)%Z.
  Hypothesis SHLO_LO : (SHHI <= lo)%Z.

  Notation POST := (ro_post bgasegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 16%Z (cmp_words a b) lo m).

  Notation ST pc mm x8 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgasegs)).
  Notation FW := [(SP + -16, SP)]%Z.

  Definition CINV (m1 : word -> option byte) : Prop :=
    limbs_at bgasegs m1 ap a /\ limbs_at bgasegs m1 bp b /\
    rw_cells bgasegs m1 (SP + -16) [C8 s0; C8 ra] /\ stk bgasegs m1 lo (SP + -16) /\
    mem_inv bgasegs m1 /\ munch FW m m1 /\ wmono bgasegs m m1.

  Definition cpure : Prop :=
    (0 <= ap /\ ap + 8 * n <= 140737488355328)%Z /\ (0 <= bp /\ bp + 8 * n <= 140737488355328)%Z /\ offshW FW.

  Lemma cpure_intro : (0 < n)%Z -> cpure.
  Proof using RA RB MI0 LEN LO SHLO_LO.
    intros Hn. unfold cpure.
    pose proof (limbs_at_bound _ _ _ _ RA) as BA. pose proof (limbs_at_bound _ _ _ _ RB) as BB.
    assert (NE : forall l : list Z, (0 < Z.of_nat (length l))%Z -> lbytes l <> []).
    { intros l Hl E. pose proof (lbytes_lengthZ l) as L. rewrite E in L. cbn [length] in L. lia. }
    pose proof (bytes_at_below bgasegs m ap _ MI0 RA (NE a Hn)) as TA. rewrite lbytes_lengthZ in TA. unfold UTOP in TA.
    pose proof (bytes_at_below bgasegs m bp _ MI0 RB (NE b ltac:(rewrite LEN; exact Hn))) as TB. rewrite lbytes_lengthZ, LEN in TB. unfold UTOP in TB.
    split; [lia|]. split; [lia|]. cbn [offshW]. split; [right; lia | exact I].
  Qed.

  Lemma shA : forall m1 (k : nat) ad, cpure -> CINV m1 -> (k < length a)%nat -> ad = wa (shad (ap + 8 * Z.of_nat k)) ->
    ov_read_bytes bgasegs m1 ad 1 = Some [z8].
  Proof using ACA AL8A LEN.
    intros m1 k ad (BA & _ & OFF) (_ & _ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bgasegs FW m m1 ap n 0 (Z.of_nat k) _ ACA MU OFF AL8A BA); [reflexivity | lia | lia | lia |].
    rewrite Z.add_0_r. reflexivity.
  Qed.
  Lemma shB : forall m1 (k : nat) ad, cpure -> CINV m1 -> (k < length a)%nat -> ad = wa (shad (bp + 8 * Z.of_nat k)) ->
    ov_read_bytes bgasegs m1 ad 1 = Some [z8].
  Proof using ACB AL8B LEN.
    intros m1 k ad (_ & BB & OFF) (_ & _ & _ & _ & _ & MU & _) Hk ->.
    apply (acc_rd_limb bgasegs FW m m1 bp n 0 (Z.of_nat k) _ ACB MU OFF AL8B BB); [reflexivity | lia | lia | lia |].
    rewrite Z.add_0_r. reflexivity.
  Qed.

  Lemma cw_ret : forall m1 res x8 x11 x12 x13 x14 x15 x16 x17, CINV m1 -> res = cmp_words a b ->
    evt bgasegs POST (ST 0x22656c m1 x8 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 res x8 x11 x12 x13 x14 x15 x16 x17 (HA & HB & FR & ST & MI & MU & WM) ->.
    do 4 zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  Lemma cw_differ : forall m1 x y x8 x11 x12 x13 x14 x15 x16 x17, CINV m1 ->
    (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z -> x <> y -> cmp1 x y = cmp_words a b ->
    evt bgasegs POST (ST 0x226564 m1 x8 (Z_to_bv 64 (if (y <? x)%Z then 1 else 0)) x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x y x8 x11 x12 x13 x14 x15 x16 x17 I Rx Ry NE E.
    do 2 zstep.
    setreg 10%Z (Z_to_bv 64 (cmp1 x y))
      ltac:(unfold cmp1; destruct (Z.eqb_spec x y) as [|_]; [contradiction|]; destruct (y <? x)%Z; apply Z_to_bv_eqm; vm_compute; reflexivity).
    eapply cw_ret; [exact I | exact E].
  Qed.

  Lemma cw_zero : forall m1 x8 x10 x11 x12 x13 x14 x15 x16 x17, CINV m1 -> cmp_words a b = 0%Z ->
    evt bgasegs POST (ST 0x2265c4 m1 x8 x10 x11 x12 x13 x14 x15 x16 x17).
  Proof.
    intros m1 x8 x10 x11 x12 x13 x14 x15 x16 x17 I E.
    do 2 zstep.
    eapply cw_ret; [exact I | symmetry; exact E].
  Qed.

  Lemma cw_loop : forall (k : nat) m1 x8 x12 x13 x14 x17, cpure -> CINV m1 -> (1 <= k <= length a)%nat ->
    cmp_words a b = cmp_words (firstn k a) (firstn k b) ->
    evt bgasegs POST (ST 0x226584 m1 x8 a0 a1 x12 x13 x14 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat k)) x17).
  Proof.
    induction k as [|k IH]; intros m1 x8 x12 x13 x14 x17 P I Hk E; [exfalso; lia|].
    pose proof I as (HA & HB & _).
    assert (Hka : (k < length a)%nat) by lia. assert (Hkb : (k < length b)%nat) by lia.
    destruct (nth_error a k) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    destruct (nth_error b k) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
    pose proof (limbs_nth_error_lit a k x LA Ex) as Rx. pose proof (limbs_nth_error_lit b k y LB Ey) as Ry.
    pose proof P as (BA & BB & _).
    zstep.
    rewrite (bn_swrap32_small (Z.of_nat (S k) + -1)) by (clear - Hk N31; lia).
    replace (Z.of_nat (S k) + -1)%Z with (Z.of_nat k) by (clear; lia).
    zstep.
    replace (Z.of_nat k ≪ 3)%Z with (8 * Z.of_nat k)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    do 3 zstep.
    (let ad := cur_mem_addr in pose proof (shA m1 k ad P I Hka ltac:(sh_addr)) as RD); zstep; clear RD.
    chk0.
    do 3 zstep.
    (let ad := cur_mem_addr in pose proof (shB m1 k ad P I Hka ltac:(sh_addr)) as RD); zstep; clear RD.
    chk0.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgasegs m1 ap a k x ad HA Ex ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgasegs m1 bp b k y ad HB Ey ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
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
    evt bgasegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x226504) fc None m (seg_rom bgasegs)).
  Proof.
    pose proof (munch_refl [(SP - 16, SP)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
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
    pose proof (hide_elim _ Ph ltac:(lia)) as P. clear Ph. pose proof P as (BA & BB & _).
    do 4 zstep.
    rewrite A2. rewrite (bn_swrap32_small (n + -1)) by (clear - Hn N31; lia).
    replace (n + -1)%Z with (Z.of_nat k) by (clear - Ek; lia).
    zstep.
    replace (Z.of_nat k ≪ 3)%Z with (8 * Z.of_nat k)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    do 3 zstep.
    (let ad := cur_mem_addr in pose proof (shA m1 k ad P I Hka ltac:(sh_addr)) as RD); zstep; clear RD.
    chk0.
    do 3 zstep.
    (let ad := cur_mem_addr in pose proof (shB m1 k ad P I Hka ltac:(sh_addr)) as RD); zstep; clear RD.
    chk0.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgasegs m1 ap a k x ad HA Ex ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgasegs m1 bp b k y ad HB Ey ltac:(unfold wa; f_equal; lia)) as RD); zstep; clear RD.
    pose proof (cmp_words_top a b k x y (eq_sym LEN) Ex Ey) as T.
    assert (EF : cmp_words a b = cmp_words (firstn (S k) a) (firstn (S k) b)).
    { replace (S k) with (length a) by (subst k; clear - Hn; lia). rewrite firstn_all. rewrite <- LEN, firstn_all. reflexivity. }
    clear RA RB FR STK MI0 MU WM G1 G2.
    zstep. if_cases K1; zify_cond K1.
    -
      assert (E' : cmp_words a b = cmp_words (firstn k a) (firstn k b)).
      { rewrite EF, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
      zstep.
      assert (Ea2 : a2 = Z_to_bv 64 n) by (rewrite <- A2; symmetry; apply Z_to_bv_bv_unsigned).
      zstep. rewrite Ea2. rewrite lts_small by (clear - N31; lia).
      if_cases K2; zify_cond K2.
      +
        assert (H0 : k = 0%nat) by (subst k; clear - K2 Hn; lia).
        eapply cw_zero; [exact I | rewrite E', H0; reflexivity].
      + eapply evt_eq; [ | eapply (cw_loop k m1); [exact P | exact I | subst k; clear - K2 Hn; lia | exact E'] ].
        reflexivity.
    -
      zstep.
      eapply cw_differ; [exact I | exact Rx | exact Ry | exact K1 |].
      rewrite EF, T. destruct (Z.eqb_spec x y) as [|_]; [contradiction | reflexivity].
  Qed.
End Proofs.
