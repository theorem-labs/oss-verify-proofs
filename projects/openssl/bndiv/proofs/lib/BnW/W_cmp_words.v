(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnCmp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition bn_cmp_words_entry := 0xdea5c%Z.

(* [comment removed for export] *)
Definition ro_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fs : Z) (res : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(bv_unsigned sp - fs, bv_unsigned sp)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ stk segs m' lo (bv_unsigned sp).

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
  Hypothesis RA : limbs_at psegs m ap a.
  Hypothesis RB : limbs_at psegs m bp b.
  Hypothesis STK : stk psegs m lo SP.
  Hypothesis LO : (lo <= SP - 16)%Z.
  Hypothesis SEPA : (ap + 8 * n <= SP - 16 \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * n <= SP - 16 \/ SP <= bp)%Z.
  Hypothesis MI0 : mem_inv psegs m.

  Notation POST := (ro_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 16%Z (cmp_words a b) lo m).

  (* [comment removed for export] *)
  Notation ST pc mm x8 x10 x11 x12 x13 x14 x15 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 x8 s1 x10 x11 x12 x13 x14 x15 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Definition CINV (m1 : word -> option byte) : Prop :=
    limbs_at psegs m1 ap a /\ limbs_at psegs m1 bp b /\
    rw_cells psegs m1 (SP + -16) [C8 s0; C8 ra] /\ stk psegs m1 lo (SP + -16) /\
    mem_inv psegs m1 /\ munch [(SP + -16, SP)]%Z m m1 /\ wmono psegs m m1.

  (* [comment removed for export] *)
  Lemma cw_ret : forall m1 res x8 x11 x12 x13 x14 x15, CINV m1 -> res = cmp_words a b ->
    evt psegs POST (ST 0xdea98 m1 x8 (Z_to_bv 64 res) x11 x12 x13 x14 x15).
  Proof.
    intros m1 res x8 x11 x12 x13 x14 x15 (HA & HB & FR & ST & MI & MU & WM) ->.
    do 4 zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma cw_differ : forall m1 x y x8 x10 x11 x12 x15, CINV m1 ->
    (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z -> x <> y -> cmp1 x y = cmp_words a b ->
    evt psegs POST (ST 0xdea8c m1 x8 x10 x11 x12 (Z_to_bv 64 x) (Z_to_bv 64 y) x15).
  Proof.
    intros m1 x y x8 x10 x11 x12 x15 I Rx Ry NE E.
    do 3 zstep.
    setreg 10%Z (Z_to_bv 64 (cmp1 x y))
      ltac:(unfold cmp1; destruct (Z.eqb_spec x y) as [|_]; [contradiction|]; destruct (y <? x)%Z; apply Z_to_bv_eqm; vm_compute; reflexivity).
    eapply cw_ret; [exact I | exact E].
  Qed.

  (* [comment removed for export] *)
  Lemma cw_zero : forall m1 x8 x10 x11 x12 x13 x14 x15, CINV m1 -> cmp_words a b = 0%Z ->
    evt psegs POST (ST 0xdead4 m1 x8 x10 x11 x12 x13 x14 x15).
  Proof.
    intros m1 x8 x10 x11 x12 x13 x14 x15 I E.
    do 2 zstep.
    eapply cw_ret; [exact I | symmetry; exact E].
  Qed.

  (* [comment removed for export] *)
  Lemma cw_loop : forall (k : nat) m1 x8 x13 x14 x15, CINV m1 -> (1 <= k <= length a)%nat ->
    cmp_words a b = cmp_words (firstn k a) (firstn k b) ->
    evt psegs POST (ST 0xdeab4 m1 x8 a0 a1 (Z_to_bv 64 (Z.of_nat k)) x13 x14 x15).
  Proof.
    induction k as [|k IH]; intros m1 x8 x13 x14 x15 I Hk E; [exfalso; lia|].
    pose proof I as (HA & HB & _).
    assert (Hka : (k < length a)%nat) by lia. assert (Hkb : (k < length b)%nat) by lia.
    destruct (nth_error a k) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
    destruct (nth_error b k) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
    pose proof (limbs_nth_error_lit a k x LA Ex) as Rx. pose proof (limbs_nth_error_lit b k y LB Ey) as Ry.
    zstep.
    rewrite (bn_swrap32_small (Z.of_nat (S k) + -1)) by (clear - Hk N31; lia).
    replace (Z.of_nat (S k) + -1)%Z with (Z.of_nat k) by (clear; lia).
    do 3 zstep.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth psegs m1 ap a k x ad HA Ex ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD); zstep; clear RD.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth psegs m1 bp b k y ad HB Ey ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD); zstep; clear RD.
    pose proof (cmp_words_top a b k x y (eq_sym LEN) Ex Ey) as T.
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      eapply cw_differ; [exact I | exact Rx | exact Ry | exact K1 |].
      rewrite E, T. destruct (Z.eqb_spec x y) as [|_]; [contradiction | reflexivity].
    - assert (E' : cmp_words a b = cmp_words (firstn k a) (firstn k b)).
      { rewrite E, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
      zstep. if_cases K2; zify_cond K2.
      + eapply IH; [exact I | clear - K0 Hk; lia | exact E'].
      + assert (k = 0%nat).
        { apply andb_false_iff in K2. destruct K2 as [K2|K2]; apply Z.ltb_ge in K2; clear - K2 Hk N31; lia. }
        subst k.
        eapply cw_zero; [exact I | rewrite E'; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma bn_cmp_words_spec :
    evt psegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xdea5c) fc None m (seg_rom psegs)).
  Proof.
    pose proof (munch_refl [(SP - 16, SP)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    carve_frame 16%nat STK.
    do 4 zstep.
    assert (I : CINV m1).
    { unfold CINV. split; [|split].
      - eapply limbs_at_transport; [exact RA | exact MU | cbn [disjoint_from]; lia].
      - eapply limbs_at_transport; [exact RB | exact MU | cbn [disjoint_from]; rewrite LEN; lia].
      - split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM]. }
    clear RA RB FR STK MI0 MU WM.
    zstep. if_cases K; zify_cond K.
    { (* [comment removed for export] *)
      assert (E0 : cmp_words a b = 0%Z) by (clear - K A2; destruct a; [reflexivity | exfalso; cbn [length] in *; lia]).
      eapply cw_zero; [exact I | exact E0]. }
    assert (Hn : (1 <= length a)%nat) by (clear - K A2; lia).
    set (k := (length a - 1)%nat).
    assert (Ek : (Z.of_nat k = n - 1)%Z) by (subst k; clear - Hn; lia).
    destruct (nth_error a k) as [x|] eqn:Ex; [|apply nth_error_None in Ex; subst k; lia].
    destruct (nth_error b k) as [y|] eqn:Ey; [|apply nth_error_None in Ey; subst k; lia].
    pose proof (limbs_nth_error_lit a k x LA Ex) as Rx. pose proof (limbs_nth_error_lit b k y LB Ey) as Ry.
    pose proof I as (HA & HB & _).
    do 4 zstep.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth psegs m1 ap a k x ad HA Ex ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD); zstep; clear RD.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth psegs m1 bp b k y ad HB Ey ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD); zstep; clear RD.
    pose proof (cmp_words_top a b k x y (eq_sym LEN) Ex Ey) as T.
    assert (EF : cmp_words a b = cmp_words (firstn (S k) a) (firstn (S k) b)).
    { replace (S k) with (length a) by (subst k; clear - Hn; lia). rewrite firstn_all. rewrite <- LEN, firstn_all. reflexivity. }
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      assert (E' : cmp_words a b = cmp_words (firstn k a) (firstn k b)).
      { rewrite EF, T. destruct (Z.eqb_spec x y) as [_|]; [reflexivity | contradiction]. }
      zstep.
      assert (Ea2 : a2 = Z_to_bv 64 n) by (rewrite <- A2; symmetry; apply Z_to_bv_bv_unsigned).
      zstep. rewrite Ea2. rewrite lts_small by (clear - N31; lia).
      if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (H0 : k = 0%nat) by (subst k; clear - K2 Hn; lia).
        eapply cw_zero; [exact I | rewrite E', H0; reflexivity].
      + zstep.
        replace (n + -1)%Z with (Z.of_nat k) by (clear - Ek; lia).
        eapply evt_eq; [ | eapply (cw_loop k m1 sp (Z_to_bv 64 2) (Z_to_bv 64 y)); [exact I | subst k; clear - K2 Hn; lia | exact E'] ].
        reflexivity.
    - (* [comment removed for export] *)
      eapply cw_differ; [exact I | exact Rx | exact Ry | exact K1 |].
      rewrite EF, T. destruct (Z.eqb_spec x y) as [|_]; [contradiction | reflexivity].
  Qed.
End Proofs.
