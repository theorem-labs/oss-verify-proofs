(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls F_inet_pton_A.
Import ListNotations.
Open Scope bv_scope.
Local Ltac flia ::= flia_cheap.

Notation w z := (Z_to_bv 64 z) (only parsing).
Ltac zs := zstep; fix_lit_store.

Section IP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (S : Z) (str : list byte) (A : Z) (N : nat) (canary : word) (lo : Z).
  Hypothesis LO : (lo <= bv_unsigned sp - 80)%Z.
  Hypothesis BND : (0 <= S /\ S + Z.of_nat (length str) + 1 <= 2^64 /\ 0 <= A /\ A + Z.of_nat N <= 2^64 /\ 0 <= lo /\ bv_unsigned sp < 2^64)%Z.
  Hypothesis SEPS : (S + Z.of_nat (length str) + 1 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= S)%Z.
  Hypothesis SEPA : (A + Z.of_nat N <= bv_unsigned sp - 80 \/ bv_unsigned sp <= A)%Z.
  Hypothesis SEPAS : (A + Z.of_nat N <= S \/ S + Z.of_nat (length str) + 1 <= A)%Z.
  Hypothesis SEPG : (got_ssp + 8 <= bv_unsigned sp - 80)%Z.
  Hypothesis SEPC : (ssp_guard + 8 <= bv_unsigned sp - 80)%Z.
  Hypothesis SEPAG : (A + Z.of_nat N <= got_ssp \/ got_ssp + 8 <= A)%Z.
  Hypothesis SEPAC : (A + Z.of_nat N <= ssp_guard \/ ssp_guard + 8 <= A)%Z.

  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ [Z_to_bv 8 0]).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + Z.of_nat N)]%Z.
  Notation POST := (inet_pton_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str A N canary lo m).

  Notation INV' := (INV ra sp s0 s1 s2 s3 s4 s5 m S str A N canary lo).
  Notation VR' := (VR sp gp tp s6 s7 s8 s9 s10 s11).
  Notation CONTv' := (CONTv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S str A N canary lo).
  Notation str_read' := (str_read ra sp s0 s1 s2 s3 s4 s5 m S str A N canary lo SEPS SEPA SEPAS SEPG SEPC).
  Notation out_store' := (out_store ra sp s0 s1 s2 s3 s4 s5 m S str A N canary lo LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC).
  Notation ip_exit' := (ip_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S str A N canary lo LO BND).
  Notation ip_ret0' := (ip_ret0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S str A N canary lo LO BND).

  Ltac st_name :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs0) _) =>
      repeat match goal with
      | H : store_ok _ m1 _ _ = true |- _ => clear H
      | H : ov_read_bytes _ m1 _ _ = Some _ |- _ => clear H
      | H : INV' m1 |- _ => clear H
      end;
      let m' := fresh "m" in remember (write_to_mem m1 a bs0) as m' eqn:E; clear E; try clear m1
    end.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC"] Lemma v4b_tail : forall m1 (ao k i j : Z) x1 (xa1 xt1 xt2 xs1 xa0 : word) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6,
    INV' m1 -> (i < 3 -> CONTv' 0x1a3e4 ao i)%Z -> (0 <= i <= 3)%Z -> (1 <= j <= 3)%Z -> (0 <= k)%Z -> (k + j <= len)%Z ->
    (A <= ao)%Z -> (ao + 4 <= A + Z.of_nat N)%Z ->
    xa1 = w (S + k) -> xa0 = w j -> xt1 = w i ->
    evt rsegs POST (MS (VR' x1 xa1 ao xt1 xt2 xs1 xa0 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a438) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until xt6. intros I CO Hi Hj Hk Hkj HA1 HA2 -> -> ->. pose proof BND as BD. unfold VR. unfold got_ssp, ssp_guard in *.
    destruct (str_read' m1 (k + j) (w (S + (k + j))) I ltac:(lia) eq_refl) as (b & RD & Rb & Hb).
    zs. zs. zs.
    destruct (out_store' m1 (ao - A + i) (w (ao + i)) (le1 xt2) I ltac:(lia) ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia) eq_refl) as [SOK I2].
    zs. st_name.
    zs. if_cases Ki; zify_cond Ki.
    -   zs. zs. if_cases Kd; zify_cond Kd.
      +   apply ip_exit'; [exact I2| left; reflexivity].
      + zs. zs. zs. if_cases Kl; zify_cond Kl. 2:{ exfalso. lia. }
        specialize (CO ltac:(lia)). unfold CONTv in CO. eapply (CO _ (k + j + 1)%Z); [exact I2 | lia | word_eq_tac | word_eq_tac].
    -   zs. zs. if_cases Kz; zify_cond Kz.
      + apply ip_exit'; [exact I2| right; reflexivity].
      + zs. zs. if_cases Kd; zify_cond Kd.
        * apply ip_exit'; [exact I2| left; reflexivity].
        * zs. zs. zs. if_cases Kl; zify_cond Kl. { exfalso. lia. }
          zs. apply ip_exit'; [exact I2| left; reflexivity].
  Qed.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC"] Lemma v4b_loop : forall (fuel : nat) m1 (ao k i : Z) x1 (xa1 xt1 xt2 xs1 xa0 : word) xs2 xs3 xs4 xs5 xt3 (xt4 : word) xt5 xt6,
    INV' m1 -> (Z.to_nat (3 - i) < fuel)%nat -> (0 <= i <= 3)%Z -> (0 <= k <= len)%Z ->
    (A <= ao)%Z -> (ao + 4 <= A + Z.of_nat N)%Z ->
    xa1 = w (S + k) -> xt4 = w i ->
    evt rsegs POST (MS (VR' x1 xa1 ao xt1 xt2 xs1 xa0 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a3e4) fc None m1 (seg_rom rsegs)).
  Proof.
    induction fuel as [|fuel IH]; [lia|].
    intros until xt6. intros I Hf Hi Hk HA1 HA2 -> ->. pose proof BND as BD. unfold VR. unfold got_ssp, ssp_guard in *.
    assert (CO : (i < 3 -> CONTv' 0x1a3e4 ao i)%Z).
    { intros Hi3. unfold CONTv. intros m2 k' x1' xa1' xt1' xt2' xs1' xa0' xs2' xs3' xs4' xs5' xt3' xt4' xt5' xt6' I' Hk' -> ->.
      eapply (IH m2 ao k' (i + 1)%Z); try reflexivity; try exact I'; lia. }
    destruct (str_read' m1 k (w (S + k)) I ltac:(lia) eq_refl) as (b0 & RD0 & R0 & Hb0).
    zs. zs. zs. if_cases K0; zify_cond K0.
    {   apply ip_ret0'. exact I. }
    assert (Hk0 : (k < len)%Z). { apply Hb0. intros E0. rewrite E0 in K0. revert K0. clear. intros K0. cbv in K0. lia. }
    zs. destruct (str_read' m1 (k + 1) (w (S + (k + 1))) I ltac:(lia) eq_refl) as (b1 & RD1 & R1 & Hb1).
    zs. zs. zs. zs. if_cases K1; zify_cond K1.
    {   eapply (v4b_tail m1 ao k i 1); [exact I | exact CO | lia | lia | lia | lia | lia | lia | word_eq_tac | word_eq_tac | word_eq_tac]. }
    assert (Hk1 : (k + 1 < len)%Z). { apply Hb1. intros E1. rewrite E1 in K1. revert K1. clear. intros K1. cbv in K1. lia. }
    destruct (str_read' m1 (k + 2) (w (S + (k + 2))) I ltac:(lia) eq_refl) as (b2 & RD2 & R2 & Hb2).
    zs. zs. zs. zs. zs. zs. if_cases K2; zify_cond K2; [ | zs; zs ].

    all: zs; zs; if_cases K3; [ apply ip_exit'; [exact I | left; reflexivity] | clear K3 ].
    all: zs; if_cases K4; [ apply ip_exit'; [exact I | left; reflexivity] | clear K4 ].
    all: zs; zs.
    -
      replace ((bv_unsigned b2 + -48) mod 18446744073709551616 <? 10)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      eapply (v4b_tail m1 ao k i 2); [exact I | exact CO | lia | lia | lia | lia | lia | lia | word_eq_tac | word_eq_tac | word_eq_tac].
    -
      pose proof (dig_mod _ R2 K2) as D2. assert (Hk2 : (k + 2 < len)%Z) by (apply Hb2; lia).
      replace (bv_unsigned b2 + -48 <? 10)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
      eapply (v4b_tail m1 ao k i 3); [exact I | exact CO | lia | lia | lia | lia | lia | lia | word_eq_tac | word_eq_tac | word_eq_tac].
  Qed.
End IP.
