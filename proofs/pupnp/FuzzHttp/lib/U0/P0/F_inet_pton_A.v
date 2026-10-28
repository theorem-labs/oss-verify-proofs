(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls.
Import ListNotations.
Open Scope bv_scope.
Local Ltac flia ::= flia_cheap.

Definition inet_pton_entry := 0x1a008%Z.
Notation w z := (Z_to_bv 64 z) (only parsing).
Ltac zs := zstep; fix_lit_store.

Definition inet_pton_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (A : Z) (N : nat) (canary : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (outs : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (w r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + Z.of_nat N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' S (str ++ [Z_to_bv 8 0])
    /\ rw_cells rsegs m' got_ssp [C8 (w ssp_guard)]
    /\ rw_cells rsegs m' ssp_guard [C8 canary]
    /\ u8arr rsegs m' A outs /\ length outs = N
    /\ (r = 0 \/ r = 1)%Z.

Lemma dig_mod : forall b, (0 <= b < 256)%Z -> ((b + -48) mod 18446744073709551616 < 10)%Z -> (48 <= b < 58)%Z.
Proof. intros b Hb H. Z.div_mod_to_equations. lia. Qed.

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

  Definition FRC : list cell := [C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition INV (m1 : word -> option byte) : Prop :=
    bytes_at rsegs m1 S full /\ mem_inv rsegs m1 /\ munch W m m1 /\ wmono rsegs m m1
    /\ stk rsegs m1 lo (SP - 80)
    /\ rw_cells rsegs m1 got_ssp [C8 (w ssp_guard)] /\ rw_cells rsegs m1 ssp_guard [C8 canary]
    /\ rw_cells rsegs m1 (SP + -64) FRC
    /\ (exists ips, u8arr rsegs m1 (SP + -80) ips /\ length ips = 16%nat)
    /\ (exists outs, u8arr rsegs m1 A outs /\ length outs = N).
  Ltac open_inv I := destruct I as (STR & MI & MU & WM & STK & GOT & GUARD & FR & (ips & IPS & LIP) & (outs & OUT & LOUT)); unfold FRC in FR.

  #[using="N"] Lemma full_length : length full = (length str + 1)%nat.
  Proof. rewrite length_app. cbn. lia. Qed.

  #[using="SEPS SEPA SEPAS SEPG SEPC"] Lemma str_read : forall m1 p a, INV m1 -> (0 <= p <= len)%Z -> a = w (S + p) ->
    exists b, ov_read_bytes rsegs m1 a 1 = Some [b] /\ (0 <= bv_unsigned b < 256)%Z /\ (bv_unsigned b <> 0%Z -> p < len)%Z.
  Proof.
    intros m1 p a I Hp Ha; open_inv I.
    destruct (nth_error full (Z.to_nat p)) as [b|] eqn:E.
    2:{ apply nth_error_None in E. rewrite full_length in E. lia. }
    exists b. split. { eapply u8ro_read; eauto. lia. }
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. split; [cbn; lia|].
    intros NZ. destruct (Z.eq_dec p len) as [->|]; [|lia]. exfalso. apply NZ.
    rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag in E by lia. cbn in E. injection E as <-. reflexivity.
  Qed.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC"] Lemma out_store : forall m1 (o : Z) a (bs : list byte), INV m1 -> (0 <= o)%Z -> (o + 1 <= Z.of_nat N)%Z -> a = wa (A + o) -> length bs = 1%nat ->
    store_ok rsegs m1 a 1 = true /\ INV (write_to_mem m1 a bs).
  Proof.
    intros m1 o a bs I Ho HoN Ha Hl; pose proof I as I'; open_inv I. pose proof BND as BD.
    assert (SOK : store_ok rsegs m1 a 1 = true).
    { eapply (u8arr_store_ok_n rsegs m1 A outs o 1 a OUT); [lia| rewrite LOUT; cbn; lia | exact Ha]. }
    split; [exact SOK|]. subst a.
    split. { apply bytes_at_write_other; [exact STR|lia|rewrite Hl; lia|]. rewrite full_length, Hl. lia. }
    split. { apply mem_inv_store; [exact MI|]. rewrite Hl. exact SOK. }
    split. { apply munch_write; [exact MU|lia|rewrite Hl; lia|]. rewrite Hl. cbn [inside]. right. left. lia. }
    split. { apply wmono_write. exact WM. }
    split. { apply stk_write; [exact STK|lia|rewrite Hl; lia]. }
    split. { apply rw_cells_frame; [exact GOT|lia|rewrite Hl; lia|]. cbn [cells_size csize Nat.add]. rewrite Hl. unfold got_ssp in *. lia. }
    split. { apply rw_cells_frame; [exact GUARD|lia|rewrite Hl; lia|]. cbn [cells_size csize Nat.add]. rewrite Hl. unfold ssp_guard in *. lia. }
    split. { apply rw_cells_frame; [exact FR|lia|rewrite Hl; lia|]. cbn [cells_size csize Nat.add FRC]. rewrite Hl. lia. }
    split. { exists ips. split; [|exact LIP]. apply u8arr_frame; [exact IPS|lia|rewrite Hl; lia|]. rewrite LIP, Hl. lia. }
    exists (upd_bytes outs (Z.to_nat o) bs). split.
    - apply (u8arr_write_bytes rsegs m1 A outs o bs OUT); [lia|]. rewrite LOUT, Hl. lia.
    - rewrite upd_bytes_length; [exact LOUT|]. rewrite Hl, LOUT. lia.
  Qed.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC"] Lemma ip_store : forall m1 (o : Z) a (bs : list byte), INV m1 -> (0 <= o)%Z -> (o + 2 <= 16)%Z -> a = wa (SP + -80 + o) -> length bs = 2%nat ->
    store_ok rsegs m1 a 2 = true /\ INV (write_to_mem m1 a bs).
  Proof.
    intros m1 o a bs I Ho HoN Ha Hl; pose proof I as I'; open_inv I. pose proof BND as BD.
    assert (SOK : store_ok rsegs m1 a 2 = true).
    { eapply (u8arr_store_ok_n rsegs m1 (SP + -80) ips o 2 a IPS); [lia| rewrite LIP; cbn; lia | exact Ha]. }
    split; [exact SOK|]. subst a.
    split. { apply bytes_at_write_other; [exact STR|lia|rewrite Hl; lia|]. rewrite full_length, Hl. lia. }
    split. { apply mem_inv_store; [exact MI|]. rewrite Hl. exact SOK. }
    split. { apply munch_write; [exact MU|lia|rewrite Hl; lia|]. rewrite Hl. cbn [inside]. left. lia. }
    split. { apply wmono_write. exact WM. }
    split. { apply stk_write; [exact STK|lia|rewrite Hl; lia]. }
    split. { apply rw_cells_frame; [exact GOT|lia|rewrite Hl; lia|]. cbn [cells_size csize Nat.add]. rewrite Hl. unfold got_ssp in *. lia. }
    split. { apply rw_cells_frame; [exact GUARD|lia|rewrite Hl; lia|]. cbn [cells_size csize Nat.add]. rewrite Hl. unfold ssp_guard in *. lia. }
    split. { apply rw_cells_frame; [exact FR|lia|rewrite Hl; lia|]. cbn [cells_size csize Nat.add FRC]. rewrite Hl. lia. }
    split.
    - exists (upd_bytes ips (Z.to_nat o) bs). split.
      + apply (u8arr_write_bytes rsegs m1 (SP + -80) ips o bs IPS); [lia|]. rewrite LIP, Hl. lia.
      + rewrite upd_bytes_length; [exact LIP|]. rewrite Hl, LIP. lia.
    - exists outs. split; [|exact LOUT]. apply u8arr_frame; [exact OUT|lia|rewrite Hl; lia|]. rewrite LOUT, Hl. lia.
  Qed.

  Ltac st_name :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs0) _) =>
      repeat match goal with
      | H : store_ok _ m1 _ _ = true |- _ => clear H
      | H : ov_read_bytes _ m1 _ _ = Some _ |- _ => clear H
      | H : INV m1 |- _ => clear H
      end;
      let m' := fresh "m" in remember (write_to_mem m1 a bs0) as m' eqn:E; clear E; try clear m1
    end.

  #[using="LO BND"] Lemma ip_exit : forall m1 (r : Z) x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV m1 -> (r = 0 \/ r = 1)%Z ->
    evt rsegs POST (MS (mkR x1 (w (SP + -80)) gp tp x5 x6 x7 (w ssp_guard) x9 (w r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (w 0x1a394) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros I Hr; open_inv I. pose proof BND as BD. unfold got_ssp, ssp_guard in *.
    do 3 zs. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
    do 9 zs.
    pose proof (rw_cells_of_u8arr rsegs _ _ _ IPS) as IPC. rewrite LIP in IPC.
    release_frame IPC STK (bv_unsigned sp - 64)%Z. release_frame FR STK (bv_unsigned sp).
    finish. all: first [exact OUT | exact LOUT | exact Hr].
  Qed.

  #[using="LO BND"] Lemma ip_ret0 : forall m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV m1 ->
    evt rsegs POST (MS (mkR x1 (w (SP + -80)) gp tp x5 x6 x7 (w ssp_guard) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (w 0x1a390) fc None m1 (seg_rom rsegs)).
  Proof. intros until x31. intros I. zs. apply ip_exit; [exact I| left; reflexivity]. Qed.

  Definition VR (x1 : word) (xa1 : word) (ao : Z) (xt1 xt2 xs1 xa0 : word) (xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6 : word) :=
    mkR x1 (w (SP + -80)) gp tp (w 46) xt1 xt2 (w ssp_guard) xs1 xa0 xa1 (w ao) (w 9) (w 10) (w 48) (w 255) (w 3)
        xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6.

  Definition CONTv (hd : Z) (ao i : Z) : Prop :=
    forall m2 k x1 (xa1 : word) xt1 xt2 xs1 xa0 xs2 xs3 xs4 xs5 xt3 (xt4 : word) xt5 xt6,
      INV m2 -> (0 <= k <= len)%Z -> xa1 = w (S + k) -> xt4 = w (i + 1) ->
      evt rsegs POST (MS (VR x1 xa1 ao xt1 xt2 xs1 xa0 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w hd) fc None m2 (seg_rom rsegs)).

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC"] Lemma v4a_tail : forall m1 (ao k i j : Z) x1 (xa1 xt1 xt2 xs1 xa0 : word) xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6,
    INV m1 -> (i < 3 -> CONTv 0x1a064 ao i)%Z -> (0 <= i <= 3)%Z -> (1 <= j <= 3)%Z -> (0 <= k)%Z -> (k + j <= len)%Z ->
    (A <= ao)%Z -> (ao + 4 <= A + Z.of_nat N)%Z ->
    xa1 = w (S + k) -> xa0 = w j -> xt1 = w i ->
    evt rsegs POST (MS (VR x1 xa1 ao xt1 xt2 xs1 xa0 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a0b8) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until xt6. intros I CO Hi Hj Hk Hkj HA1 HA2 -> -> ->. pose proof BND as BD. unfold VR. unfold got_ssp, ssp_guard in *.
    destruct (str_read m1 (k + j) (w (S + (k + j))) I ltac:(lia) eq_refl) as (b & RD & Rb & Hb).
    zs. zs. zs.
    destruct (out_store m1 (ao - A + i) (w (ao + i)) (le1 xt2) I ltac:(lia) ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia) eq_refl) as [SOK I2].
    zs. st_name.
    zs. if_cases Ki; zify_cond Ki.
    -   zs. zs. if_cases Kd; zify_cond Kd.
      +   apply ip_exit; [exact I2| left; reflexivity].
      + zs. zs. zs. if_cases Kl; zify_cond Kl. 2:{ exfalso. lia. }
        specialize (CO ltac:(lia)). unfold CONTv in CO. eapply (CO _ (k + j + 1)%Z); [exact I2 | lia | word_eq_tac | word_eq_tac].
    -   zs. zs. if_cases Kz; zify_cond Kz.
      + apply ip_exit; [exact I2| right; reflexivity].
      + zs. zs. if_cases Kd; zify_cond Kd.
        * apply ip_exit; [exact I2| left; reflexivity].
        * zs. zs. zs. if_cases Kl; zify_cond Kl. { exfalso. lia. }
          zs. apply ip_exit; [exact I2| left; reflexivity].
  Qed.

  #[using="LO BND SEPS SEPA SEPAS SEPG SEPC SEPAG SEPAC"] Lemma v4a_loop : forall (fuel : nat) m1 (ao k i : Z) x1 (xa1 xt1 xt2 xs1 xa0 : word) xs2 xs3 xs4 xs5 xt3 (xt4 : word) xt5 xt6,
    INV m1 -> (Z.to_nat (3 - i) < fuel)%nat -> (0 <= i <= 3)%Z -> (0 <= k <= len)%Z ->
    (A <= ao)%Z -> (ao + 4 <= A + Z.of_nat N)%Z ->
    xa1 = w (S + k) -> xt4 = w i ->
    evt rsegs POST (MS (VR x1 xa1 ao xt1 xt2 xs1 xa0 xs2 xs3 xs4 xs5 xt3 xt4 xt5 xt6) F (w 0x1a064) fc None m1 (seg_rom rsegs)).
  Proof.
    induction fuel as [|fuel IH]; [lia|].
    intros until xt6. intros I Hf Hi Hk HA1 HA2 -> ->. pose proof BND as BD. unfold VR. unfold got_ssp, ssp_guard in *.
    assert (CO : (i < 3 -> CONTv 0x1a064 ao i)%Z).
    { intros Hi3. unfold CONTv. intros m2 k' x1' xa1' xt1' xt2' xs1' xa0' xs2' xs3' xs4' xs5' xt3' xt4' xt5' xt6' I' Hk' -> ->.
      eapply (IH m2 ao k' (i + 1)%Z); try reflexivity; try exact I'; lia. }
    destruct (str_read m1 k (w (S + k)) I ltac:(lia) eq_refl) as (b0 & RD0 & R0 & Hb0).
    zs. zs. zs. if_cases K0; zify_cond K0.
    {   apply ip_ret0. exact I. }
    assert (Hk0 : (k < len)%Z). { apply Hb0. intros E0. rewrite E0 in K0. revert K0. clear. intros K0. cbv in K0. lia. }
    zs. destruct (str_read m1 (k + 1) (w (S + (k + 1))) I ltac:(lia) eq_refl) as (b1 & RD1 & R1 & Hb1).
    zs. zs. zs. zs. if_cases K1; zify_cond K1.
    {   eapply (v4a_tail m1 ao k i 1); [exact I | exact CO | lia | lia | lia | lia | lia | lia | word_eq_tac | word_eq_tac | word_eq_tac]. }
    assert (Hk1 : (k + 1 < len)%Z). { apply Hb1. intros E1. rewrite E1 in K1. revert K1. clear. intros K1. cbv in K1. lia. }
    destruct (str_read m1 (k + 2) (w (S + (k + 2))) I ltac:(lia) eq_refl) as (b2 & RD2 & R2 & Hb2).
    zs. zs. zs. zs. zs. zs. if_cases K2; zify_cond K2; [ | zs; zs ].

    all: zs; zs; if_cases K3; [ apply ip_exit; [exact I | left; reflexivity] | clear K3 ].
    all: zs; if_cases K4; [ apply ip_exit; [exact I | left; reflexivity] | clear K4 ].
    all: zs; zs.
    -
      replace ((bv_unsigned b2 + -48) mod 18446744073709551616 <? 10)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      eapply (v4a_tail m1 ao k i 2); [exact I | exact CO | lia | lia | lia | lia | lia | lia | word_eq_tac | word_eq_tac | word_eq_tac].
    -
      pose proof (dig_mod _ R2 K2) as D2. assert (Hk2 : (k + 2 < len)%Z) by (apply Hb2; lia).
      replace (bv_unsigned b2 + -48 <? 10)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
      eapply (v4a_tail m1 ao k i 3); [exact I | exact CO | lia | lia | lia | lia | lia | lia | word_eq_tac | word_eq_tac | word_eq_tac].
  Qed.
End IP.
