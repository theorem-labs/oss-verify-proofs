(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype.
Import ListNotations.
Open Scope bv_scope.

Definition strncasecmp_entry := 0x2493c%Z.

Definition strncasecmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (ls rs : list byte) (v : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) ls /\ bytes_at rsegs m' (bv_unsigned a1) rs.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (v : Z) (lo : Z).
  Hypothesis LO : (lo <= bv_unsigned sp - 48)%Z.

  Hypothesis BND : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + Z.of_nat (length ls) <= 2^64 /\
                    0 <= bv_unsigned a1 /\ bv_unsigned a1 + Z.of_nat (length rs) <= 2^64 /\ 0 <= lo /\ bv_unsigned sp < 2^64)%Z.
  Hypothesis SEPL : (bv_unsigned a0 + Z.of_nat (length ls) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a0)%Z.
  Hypothesis SEPR : (bv_unsigned a1 + Z.of_nat (length rs) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a1)%Z.

  Notation A := (bv_unsigned a0).
  Notation B := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 48, bv_unsigned sp)]%Z.
  Notation POST := (strncasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v lo m).

  Notation ST pc m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x8 x18 x19 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

  Definition INV (m1 : word -> option byte) : Prop :=
    bytes_at rsegs m1 A ls /\ bytes_at rsegs m1 B rs /\ mem_inv rsegs m1 /\ munch W m m1 /\ wmono rsegs m m1
    /\ stk rsegs m1 lo (SP - 48)
    /\ exists junk, rw_cells rsegs m1 (SP + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  #[using="BND"] Lemma bounds : (0 <= A /\ A + Z.of_nat (length ls) <= 2^64 /\ 0 <= B /\ B + Z.of_nat (length rs) <= 2^64 /\ 0 <= lo /\ SP < 2^64)%Z.
  Proof. exact BND. Qed.

  Ltac pg := match goal with |- ?G => idtac G end.

  #[using="ls rs"] Lemma swrap32_id : forall x, (-2^31 <= x < 2^31)%Z -> bv_swrap 32 x = x.
  Proof. intros x Hx. rewrite bv_swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.
  Ltac open_inv H := destruct H as (LS & RS & MI & MU & WM & STK & [junk FR]).

  #[using="Type"] Lemma walk_at : forall i k r,
    strncasecmp_walk (skipn i ls) (skipn i rs) k = Some r ->
    exists a b, nth_error ls i = Some a /\ nth_error rs i = Some b /\
      (if ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0
           || negb ((bv_unsigned a =? bv_unsigned b) || (to_lower (bv_unsigned a) =? to_lower (bv_unsigned b))))%Z%bool
       then r = (to_lower (bv_unsigned a) - to_lower (bv_unsigned b))%Z
       else exists k', k = S k' /\ strncasecmp_walk (skipn (S i) ls) (skipn (S i) rs) k' = Some r).
  Proof.
    intros i k r H.
    destruct (skipn i ls) as [|a l'] eqn:EL; [cbn in H; discriminate|].
    destruct (skipn i rs) as [|b r'] eqn:ER; [cbn in H; destruct l'; discriminate|].
    apply skipn_cons_nth in EL. apply skipn_cons_nth in ER. destruct EL as [Hna ->]. destruct ER as [Hnb ->].
    exists a, b. split; [exact Hna|]. split; [exact Hnb|].
    cbn [strncasecmp_walk] in H.
    destruct ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0
              || negb ((bv_unsigned a =? bv_unsigned b) || (to_lower (bv_unsigned a) =? to_lower (bv_unsigned b))))%Z%bool eqn:E.
    - congruence.
    - destruct k as [|k']. { cbn [Nat.eqb] in E. rewrite !orb_true_r in E. cbn in E. congruence. } exists k'. auto.
  Qed.

  #[using="LO BND"] Lemma sc_ret : forall m1 (i : Z) (lv : Z) (b : byte) x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV m1 -> (0 <= i)%Z -> nth_error rs (Z.to_nat i) = Some b -> (0 <= lv < 256)%Z ->
    v = (to_lower lv - to_lower (bv_unsigned b))%Z ->
    evt rsegs POST (ST 0x249cc m1 x1 x5 x6 x7 x9 (Z_to_bv 64 lv) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (B + i)) x18 x19 x28 x29 x30 x31).
  Proof.
    intros m1 i lv b x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 I Hi Hnb Hlv Hv; open_inv I.
    pose proof bounds as BD. pose proof (nth_error_lt _ _ _ Hnb). pose proof (byte_range b).
    pose proof (to_lower_range lv Hlv). pose proof (to_lower_range (bv_unsigned b) ltac:(lia)).
    zstep. call tolower_spec. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact MI. }
    rewrite unsigned_lit by lia.
    pose proof (u8ro_read rsegs _ B rs i b _ RS Hnb ltac:(lia) eq_refl) as RD.
    zstep. zstep. zstep. zstep. call tolower_spec. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact MI. }
    rewrite unsigned_lit by lia.
    zstep. rewrite swrap32_id by lia. rewrite <- Hv.
    do 7 zstep. release_frame FR STK (bv_unsigned sp). finish.
  Qed.

  #[using="LO BND"] Lemma sc_fin : forall m1 (i : Z) (la b : byte) x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV m1 -> (0 <= i)%Z -> nth_error rs (Z.to_nat i) = Some b ->
    v = (to_lower (bv_unsigned la) - to_lower (bv_unsigned b))%Z ->
    evt rsegs POST (ST 0x249b8 m1 x1 x5 x6 x7 x9 x10 (Z_to_bv 64 (bv_unsigned la)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (B + i)) x18 x19 x28 x29 x30 x31).
  Proof.
    intros m1 i la b x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 I Hi Hnb Hv.
    pose proof (byte_range la).
    zstep. replace (Z.land (bv_unsigned la) 255) with (bv_unsigned la).
    2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask, Z.mod_small by lia. reflexivity. }
    zstep. eapply sc_ret; eauto.
  Qed.

  #[using="LO BND"] Lemma sc_loop : forall (k : nat) (i : Z) (li : byte) m1 x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    INV m1 -> (0 <= i)%Z -> nth_error ls (Z.to_nat i) = Some li -> bv_unsigned li <> 0%Z ->
    strncasecmp_walk (skipn (Z.to_nat i) ls) (skipn (Z.to_nat i) rs) k = Some v -> (Z.of_nat k < 2^64)%Z ->
    evt rsegs POST (ST 0x24984 m1 x1 x5 x6 x7 x9 x10 (Z_to_bv 64 (bv_unsigned li)) x12 x13 x14 x15 x16 x17
                       (Z_to_bv 64 (B + i)) (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 (Z.of_nat k)) x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros i li m1 x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 I Hi Hli Hnz HW Hk;
      pose proof bounds as BD; pose proof (nth_error_lt _ _ _ Hli); pose proof (byte_range li);
      destruct (walk_at _ _ _ HW) as (a & b & Hna & Hnb & HC); rewrite Hli in Hna; injection Hna as <-;
      pose proof (nth_error_lt _ _ _ Hnb); pose proof (byte_range b);
      pose proof I as I'; open_inv I';
      pose proof (u8ro_read rsegs m1 B rs i b _ RS Hnb ltac:(lia) eq_refl) as RD.
    -
      zstep. zstep. if_cases Kb0; zify_cond Kb0.
      { apply (sc_fin m1 i li b); try assumption. rewrite (proj2 (Z.eqb_eq _ _) Kb0) in HC. cbn [orb] in HC.
        rewrite ?orb_true_r in HC. cbn in HC. exact HC. }
      zstep. zstep. if_cases K0; zify_cond K0. 2:{ exfalso. cbn in K0. lia. }
      apply (sc_fin m1 i li b); try assumption. cbn [Nat.eqb] in HC. rewrite !orb_true_r in HC. cbn in HC. exact HC.
    -
      assert (ADV : forall m2 x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31',
        INV m2 ->
        (exists k', S k = S k' /\ strncasecmp_walk (skipn (S (Z.to_nat i)) ls) (skipn (S (Z.to_nat i)) rs) k' = Some v) ->
        evt rsegs POST (ST 0x24970 m2 x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17'
                           (Z_to_bv 64 (B + i)) (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 (Z.of_nat (S k))) x28' x29' x30' x31')).
      { intros m2 x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' I2 (k' & Ek & HW').
        injection Ek as <-. clear LS RS MI MU WM STK FR junk RD. pose proof I2 as I2'; open_inv I2'.
        destruct (walk_at _ _ _ HW') as (a' & b' & Hna' & Hnb' & HC2).
        pose proof (nth_error_lt _ _ _ Hna'). pose proof (byte_range a'). pose proof (nth_error_lt _ _ _ Hnb').
        pose proof (u8ro_read rsegs m2 A ls (i + 1) a' (Z_to_bv 64 (A + i + 1)) LS ltac:(replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; exact Hna') ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDa.
        zstep. zstep. zstep. zstep. zstep. if_cases Kz; zify_cond Kz.
        -
          replace (B + i + 1)%Z with (B + (i + 1))%Z by lia.
          apply (sc_fin m2 (i + 1) a' b'); try assumption; try lia.
          { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact Hnb'. }
          rewrite (proj2 (Z.eqb_eq _ _) Kz) in HC2. cbn [orb] in HC2. exact HC2.
        - replace (B + i + 1)%Z with (B + (i + 1))%Z by lia. replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia.
          replace (Z.of_nat (S k) + -1)%Z with (Z.of_nat k) by lia.
          apply (IH (i + 1)%Z a'); try assumption; try lia.
          all: replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; assumption. }
      zstep. zstep. if_cases Kb0; zify_cond Kb0.
      { apply (sc_fin m1 i li b); try assumption. rewrite (proj2 (Z.eqb_eq _ _) Kb0) in HC. cbn [orb] in HC.
        rewrite ?orb_true_r in HC. cbn in HC. exact HC. }
      zstep. zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
      zstep. if_cases Keq; zify_cond Keq.
      +
        apply ADV. { exact I. }
        rewrite (proj2 (Z.eqb_neq _ _) Hnz), (proj2 (Z.eqb_neq _ _) Kb0), (proj2 (Z.eqb_eq _ _) Keq) in HC. cbn in HC. exact HC.
      + pose proof (to_lower_range (bv_unsigned li) ltac:(lia)). pose proof (to_lower_range (bv_unsigned b) ltac:(lia)).
        zstep. replace (Z.land (bv_unsigned li) 255) with (bv_unsigned li).
        2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask, Z.mod_small by lia. reflexivity. }
        zstep. call tolower_spec. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact MI. }
        rewrite unsigned_lit by lia.
        pose proof (u8ro_read rsegs _ B rs i b _ RS Hnb ltac:(lia) eq_refl) as RD2.
        zstep. zstep. zstep. zstep. call tolower_spec. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact MI. }
        rewrite unsigned_lit by lia.
        zstep. if_cases Ktl; zify_cond Ktl.
        *
          apply ADV. { exact I. }
          rewrite (proj2 (Z.eqb_neq _ _) Hnz), (proj2 (Z.eqb_neq _ _) Kb0), (proj2 (Z.eqb_eq _ _) Ktl) in HC.
          rewrite orb_true_r in HC. cbn in HC. exact HC.
        * pose proof (u8ro_read rsegs _ A ls i li (Z_to_bv 64 (A + i + 1 + -1)) LS Hli ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD3.
          zstep. cbv beta. apply (sc_fin _ i li b); try assumption.
          rewrite (proj2 (Z.eqb_neq _ _) Hnz), (proj2 (Z.eqb_neq _ _) Kb0), (proj2 (Z.eqb_neq _ _) Keq), (proj2 (Z.eqb_neq _ _) Ktl) in HC.
          cbn in HC. exact HC.
  Qed.

  Ltac reg_eq := first [ reflexivity | f_equal; lia | etransitivity; [symmetry; apply Z_to_bv_bv_unsigned|]; f_equal; lia ].

  #[using="LO BND"] Lemma sc_ret' : forall m1 (i : Z) (lv : Z) (b : byte) x1 x5 x6 x7 x9 xa0 x11 x12 x13 x14 x15 x16 x17 xs0 x18 x19 x28 x29 x30 x31,
    INV m1 -> (0 <= i)%Z -> nth_error rs (Z.to_nat i) = Some b -> (0 <= lv < 256)%Z ->
    v = (to_lower lv - to_lower (bv_unsigned b))%Z ->
    xa0 = Z_to_bv 64 lv -> xs0 = Z_to_bv 64 (B + i) ->
    evt rsegs POST (ST 0x249cc m1 x1 x5 x6 x7 x9 xa0 x11 x12 x13 x14 x15 x16 x17 xs0 x18 x19 x28 x29 x30 x31).
  Proof. intros; subst xa0 xs0; eapply sc_ret; eauto. Qed.

  #[using="LO BND"] Lemma sc_loop' : forall (k : nat) (i : Z) (li : byte) m1 x1 x5 x6 x7 x9 x10 xa1 x12 x13 x14 x15 x16 x17 xs0 xs2 xs3 x28 x29 x30 x31,
    INV m1 -> (0 <= i)%Z -> nth_error ls (Z.to_nat i) = Some li -> bv_unsigned li <> 0%Z ->
    strncasecmp_walk (skipn (Z.to_nat i) ls) (skipn (Z.to_nat i) rs) k = Some v -> (Z.of_nat k < 2^64)%Z ->
    xa1 = Z_to_bv 64 (bv_unsigned li) -> xs0 = Z_to_bv 64 (B + i) -> xs2 = Z_to_bv 64 (A + i + 1) -> xs3 = Z_to_bv 64 (Z.of_nat k) ->
    evt rsegs POST (ST 0x24984 m1 x1 x5 x6 x7 x9 x10 xa1 x12 x13 x14 x15 x16 x17 xs0 xs2 xs3 x28 x29 x30 x31).
  Proof. intros; subst xa1 xs0 xs2 xs3; eapply sc_loop; eauto. Qed.

  #[using="LO BND SEPL SEPR"] Lemma sc_body :
    mem_inv rsegs m -> bytes_at rsegs m A ls -> bytes_at rsegs m B rs -> stk rsegs m lo SP ->
    strncasecmp_model ls rs n = Some v ->
    evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x2493c) fc None m (seg_rom rsegs)).
  Proof.
    intros MI LS RS STK HM; pose proof bounds as BD. unfold strncasecmp_model in HM.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K0; zify_cond K0.
    - rewrite K0 in HM. cbn in HM. injection HM as <-. zstep. zstep. finish.
    - rewrite (proj2 (Z.eqb_neq _ _) K0) in HM.
      rewrite <- (skipn_O ls), <- (skipn_O rs) in HM.
      destruct (walk_at _ _ _ HM) as (a & b & Hna & Hnb & HC).
      pose proof (nth_error_lt _ _ _ Hna). pose proof (nth_error_lt _ _ _ Hnb). pose proof (byte_range a). pose proof (byte_range b).
      carve_frame 48%nat STK.
      do 7 zstep.
      pose proof (u8ro_read rsegs _ A ls 0 a a0 LS Hna ltac:(lia) (eq_sym (Z_to_bv_plus0 a0))) as RD.
      zstep. zstep.
      assert (I : INV m0). { split; [exact LS|]. split; [exact RS|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|].
                             split; [exact STK|]. eexists. exact FR. }
      if_cases Ka; zify_cond Ka.
      +   zstep.
        eapply (sc_ret' _ 0 0 b); try lia; try reg_eq. { exact I. } { exact Hnb. }
        rewrite Ka in HC. cbn [Z.eqb orb] in HC. exact HC.
      + zstep. zstep. zstep.
        eapply (sc_loop' (Z.to_nat (n - 1)) 0 a); try lia; try reg_eq. { exact I. } { exact Hna. } exact HC || exact HM.
  Qed.
End Proofs.

Lemma strncasecmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v : Z),
  bytes_at rsegs m (bv_unsigned a0) ls ->
  bytes_at rsegs m (bv_unsigned a1) rs ->
  strncasecmp_model ls rs (bv_unsigned a2) = Some v ->
  stk rsegs m (bv_unsigned sp - 48) (bv_unsigned sp) -> (64 <= bv_unsigned sp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length ls) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + Z.of_nat (length rs) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  mem_inv rsegs m ->
  evt rsegs (strncasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v (bv_unsigned sp - 48) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2493c) fc None m (seg_rom rsegs)).
Proof.
  intros until v. intros LS RS HM ST SP64 SEPL SEPR MI.
  apply sc_body; try assumption; try lia.
  pose proof (bytes_at_bound _ _ _ _ LS). pose proof (bytes_at_bound _ _ _ _ RS).
  pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R; cbn in R. lia.
Qed.

Lemma strncasecmp_spec_lo : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
  bytes_at rsegs m (bv_unsigned a0) ls ->
  bytes_at rsegs m (bv_unsigned a1) rs ->
  strncasecmp_model ls rs (bv_unsigned a2) = Some v ->
  stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned a0 + Z.of_nat (length ls) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + Z.of_nat (length rs) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  mem_inv rsegs m ->
  evt rsegs (strncasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2493c) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros LS RS HM ST LO SEPL SEPR MI.
  apply sc_body; try assumption; try lia.
  pose proof (bytes_at_bound _ _ _ _ LS). pose proof (bytes_at_bound _ _ _ _ RS). destruct ST as [? _].
  pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R; cbn in R. lia.
Qed.
