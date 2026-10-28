(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition strncmp_entry := 0x2bba24%Z.

(* [comment removed for export] *)
Definition strncmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (ls rs : list byte) (v : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ bytes_at usegs m' (bv_unsigned a0) ls /\ bytes_at usegs m' (bv_unsigned a1) rs.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (v : Z).
  Hypothesis MI : mem_inv usegs m.
  Hypothesis LS : bytes_at usegs m (bv_unsigned a0) ls.
  Hypothesis RS : bytes_at usegs m (bv_unsigned a1) rs.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono usegs m m := wmono_refl usegs m.

  Notation A := (bv_unsigned a0).
  Notation B := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Notation POST := (strncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m).
  (* [comment removed for export] *)
  Notation ST pc x10 x11 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Lemma bounds : (0 <= A /\ A + Z.of_nat (length ls) <= 2^64 /\ 0 <= B /\ B + Z.of_nat (length rs) <= 2^64)%Z.
  Proof. pose proof (bytes_at_bound _ _ _ _ LS). pose proof (bytes_at_bound _ _ _ _ RS). lia. Qed.

  Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
  Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

  (* [comment removed for export] *)
  Lemma walk_at : forall i k r,
    strncmp_walk (skipn i ls) (skipn i rs) k = Some r ->
    exists a b, nth_error ls i = Some a /\ nth_error rs i = Some b /\
      (if ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0 || negb (bv_unsigned a =? bv_unsigned b))%Z%bool
       then r = (bv_unsigned a - bv_unsigned b)%Z
       else exists k', k = S k' /\ strncmp_walk (skipn (S i) ls) (skipn (S i) rs) k' = Some r).
  Proof.
    intros i k r H.
    destruct (skipn i ls) as [|a l'] eqn:EL; [cbn in H; discriminate|].
    destruct (skipn i rs) as [|b r'] eqn:ER; [cbn in H; discriminate|].
    apply skipn_cons_nth in EL. apply skipn_cons_nth in ER. destruct EL as [Hna ->]. destruct ER as [Hnb ->].
    exists a, b. split; [exact Hna|]. split; [exact Hnb|].
    cbn [strncmp_walk] in H.
    destruct ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0 || negb (bv_unsigned a =? bv_unsigned b))%Z%bool eqn:E.
    - congruence.
    - destruct k as [|k']. { cbn [Nat.eqb] in E. rewrite !orb_true_r in E. cbn in E. congruence. } exists k'. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma strncmp_ret : forall (i : Z) (a b : byte) x10 x12 x14,
    (0 <= i)%Z -> nth_error rs (Z.to_nat i) = Some b -> v = (bv_unsigned a - bv_unsigned b)%Z ->
    evt usegs POST (ST 0x2bba60 x10 (Z_to_bv 64 (B + i)) x12 (Z_to_bv 64 (bv_unsigned a)) x14).
  Proof.
    intros i a b x10 x12 x14 Hi Hnb Hv; pose proof bounds as BD. pose proof (nth_error_lt _ _ _ Hnb).
    pose proof (byte_range a). pose proof (byte_range b).
    pose proof (u8ro_read usegs m B rs i b _ RS Hnb ltac:(lia) eq_refl) as RD.
    zstep. replace (Z.land (bv_unsigned a) 255) with (bv_unsigned a).
    2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask, Z.mod_small by lia. reflexivity. }
    zstep. zstep. zstep. subst v. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma strncmp_loop : forall (k : nat) (i : Z) (li : byte) x14,
    (0 <= i)%Z -> nth_error ls (Z.to_nat i) = Some li -> bv_unsigned li <> 0%Z ->
    strncmp_walk (skipn (Z.to_nat i) ls) (skipn (Z.to_nat i) rs) k = Some v -> (Z.of_nat k < 2^64)%Z ->
    evt usegs POST (ST 0x2bba38 (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (bv_unsigned li)) x14).
  Proof.
    induction k as [|k IH]; intros i li x14 Hi Hli Hnz HW Hk; pose proof bounds as BD; pose proof (nth_error_lt _ _ _ Hli);
      pose proof (byte_range li);
      destruct (walk_at _ _ _ HW) as (a & b & Hna & Hnb & HC); rewrite Hli in Hna; injection Hna as <-;
      pose proof (nth_error_lt _ _ _ Hnb); pose proof (byte_range b);
      pose proof (u8ro_read usegs m B rs i b _ RS Hnb ltac:(lia) eq_refl) as RD.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases Kne; zify_cond Kne.
      + apply (strncmp_ret i li b); try lia; try assumption.
        replace (negb (bv_unsigned li =? bv_unsigned b))%Z with true in HC by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Kne).
        rewrite !orb_true_r in HC. exact HC.
      + zstep. if_cases Kb0; zify_cond Kb0. { exfalso. lia. }
        zstep. zstep. if_cases K0; zify_cond K0. 2:{ exfalso. cbn in K0. lia. }
        apply (strncmp_ret i li b); try lia; try assumption.
        cbn [Nat.eqb] in HC. rewrite !orb_true_r in HC. cbn in HC. exact HC.
    - zstep. zstep. if_cases Kne; zify_cond Kne.
      + apply (strncmp_ret i li b); try lia; try assumption.
        replace (negb (bv_unsigned li =? bv_unsigned b))%Z with true in HC by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Kne).
        rewrite !orb_true_r in HC. exact HC.
      + zstep. if_cases Kb0; zify_cond Kb0. { exfalso. lia. }
        zstep. zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
        (* [comment removed for export] *)
        replace ((bv_unsigned li =? 0) || (bv_unsigned b =? 0) || Nat.eqb (S k) 0 || negb (bv_unsigned li =? bv_unsigned b))%Z%bool
          with false in HC.
        2:{ symmetry. rewrite (proj2 (Z.eqb_neq _ _) Hnz), (proj2 (Z.eqb_neq _ _) Kb0). cbn [orb Nat.eqb].
            rewrite (proj2 (Z.eqb_eq _ _) Kne). reflexivity. }
        destruct HC as (k' & Ek & HW'). injection Ek as <-.
        destruct (walk_at _ _ _ HW') as (a' & b' & Hna' & Hnb' & _).
        pose proof (nth_error_lt _ _ _ Hna'). pose proof (byte_range a').
        pose proof (u8ro_read usegs m A ls (i + 1) a' (Z_to_bv 64 (A + i + 1)) LS ltac:(replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; exact Hna') ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD2.
        zstep. zstep. zstep. zstep. zstep. if_cases Kz; zify_cond Kz.
        * replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia. replace (B + i + 1)%Z with (B + (i + 1))%Z by lia.
          replace (Z.of_nat (S k) + -1)%Z with (Z.of_nat k) by lia.
          apply (IH (i + 1)%Z a'); try lia; try assumption.
          all: replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; assumption.
        * replace (B + i + 1)%Z with (B + (i + 1))%Z by lia.
          destruct (walk_at _ _ _ HW') as (a2' & b2 & Hna2 & Hnb2 & HC2). rewrite Hna' in Hna2. injection Hna2 as <-.
          apply (strncmp_ret (i + 1) a' b2); try lia.
          { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact Hnb2. }
          rewrite (proj2 (Z.eqb_eq _ _) Kz) in HC2. cbn [orb] in HC2. exact HC2.
  Qed.

  Lemma strncmp_body :
    strncmp_model ls rs n = Some v ->
    evt usegs POST (ST 0x2bba24 a0 a1 a2 a3 a4).
  Proof.
    intros HM; pose proof bounds as BD. unfold strncmp_model in HM.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
    zstep. if_cases K0; zify_cond K0.
    - rewrite K0 in HM. cbn in HM. injection HM as <-. zstep. zstep. finish.
    - rewrite (proj2 (Z.eqb_neq _ _) K0) in HM.
      rewrite <- (skipn_O ls), <- (skipn_O rs) in HM.
      destruct (walk_at _ _ _ HM) as (a & b & Hna & Hnb & HC).
      pose proof (nth_error_lt _ _ _ Hna). pose proof (nth_error_lt _ _ _ Hnb). pose proof (byte_range a). pose proof (byte_range b).
      pose proof (u8ro_read usegs m A ls 0 a a0 LS Hna ltac:(lia) (eq_sym (Z_to_bv_plus0 a0))) as RD.
      zstep. zstep. if_cases Ka; zify_cond Ka.
      + (* [comment removed for export] *)
        pose proof (u8ro_read usegs m B rs 0 b a1 RS Hnb ltac:(lia) (eq_sym (Z_to_bv_plus0 a1))) as RD2.
        zstep. zstep. zstep.
        rewrite Ka in HC. cbn [Z.eqb orb] in HC. subst v.
        replace (0 - bv_unsigned b)%Z with (bv_unsigned a - bv_unsigned b)%Z by lia. finish.
      + zstep. zstep.
        eapply evt_eq.
        2:{ apply (strncmp_loop (Z.to_nat (n - 1)) 0 a a4); try lia; try assumption. }
        unfold mkR. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. repeat f_equal; lia.
  Qed.
End Proofs.

Lemma strncmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v : Z),
  bytes_at usegs m (bv_unsigned a0) ls ->
  bytes_at usegs m (bv_unsigned a1) rs ->
  strncmp_model ls rs (bv_unsigned a2) = Some v ->
  mem_inv usegs m ->
  evt usegs (strncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2bba24) fc None m (seg_rom usegs)).
Proof. intros until v. intros LS RS HM MI. apply strncmp_body; assumption. Qed.
