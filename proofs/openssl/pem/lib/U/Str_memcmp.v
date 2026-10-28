(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Fixpoint memcmp_walk (l r : list byte) (k : nat) {struct k} : option Z :=
  match k with
  | O => Some 0%Z
  | S k' => match l, r with
            | a :: l', b :: r' => if (bv_unsigned a =? bv_unsigned b)%Z then memcmp_walk l' r' k' else Some (bv_unsigned a - bv_unsigned b)%Z
            | _, _ => None
            end
  end.

Definition memcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (v : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1' a2' a3' a4',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (v : Z).
  Hypothesis MI : mem_inv usegs m.
  Hypothesis LS : bytes_at usegs m (bv_unsigned a0) ls.
  Hypothesis RS : bytes_at usegs m (bv_unsigned a1) rs.

  Notation A := (bv_unsigned a0).
  Notation B := (bv_unsigned a1).
  Notation POST := (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 F fc v m).
  Notation ST pc x10 x11 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Lemma bounds : (0 <= A /\ A + Z.of_nat (length ls) <= 2^64 /\ 0 <= B /\ B + Z.of_nat (length rs) <= 2^64)%Z.
  Proof. pose proof (bytes_at_bound _ _ _ _ LS). pose proof (bytes_at_bound _ _ _ _ RS). lia. Qed.

  Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
  Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

  Lemma walk_at : forall i k r,
    memcmp_walk (skipn i ls) (skipn i rs) (S k) = Some r ->
    exists a b, nth_error ls i = Some a /\ nth_error rs i = Some b /\
      (if (bv_unsigned a =? bv_unsigned b)%Z then memcmp_walk (skipn (S i) ls) (skipn (S i) rs) k = Some r else r = (bv_unsigned a - bv_unsigned b)%Z).
  Proof.
    intros i k r H. cbn [memcmp_walk] in H.
    destruct (skipn i ls) as [|a l'] eqn:EL; [discriminate|].
    destruct (skipn i rs) as [|b r'] eqn:ER; [discriminate|].
    apply skipn_cons_nth in EL. apply skipn_cons_nth in ER. destruct EL as [Hna ->]. destruct ER as [Hnb ->].
    exists a, b. split; [exact Hna|]. split; [exact Hnb|].
    destruct (bv_unsigned a =? bv_unsigned b)%Z; [exact H | congruence].
  Qed.

  (* [comment removed for export] *)
  Lemma memcmp_loop : forall (k : nat) (i : Z) x13 x14,
    (0 <= i)%Z -> memcmp_walk (skipn (Z.to_nat i) ls) (skipn (Z.to_nat i) rs) (S k) = Some v -> (Z.of_nat (S k) < 2^64)%Z ->
    evt usegs POST (ST 0x2baf04 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (Z.of_nat (S k))) x13 x14).
  Proof.
    induction k as [|k IH]; intros i x13 x14 Hi HW Hk; pose proof bounds as BD;
      destruct (walk_at _ _ _ HW) as (a & b & Hna & Hnb & HC);
      pose proof (nth_error_lt _ _ _ Hna); pose proof (nth_error_lt _ _ _ Hnb); pose proof (byte_range a); pose proof (byte_range b);
      pose proof (u8ro_read usegs m A ls i a _ LS Hna ltac:(lia) eq_refl) as RDa;
      pose proof (u8ro_read usegs m B rs i b _ RS Hnb ltac:(lia) eq_refl) as RDb.
    - zstep. zstep. zstep. if_cases Kne; zify_cond Kne.
      + replace (bv_unsigned a =? bv_unsigned b)%Z with false in HC by (symmetry; apply Z.eqb_neq; exact Kne).
        zstep. zstep. subst v. finish.
      + rewrite (proj2 (Z.eqb_eq _ _) Kne) in HC. cbn [memcmp_walk] in HC. injection HC as <-.
        zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0. { exfalso. cbn in K0. lia. }
        zstep. zstep. finish.
    - zstep. zstep. zstep. if_cases Kne; zify_cond Kne.
      + replace (bv_unsigned a =? bv_unsigned b)%Z with false in HC by (symmetry; apply Z.eqb_neq; exact Kne).
        zstep. zstep. subst v. finish.
      + rewrite (proj2 (Z.eqb_eq _ _) Kne) in HC.
        zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0.
        * replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (B + i + 1)%Z with (B + (i + 1))%Z by lia.
          replace (Z.of_nat (S (S k)) + -1)%Z with (Z.of_nat (S k)) by lia.
          apply (IH (i + 1)%Z); try lia.
          replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact HC.
        * exfalso. lia.
  Qed.

  Lemma memcmp_body :
    memcmp_walk ls rs (Z.to_nat (bv_unsigned a2)) = Some v ->
    evt usegs POST (ST 0x2baf00 a0 a1 a2 a3 a4).
  Proof.
    intros HM; pose proof bounds as BD.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
    zstep. if_cases K0; zify_cond K0.
    - rewrite K0 in HM. cbn in HM. injection HM as <-. zstep. zstep. finish.
    - destruct (Z.to_nat (bv_unsigned a2)) as [|k] eqn:EK; [exfalso; lia|].
      eapply evt_eq.
      2:{ apply (memcmp_loop k 0 a3 a4); [lia | rewrite !skipn_O; exact HM | lia]. }
      unfold mkR. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. repeat f_equal.
      rewrite <- EK, Z2Nat.id by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  Qed.
End Proofs.

Definition memcmp_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v : Z),
  mem_inv usegs m ->
  bytes_at usegs m (bv_unsigned a0) ls ->
  bytes_at usegs m (bv_unsigned a1) rs ->
  memcmp_walk ls rs (Z.to_nat (bv_unsigned a2)) = Some v ->
  evt usegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 F fc v m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2baf00) fc None m (seg_rom usegs)).

Theorem memcmp_proof : memcmp_stmt.
Proof. unfold memcmp_stmt. intros. eapply memcmp_body; eassumption. Qed.

(* [comment removed for export] *)
Definition bcmp_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v : Z),
  mem_inv usegs m ->
  bytes_at usegs m (bv_unsigned a0) ls ->
  bytes_at usegs m (bv_unsigned a1) rs ->
  memcmp_walk ls rs (Z.to_nat (bv_unsigned a2)) = Some v ->
  evt usegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 F fc v m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2bae30) fc None m (seg_rom usegs)).

Theorem bcmp_proof : bcmp_stmt.
Proof. unfold bcmp_stmt. intros. zstep. eapply memcmp_proof; eassumption. Qed.
