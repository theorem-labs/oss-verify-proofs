(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
Import ListNotations.
Open Scope bv_scope.

Definition memcmp_entry := 0x240b0%Z.

Definition memcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (ls rs : list byte) (v : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ bytes_at rsegs m' (bv_unsigned a0) ls /\ bytes_at rsegs m' (bv_unsigned a1) rs.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (v : Z).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis LS : bytes_at rsegs m (bv_unsigned a0) ls.
  Hypothesis RS : bytes_at rsegs m (bv_unsigned a1) rs.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono rsegs m m := wmono_refl rsegs m.

  Notation A := (bv_unsigned a0).
  Notation B := (bv_unsigned a1).
  Notation n := (bv_unsigned a2).
  Notation POST := (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m).

  Notation ST pc x10 x11 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  #[using="m LS RS"] Lemma bounds : (0 <= A /\ A + Z.of_nat (length ls) <= 2^64 /\ 0 <= B /\ B + Z.of_nat (length rs) <= 2^64)%Z.
  Proof. pose proof (bytes_at_bound _ _ _ _ LS). pose proof (bytes_at_bound _ _ _ _ RS). lia. Qed.

  #[using="Type"] Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
  Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

  #[using="MI LS RS MU WM"] Lemma memcmp_loop : forall (k : nat) (i : Z) x13 x14,
    (0 <= i)%Z -> (0 < Z.of_nat k < 2^64)%Z ->
    memcmp_model (skipn (Z.to_nat i) ls) (skipn (Z.to_nat i) rs) k = Some v ->
    evt rsegs POST (ST 0x240b4 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (Z.of_nat k)) x13 x14).
  Proof.
    induction k as [|k IH]; intros i x13 x14 Hi Hk HW; pose proof bounds as BD; [lia|].
    cbn [memcmp_model] in HW.
    destruct (skipn (Z.to_nat i) ls) as [|a l'] eqn:EL; [discriminate|].
    destruct (skipn (Z.to_nat i) rs) as [|b r'] eqn:ER; [discriminate|].
    apply skipn_cons_nth in EL. apply skipn_cons_nth in ER. destruct EL as [Hna ->]. destruct ER as [Hnb ->].
    pose proof (nth_error_lt _ _ _ Hna). pose proof (nth_error_lt _ _ _ Hnb). pose proof (byte_range a). pose proof (byte_range b).
    pose proof (u8ro_read rsegs m A ls i a _ LS Hna ltac:(lia) eq_refl) as RD1.
    pose proof (u8ro_read rsegs m B rs i b _ RS Hnb ltac:(lia) eq_refl) as RD2.
    zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
    -
      assert (Kn : (bv_unsigned a =? bv_unsigned b) = false) by (apply Z.eqb_neq; lia). rewrite Kn in HW. injection HW as <-.
      zstep. zstep. finish.
    - assert (Kn : (bv_unsigned a =? bv_unsigned b) = true) by (apply Z.eqb_eq; lia). rewrite Kn in HW.
      zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0.
      +
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (B + i + 1)%Z with (B + (i + 1))%Z by lia.
        replace (Z.of_nat (S k) + -1)%Z with (Z.of_nat k) by lia.
        apply (IH (i + 1)%Z); try lia. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact HW.
      +
        destruct k; [|exfalso; lia]. cbn in HW. injection HW as <-.
        zstep. zstep. finish.
  Qed.

  #[using="MI LS RS MU WM"] Lemma memcmp_body :
    memcmp_model ls rs (Z.to_nat n) = Some v ->
    evt rsegs POST (ST 0x240b0 a0 a1 a2 a3 a4).
  Proof.
    intros HM; pose proof bounds as BD.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
    zstep. if_cases K0; zify_cond K0.
    -   replace (Z.to_nat n) with 0%nat in HM by lia. cbn in HM. injection HM as <-.
      zstep. zstep. finish.
    - eapply evt_eq.
      2:{ apply (memcmp_loop (Z.to_nat n) 0 a3 a4); try lia. cbn [Z.to_nat skipn]. exact HM. }
      unfold mkR. rewrite !Z_to_bv_plus0. repeat f_equal. rewrite Z2Nat.id by lia. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.
End Proofs.

Lemma memcmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v : Z),
  bytes_at rsegs m (bv_unsigned a0) ls ->
  bytes_at rsegs m (bv_unsigned a1) rs ->
  memcmp_model ls rs (Z.to_nat (bv_unsigned a2)) = Some v ->
  mem_inv rsegs m ->
  evt rsegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x240b0) fc None m (seg_rom rsegs)).
Proof. intros until v. intros LS RS HM MI. apply memcmp_body; assumption. Qed.
