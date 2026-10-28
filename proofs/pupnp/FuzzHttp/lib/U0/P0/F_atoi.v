(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim ScanInt ScanIntProps.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs Printf_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_shgetc_A F_strtol.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac mlia2 := rewrite ?land_W64 in *; Z.div_mod_to_equations; lia.

Definition atoi_entry := 0x23d2c%Z.

Definition atoi_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Definition atoi_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (str : list byte),
  bytes_at rsegs m S (str ++ [Z_to_bv 8 0]) -> mem_inv rsegs m -> (1 <= S)%Z ->
  evt rsegs (atoi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 atoi_entry) fc None m (seg_rom rsegs)).

Section A.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (S : Z) (str : list byte).
  Hypothesis BY : bytes_at rsegs m S (str ++ [Z_to_bv 8 0]).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis S1 : (1 <= S)%Z.
  Notation txt := (map bv_unsigned (str ++ [Z_to_bv 8 0])).
  Notation p := (Z.of_nat (first_nul txt)).
  Notation POST := (atoi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).

  #[using="m BY"] Lemma facts : (0 <= p < zlength txt)%Z /\ znth txt p = 0%Z /\ (forall i, 0 <= i < p -> znth txt i <> 0)%Z /\
                zbytes txt = str ++ [Z_to_bv 8 0] /\ length txt = (length str + 1)%nat /\
                (forall i, 0 <= i < zlength txt -> 0 <= znth txt i < 256)%Z /\ (S + zlength txt <= 2^64)%Z.
  Proof.
    assert (IN0 : In 0%Z txt). { rewrite map_app. apply in_or_app. right. left. reflexivity. }
    destruct (first_nul_spec txt IN0) as (PL & PNUL & PNZ).
    assert (LT : length txt = (length str + 1)%nat) by (rewrite length_map, length_app; cbn; lia).
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    assert (RNG : forall k, (0 <= k < zlength txt)%Z -> (0 <= znth txt k < 256)%Z).
    { intros k Hk. refine (txt_rng _ _ k Hk). apply Forall_map. apply Forall_forall. intros b _.
      pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. cbn. lia. }
    unfold zlength in *. repeat split; try assumption; try lia.
    - apply zbytes_bytes.
    - intros. apply RNG. lia.
    - intros. apply RNG. lia.
  Qed.

  Ltac rd i := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8ro_read rsegs mm S (zbytes txt) i _ _ ltac:(rewrite (proj1 (proj2 (proj2 (proj2 facts)))); exact BY)
                  (zbytes_nth txt i ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb end.

  #[using="BY MI"] Lemma L_dig : forall n j (x5 x6 x7 x10 x12 x13 x15 x16 x17 x28 x29 x30 x31 : word),
    (0 <= j <= p)%Z -> (p - j < Z.of_nat n)%Z ->
    evt rsegs POST
      (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 (Z_to_bv 64 (S + j)) x12 x13 (Z_to_bv 64 10) x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x23d94) fc None m (seg_rom rsegs)).
  Proof.
    induction n as [|n IH]; intros j x5 x6 x7 x10 x12 x13 x15 x16 x17 x28 x29 x30 x31 Hj Hn; [lia|].
    pose proof facts as (Hp & PNUL & PNZ & ZB & LT & RNG & BB). unfold zlength in *.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (RNG j ltac:(lia)) as Rj. pose_word_ranges.
    rd j. zs. cbv beta. rewrite (unsigned_lit8 (znth txt j)) by lia. clear RDb.
    zs. zs. zs. zs. zs. brf K1.
    -
      assert (j < p)%Z by (destruct (Z.eq_dec j p) as [E|]; [rewrite E, PNUL in K1; exfalso; mlia2 | lia]).
      replace (Z_to_bv 64 (S + j + 1)) with (Z_to_bv 64 (S + (j + 1))) by (f_equal; lia).
      apply IH; lia.
    - zs. brf K2.
      + zs. apply evt_done. unfold atoi_post. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. repeat split; assumption.
      + zs. zs. apply evt_done. unfold atoi_post. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. repeat split; assumption.
  Qed.
  Ltac fin := apply evt_done; unfold atoi_post; repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|]; repeat split; assumption.

  #[using="BY MI"] Lemma L_ce8 : forall j (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    (0 <= j <= p)%Z ->
    evt rsegs POST
      (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (znth txt j)) (Z_to_bv 64 (S + j)) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x23d7c) fc None m (seg_rom rsegs)).
  Proof.
    intros j x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hj.
    pose proof facts as (Hp & PNUL & PNZ & ZB & LT & RNG & BB). unfold zlength in *.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (RNG j ltac:(lia)) as Rj. pose_word_ranges.
    zs. zs. zs. brf K1.
    -
      zs. zs. brf K2.
      + zs. zs. fin.
      + zs. zs. fin.
    - assert (j < p)%Z by (destruct (Z.eq_dec j p) as [E|]; [rewrite E, PNUL in K1; exfalso; mlia2 | lia]).
      zs. zs. zs.
      replace (Z_to_bv 64 (S + j + 1)) with (Z_to_bv 64 (S + (j + 1))) by (f_equal; lia).
      apply (L_dig (Datatypes.S (Z.to_nat (p - j)))); lia.
  Qed.

  #[using="BY MI"] Lemma L_ws : forall n i (x5 x6 x7 x10 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    (0 <= i <= p)%Z -> (p - i < Z.of_nat n)%Z ->
    evt rsegs POST
      (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 (Z_to_bv 64 (S + (i + 1))) (Z_to_bv 64 5) (Z_to_bv 64 32) x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x23d40) fc None m (seg_rom rsegs)).
  Proof.
    induction n as [|n IH]; intros i x5 x6 x7 x10 x14 x15 x16 x17 x28 x29 x30 x31 Hi Hn; [lia|].
    pose proof facts as (Hp & PNUL & PNZ & ZB & LT & RNG & BB). unfold zlength in *.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (RNG i ltac:(lia)) as Ri. pose_word_ranges.
    rd i. zs. cbv beta. rewrite (unsigned_lit8 (znth txt i)) by lia. clear RDb.
    zs. zs. brf K1.
    -
      assert (i < p)%Z by (destruct (Z.eq_dec i p) as [E|]; [rewrite E, PNUL in K1; exfalso; mlia2 | lia]).
      zs. replace (Z_to_bv 64 (S + (i + 1) + 1)) with (Z_to_bv 64 (S + (i + 1 + 1))) by (f_equal; lia).
      apply IH; lia.
    - zs. brf K2.
      + assert (i < p)%Z by (destruct (Z.eq_dec i p) as [E|]; [rewrite E, PNUL in K2; exfalso; mlia2 | lia]).
        zs. replace (Z_to_bv 64 (S + (i + 1) + 1)) with (Z_to_bv 64 (S + (i + 1 + 1))) by (f_equal; lia).
        apply IH; lia.
      +
        zs. zs. brf K3.
        *
          assert (i < p)%Z by (destruct (Z.eq_dec i p) as [E|]; [rewrite E, PNUL in K3; exfalso; mlia2 | lia]).
          pose proof (RNG (i + 1)%Z ltac:(lia)) as Ri1.
          rd (i + 1)%Z. zs. cbv beta. rewrite (unsigned_lit8 (znth txt (i + 1)%Z)) by lia. clear RDb.
          zs. zs. apply L_ce8. lia.
        * zs. zs. brf K4.
          --
             zs. zs. replace (Z_to_bv 64 (S + (i + 1) + -1)) with (Z_to_bv 64 (S + i)) by (f_equal; lia).
             apply L_ce8. lia.
          --
             assert (i < p)%Z by (destruct (Z.eq_dec i p) as [E|]; [rewrite E, PNUL in K4; exfalso; mlia2 | lia]).
             pose proof (RNG (i + 1)%Z ltac:(lia)) as Ri1.
             rd (i + 1)%Z. zs. cbv beta. rewrite (unsigned_lit8 (znth txt (i + 1)%Z)) by lia. clear RDb.
             zs. zs. apply L_ce8. lia.
  Qed.

  #[using="str BY MI"] Lemma L_main : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    evt rsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 atoi_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros. unfold atoi_entry.
    pose proof facts as (Hp & PNUL & PNZ & ZB & LT & RNG & BB). unfold zlength in *.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM. pose_word_ranges.
    zs. zs. zs. zs.
    replace (Z_to_bv 64 (S + 1)) with (Z_to_bv 64 (S + (0 + 1))) by (f_equal; lia).
    apply (L_ws (Datatypes.S (Z.to_nat p))); lia.
  Qed.
End A.

Theorem atoi_spec : atoi_stmt.
Proof. unfold atoi_stmt. intros. eapply L_main; eassumption. Qed.
