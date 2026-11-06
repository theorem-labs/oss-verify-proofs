(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5AChk L5AChkAs0 L5ADetailP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADZ.
Import L5A. Import L5CA. Import L5SA. Import L5CB. Import L5ADTP.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | blia] ].
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Definition KSZ : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Lemma KSZ_chk k : In k KSZ -> (k < 32)%nat /\ k <> 13%nat /\ k <> 14%nat.
Proof.
  intros H. assert (X : forallb (fun x => (x <? 32)%nat && negb (x =? 13)%nat && negb (x =? 14)%nat) KSZ = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in X. specialize (X k H). apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
  apply Nat.ltb_lt in X1. apply negb_true_iff in X2, X3. apply Nat.eqb_neq in X2, X3. auto.
Qed.

Section Z.
Variables (sb F p : Z) (s : list Z) (MV : word -> option byte).
Local Notation n := (Z.of_nat (length s)).
Hypothesis SBR : 140735332487488 <= sb <= 140737488355312.
Hypothesis SBA : aligned sb 32.
Hypothesis W176 : L5.writable RSEGS MV (sb - 160) 176.
Hypothesis IMGC : L5.img_clear MV 860160 880640.
Hypothesis CSB : L5.u64_at RSEGS MV 908088 2147450880.
Hypothesis CUAR : L5.u32_at RSEGS MV 908096 1.
Hypothesis FR : 0 <= F < 2 ^ 64.
Hypothesis PR : 4096 <= p /\ p + n <= 140737479966720.
Hypothesis BYTES : L5.bytes_at RSEGS MV p s.
Hypothesis BR : Forall (fun c => 0 <= c < 256) s.
Hypothesis ACC : aacc MV p n.
Hypothesis LEN : (length s <= 4999)%nat.

Definition zhead (R : bvmap 5 word) (j : nat) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sb - 160) /\ getr R (reg 8) = Z_to_bv 64 (sb + 16) /\ getr R (reg 9) = Z_to_bv 64 (sb - 160) /\
  getr R (reg 10) = Z_to_bv 64 (p + Z.of_nat j) /\ getr R (reg 11) = Z_to_bv 64 (p + Z.of_nat j) /\ getr R (reg 12) = Z_to_bv 64 48 /\
  getr R (reg 13) = Z_to_bv 64 ((p + Z.of_nat j) / 8 + 2147450880) /\ getr R (reg 19) = Z_to_bv 64 (p + n) /\
  getr R (reg 21) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R (reg 23) = Z_to_bv 64 (F + 96) /\ getr R (reg 26) = Z_to_bv 64 2147450880 /\
  getr R (reg 27) = Z_to_bv 64 F.

Lemma zskip_run : forall (rem j : nat) fx R, (j + rem = length s)%nat -> (1 <= rem)%nat ->
  (forall i, (i < j)%nat -> nth i s 0 = 48) -> zhead R j ->
  exists fx' R' (z : nat), msteps RSEGS (st fx R 0x8eb64 MV) (st fx' R' 0x8eb90 MV)
    /\ (forall x, In x KSZ -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 11) = Z_to_bv 64 (p + Z.of_nat z)
    /\ (z <= length s)%nat /\ (forall i, (i < z)%nat -> nth i s 0 = 48) /\ ((z < length s)%nat -> nth z s 0 <> 48).
Proof.
  induction rem as [|rem IH]; intros j fx R EJ HR Z0 (G2 & G8 & G9 & G10 & G11 & G12 & G13 & G19 & G21 & G23 & G26 & G27). lia.
  assert (JL : (j < length s)%nat) by lia.
  set (cur := p + Z.of_nat j) in *.
  assert (CR : 4096 <= cur /\ cur + 1 <= p + n) by (subst cur; clear - PR JL; lia).
  set (c := nth j s 0).
  assert (CB : 0 <= c < 256). { subst c. rewrite Forall_forall in BR. apply BR. apply nth_In. exact JL. }
  assert (Bc : L5.u8_at RSEGS MV cur c) by (apply BYTES; exact JL).
  destruct (L5ACHK0.chk_8e810 fx R MV cur ltac:(unfold S, SB; exact G13) G10 ltac:(clear - CR PR; lia) ltac:(eapply aacc_sub; [exact ACC | clear - CR; lia | clear - CR; lia]))
    as (R1 & MS1 & K1).
  assert (KK : forall x, In x KSZ -> getr R1 (reg x) = getr R (reg x)). { intros x Hx. destruct (KSZ_chk x Hx) as (X1 & X2 & X3). apply K1; assumption. }
  assert (J10 : getr R1 (reg 10) = Z_to_bv 64 cur) by (rewrite K1 by lia; exact G10).
  assert (J11 : getr R1 (reg 11) = Z_to_bv 64 cur) by (rewrite K1 by lia; exact G11).
  assert (HV55 : 4096 <= cur <= 140737488355327) by (clear - CR PR; lia).
  assert (HV55' : 4096 <= cur <= 140737479966720) by (clear - CR PR; lia).
  destruct (Z.eq_dec c 48) as [E48|N48].
  - (* [comment removed for export] *)
    assert (C48 : 48 <= c <= 48) by (clear - E48; lia).
    destruct rem as [|rem'].
    + (* [comment removed for export] *)
      pose proof (dtZx_conc fx R1 MV (fun k => match k with 2%nat => sb | 40%nat => F | 55%nat => cur | 56%nat => c | 58%nat => U R1 1 | 59%nat => U R1 13 | 60%nat => U R1 14 | _ => 0 end)) as P.
      cbn beta iota in P.
      assert (J19 : getr R1 (reg 19) = Z_to_bv 64 (cur + 1)). { rewrite KK by inl. rewrite G19. f_equal. subst cur. clear - EJ; lia. }
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite KK by inl; assumption)]).
      destruct P as (fx2 & R2 & M2 & _ & FR2 & _ & (MS2 & KS2 & Q10 & Q11 & Q13)).
      assert (E2 : M2 = MV) by (apply mem_eq_of_agree; intros a Ha; apply FR2). subst M2.
      exists fx2, R2, (Datatypes.S j). split. { eapply msteps_trans. exact MS1. exact MS2. }
      split. { intros x Hx. rewrite (KS2 x). apply KK. exact Hx. revert Hx. apply (L5K.incl_b KSZ KS_dtZx). vm_compute; reflexivity. }
      split. { rewrite Q11. f_equal. subst cur. clear; lia. }
      split. lia. split. { intros i Hi. destruct (Nat.eq_dec i j) as [->|NE]. exact E48. apply Z0. lia. } intros X. exfalso. lia.
    + (* [comment removed for export] *)
      pose proof (dtZe_conc fx R1 MV (fun k => match k with 2%nat => sb | 40%nat => F | 55%nat => cur | 56%nat => c | 57%nat => Z.of_nat (Datatypes.S rem') | 58%nat => U R1 1 | 59%nat => U R1 13 | 60%nat => U R1 14 | _ => 0 end)) as P.
      cbn beta iota in P.
      assert (J19 : getr R1 (reg 19) = Z_to_bv 64 (cur + 1 + Z.of_nat (Datatypes.S rem'))). { rewrite KK by inl. rewrite G19. f_equal. subst cur. clear - EJ; lia. }
      assert (HV57 : 1 <= Z.of_nat (Datatypes.S rem') <= 67108863) by (clear - LEN EJ; lia).
      assert (R57 : 0 <= Z.of_nat (Datatypes.S rem') < 2 ^ 64) by (clear - HV57; lia).
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite KK by inl; assumption)]).
      destruct P as (fx2 & R2 & M2 & _ & FR2 & _ & (MS2 & KS2 & Q10 & Q11 & Q13)).
      assert (E2 : M2 = MV) by (apply mem_eq_of_agree; intros a Ha; apply FR2). subst M2.
      assert (KK2 : forall x, In x KSZ -> getr R2 (reg x) = getr R (reg x)).
      { intros x Hx. rewrite (KS2 x). apply KK. exact Hx. revert Hx. apply (L5K.incl_b KSZ KS_dtZe). vm_compute; reflexivity. }
      destruct (IH (Datatypes.S j) fx2 R2 ltac:(lia) ltac:(lia)) as (fx3 & R3 & z & MS3 & KS3 & Q11' & ZL & ZZ & ZN).
      { intros i Hi. destruct (Nat.eq_dec i j) as [->|NE]. exact E48. apply Z0. lia. }
      { unfold zhead. replace (p + Z.of_nat (Datatypes.S j)) with (cur + 1) by (subst cur; clear; lia).
        repeat split; try assumption; try (rewrite KK2 by inl; assumption). }
      exists fx3, R3, z. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. exact MS3. }
      split. { intros x Hx. rewrite (KS3 x Hx). apply KK2. exact Hx. } split. exact Q11'. split. exact ZL. split. exact ZZ. exact ZN.
  - (* [comment removed for export] *)
    assert (EX : exists fx2 R2, msteps RSEGS (st fx R1 0x8eb6c MV) (st fx2 R2 0x8eb90 MV) /\ (forall x, In x KSZ -> getr R2 (reg x) = getr R1 (reg x)) /\ getr R2 (reg 11) = Z_to_bv 64 cur).
    { destruct (Z_lt_le_dec c 48) as [LT|GE].
      - assert (C47 : 0 <= c <= 47) by (clear - CB LT; lia).
        pose proof (dtZl_conc fx R1 MV (fun k => match k with 2%nat => sb | 40%nat => F | 55%nat => cur | 56%nat => c | 58%nat => U R1 1 | 59%nat => U R1 13 | 60%nat => U R1 14 | _ => 0 end)) as P.
        cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc | (rewrite KK by inl; assumption)]).
        destruct P as (fx2 & R2 & M2 & _ & FR2 & _ & (MS2 & KS2 & Q13)).
        assert (E2 : M2 = MV) by (apply mem_eq_of_agree; intros a Ha; apply FR2). subst M2.
        exists fx2, R2. split. exact MS2. split. { intros x Hx. apply KS2. revert Hx. apply (L5K.incl_b KSZ KS_dtZl). vm_compute; reflexivity. }
        rewrite (KS2 11%nat) by inl. exact J11.
      - assert (C49 : 49 <= c <= 255) by (clear - CB GE N48; lia).
        pose proof (dtZh_conc fx R1 MV (fun k => match k with 2%nat => sb | 40%nat => F | 55%nat => cur | 56%nat => c | 58%nat => U R1 1 | 59%nat => U R1 13 | 60%nat => U R1 14 | _ => 0 end)) as P.
        cbn beta iota in P. feed P ltac:(first [apply UR | apply U_to | sc | (rewrite KK by inl; assumption)]).
        destruct P as (fx2 & R2 & M2 & _ & FR2 & _ & (MS2 & KS2 & Q13)).
        assert (E2 : M2 = MV) by (apply mem_eq_of_agree; intros a Ha; apply FR2). subst M2.
        exists fx2, R2. split. exact MS2. split. { intros x Hx. apply KS2. revert Hx. apply (L5K.incl_b KSZ KS_dtZh). vm_compute; reflexivity. }
        rewrite (KS2 11%nat) by inl. exact J11. }
    destruct EX as (fx2 & R2 & MS2 & KS2 & Q11).
    exists fx2, R2, j. split. { eapply msteps_trans. exact MS1. exact MS2. }
    split. { intros x Hx. rewrite (KS2 x Hx). apply KK. exact Hx. } split. exact Q11. split. lia. split. exact Z0. intros _. exact N48.
Qed.
End Z.
End L5ADZ.
