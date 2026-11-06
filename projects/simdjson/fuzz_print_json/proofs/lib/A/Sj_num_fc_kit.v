(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber SjNumSwar.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd Sj_stage1_kit Sj_num_kit Sj_num_walk Sj_num_sp_pdefs.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface D_defs D_kit Sj_akit Sj_num_akit Sj_num_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition ftb (A : Z) (txt : list byte) (i : Z) : Z := bv_unsigned (nth (Z.to_nat (i - A)) txt (Z_to_bv 8 0)).
Definition fge48 (A : Z) (txt : list byte) (lo hi : Z) : Prop := forall i, lo <= i < hi -> 48 <= ftb A txt i.

Lemma ftb_range : forall A txt i, 0 <= ftb A txt i < 256.
Proof. intros A txt i. unfold ftb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (i - A)) txt (Z_to_bv 8 0))) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
Lemma fge48_nil : forall A txt lo, fge48 A txt lo lo.
Proof. intros A txt lo i Hi. lia. Qed.
Lemma fge48_snoc : forall A txt lo hi, fge48 A txt lo hi -> 48 <= ftb A txt hi -> fge48 A txt lo (hi + 1).
Proof. intros A txt lo hi H Hb i Hi. destruct (Z.eq_dec i hi) as [->|NE]; [exact Hb | apply H; lia]. Qed.
Lemma fge48_app : forall A txt lo mid hi, fge48 A txt lo mid -> fge48 A txt mid hi -> fge48 A txt lo hi.
Proof. intros A txt lo mid hi H1 H2 i Hi. destruct (Z_lt_le_dec i mid); [apply H1 | apply H2]; lia. Qed.
Lemma fge48_sub : forall A txt lo hi lo' hi', fge48 A txt lo hi -> lo <= lo' -> hi' <= hi -> fge48 A txt lo' hi'.
Proof. intros A txt lo hi lo' hi' H H1 H2 i Hi. apply H. lia. Qed.

Lemma fge48_8 : forall A txt p,
  (48 <= ftb A txt p /\ 48 <= ftb A txt (p + 1) /\ 48 <= ftb A txt (p + 2) /\ 48 <= ftb A txt (p + 3) /\
   48 <= ftb A txt (p + 4) /\ 48 <= ftb A txt (p + 5) /\ 48 <= ftb A txt (p + 6) /\ 48 <= ftb A txt (p + 7)) -> fge48 A txt p (p + 8).
Proof.
  intros A txt p (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7) i Hi.
  assert (C : i = p \/ i = p + 1 \/ i = p + 2 \/ i = p + 3 \/ i = p + 4 \/ i = p + 5 \/ i = p + 6 \/ i = p + 7) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; assumption.
Qed.
Lemma fge48_4 : forall A txt p,
  (48 <= ftb A txt p /\ 48 <= ftb A txt (p + 1) /\ 48 <= ftb A txt (p + 2) /\ 48 <= ftb A txt (p + 3)) -> fge48 A txt p (p + 4).
Proof.
  intros A txt p (H0 & H1 & H2 & H3) i Hi.
  assert (C : i = p \/ i = p + 1 \/ i = p + 2 \/ i = p + 3) by lia.
  destruct C as [-> | [-> | [-> | ->]]]; assumption.
Qed.

Lemma fswar8 : forall A txt p X,
  Z.land (Z.lor X ((le8z (ftb A txt p) (ftb A txt (p + 1)) (ftb A txt (p + 2)) (ftb A txt (p + 3)) (ftb A txt (p + 4)) (ftb A txt (p + 5)) (ftb A txt (p + 6)) (ftb A txt (p + 7))
                    + 14974415777481871312) mod 18446744073709551616)) 9259542123273814144 = 0 ->
  fge48 A txt p (p + 8).
Proof.
  intros A txt p X H. apply fge48_8. eapply swar8_machine; [apply ftb_range .. | exact H].
Qed.

Lemma w4_eq : forall (b0 b1 b2 : Z) (c3 : byte), 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  Z.lor (Z.lor (Z.shiftl (bv_unsigned (sxb c3)) 24 mod 18446744073709551616) (Z.shiftl b2 16 mod 18446744073709551616))
        (Z.lor (Z.shiftl b1 8 mod 18446744073709551616) b0)
  = b0 + 256 * (b1 + 256 * (b2 + 256 * (bv_unsigned c3 + 256 * (if bv_unsigned c3 <? 128 then 0 else 4294967295)))).
Proof.
  intros b0 b1 b2 c3 H0 H1 H2.
  pose proof (bv_unsigned_in_range 8 c3) as R3. unfold bv_modulus in R3. cbn in R3.
  assert (E8 : Z_to_bv 8 (bv_unsigned c3) = c3).
  { apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. }
  pose proof (sxb_small (bv_unsigned c3) ltac:(lia)) as E. rewrite E8 in E. rewrite E. clear E E8.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  rewrite (Z.mod_small (b2 * 65536)) by lia. rewrite (Z.mod_small (b1 * 256)) by lia.
  assert (E3 : ((if bv_unsigned c3 <? 128 then bv_unsigned c3 else bv_unsigned c3 - 256) mod 18446744073709551616 * 16777216) mod 18446744073709551616
               = bv_unsigned c3 * 16777216 + 4294967296 * (if bv_unsigned c3 <? 128 then 0 else 4294967295)).
  { destruct (Z.ltb_spec (bv_unsigned c3) 128).
    - rewrite (Z.mod_small (bv_unsigned c3)) by lia. rewrite Z.mod_small by lia. lia.
    - replace ((bv_unsigned c3 - 256) mod 18446744073709551616) with (bv_unsigned c3 - 256 + 18446744073709551616)
        by (apply (Z.mod_unique _ _ (-1)); lia).
      symmetry. apply (Z.mod_unique _ _ 16777215); lia. }
  rewrite E3. clear E3.
  set (hi := if bv_unsigned c3 <? 128 then 0 else 4294967295).
  assert (Hhi : 0 <= hi <= 4294967295) by (unfold hi; destruct (bv_unsigned c3 <? 128); lia).
  rewrite (lor_disj (b1 * 256) b0 8) by (try lia; rewrite Z.mod_mul by lia; reflexivity).
  rewrite (lor_disj (bv_unsigned c3 * 16777216 + 4294967296 * hi) (b2 * 65536) 24)
    by (try lia; change (2 ^ 24) with 16777216; Z.div_mod_to_equations; lia).
  rewrite (lor_disj _ (b1 * 256 + b0) 16) by (try lia; change (2 ^ 16) with 65536; Z.div_mod_to_equations; lia).
  lia.
Qed.

Lemma fswar4 : forall A txt p X,
  Z.land (Z.lor X (bv_swrap 32
            (Z.lor (Z.lor (Z.shiftl (bv_unsigned (sxb (nth (Z.to_nat (p + 3 - A)) txt (Z_to_bv 8 0)))) 24 mod 18446744073709551616)
                          (Z.shiftl (ftb A txt (p + 2)) 16 mod 18446744073709551616))
                   (Z.lor (Z.shiftl (ftb A txt (p + 1)) 8 mod 18446744073709551616) (ftb A txt p)) + 18446744072901087184)
          mod 18446744073709551616)) 18446744071570489472 = 0 ->
  fge48 A txt p (p + 4).
Proof.
  intros A txt p X H. apply fge48_4.
  rewrite w4_eq in H by apply ftb_range.
  rewrite bv_swrap32 in H. unfold swrap32 in H.
  change (bv_unsigned (nth (Z.to_nat (p + 3 - A)) txt (Z_to_bv 8 0))) with (ftb A txt (p + 3)) in H.
  eapply swar4_ge48; [apply ftb_range .. | exact H].
Qed.

Definition fpfacts (A : Z) (txt : list byte) (FIRST LAST IP IL FPT FL : Z) : Prop :=
  (FIRST <= IP /\ 1 <= IL /\ IP + IL <= LAST) /\ fge48 A txt IP (IP + IL) /\
  ((FPT = 0 /\ FL = 0) \/
   (FPT = IP + IL + 1 /\ 1 <= FL /\ FPT + FL <= LAST /\ ftb A txt (IP + IL) = 46) /\ fge48 A txt FPT (FPT + FL)).

Definition fffacts (A : Z) (txt : list byte) (FIRST LAST IP IL p : Z) : Prop :=
  (FIRST <= IP /\ 1 <= IL /\ IP + IL + 1 <= p /\ p <= LAST) /\ fge48 A txt IP (IP + IL) /\ ftb A txt (IP + IL) = 46 /\ fge48 A txt (IP + IL + 1) p.

Lemma fffacts_app : forall A txt FIRST LAST IP IL p n, fffacts A txt FIRST LAST IP IL p -> 0 <= n -> p + n <= LAST ->
  fge48 A txt p (p + n) -> fffacts A txt FIRST LAST IP IL (p + n).
Proof.
  intros A txt FIRST LAST IP IL p n ((H1 & H2 & H3 & H4) & G1 & D & G2) Hn Hl Hb.
  split; [lia|]. split; [exact G1|]. split; [exact D|]. eapply fge48_app; [exact G2 | exact Hb].
Qed.
Lemma fffacts_app_eq : forall A txt FIRST LAST IP IL p n q, fffacts A txt FIRST LAST IP IL p -> 0 <= n -> p + n <= LAST ->
  fge48 A txt p (p + n) -> q = p + n -> fffacts A txt FIRST LAST IP IL q.
Proof. intros A txt FIRST LAST IP IL p n q H Hn Hl Hb ->. apply fffacts_app; assumption. Qed.
Lemma fffacts_pfacts : forall A txt FIRST LAST IP IL p, fffacts A txt FIRST LAST IP IL p -> IP + IL + 1 < p ->
  fpfacts A txt FIRST LAST IP IL (IP + IL + 1) (p - (IP + IL + 1)).
Proof.
  intros A txt FIRST LAST IP IL p ((H1 & H2 & H3 & H4) & G1 & D & G2) Hp.
  split; [lia|]. split; [exact G1|]. right. split; [split; [reflexivity|]; split; [lia|]; split; [lia | exact D]|].
  replace (IP + IL + 1 + (p - (IP + IL + 1))) with p by lia. exact G2.
Qed.
Lemma fge48_1 : forall A txt p, 48 <= ftb A txt p -> fge48 A txt p (p + 1).
Proof. intros A txt p H i Hi. replace i with p by lia. exact H. Qed.

Ltac akstep := kstep; anorm.
Ltac akwalk_fuel n K :=
  lazymatch n with
  | O => lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "akwalk: out of fuel at" pc end
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (akstep; akwalk_fuel n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H; knorm_in H;
          first [ solve [exfalso; lia] | akwalk_fuel n' K ]
      end
  end.
Ltac akwalk K := akwalk_fuel 300%nat K.
Ltac akwalkd_fuel n K :=
  lazymatch n with
  | O => idtac "akwalkd: out of fuel"
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (akstep; akwalkd_fuel n' K) | idtac "STUCK at" pc ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H; knorm_in H;
          first [ solve [exfalso; lia] | akwalkd_fuel n' K ]
      end
  end.
Ltac akwalkd K := akwalkd_fuel 300%nat K.
