(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition sp_tb (E : fcbenv) (i : Z) : Z := bv_unsigned (nth (Z.to_nat (i - q_A E)) (q_txt E) (Z_to_bv 8 0)).
Definition sp_ge48 (E : fcbenv) (lo hi : Z) : Prop := forall i, (lo <= i < hi)%Z -> (48 <= sp_tb E i)%Z.

Lemma sp_tb_range : forall E i, (0 <= sp_tb E i < 256)%Z.
Proof. intros E i. unfold sp_tb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (i - q_A E)) (q_txt E) (Z_to_bv 8 0))) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Lemma sp_ge48_nil : forall E lo, sp_ge48 E lo lo.
Proof. intros E lo i Hi. lia. Qed.
Lemma sp_ge48_snoc : forall E lo hi, sp_ge48 E lo hi -> (48 <= sp_tb E hi)%Z -> sp_ge48 E lo (hi + 1).
Proof. intros E lo hi H Hb i Hi. destruct (Z.eq_dec i hi) as [->|NE]; [exact Hb | apply H; lia]. Qed.
Lemma sp_ge48_app : forall E lo mid hi, sp_ge48 E lo mid -> sp_ge48 E mid hi -> sp_ge48 E lo hi.
Proof. intros E lo mid hi H1 H2 i Hi. destruct (Z_lt_le_dec i mid); [apply H1 | apply H2]; lia. Qed.

Ltac kb2z :=
  repeat match goal with
  | |- context [Z.b2z ?t] =>
      lazymatch t with context [bv_unsigned _] => fail | _ => idtac end;

      match t with context [?x] => is_var x; fail 1 | _ => idtac end;
      let v := eval vm_compute in (Z.b2z t) in
      lazymatch v with 0%Z => idtac | 1%Z => idtac end;
      change (Z.b2z t) with v
  end.
Ltac kstep := bkstep; kb2z.

Lemma land_255 : forall x, Z.land x 255 = (x mod 256)%Z.
Proof. intros x. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Ltac knorm_in H := rewrite ?land_255 in H.
Ltac kwalk_fuel n K :=
  lazymatch n with
  | O => lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "kwalk: out of fuel at" pc end
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (kstep; kwalk_fuel n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H; knorm_in H;
          first [ solve [exfalso; lia] | kwalk_fuel n' K ]
      end
  end.
Ltac kwalk K := kwalk_fuel 200%nat K.

Ltac kwalkn n K :=
  lazymatch n with
  | O => idtac
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (kstep; kwalkn n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H; knorm_in H;
          first [ solve [exfalso; lia] | kwalkn n' K ]
      end
  end.

Lemma num_wz_signed : forall w : word, Z_to_bv 64 (bv_signed w) = w.
Proof.
  intros w. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in *. change (18446744073709551616 / 2)%Z with 9223372036854775808%Z.
  Z.div_mod_to_equations. lia.
Qed.

Definition sp_pfacts (E : fcbenv) (IP IL FPT FL : Z) : Prop :=
  (q_A E <= IP /\ 1 <= IL /\ IP + IL <= q_LAST E)%Z /\ sp_ge48 E IP (IP + IL) /\
  ((FPT = 0 /\ FL = 0)%Z \/
   (FPT = IP + IL + 1 /\ 1 <= FL /\ FPT + FL <= q_LAST E /\ sp_tb E (IP + IL) = 46)%Z /\ sp_ge48 E FPT (FPT + FL)).

Lemma sp_pfacts_spans : forall E IP IL FPT FL, fcb_ok E -> sp_pfacts E IP IL FPT FL -> pm_spans_ok (q_A E) (q_txt E) IP IL FPT FL.
Proof.
  intros E IP IL FPT FL OK ((H1 & H2 & H3) & _ & [[-> ->] | [(-> & F1 & F2 & _) _]]); destruct OK as [_ _ _ _ _ _ _ HF _ _]; unfold pm_spans_ok.
  - split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
  - split; [lia|]. split; [lia|]. split; [lia|]. right. lia.
Qed.

Definition sp_nz (E : fcbenv) (IP IL FPT FL z : Z) : Prop :=
  (49 <= sp_tb E z)%Z /\ ((IP <= z < IP + IL)%Z \/ (FPT <> 0 /\ FPT <= z < FPT + FL)%Z).

Definition sp_ffacts (E : fcbenv) (IP IL p : Z) : Prop :=
  (q_A E <= IP /\ 1 <= IL /\ IP + IL + 1 <= p /\ p <= q_LAST E)%Z /\ sp_ge48 E IP (IP + IL) /\ sp_tb E (IP + IL) = 46%Z /\ sp_ge48 E (IP + IL + 1) p.

Lemma sp_ffacts_app : forall E IP IL p n, sp_ffacts E IP IL p -> (0 <= n)%Z -> (p + n <= q_LAST E)%Z ->
  (forall i, (p <= i < p + n)%Z -> (48 <= sp_tb E i)%Z) -> sp_ffacts E IP IL (p + n).
Proof.
  intros E IP IL p n ((H1 & H2 & H3 & H4) & G1 & D & G2) Hn Hl Hb.
  split; [lia|]. split; [exact G1|]. split; [exact D|]. eapply sp_ge48_app; [exact G2 | exact Hb].
Qed.

Lemma sp_ffacts_pfacts : forall E IP IL p, sp_ffacts E IP IL p -> (IP + IL + 1 < p)%Z -> sp_pfacts E IP IL (IP + IL + 1) (p - (IP + IL + 1)).
Proof.
  intros E IP IL p ((H1 & H2 & H3 & H4) & G1 & D & G2) Hp.
  split; [lia|]. split; [exact G1|]. right. split; [split; [reflexivity|]; split; [lia|]; split; [lia | exact D]|].
  replace (IP + IL + 1 + (p - (IP + IL + 1)))%Z with p by lia. exact G2.
Qed.

Lemma sp_ge48_1 : forall E p, (48 <= sp_tb E p)%Z -> forall i, (p <= i < p + 1)%Z -> (48 <= sp_tb E i)%Z.
Proof. intros E p H i Hi. replace i with p by lia. exact H. Qed.

Lemma sp_ge48_4 : forall E p, (48 <= sp_tb E p /\ 48 <= sp_tb E (p + 1) /\ 48 <= sp_tb E (p + 2) /\ 48 <= sp_tb E (p + 3))%Z ->
  forall i, (p <= i < p + 4)%Z -> (48 <= sp_tb E i)%Z.
Proof.
  intros E p (H0 & H1 & H2 & H3) i Hi.
  assert (C : (i = p \/ i = p + 1 \/ i = p + 2 \/ i = p + 3)%Z) by lia.
  destruct C as [-> | [-> | [-> | ->]]]; assumption.
Qed.

Lemma sp_ge48_8 : forall E p,
  (48 <= sp_tb E p /\ 48 <= sp_tb E (p + 1) /\ 48 <= sp_tb E (p + 2) /\ 48 <= sp_tb E (p + 3) /\
   48 <= sp_tb E (p + 4) /\ 48 <= sp_tb E (p + 5) /\ 48 <= sp_tb E (p + 6) /\ 48 <= sp_tb E (p + 7))%Z ->
  forall i, (p <= i < p + 8)%Z -> (48 <= sp_tb E i)%Z.
Proof.
  intros E p (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7) i Hi.
  assert (C : (i = p \/ i = p + 1 \/ i = p + 2 \/ i = p + 3 \/ i = p + 4 \/ i = p + 5 \/ i = p + 6 \/ i = p + 7)%Z) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; assumption.
Qed.

Lemma sp_swar8 : forall E p X,
  Z.land (Z.lor X ((le8z (sp_tb E p) (sp_tb E (p + 1)) (sp_tb E (p + 2)) (sp_tb E (p + 3)) (sp_tb E (p + 4)) (sp_tb E (p + 5)) (sp_tb E (p + 6)) (sp_tb E (p + 7))
                    + 14974415777481871312) mod 18446744073709551616)) 9259542123273814144 = 0%Z ->
  forall i, (p <= i < p + 8)%Z -> (48 <= sp_tb E i)%Z.
Proof.
  intros E p X H. apply sp_ge48_8. eapply swar8_machine; [apply sp_tb_range .. | exact H].
Qed.

Lemma sp_swar4 : forall E p w hi X,
  w = (sp_tb E p + 256 * (sp_tb E (p + 1) + 256 * (sp_tb E (p + 2) + 256 * (sp_tb E (p + 3) + 256 * hi))))%Z ->
  Z.land (Z.lor X (bv_swrap 32 (w mod 18446744073709551616 + 18446744072901087184) mod 18446744073709551616)) 18446744071570489472 = 0%Z ->
  forall i, (p <= i < p + 4)%Z -> (48 <= sp_tb E i)%Z.
Proof.
  intros E p w hi X -> H. apply sp_ge48_4. rewrite bv_swrap32, swrap32_mod64 in H. unfold swrap32 in H.
  eapply swar4_ge48; [apply sp_tb_range .. | exact H].
Qed.

