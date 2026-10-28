(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3SoundK.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_avsA_b LibSegBa_avsB_b LibSegBa_avsC_b LibSegBa_avaA_b LibSegBa_avaA0_b LibSegBa_avaB_b LibSegBa_avaC_b LibSegBa_avaG_b LibSegBa_avaI_b LibSegBa_avaJ_b LibSegBa_avaBL_b LibSegBa_avaBL1_b LibSegBa_avaGL_b LibSegBa_avaGL1_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require PnAVu8GrowP_b.


Module PMAVLP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Notation aligned := PnAVu8GrowP_b.PMAVGP.aligned (only parsing).


Definition KS_avaBLoop : list nat := [2; 3; 4; 5; 6; 7; 8; 9; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Definition KS_avaGLoop : list nat := [3; 4; 5; 6; 8; 9; 12; 14; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%nat.
Definition KS_avaGLstep : list nat := [1; 2; 3; 4; 5; 6; 8; 9; 10; 12; 14; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%nat.



Lemma in_of_b (x : nat) (l : list nat) : existsb (Nat.eqb x) l = true -> In x l.
Proof. intros H. apply existsb_exists in H. destruct H as (y & Hy & E). apply Nat.eqb_eq in E. subst y. exact Hy. Qed.
Lemma incl_of_b (a b : list nat) : forallb (fun x => existsb (Nat.eqb x) b) a = true -> incl a b.
Proof. intros H x Hx. rewrite forallb_forall in H. apply in_of_b. exact (H x Hx). Qed.
Lemma KSB_0 : incl KS_avaBLoop PnAVu8GrowP_b.PMAVGP.KS_avaBL_0. Proof. apply incl_of_b. vm_compute. reflexivity. Qed.
Lemma KSB_1 : incl KS_avaBLoop PnAVu8GrowP_b.PMAVGP.KS_avaBL_1. Proof. apply incl_of_b. vm_compute. reflexivity. Qed.
Lemma KSB1_0 : incl KS_avaBLoop PnAVu8GrowP_b.PMAVGP.KS_avaBL1_0. Proof. apply incl_of_b. vm_compute. reflexivity. Qed.
Lemma KSB1_1 : incl KS_avaBLoop PnAVu8GrowP_b.PMAVGP.KS_avaBL1_1. Proof. apply incl_of_b. vm_compute. reflexivity. Qed.
Lemma KSG_0 : incl KS_avaGLoop PnAVu8GrowP_b.PMAVGP.KS_avaGL_0. Proof. apply incl_of_b. vm_compute. reflexivity. Qed.
Lemma KSG1_0 : incl KS_avaGLoop PnAVu8GrowP_b.PMAVGP.KS_avaGL1_0. Proof. apply incl_of_b. vm_compute. reflexivity. Qed.
Lemma KSGS_1 : incl KS_avaGLstep PnAVu8GrowP_b.PMAVGP.KS_avaGL_1. Proof. apply incl_of_b. vm_compute. reflexivity. Qed.
Lemma KSGS1_1 : incl KS_avaGLstep PnAVu8GrowP_b.PMAVGP.KS_avaGL1_1. Proof. apply incl_of_b. vm_compute. reflexivity. Qed.
Lemma KSG_S : incl KS_avaGLoop KS_avaGLstep. Proof. apply incl_of_b. vm_compute. reflexivity. Qed.

Lemma div8_bounds a : 0 <= a -> 0 <= a / 8 /\ 0 <= a - 8 * (a / 8) < 8.
Proof.
  intros H. pose proof (Z.div_mod a 8 ltac:(clear; lia)) as E. pose proof (Z.mod_pos_bound a 8 ltac:(clear; lia)) as Bd.
  split; [apply Z.div_pos; clear - H; lia | clear - E Bd; lia].
Qed.

Lemma condB_lt (p q y : Z) : 0 <= p -> 0 <= q -> 0 <= y -> q < y -> p + y < 2 ^ 64 ->
  ((((((p + q) mod 2 ^ 64) + 1) mod 2 ^ 64) - ((p + (y mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) < 1 -> q + 1 = y.
Proof.
  intros H0 H1 H2 H3 H4 C.
  rewrite (Z.mod_small (p + q) (2 ^ 64)) in C by (clear - H0 H1 H3 H4; lia).
  rewrite (Z.mod_small (p + q + 1) (2 ^ 64)) in C by (clear - H0 H1 H3 H4; lia).
  rewrite (Z.mod_small y (2 ^ 64)) in C by (clear - H0 H2 H4; lia).
  rewrite (Z.mod_small (p + y) (2 ^ 64)) in C by (clear - H0 H2 H4; lia).
  destruct (Z.eq_dec (q + 1) y) as [E | E]; [exact E | exfalso].
  assert (Dm : (p + q + 1 - (p + y)) mod 2 ^ 64 = p + q + 1 - (p + y) + 2 ^ 64).
  { symmetry. apply (Z.mod_unique_pos _ _ (-1)); clear - H0 H1 H2 H3 H4 E; lia. }
  rewrite Dm in C. clear - C H0 H1 H2 H3 H4 E. lia.
Qed.
Lemma condB_ge (p q y : Z) : 0 <= p -> 0 <= q -> 0 <= y -> q < y -> p + y < 2 ^ 64 ->
  1 <= ((((((p + q) mod 2 ^ 64) + 1) mod 2 ^ 64) - ((p + (y mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) -> q + 1 < y.
Proof.
  intros H0 H1 H2 H3 H4 C.
  rewrite (Z.mod_small (p + q) (2 ^ 64)) in C by (clear - H0 H1 H3 H4; lia).
  rewrite (Z.mod_small (p + q + 1) (2 ^ 64)) in C by (clear - H0 H1 H3 H4; lia).
  rewrite (Z.mod_small y (2 ^ 64)) in C by (clear - H0 H2 H4; lia).
  rewrite (Z.mod_small (p + y) (2 ^ 64)) in C by (clear - H0 H2 H4; lia).
  destruct (Z.eq_dec (q + 1) y) as [E | E]; [exfalso | clear - H3 E; lia].
  replace (p + q + 1 - (p + y)) with 0 in C by (clear - E; lia).
  rewrite Z.mod_0_l in C by (clear; lia). clear - C. lia.
Qed.

Lemma condG_val (L a b j : Z) : L = 2 ^ 64 - 1 -> 0 <= a -> 0 <= b -> 0 <= j -> j < a + b -> a + b < 2 ^ 64 ->
  ((((((a + ((b + ((L * j) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) + L) mod 2 ^ 64) - 0) mod 2 ^ 64) = a + b - j - 1.
Proof.
  intros HL H0 H1 H2 H3 H4.
  rewrite Z.sub_0_r, Z.mod_mod by (clear; lia).
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  rewrite <- (Z.add_assoc a ((b + L * j) mod 2 ^ 64) L), (Z.add_comm ((b + L * j) mod 2 ^ 64) L), Z.add_assoc, Zplus_mod_idemp_r.
  subst L. symmetry. apply (Z.mod_unique_pos _ _ (1 + j)); clear - H0 H1 H2 H3 H4; lia.
Qed.
Lemma condG_lt (L a b j : Z) : L = 2 ^ 64 - 1 -> 0 <= a -> 0 <= b -> 0 <= j -> j < a + b -> a + b < 2 ^ 64 ->
  ((((((a + ((b + ((L * j) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) + L) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1 -> j + 1 = a + b.
Proof. intros HL H0 H1 H2 H3 H4 C. rewrite (condG_val L a b j HL H0 H1 H2 H3 H4) in C. clear - C H3. lia. Qed.
Lemma condG_ge (L a b j : Z) : L = 2 ^ 64 - 1 -> 0 <= a -> 0 <= b -> 0 <= j -> j < a + b -> a + b < 2 ^ 64 ->
  1 <= ((((((a + ((b + ((L * j) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) + L) mod 2 ^ 64) - 0) mod 2 ^ 64) -> j + 1 < a + b.
Proof. intros HL H0 H1 H2 H3 H4 C. rewrite (condG_val L a b j HL H0 H1 H2 H3 H4) in C. clear - C H3. lia. Qed.

Section Carry.
Variables (M M1 : word -> option byte) (s0 n p q : Z).
Hypothesis HF : forall a : word, ~ (s0 <= bv_unsigned a < s0 + n) -> ~ (p <= bv_unsigned a < q) -> M1 a = M a.

Lemma c_fb : L5.frame_but [(s0, n); (p, q - p)] M M1.
Proof.
  intros x Hx. apply HF.
  - intros C. apply (Hx (s0, n)); [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; exact C].
  - intros C. apply (Hx (p, q - p)); [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - C; lia].
Qed.
Lemma c_out x : ~ (s0 <= x < s0 + n) -> ~ (p <= x < q) -> L5.outside [(s0, n); (p, q - p)] x.
Proof.
  intros H1 H2 r Hr. destruct Hr as [Er | [Er | []]]; subst r; unfold L5.in_rng; cbn [fst snd]; clear - H1 H2; lia.
Qed.
Lemma c_u64 a v : 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= s0 \/ s0 + n <= a) -> (q <= a \/ a + 8 <= p) ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v.
Proof.
  intros H0 H1 H2 H3 U. eapply L5.u64_at_frame; [exact c_fb | exact H0 | exact H1 | | exact U].
  intros i Hi. apply c_out; clear - H2 H3 Hi; lia.
Qed.
Lemma c_u32 a v : 0 <= a -> a + 4 <= 2 ^ 64 -> (a + 4 <= s0 \/ s0 + n <= a) -> (q <= a \/ a + 4 <= p) ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M1 a v.
Proof.
  intros H0 H1 H2 H3 U. unfold L5.u32_at in *.
  rewrite (L5.rdn_frame RSEGS M M1 _ c_fb 4%nat a H0); [exact U | change (Z.of_nat 4) with 4; clear - H1; lia |].
  intros i Hi. change (Z.of_nat 4) with 4 in Hi. apply c_out; clear - H2 H3 Hi; lia.
Qed.
Lemma c_u8 a v : 0 <= a < 2 ^ 64 -> ~ (s0 <= a < s0 + n) -> ~ (p <= a < q) -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M1 a v.
Proof.
  intros H0 H1 H2 U. eapply L5.u8_at_frame; [exact c_fb | clear - H0; lia | clear - H0; lia | apply c_out; assumption | exact U].
Qed.
Lemma c_img lo hi : 0 <= lo -> hi <= 2 ^ 64 -> (hi <= s0 \/ s0 + n <= lo) -> (q <= lo \/ hi <= p) ->
  L5.img_clear M lo hi -> L5.img_clear M1 lo hi.
Proof.
  intros H0 H1 H2 H3 C i Hi.
  rewrite HF; [exact (C i Hi) | |]; rewrite L5.unsigned_lit by (clear - H0 H1 Hi; lia); clear - H2 H3 Hi; lia.
Qed.
Lemma c_zeros a k : 0 <= a -> a + k <= 2 ^ 64 -> (a + k <= s0 \/ s0 + n <= a) -> mem_grows M M1 ->
  (forall x, p <= x < q -> L5.u8_at RSEGS M1 x 0) -> L5KA.zeros_at M a k -> L5KA.zeros_at M1 a k.
Proof.
  intros H0 H1 H2 G U Zs i Hi.
  destruct (Z_lt_le_dec (a + i) p) as [L1 | L1]; [| destruct (Z_lt_le_dec (a + i) q) as [L2 | L2]].
  - rewrite HF; [exact (Zs i Hi) | |]; rewrite L5.unsigned_lit by (clear - H0 H1 Hi; lia); clear - H2 Hi L1; lia.
  - pose proof (Zs i Hi) as Zi. pose proof (U (a + i) (conj L1 L2)) as Ui.
    assert (Dn : M1 (Z_to_bv 64 (a + i)) <> None) by exact (G (Z_to_bv 64 (a + i)) ltac:(rewrite Zi; discriminate)).
    unfold L5.u8_at in Ui. cbn [rdn] in Ui.
    destruct (M1 (Z_to_bv 64 (a + i))) as [b|]; [| exfalso; apply Dn; reflexivity].
    cbv beta iota in Ui. injection Ui as Hb. rewrite Hb. reflexivity.
  - rewrite HF; [exact (Zs i Hi) | |]; rewrite L5.unsigned_lit by (clear - H0 H1 Hi; lia); clear - H2 Hi L2; lia.
Qed.
Lemma c_sdw x (P : Z -> Prop) : 0 <= x < 2 ^ 64 -> ~ (s0 <= x < s0 + n) -> (forall y, p <= y < q -> L5.u8_at RSEGS M1 y 0) -> P 0 ->
  (exists s, L5.u8_at RSEGS M x s /\ P s) -> exists s, L5.u8_at RSEGS M1 x s /\ P s.
Proof.
  intros H0 H1 U P0 (s & Us & Ps).
  destruct (Z_lt_le_dec x p) as [L1 | L1]; [| destruct (Z_lt_le_dec x q) as [L2 | L2]].
  - exists s. split; [| exact Ps]. apply c_u8; [exact H0 | exact H1 | clear - L1; lia | exact Us].
  - exists 0. split; [apply U; split; assumption | exact P0].
  - exists s. split; [| exact Ps]. apply c_u8; [exact H0 | exact H1 | clear - L2; lia | exact Us].
Qed.
End Carry.

Definition vB (V : nat -> Z) (j s : Z) : nat -> Z := fun k => if Nat.eqb k 56 then j else if Nat.eqb k 55 then s else V k.


Definition KB (V : nat -> Z) : Prop :=
  (0 <= (V 2%nat) < 2 ^ 64) /\ (0 <= (V 37%nat) < 2 ^ 64) /\ (0 <= (V 40%nat) < 2 ^ 64) /\ (0 <= (V 41%nat) < 2 ^ 64) /\ (0 <= (V 42%nat) < 2 ^ 64) /\ (0 <= (V 43%nat) < 2 ^ 64) /\ (0 <= (V 48%nat) < 2 ^ 64) /\ (0 <= (V 49%nat) < 2 ^ 64) /\ (0 <= (V 50%nat) < 2 ^ 64) /\ (140735332487264 <= (V 2%nat) <= 140737488355328) /\ (aligned (V 2%nat) 16) /\ (6905856 <= (V 37%nat) <= 140737488355304) /\ (aligned (V 37%nat) 8) /\ ((2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784)) /\ ((((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128))) /\ (1 <= (V 43%nat) <= 134217728) /\ (4096 <= (V 40%nat) <= 140737488355328) /\ (0 <= (V 41%nat) <= 134217728) /\ ((((V 2%nat) - 128) + 128 <= (V 40%nat) \/ (V 40%nat) + (V 42%nat) <= ((V 2%nat) - 128))) /\ (1 <= (V 42%nat) <= 134217728) /\ (1 <= (((-1) * (V 41%nat)) + (V 42%nat)) <= 134217728) /\ ((V 41%nat) + (V 43%nat) <= (V 42%nat)).

Definition HB (V : nat -> Z) (j : Z) R M : Prop :=
  (0 <= j < 2 ^ 64) /\ (getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)) /\ (getr R (reg 8) = Z_to_bv 64 2147450880) /\ (getr R (reg 9) = Z_to_bv 64 ((V 40%nat) + ((V 41%nat) + (V 43%nat)))) /\ (getr R (reg 10) = Z_to_bv 64 ((V 40%nat) + j)) /\ (getr R (reg 11) = Z_to_bv 64 ((V 40%nat) + j)) /\ (getr R (reg 12) = Z_to_bv 64 18446744073709551615) /\ (getr R (reg 13) = Z_to_bv 64 ((((V 40%nat) + j) / 8) + 2147450880)) /\ (L5.img_clear M 1249280 1282048) /\ (L5.u64_at RSEGS M 1309752 2147450880) /\ (L5.u32_at RSEGS M 1309760 1) /\ (L5.writable RSEGS M ((V 2%nat) - 128) 128) /\ (L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3) /\ (L5.writable RSEGS M (V 37%nat) 24) /\ (L5.writable RSEGS M (V 40%nat) (V 42%nat)) /\ (L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512) /\ (L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))) /\ (L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 40%nat) + j)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 48) (V 37%nat)) /\ (0 <= j <= 134217728) /\ (0 <= (((-1) * (V 41%nat)) + j) <= 134217728) /\ (1 <= (((-1) * j) + ((V 41%nat) + (V 43%nat))) <= 134217728) /\ (1 <= (((-1) * j) + (V 42%nat)) <= 134217728).

Definition SB (V : nat -> Z) (j : Z) M : Prop :=
  (forall i, j <= i < (V 41%nat) + (V 43%nat) -> exists s, L5.u8_at RSEGS M ((((V 40%nat) + i) / 8) + 2147450880) s /\ (s = 0 \/ (1 <= s <= 7 /\ 1 <= s - Z.land ((V 40%nat) + i) 7))).

Definition XB (V : nat -> Z) (j : Z) : Prop :=
  (forall i, j <= i < (V 41%nat) + (V 43%nat) -> ~ (1249280 <= (V 40%nat) + i < 1282048) /\ ~ (1309752 <= (V 40%nat) + i < 1309752 + 8) /\ ~ (1309760 <= (V 40%nat) + i < 1309760 + 4)).

Definition CB (V : nat -> Z) (j : Z) fx R M : Prop :=
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + j) <= bv_unsigned a < (V 40%nat) + ((V 41%nat) + (V 43%nat))) -> M' a = M a)
    /\ msteps RSEGS (st fx R 0xb5a34 M) (st fx' R' 0xb5fbc M')
    /\ (forall x, In x KS_avaBLoop -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 1) = Z_to_bv 64 744044
    /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 48)
    /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 37%nat)
    /\ (forall i, j <= i < (V 41%nat) + (V 43%nat) -> L5.u8_at RSEGS M' ((V 40%nat) + i) 0).

Definition StepB (V : nat -> Z) : Prop :=
  forall j fx R M, KB V -> HB V j R M ->
  (exists s, L5.u8_at RSEGS M ((((V 40%nat) + j) / 8) + 2147450880) s /\ (s = 0 \/ (1 <= s <= 7 /\ 1 <= s - Z.land ((V 40%nat) + j) 7))) ->
  exists fx1 R1 M1, mem_grows M M1
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ ((V 40%nat) + j <= bv_unsigned a < (V 40%nat) + j + 1) -> M1 a = M a)
    /\ L5.u8_at RSEGS M1 ((V 40%nat) + j) 0
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 8) (V 48%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 16) (V 49%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 24) (V 50%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 40) ((V 40%nat) + (j + 1))
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 48) (V 37%nat)
    /\ ((msteps RSEGS (st fx R 0xb5a34 M) (st fx1 R1 0xb5fbc M1)
         /\ (forall x, In x KS_avaBLoop -> getr R1 (reg x) = getr R (reg x))
         /\ getr R1 (reg 1) = Z_to_bv 64 744044
         /\ getr R1 (reg 10) = Z_to_bv 64 ((V 2%nat) - 48)
         /\ getr R1 (reg 11) = Z_to_bv 64 ((V 40%nat) + (j + 1))
         /\ j + 1 = (V 41%nat) + (V 43%nat))
      \/ (msteps RSEGS (st fx R 0xb5a34 M) (st fx1 R1 0xb5a34 M1)
         /\ (forall x, In x KS_avaBLoop -> getr R1 (reg x) = getr R (reg x))
         /\ getr R1 (reg 10) = Z_to_bv 64 ((V 40%nat) + (j + 1))
         /\ getr R1 (reg 11) = Z_to_bv 64 ((V 40%nat) + (j + 1))
         /\ getr R1 (reg 13) = Z_to_bv 64 ((((V 40%nat) + (j + 1)) / 8) + 2147450880)
         /\ j + 1 < (V 41%nat) + (V 43%nat))).

Lemma stepB_ok (V : nat -> Z) : StepB V.
Proof.
  intros j fx R M K H (s & Us & Ps).
  destruct K as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b21 & b22 & b24 & b25 & b26 & b29 & b30 & b31 & b32 & b34 & b35 & b36 & bD).
  destruct H as (b10 & b11 & b12 & b13 & b14 & b15 & b16 & b17 & b18 & b19 & b20 & b23 & b27 & b28 & b33 & b37 & b38 & b39 & b40 & b41 & b42 & b43 & b44 & b45 & b46 & b47).
  assert (R55 : 0 <= s < 2 ^ 64) by (clear - Ps; destruct Ps as [P0 | (P1 & _)]; lia).
  assert (LN : 0 <= Z.land ((V 40%nat) + j) 7) by (apply Z.land_nonneg; right; clear; lia).
  destruct Ps as [P0 | (P1 & P2)].
  -
    pose proof (PnAVu8GrowP_b.PMAVGP.avaBL_conc fx R M (vB V j s) b0 b1 b2 b3 b4 b5 b6 b7 b8 R55 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 Us ltac:(cbn [vB Nat.eqb]; clear - P0; lia)) as E.
    cbn [vB Nat.eqb] in E.
    destruct E as (fx1 & R1 & M1 & G & F & FZ & [E0 | E1]).
    + destruct E0 as (MS & KP & r1 & r10 & r11 & r13 & C & c40 & U & c8 & c16 & c24 & c32 & c48).
      exists fx1, R1, M1.
      split; [exact G|]. split; [intros a Ha Hb; apply F; [exact Ha | intros Cc; apply Hb; clear - Cc; lia]|].
      split; [exact U|]. split; [exact c8|]. split; [exact c16|]. split; [exact c24|]. split; [exact c32|].
      split; [replace ((V 40%nat) + (j + 1)) with (((V 40%nat) + j) + 1) by (clear; lia); exact c40|]. split; [exact c48|].
      left. split; [exact MS|]. split; [intros x Hx; exact (KP x (KSB_0 x Hx))|].
      split; [exact r1|]. split; [exact r10|]. split; [replace ((V 40%nat) + (j + 1)) with (((V 40%nat) + j) + 1) by (clear; lia); exact r11|].
      apply (condB_lt (V 40%nat) j ((V 41%nat) + (V 43%nat))); [clear - b2; lia | clear - b44; lia | clear - b3 b5; lia | clear - b46; lia | clear - b31 b35 bD; lia | exact C].
    + destruct E1 as (MS & KP & r10 & r11 & r13 & C & c40 & U & c8 & c16 & c24 & c32 & c48).
      exists fx1, R1, M1.
      split; [exact G|]. split; [intros a Ha Hb; apply F; [exact Ha | intros Cc; apply Hb; clear - Cc; lia]|].
      split; [exact U|]. split; [exact c8|]. split; [exact c16|]. split; [exact c24|]. split; [exact c32|].
      split; [replace ((V 40%nat) + (j + 1)) with (((V 40%nat) + j) + 1) by (clear; lia); exact c40|]. split; [exact c48|].
      right. split; [exact MS|]. split; [intros x Hx; exact (KP x (KSB_1 x Hx))|].
      split; [replace ((V 40%nat) + (j + 1)) with (((V 40%nat) + j) + 1) by (clear; lia); exact r10|]. split; [replace ((V 40%nat) + (j + 1)) with (((V 40%nat) + j) + 1) by (clear; lia); exact r11|]. split; [replace ((V 40%nat) + (j + 1)) with (((V 40%nat) + j) + 1) by (clear; lia); exact r13|].
      apply (condB_ge (V 40%nat) j ((V 41%nat) + (V 43%nat))); [clear - b2; lia | clear - b44; lia | clear - b3 b5; lia | clear - b46; lia | clear - b31 b35 bD; lia | exact C].
  -
    pose proof (PnAVu8GrowP_b.PMAVGP.avaBL1_conc fx R M (vB V j s) b0 b1 b2 b3 b4 b5 b6 b7 b8 R55 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 Us ltac:(cbn [vB Nat.eqb]; clear - P1; lia) ltac:(cbn [vB Nat.eqb]; clear - P1 P2 LN; lia)) as E.
    cbn [vB Nat.eqb] in E.
    destruct E as (fx1 & R1 & M1 & G & F & FZ & [E0 | E1]).
    + destruct E0 as (MS & KP & r1 & r10 & r11 & r13 & C & c40 & U & c8 & c16 & c24 & c32 & c48).
      exists fx1, R1, M1.
      split; [exact G|]. split; [intros a Ha Hb; apply F; [exact Ha | intros Cc; apply Hb; clear - Cc; lia]|].
      split; [exact U|]. split; [exact c8|]. split; [exact c16|]. split; [exact c24|]. split; [exact c32|].
      split; [replace ((V 40%nat) + (j + 1)) with (((V 40%nat) + j) + 1) by (clear; lia); exact c40|]. split; [exact c48|].
      left. split; [exact MS|]. split; [intros x Hx; exact (KP x (KSB1_0 x Hx))|].
      split; [exact r1|]. split; [exact r10|]. split; [replace ((V 40%nat) + (j + 1)) with (((V 40%nat) + j) + 1) by (clear; lia); exact r11|].
      apply (condB_lt (V 40%nat) j ((V 41%nat) + (V 43%nat))); [clear - b2; lia | clear - b44; lia | clear - b3 b5; lia | clear - b46; lia | clear - b31 b35 bD; lia | exact C].
    + destruct E1 as (MS & KP & r10 & r11 & r13 & C & c40 & U & c8 & c16 & c24 & c32 & c48).
      exists fx1, R1, M1.
      split; [exact G|]. split; [intros a Ha Hb; apply F; [exact Ha | intros Cc; apply Hb; clear - Cc; lia]|].
      split; [exact U|]. split; [exact c8|]. split; [exact c16|]. split; [exact c24|]. split; [exact c32|].
      split; [replace ((V 40%nat) + (j + 1)) with (((V 40%nat) + j) + 1) by (clear; lia); exact c40|]. split; [exact c48|].
      right. split; [exact MS|]. split; [intros x Hx; exact (KP x (KSB1_1 x Hx))|].
      split; [replace ((V 40%nat) + (j + 1)) with (((V 40%nat) + j) + 1) by (clear; lia); exact r10|]. split; [replace ((V 40%nat) + (j + 1)) with (((V 40%nat) + j) + 1) by (clear; lia); exact r11|]. split; [replace ((V 40%nat) + (j + 1)) with (((V 40%nat) + j) + 1) by (clear; lia); exact r13|].
      apply (condB_ge (V 40%nat) j ((V 41%nat) + (V 43%nat))); [clear - b2; lia | clear - b44; lia | clear - b3 b5; lia | clear - b46; lia | clear - b31 b35 bD; lia | exact C].
Qed.

Lemma loopB_gen (V : nat -> Z) : StepB V -> KB V ->
  forall (n : nat) (j : Z) fx R M, Z.of_nat n = (V 41%nat) + (V 43%nat) - j ->
  HB V j R M -> SB V j M -> XB V j -> CB V j fx R M.
Proof.
  intros ST K. pose proof K as K0. destruct K0 as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b21 & b22 & b24 & b25 & b26 & b29 & b30 & b31 & b32 & b34 & b35 & b36 & bD).
  pose proof (div8_bounds (V 37%nat) ltac:(clear - b1; lia)) as d37.
  pose proof (div8_bounds (V 2%nat) ltac:(clear - b0; lia)) as d2.
  induction n as [|n IH]; intros j fx R M En Hh Hs Hx.
  { destruct Hh as (b10 & b11 & b12 & b13 & b14 & b15 & b16 & b17 & b18 & b19 & b20 & b23 & b27 & b28 & b33 & b37 & b38 & b39 & b40 & b41 & b42 & b43 & b44 & b45 & b46 & b47). exfalso. cbn [Z.of_nat] in En. clear - En b46. lia. }
  pose proof Hh as Hh0. destruct Hh0 as (b10 & b11 & b12 & b13 & b14 & b15 & b16 & b17 & b18 & b19 & b20 & b23 & b27 & b28 & b33 & b37 & b38 & b39 & b40 & b41 & b42 & b43 & b44 & b45 & b46 & b47).
  rewrite Nat2Z.inj_succ in En. unfold Z.succ in En.
  destruct (Hs j ltac:(clear - b46; lia)) as (s & Us & Ps).
  destruct (Hx j ltac:(clear - b46; lia)) as (x1 & x2 & x3).
  destruct (ST j fx R M K Hh (ex_intro _ s (conj Us Ps))) as (fx1 & R1 & M1 & G1 & F1 & U1 & c8 & c16 & c24 & c32 & c40 & c48 & [E0 | E1]).
  - destruct E0 as (MS & KP & r1 & r10 & r11 & Ej).
    exists fx1, R1, M1.
    split; [exact G1|].
    split; [intros a Ha Hb; apply F1; [exact Ha | intros Cc; apply Hb; clear - Cc b46; lia]|].
    split; [exact MS|]. split; [exact KP|]. split; [exact r1|]. split; [exact r10|].
    split; [replace ((V 40%nat) + ((V 41%nat) + (V 43%nat))) with ((V 40%nat) + (j + 1)) by (clear - Ej; lia); exact r11|].
    split; [exact c8|]. split; [exact c16|]. split; [exact c24|]. split; [exact c32|].
    split; [replace ((V 40%nat) + ((V 41%nat) + (V 43%nat))) with ((V 40%nat) + (j + 1)) by (clear - Ej; lia); exact c40|]. split; [exact c48|].
    intros i Hi. replace i with j by (clear - Hi Ej; lia). exact U1.
  - destruct E1 as (MS & KP & r10 & r11 & r13 & Ej).
    assert (W : forall y, (V 40%nat) + j <= y < (V 40%nat) + j + 1 -> L5.u8_at RSEGS M1 y 0).
    { intros y Hy. replace y with ((V 40%nat) + j) by (clear - Hy; lia). exact U1. }
    assert (Hh1 : HB V (j + 1) R1 M1).
    { unfold HB.
      split; [clear - b44; lia|].
      split; [rewrite (KP 2%nat (in_of_b 2%nat KS_avaBLoop eq_refl)); exact b11|].
      split; [rewrite (KP 8%nat (in_of_b 8%nat KS_avaBLoop eq_refl)); exact b12|].
      split; [rewrite (KP 9%nat (in_of_b 9%nat KS_avaBLoop eq_refl)); exact b13|].
      split; [exact r10|].
      split; [exact r11|].
      split; [rewrite (KP 12%nat (in_of_b 12%nat KS_avaBLoop eq_refl)); exact b16|].
      split; [exact r13|].
      split; [apply (c_img _ _ _ _ _ _ F1); [clear; lia | clear; lia | clear - b21; lia | clear - x1; lia | exact b18]|].
      split; [apply (c_u64 _ _ _ _ _ _ F1); [clear; lia | clear; lia | clear - b21; lia | clear - x2; lia | exact b19]|].
      split; [apply (c_u32 _ _ _ _ _ _ F1); [clear; lia | clear; lia | clear - b21; lia | clear - x3; lia | exact b20]|].
      split; [eapply L5.writable_grows; [exact G1 | exact b23]|].
      split; [apply (c_zeros _ _ _ _ _ _ F1); [clear - d37; lia | clear - d37 b24; lia | clear - d37 b24 b21; lia | exact G1 | exact W | exact b27]|].
      split; [eapply L5.writable_grows; [exact G1 | exact b28]|].
      split; [eapply L5.writable_grows; [exact G1 | exact b33]|].
      split; [apply (c_zeros _ _ _ _ _ _ F1); [clear - d2; lia | clear - d2 b21; lia | clear - d2 b21; lia | exact G1 | exact W | exact b37]|].
      split; [exact c8|].
      split; [exact c16|].
      split; [exact c24|].
      split; [exact c32|].
      split; [exact c40|].
      split; [exact c48|].
      split; [clear - b44 Ej b35 bD; lia|].
      split; [clear - b45 Ej b35 bD b32; lia|].
      split; [clear - Ej b46; lia|].
      clear - Ej bD b47; lia.
    }
    assert (Hs1 : SB V (j + 1) M1).
    { intros i Hi. destruct (Hs i ltac:(clear - Hi; lia)) as (s' & Us' & Ps').
      pose proof (div8_bounds ((V 40%nat) + i) ltac:(clear - b2 Hi b44; lia)) as di.
      apply (c_sdw _ _ _ _ _ _ F1 _ (fun t => t = 0 \/ (1 <= t <= 7 /\ 1 <= t - Z.land ((V 40%nat) + i) 7))).
      - clear - di b31 b35 bD Hi b44; lia.
      - clear - di b31 b35 bD Hi b44 b21; lia.
      - exact W.
      - left; reflexivity.
      - exists s'; split; [exact Us' | exact Ps']. }
    assert (Hx1 : XB V (j + 1)) by (intros i Hi; exact (Hx i ltac:(clear - Hi; lia))).
    destruct (IH (j + 1) fx1 R1 M1 ltac:(clear - En; lia) Hh1 Hs1 Hx1)
      as (fx2 & R2 & M2 & G2 & F2 & MS2 & KP2 & r1' & r10' & r11' & e8 & e16 & e24 & e32 & e40 & e48 & Z2).
    exists fx2, R2, M2.
    split; [exact (mem_grows_trans _ _ _ G1 G2)|].
    split.
    { intros a Ha Hb. rewrite (F2 a Ha); [apply F1; [exact Ha | intros Cc; apply Hb; clear - Cc b46; lia] | intros Cc; apply Hb; clear - Cc; lia]. }
    split; [eapply CatSim.msteps_trans; [exact MS | exact MS2]|].
    split; [intros x Hx2; rewrite (KP2 x Hx2); exact (KP x Hx2)|].
    split; [exact r1'|]. split; [exact r10'|]. split; [exact r11'|].
    split; [exact e8|]. split; [exact e16|]. split; [exact e24|]. split; [exact e32|]. split; [exact e40|]. split; [exact e48|].
    intros i Hi. destruct (Z.eq_dec i j) as [Ei | Ei].
    + subst i. apply (c_u8 _ _ _ _ _ _ F2); [clear - b2 b31 b35 bD b44 b46; lia | clear - b34 b44 b46 bD; lia | clear; lia | exact U1].
    + apply Z2. clear - Hi Ei; lia.
Qed.

Lemma avaBLoop_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  0 <= (V 37%nat) < 2 ^ 64 ->
  0 <= (V 40%nat) < 2 ^ 64 ->
  0 <= (V 41%nat) < 2 ^ 64 ->
  0 <= (V 42%nat) < 2 ^ 64 ->
  0 <= (V 43%nat) < 2 ^ 64 ->
  0 <= (V 48%nat) < 2 ^ 64 ->
  0 <= (V 49%nat) < 2 ^ 64 ->
  0 <= (V 50%nat) < 2 ^ 64 ->
  0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) ->
  getr R (reg 8) = Z_to_bv 64 2147450880 ->
  getr R (reg 9) = Z_to_bv 64 ((V 40%nat) + ((V 41%nat) + (V 43%nat))) ->
  getr R (reg 10) = Z_to_bv 64 ((V 40%nat) + (V 56%nat)) ->
  getr R (reg 11) = Z_to_bv 64 ((V 40%nat) + (V 56%nat)) ->
  getr R (reg 12) = Z_to_bv 64 18446744073709551615 ->
  getr R (reg 13) = Z_to_bv 64 ((((V 40%nat) + (V 56%nat)) / 8) + 2147450880) ->
  L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 ->
  L5.u32_at RSEGS M 1309760 1 ->
  140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 ->
  L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  6905856 <= (V 37%nat) <= 140737488355304 ->
  aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 ->
  L5.writable RSEGS M (V 37%nat) 24 ->
  (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128)) ->
  1 <= (V 43%nat) <= 134217728 ->
  4096 <= (V 40%nat) <= 140737488355328 ->
  0 <= (V 41%nat) <= 134217728 ->
  L5.writable RSEGS M (V 40%nat) (V 42%nat) ->
  (((V 2%nat) - 128) + 128 <= (V 40%nat) \/ (V 40%nat) + (V 42%nat) <= ((V 2%nat) - 128)) ->
  1 <= (V 42%nat) <= 134217728 ->
  1 <= (((-1) * (V 41%nat)) + (V 42%nat)) <= 134217728 ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 40%nat) + (V 56%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 37%nat) ->
  0 <= (V 56%nat) <= 134217728 ->
  0 <= (((-1) * (V 41%nat)) + (V 56%nat)) <= 134217728 ->
  1 <= (((-1) * (V 56%nat)) + ((V 41%nat) + (V 43%nat))) <= 134217728 ->
  1 <= (((-1) * (V 56%nat)) + (V 42%nat)) <= 134217728 ->
  (forall i, (V 56%nat) <= i < (V 41%nat) + (V 43%nat) -> exists s, L5.u8_at RSEGS M ((((V 40%nat) + i) / 8) + 2147450880) s /\ (s = 0 \/ (1 <= s <= 7 /\ 1 <= s - Z.land ((V 40%nat) + i) 7))) ->
  (forall i, (V 56%nat) <= i < (V 41%nat) + (V 43%nat) -> ~ (1249280 <= (V 40%nat) + i < 1282048) /\ ~ (1309752 <= (V 40%nat) + i < 1309752 + 8) /\ ~ (1309760 <= (V 40%nat) + i < 1309760 + 4)) ->
  (V 41%nat) + (V 43%nat) <= (V 42%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + (V 56%nat)) <= bv_unsigned a < (V 40%nat) + ((V 41%nat) + (V 43%nat))) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ (((V 40%nat) + (V 56%nat)) <= i < (V 40%nat) + ((V 41%nat) + (V 43%nat))) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ msteps RSEGS (st fx R 0xb5a34 M) (st fx' R' 0xb5fbc M')
    /\ (forall x, In x KS_avaBLoop -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 1) = Z_to_bv 64 744044
    /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 48)
    /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 37%nat)
    /\ (forall i, (V 56%nat) <= i < (V 41%nat) + (V 43%nat) -> L5.u8_at RSEGS M' ((V 40%nat) + i) 0).

Proof.
  intros p0 p1 p2 p3 p4 p5 p6 p7 p8 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 pS pX pD.
  destruct (loopB_gen V (stepB_ok V) (conj p0 (conj p1 (conj p2 (conj p3 (conj p4 (conj p5 (conj p6 (conj p7 (conj p8 (conj p21 (conj p22 (conj p24 (conj p25 (conj p26 (conj p29 (conj p30 (conj p31 (conj p32 (conj p34 (conj p35 (conj p36 pD))))))))))))))))))))) (Z.to_nat ((V 41%nat) + (V 43%nat) - (V 56%nat))) (V 56%nat) fx R M
    ltac:(rewrite Z2Nat.id; [reflexivity | clear - p46; lia]) (conj p10 (conj p11 (conj p12 (conj p13 (conj p14 (conj p15 (conj p16 (conj p17 (conj p18 (conj p19 (conj p20 (conj p23 (conj p27 (conj p28 (conj p33 (conj p37 (conj p38 (conj p39 (conj p40 (conj p41 (conj p42 (conj p43 (conj p44 (conj p45 (conj p46 p47))))))))))))))))))))))))) pS pX)
    as (fx' & R' & M' & G & F & MS & KP & r1 & r10 & r11 & c8 & c16 & c24 & c32 & c40 & c48 & Zs).
  exists fx', R', M'.
  split; [exact G|]. split; [exact F|].
  split; [intros i Hi Ha Hb; apply F; rewrite L5.unsigned_lit by exact Hi; assumption|].
  split; [exact MS|]. split; [exact KP|]. split; [exact r1|]. split; [exact r10|]. split; [exact r11|].
  split; [exact c8|]. split; [exact c16|]. split; [exact c24|]. split; [exact c32|]. split; [exact c40|]. split; [exact c48|].
  exact Zs.
Qed.

Definition KG (V : nat -> Z) : Prop :=
  (0 <= (V 2%nat) < 2 ^ 64) /\ (0 <= (V 37%nat) < 2 ^ 64) /\ (0 <= (V 41%nat) < 2 ^ 64) /\ (0 <= (V 43%nat) < 2 ^ 64) /\ (0 <= (V 44%nat) < 2 ^ 64) /\ (0 <= (V 46%nat) < 2 ^ 64) /\ (0 <= (V 48%nat) < 2 ^ 64) /\ (0 <= (V 49%nat) < 2 ^ 64) /\ (0 <= (V 50%nat) < 2 ^ 64) /\ (0 <= (V 51%nat) < 2 ^ 64) /\ (0 <= (V 52%nat) < 2 ^ 64) /\ (0 <= (V 53%nat) < 2 ^ 64) /\ (0 <= (V 54%nat) < 2 ^ 64) /\ (140735332487264 <= (V 2%nat) <= 140737488355328) /\ (aligned (V 2%nat) 16) /\ (6905856 <= (V 37%nat) <= 140737488355304) /\ (aligned (V 37%nat) 8) /\ ((2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784)) /\ ((((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128))) /\ (1 <= (V 43%nat) <= 134217728) /\ (4096 <= (V 44%nat) <= 140737488355328) /\ (0 <= (V 41%nat) <= 134217728) /\ (1 <= (V 46%nat) <= 134217728) /\ ((((V 2%nat) - 128) + 128 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= ((V 2%nat) - 128))) /\ ((2147446784 + 17592186048512 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= 2147446784)) /\ (((V 37%nat) + 24 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= (V 37%nat))) /\ (1 <= (((-1) * (V 41%nat)) + (V 46%nat)) <= 134217728) /\ ((V 41%nat) + (V 43%nat) <= (V 46%nat)).

Definition HG (V : nat -> Z) (j : Z) R M : Prop :=
  (0 <= j < 2 ^ 64) /\ (getr R (reg 1) = Z_to_bv 64 743604) /\ (getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)) /\ (getr R (reg 5) = Z_to_bv 64 ((((V 2%nat) - 32) / 8) + 2147450880)) /\ (getr R (reg 6) = Z_to_bv 64 18446744073709551615) /\ (getr R (reg 7) = Z_to_bv 64 ((((V 44%nat) + j) / 8) + 2147450880)) /\ (getr R (reg 8) = Z_to_bv 64 (V 37%nat)) /\ (getr R (reg 9) = Z_to_bv 64 (V 43%nat)) /\ (getr R (reg 10) = Z_to_bv 64 ((V 2%nat) - 48)) /\ (getr R (reg 11) = Z_to_bv 64 (((V 41%nat) + (V 43%nat)) - j)) /\ (getr R (reg 12) = Z_to_bv 64 ((V 2%nat) - 32)) /\ (getr R (reg 13) = Z_to_bv 64 ((V 44%nat) + j)) /\ (getr R (reg 14) = Z_to_bv 64 ((((V 2%nat) - 48) / 8) + 2147450880)) /\ (getr R (reg 15) = Z_to_bv 64 2147450880) /\ (getr R (reg 16) = Z_to_bv 64 ((V 44%nat) + j)) /\ (getr R (reg 17) = Z_to_bv 64 ((V 41%nat) + ((V 43%nat) + (V 44%nat)))) /\ (getr R (reg 18) = Z_to_bv 64 (V 51%nat)) /\ (getr R (reg 19) = Z_to_bv 64 (V 52%nat)) /\ (getr R (reg 20) = Z_to_bv 64 (V 53%nat)) /\ (getr R (reg 21) = Z_to_bv 64 (V 54%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 72) 743604) /\ (L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 44%nat) + (V 46%nat))) /\ (L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 41%nat) + (V 44%nat))) /\ (L5.u64_at RSEGS M ((V 2%nat) - 48) ((V 41%nat) + (V 44%nat))) /\ (L5.u64_at RSEGS M ((V 2%nat) - 64) (V 44%nat)) /\ (L5.img_clear M 1249280 1282048) /\ (L5.u64_at RSEGS M 1309752 2147450880) /\ (L5.u32_at RSEGS M 1309760 1) /\ (L5.writable RSEGS M ((V 2%nat) - 128) 128) /\ (L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3) /\ (L5.writable RSEGS M (V 37%nat) 24) /\ (L5.writable RSEGS M (V 44%nat) (V 46%nat)) /\ (L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512) /\ (L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 32) (V 37%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 80) (V 37%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 88) (V 43%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 96) (V 51%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 104) (V 52%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 112) (V 53%nat)) /\ (L5.u64_at RSEGS M ((V 2%nat) - 120) (V 54%nat)) /\ (0 <= j <= 134217728) /\ (0 <= (((-1) * (V 41%nat)) + j) <= 134217728) /\ (1 <= (((-1) * j) + ((V 41%nat) + (V 43%nat))) <= 134217728) /\ (1 <= (((-1) * j) + (V 46%nat)) <= 134217728).

Definition SG (V : nat -> Z) (j : Z) M : Prop :=
  (forall i, j <= i < (V 41%nat) + (V 43%nat) -> exists s, L5.u8_at RSEGS M ((((V 44%nat) + i) / 8) + 2147450880) s /\ (s = 0 \/ (1 <= s <= 7 /\ 1 <= s - Z.land ((V 44%nat) + i) 7))).

Definition XG (V : nat -> Z) (j : Z) : Prop :=
  (forall i, j <= i < (V 41%nat) + (V 43%nat) -> ~ (1249280 <= (V 44%nat) + i < 1282048) /\ ~ (1309752 <= (V 44%nat) + i < 1309752 + 8) /\ ~ (1309760 <= (V 44%nat) + i < 1309760 + 4)).

Definition CG (V : nat -> Z) (j : Z) fx R M : Prop :=
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 44%nat) + j) <= bv_unsigned a < (V 44%nat) + ((V 41%nat) + (V 43%nat))) -> M' a = M a)
    /\ msteps RSEGS (st fx R 0xb5c54 M) (st fx' R' 0xb5cb8 M')
    /\ (forall x, In x KS_avaGLoop -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 1) = Z_to_bv 64 743616
    /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
    /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
    /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 64)
    /\ getr R' (reg 13) = Z_to_bv 64 ((V 44%nat) + ((V 41%nat) + (V 43%nat)))
    /\ getr R' (reg 16) = Z_to_bv 64 ((V 41%nat) + ((V 43%nat) + (V 44%nat)))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((V 41%nat) + ((V 43%nat) + (V 44%nat)))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 743604
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 44%nat) + (V 46%nat))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 41%nat) + (V 44%nat))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 44%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 37%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 37%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 51%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 52%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 53%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 54%nat)
    /\ (forall i, j <= i < (V 41%nat) + (V 43%nat) -> L5.u8_at RSEGS M' ((V 44%nat) + i) 0).

Definition StepG (V : nat -> Z) : Prop :=
  forall j fx R M, KG V -> HG V j R M ->
  (exists s, L5.u8_at RSEGS M ((((V 44%nat) + j) / 8) + 2147450880) s /\ (s = 0 \/ (1 <= s <= 7 /\ 1 <= s - Z.land ((V 44%nat) + j) 7))) ->
  exists fx1 R1 M1, mem_grows M M1
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ ((V 44%nat) + j <= bv_unsigned a < (V 44%nat) + j + 1) -> M1 a = M a)
    /\ L5.u8_at RSEGS M1 ((V 44%nat) + j) 0
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 72) 743604
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 40) ((V 44%nat) + (V 46%nat))
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 56) ((V 41%nat) + (V 44%nat))
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 64) (V 44%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 8) (V 48%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 16) (V 49%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 24) (V 50%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 32) (V 37%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 80) (V 37%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 88) (V 43%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 96) (V 51%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 104) (V 52%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 112) (V 53%nat)
    /\ L5.u64_at RSEGS M1 ((V 2%nat) - 120) (V 54%nat)
    /\ getr R1 (reg 13) = Z_to_bv 64 ((V 44%nat) + (j + 1))
    /\ ((msteps RSEGS (st fx R 0xb5c54 M) (st fx1 R1 0xb5cb8 M1)
         /\ (forall x, In x KS_avaGLoop -> getr R1 (reg x) = getr R (reg x))
         /\ getr R1 (reg 1) = Z_to_bv 64 743616
         /\ getr R1 (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
         /\ getr R1 (reg 10) = Z_to_bv 64 (V 37%nat)
         /\ getr R1 (reg 11) = Z_to_bv 64 ((V 2%nat) - 64)
         /\ getr R1 (reg 16) = Z_to_bv 64 ((V 41%nat) + ((V 43%nat) + (V 44%nat)))
         /\ L5.u64_at RSEGS M1 ((V 2%nat) - 48) ((V 41%nat) + ((V 43%nat) + (V 44%nat)))
         /\ j + 1 = (V 41%nat) + (V 43%nat))
      \/ (msteps RSEGS (st fx R 0xb5c54 M) (st fx1 R1 0xb5c54 M1)
         /\ (forall x, In x KS_avaGLstep -> getr R1 (reg x) = getr R (reg x))
         /\ getr R1 (reg 7) = Z_to_bv 64 ((((V 44%nat) + (j + 1)) / 8) + 2147450880)
         /\ getr R1 (reg 11) = Z_to_bv 64 (((V 41%nat) + (V 43%nat)) - (j + 1))
         /\ getr R1 (reg 16) = Z_to_bv 64 ((V 44%nat) + (j + 1))
         /\ L5.u64_at RSEGS M1 ((V 2%nat) - 48) ((V 41%nat) + (V 44%nat))
         /\ j + 1 < (V 41%nat) + (V 43%nat))).

Lemma stepG_ok (V : nat -> Z) : StepG V.
Proof.
  intros j fx R M K H (s & Us & Ps).
  destruct K as (g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & g9 & g10 & g11 & g12 & g42 & g43 & g45 & g46 & g47 & g50 & g51 & g52 & g53 & g54 & g56 & g57 & g58 & g59 & gD).
  destruct H as (g14 & g15 & g16 & g17 & g18 & g19 & g20 & g21 & g22 & g23 & g24 & g25 & g26 & g27 & g28 & g29 & g30 & g31 & g32 & g33 & g34 & g35 & g36 & g37 & g38 & g39 & g40 & g41 & g44 & g48 & g49 & g55 & g60 & g61 & g62 & g63 & g64 & g65 & g66 & g67 & g68 & g69 & g70 & g71 & g72 & g73 & g74).
  assert (R55 : 0 <= s < 2 ^ 64) by (clear - Ps; destruct Ps as [P0 | (P1 & _)]; lia).
  assert (LN : 0 <= Z.land ((V 44%nat) + j) 7) by (apply Z.land_nonneg; right; clear; lia).
  destruct Ps as [P0 | (P1 & P2)].
  -
    pose proof (PnAVu8GrowP_b.PMAVGP.avaGL_conc fx R M (vB V j s) g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 R55 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 Us ltac:(cbn [vB Nat.eqb]; clear - P0; lia)) as E.
    cbn [vB Nat.eqb] in E.
    destruct E as (fx1 & R1 & M1 & G & F & FZ & [E0 | E1]).
    + destruct E0 as (MS & KP & r1 & r2 & r7 & r10 & r11 & r13 & r16 & c48 & C & U & c72 & c40 & c56 & c64 & c8 & c16 & c24 & c32 & c80 & c88 & c96 & c104 & c112 & c120).
      exists fx1, R1, M1.
      split; [exact G|]. split; [intros a Ha Hb; apply F; [exact Ha | intros Cc; apply Hb; clear - Cc; lia]|].
      split; [exact U|]. split; [exact c72|]. split; [exact c40|]. split; [exact c56|]. split; [exact c64|]. split; [exact c8|]. split; [exact c16|]. split; [exact c24|]. split; [exact c32|]. split; [exact c80|]. split; [exact c88|]. split; [exact c96|]. split; [exact c104|]. split; [exact c112|]. split; [exact c120|].
      split; [replace ((V 44%nat) + (j + 1)) with (((V 44%nat) + j) + 1) by (clear; lia); exact r13|].
      left. split; [exact MS|]. split; [intros x Hx; exact (KP x (KSG_0 x Hx))|].
      split; [exact r1|]. split; [exact r2|]. split; [exact r10|]. split; [exact r11|]. split; [exact r16|]. split; [exact c48|].
      apply (condG_lt 18446744073709551615 (V 41%nat) (V 43%nat) j); [reflexivity | clear - g2; lia | clear - g3; lia | clear - g71; lia | clear - g73; lia | clear - g51 g53; lia | exact C].
    + destruct E1 as (MS & KP & r7 & r11 & r13 & r16 & C & U & c72 & c40 & c56 & c48 & c64 & c8 & c16 & c24 & c32 & c80 & c88 & c96 & c104 & c112 & c120).
      exists fx1, R1, M1.
      split; [exact G|]. split; [intros a Ha Hb; apply F; [exact Ha | intros Cc; apply Hb; clear - Cc; lia]|].
      split; [exact U|]. split; [exact c72|]. split; [exact c40|]. split; [exact c56|]. split; [exact c64|]. split; [exact c8|]. split; [exact c16|]. split; [exact c24|]. split; [exact c32|]. split; [exact c80|]. split; [exact c88|]. split; [exact c96|]. split; [exact c104|]. split; [exact c112|]. split; [exact c120|].
      split; [replace ((V 44%nat) + (j + 1)) with (((V 44%nat) + j) + 1) by (clear; lia); exact r13|].
      right. split; [exact MS|]. split; [intros x Hx; exact (KP x (KSGS_1 x Hx))|].
      split; [replace ((V 44%nat) + (j + 1)) with (((V 44%nat) + j) + 1) by (clear; lia); exact r7|]. split; [replace (((V 41%nat) + (V 43%nat)) - (j + 1)) with (((V 41%nat) + ((V 43%nat) - j)) - 1) by (clear; lia); exact r11|]. split; [replace ((V 44%nat) + (j + 1)) with (((V 44%nat) + j) + 1) by (clear; lia); exact r16|]. split; [exact c48|].
      apply (condG_ge 18446744073709551615 (V 41%nat) (V 43%nat) j); [reflexivity | clear - g2; lia | clear - g3; lia | clear - g71; lia | clear - g73; lia | clear - g51 g53; lia | exact C].
  -
    pose proof (PnAVu8GrowP_b.PMAVGP.avaGL1_conc fx R M (vB V j s) g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 R55 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39 g40 g41 g42 g43 g44 g45 g46 g47 g48 g49 g50 g51 g52 g53 g54 g55 g56 g57 g58 g59 g60 g61 g62 g63 g64 g65 g66 g67 g68 g69 g70 g71 g72 g73 g74 Us ltac:(cbn [vB Nat.eqb]; clear - P1; lia) ltac:(cbn [vB Nat.eqb]; clear - P1 P2 LN; lia)) as E.
    cbn [vB Nat.eqb] in E.
    destruct E as (fx1 & R1 & M1 & G & F & FZ & [E0 | E1]).
    + destruct E0 as (MS & KP & r1 & r2 & r7 & r10 & r11 & r13 & r16 & c48 & C & U & c72 & c40 & c56 & c64 & c8 & c16 & c24 & c32 & c80 & c88 & c96 & c104 & c112 & c120).
      exists fx1, R1, M1.
      split; [exact G|]. split; [intros a Ha Hb; apply F; [exact Ha | intros Cc; apply Hb; clear - Cc; lia]|].
      split; [exact U|]. split; [exact c72|]. split; [exact c40|]. split; [exact c56|]. split; [exact c64|]. split; [exact c8|]. split; [exact c16|]. split; [exact c24|]. split; [exact c32|]. split; [exact c80|]. split; [exact c88|]. split; [exact c96|]. split; [exact c104|]. split; [exact c112|]. split; [exact c120|].
      split; [replace ((V 44%nat) + (j + 1)) with (((V 44%nat) + j) + 1) by (clear; lia); exact r13|].
      left. split; [exact MS|]. split; [intros x Hx; exact (KP x (KSG1_0 x Hx))|].
      split; [exact r1|]. split; [exact r2|]. split; [exact r10|]. split; [exact r11|]. split; [exact r16|]. split; [exact c48|].
      apply (condG_lt 18446744073709551615 (V 41%nat) (V 43%nat) j); [reflexivity | clear - g2; lia | clear - g3; lia | clear - g71; lia | clear - g73; lia | clear - g51 g53; lia | exact C].
    + destruct E1 as (MS & KP & r7 & r11 & r13 & r16 & C & U & c72 & c40 & c56 & c48 & c64 & c8 & c16 & c24 & c32 & c80 & c88 & c96 & c104 & c112 & c120).
      exists fx1, R1, M1.
      split; [exact G|]. split; [intros a Ha Hb; apply F; [exact Ha | intros Cc; apply Hb; clear - Cc; lia]|].
      split; [exact U|]. split; [exact c72|]. split; [exact c40|]. split; [exact c56|]. split; [exact c64|]. split; [exact c8|]. split; [exact c16|]. split; [exact c24|]. split; [exact c32|]. split; [exact c80|]. split; [exact c88|]. split; [exact c96|]. split; [exact c104|]. split; [exact c112|]. split; [exact c120|].
      split; [replace ((V 44%nat) + (j + 1)) with (((V 44%nat) + j) + 1) by (clear; lia); exact r13|].
      right. split; [exact MS|]. split; [intros x Hx; exact (KP x (KSGS1_1 x Hx))|].
      split; [replace ((V 44%nat) + (j + 1)) with (((V 44%nat) + j) + 1) by (clear; lia); exact r7|]. split; [replace (((V 41%nat) + (V 43%nat)) - (j + 1)) with (((V 41%nat) + ((V 43%nat) - j)) - 1) by (clear; lia); exact r11|]. split; [replace ((V 44%nat) + (j + 1)) with (((V 44%nat) + j) + 1) by (clear; lia); exact r16|]. split; [exact c48|].
      apply (condG_ge 18446744073709551615 (V 41%nat) (V 43%nat) j); [reflexivity | clear - g2; lia | clear - g3; lia | clear - g71; lia | clear - g73; lia | clear - g51 g53; lia | exact C].
Qed.

Lemma loopG_gen (V : nat -> Z) : StepG V -> KG V ->
  forall (n : nat) (j : Z) fx R M, Z.of_nat n = (V 41%nat) + (V 43%nat) - j ->
  HG V j R M -> SG V j M -> XG V j -> CG V j fx R M.
Proof.
  intros ST K. pose proof K as K0. destruct K0 as (g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & g9 & g10 & g11 & g12 & g42 & g43 & g45 & g46 & g47 & g50 & g51 & g52 & g53 & g54 & g56 & g57 & g58 & g59 & gD).
  pose proof (div8_bounds (V 37%nat) ltac:(clear - g1; lia)) as d37.
  pose proof (div8_bounds (V 2%nat) ltac:(clear - g0; lia)) as d2.
  induction n as [|n IH]; intros j fx R M En Hh Hs Hx.
  { destruct Hh as (g14 & g15 & g16 & g17 & g18 & g19 & g20 & g21 & g22 & g23 & g24 & g25 & g26 & g27 & g28 & g29 & g30 & g31 & g32 & g33 & g34 & g35 & g36 & g37 & g38 & g39 & g40 & g41 & g44 & g48 & g49 & g55 & g60 & g61 & g62 & g63 & g64 & g65 & g66 & g67 & g68 & g69 & g70 & g71 & g72 & g73 & g74). exfalso. cbn [Z.of_nat] in En. clear - En g73. lia. }
  pose proof Hh as Hh0. destruct Hh0 as (g14 & g15 & g16 & g17 & g18 & g19 & g20 & g21 & g22 & g23 & g24 & g25 & g26 & g27 & g28 & g29 & g30 & g31 & g32 & g33 & g34 & g35 & g36 & g37 & g38 & g39 & g40 & g41 & g44 & g48 & g49 & g55 & g60 & g61 & g62 & g63 & g64 & g65 & g66 & g67 & g68 & g69 & g70 & g71 & g72 & g73 & g74).
  rewrite Nat2Z.inj_succ in En. unfold Z.succ in En.
  destruct (Hs j ltac:(clear - g73; lia)) as (s & Us & Ps).
  destruct (Hx j ltac:(clear - g73; lia)) as (x1 & x2 & x3).
  destruct (ST j fx R M K Hh (ex_intro _ s (conj Us Ps))) as (fx1 & R1 & M1 & G1 & F1 & U1 & c72 & c40 & c56 & c64 & c8 & c16 & c24 & c32 & c80 & c88 & c96 & c104 & c112 & c120 & r13 & [E0 | E1]).
  - destruct E0 as (MS & KP & r1 & r2 & r10 & r11 & r16 & c48 & Ej).
    exists fx1, R1, M1.
    split; [exact G1|].
    split; [intros a Ha Hb; apply F1; [exact Ha | intros Cc; apply Hb; clear - Cc g73; lia]|].
    split; [exact MS|]. split; [exact KP|]. split; [exact r1|]. split; [exact r2|]. split; [exact r10|]. split; [exact r11|].
    split; [replace ((V 44%nat) + ((V 41%nat) + (V 43%nat))) with ((V 44%nat) + (j + 1)) by (clear - Ej; lia); exact r13|].
    split; [exact r16|]. split; [exact c48|].
    split; [exact c72|]. split; [exact c40|]. split; [exact c56|]. split; [exact c64|]. split; [exact c8|]. split; [exact c16|]. split; [exact c24|]. split; [exact c32|]. split; [exact c80|]. split; [exact c88|]. split; [exact c96|]. split; [exact c104|]. split; [exact c112|]. split; [exact c120|].
    intros i Hi. replace i with j by (clear - Hi Ej; lia). exact U1.
  - destruct E1 as (MS & KP & r7 & r11 & r16 & c48 & Ej).
    assert (W : forall y, (V 44%nat) + j <= y < (V 44%nat) + j + 1 -> L5.u8_at RSEGS M1 y 0).
    { intros y Hy. replace y with ((V 44%nat) + j) by (clear - Hy; lia). exact U1. }
    assert (Hh1 : HG V (j + 1) R1 M1).
    { unfold HG.
      split; [clear - g71; lia|].
      split; [rewrite (KP 1%nat (in_of_b 1%nat KS_avaGLstep eq_refl)); exact g15|].
      split; [rewrite (KP 2%nat (in_of_b 2%nat KS_avaGLstep eq_refl)); exact g16|].
      split; [rewrite (KP 5%nat (in_of_b 5%nat KS_avaGLstep eq_refl)); exact g17|].
      split; [rewrite (KP 6%nat (in_of_b 6%nat KS_avaGLstep eq_refl)); exact g18|].
      split; [exact r7|].
      split; [rewrite (KP 8%nat (in_of_b 8%nat KS_avaGLstep eq_refl)); exact g20|].
      split; [rewrite (KP 9%nat (in_of_b 9%nat KS_avaGLstep eq_refl)); exact g21|].
      split; [rewrite (KP 10%nat (in_of_b 10%nat KS_avaGLstep eq_refl)); exact g22|].
      split; [exact r11|].
      split; [rewrite (KP 12%nat (in_of_b 12%nat KS_avaGLstep eq_refl)); exact g24|].
      split; [exact r13|].
      split; [rewrite (KP 14%nat (in_of_b 14%nat KS_avaGLstep eq_refl)); exact g26|].
      split; [rewrite (KP 15%nat (in_of_b 15%nat KS_avaGLstep eq_refl)); exact g27|].
      split; [exact r16|].
      split; [rewrite (KP 17%nat (in_of_b 17%nat KS_avaGLstep eq_refl)); exact g29|].
      split; [rewrite (KP 18%nat (in_of_b 18%nat KS_avaGLstep eq_refl)); exact g30|].
      split; [rewrite (KP 19%nat (in_of_b 19%nat KS_avaGLstep eq_refl)); exact g31|].
      split; [rewrite (KP 20%nat (in_of_b 20%nat KS_avaGLstep eq_refl)); exact g32|].
      split; [rewrite (KP 21%nat (in_of_b 21%nat KS_avaGLstep eq_refl)); exact g33|].
      split; [exact c72|].
      split; [exact c40|].
      split; [exact c56|].
      split; [exact c48|].
      split; [exact c64|].
      split; [apply (c_img _ _ _ _ _ _ F1); [clear; lia | clear; lia | clear - g42; lia | clear - x1; lia | exact g39]|].
      split; [apply (c_u64 _ _ _ _ _ _ F1); [clear; lia | clear; lia | clear - g42; lia | clear - x2; lia | exact g40]|].
      split; [apply (c_u32 _ _ _ _ _ _ F1); [clear; lia | clear; lia | clear - g42; lia | clear - x3; lia | exact g41]|].
      split; [eapply L5.writable_grows; [exact G1 | exact g44]|].
      split; [apply (c_zeros _ _ _ _ _ _ F1); [clear - d37; lia | clear - d37 g45; lia | clear - d37 g45 g42; lia | exact G1 | exact W | exact g48]|].
      split; [eapply L5.writable_grows; [exact G1 | exact g49]|].
      split; [eapply L5.writable_grows; [exact G1 | exact g55]|].
      split; [apply (c_zeros _ _ _ _ _ _ F1); [clear - d2; lia | clear - d2 g42; lia | clear - d2 g42; lia | exact G1 | exact W | exact g60]|].
      split; [exact c8|].
      split; [exact c16|].
      split; [exact c24|].
      split; [exact c32|].
      split; [exact c80|].
      split; [exact c88|].
      split; [exact c96|].
      split; [exact c104|].
      split; [exact c112|].
      split; [exact c120|].
      split; [clear - g71 Ej g54 gD; lia|].
      split; [clear - g72 Ej g54 gD g53; lia|].
      split; [clear - Ej g73; lia|].
      clear - Ej gD g74; lia.
    }
    assert (Hs1 : SG V (j + 1) M1).
    { intros i Hi. destruct (Hs i ltac:(clear - Hi; lia)) as (s' & Us' & Ps').
      pose proof (div8_bounds ((V 44%nat) + i) ltac:(clear - g4 Hi g71; lia)) as di.
      apply (c_sdw _ _ _ _ _ _ F1 _ (fun t => t = 0 \/ (1 <= t <= 7 /\ 1 <= t - Z.land ((V 44%nat) + i) 7))).
      - clear - di g52 g54 gD Hi g71; lia.
      - clear - di g52 g54 gD Hi g71 g42; lia.
      - exact W.
      - left; reflexivity.
      - exists s'; split; [exact Us' | exact Ps']. }
    assert (Hx1 : XG V (j + 1)) by (intros i Hi; exact (Hx i ltac:(clear - Hi; lia))).
    destruct (IH (j + 1) fx1 R1 M1 ltac:(clear - En; lia) Hh1 Hs1 Hx1)
      as (fx2 & R2 & M2 & G2 & F2 & MS2 & KP2 & r1' & r2' & r10' & r11' & r13' & r16' & e48 & e72 & e40 & e56 & e64 & e8 & e16 & e24 & e32 & e80 & e88 & e96 & e104 & e112 & e120 & Z2).
    exists fx2, R2, M2.
    split; [exact (mem_grows_trans _ _ _ G1 G2)|].
    split.
    { intros a Ha Hb. rewrite (F2 a Ha); [apply F1; [exact Ha | intros Cc; apply Hb; clear - Cc g73; lia] | intros Cc; apply Hb; clear - Cc; lia]. }
    split; [eapply CatSim.msteps_trans; [exact MS | exact MS2]|].
    split; [intros x Hx2; rewrite (KP2 x Hx2); exact (KP x (KSG_S x Hx2))|].
    split; [exact r1'|]. split; [exact r2'|]. split; [exact r10'|]. split; [exact r11'|]. split; [exact r13'|]. split; [exact r16'|]. split; [exact e48|].
    split; [exact e72|]. split; [exact e40|]. split; [exact e56|]. split; [exact e64|]. split; [exact e8|]. split; [exact e16|]. split; [exact e24|]. split; [exact e32|]. split; [exact e80|]. split; [exact e88|]. split; [exact e96|]. split; [exact e104|]. split; [exact e112|]. split; [exact e120|].
    intros i Hi. destruct (Z.eq_dec i j) as [Ei | Ei].
    + subst i. apply (c_u8 _ _ _ _ _ _ F2); [clear - g4 g52 g54 gD g71 g73; lia | clear - g56 g71 g73 gD; lia | clear; lia | exact U1].
    + apply Z2. clear - Hi Ei; lia.
Qed.

Lemma avaGLoop_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  0 <= (V 37%nat) < 2 ^ 64 ->
  0 <= (V 41%nat) < 2 ^ 64 ->
  0 <= (V 43%nat) < 2 ^ 64 ->
  0 <= (V 44%nat) < 2 ^ 64 ->
  0 <= (V 46%nat) < 2 ^ 64 ->
  0 <= (V 48%nat) < 2 ^ 64 ->
  0 <= (V 49%nat) < 2 ^ 64 ->
  0 <= (V 50%nat) < 2 ^ 64 ->
  0 <= (V 51%nat) < 2 ^ 64 ->
  0 <= (V 52%nat) < 2 ^ 64 ->
  0 <= (V 53%nat) < 2 ^ 64 ->
  0 <= (V 54%nat) < 2 ^ 64 ->
  0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 743604 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) ->
  getr R (reg 5) = Z_to_bv 64 ((((V 2%nat) - 32) / 8) + 2147450880) ->
  getr R (reg 6) = Z_to_bv 64 18446744073709551615 ->
  getr R (reg 7) = Z_to_bv 64 ((((V 44%nat) + (V 56%nat)) / 8) + 2147450880) ->
  getr R (reg 8) = Z_to_bv 64 (V 37%nat) ->
  getr R (reg 9) = Z_to_bv 64 (V 43%nat) ->
  getr R (reg 10) = Z_to_bv 64 ((V 2%nat) - 48) ->
  getr R (reg 11) = Z_to_bv 64 (((V 41%nat) + (V 43%nat)) - (V 56%nat)) ->
  getr R (reg 12) = Z_to_bv 64 ((V 2%nat) - 32) ->
  getr R (reg 13) = Z_to_bv 64 ((V 44%nat) + (V 56%nat)) ->
  getr R (reg 14) = Z_to_bv 64 ((((V 2%nat) - 48) / 8) + 2147450880) ->
  getr R (reg 15) = Z_to_bv 64 2147450880 ->
  getr R (reg 16) = Z_to_bv 64 ((V 44%nat) + (V 56%nat)) ->
  getr R (reg 17) = Z_to_bv 64 ((V 41%nat) + ((V 43%nat) + (V 44%nat))) ->
  getr R (reg 18) = Z_to_bv 64 (V 51%nat) ->
  getr R (reg 19) = Z_to_bv 64 (V 52%nat) ->
  getr R (reg 20) = Z_to_bv 64 (V 53%nat) ->
  getr R (reg 21) = Z_to_bv 64 (V 54%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) 743604 ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 44%nat) + (V 46%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 41%nat) + (V 44%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) ((V 41%nat) + (V 44%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 44%nat) ->
  L5.img_clear M 1249280 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 ->
  L5.u32_at RSEGS M 1309760 1 ->
  140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 ->
  L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  6905856 <= (V 37%nat) <= 140737488355304 ->
  aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 ->
  L5.writable RSEGS M (V 37%nat) 24 ->
  (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128)) ->
  1 <= (V 43%nat) <= 134217728 ->
  4096 <= (V 44%nat) <= 140737488355328 ->
  0 <= (V 41%nat) <= 134217728 ->
  1 <= (V 46%nat) <= 134217728 ->
  L5.writable RSEGS M (V 44%nat) (V 46%nat) ->
  (((V 2%nat) - 128) + 128 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= ((V 2%nat) - 128)) ->
  (2147446784 + 17592186048512 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= 2147446784) ->
  ((V 37%nat) + 24 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= (V 37%nat)) ->
  1 <= (((-1) * (V 41%nat)) + (V 46%nat)) <= 134217728 ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) (V 51%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 52%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 112) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 54%nat) ->
  0 <= (V 56%nat) <= 134217728 ->
  0 <= (((-1) * (V 41%nat)) + (V 56%nat)) <= 134217728 ->
  1 <= (((-1) * (V 56%nat)) + ((V 41%nat) + (V 43%nat))) <= 134217728 ->
  1 <= (((-1) * (V 56%nat)) + (V 46%nat)) <= 134217728 ->
  (forall i, (V 56%nat) <= i < (V 41%nat) + (V 43%nat) -> exists s, L5.u8_at RSEGS M ((((V 44%nat) + i) / 8) + 2147450880) s /\ (s = 0 \/ (1 <= s <= 7 /\ 1 <= s - Z.land ((V 44%nat) + i) 7))) ->
  (forall i, (V 56%nat) <= i < (V 41%nat) + (V 43%nat) -> ~ (1249280 <= (V 44%nat) + i < 1282048) /\ ~ (1309752 <= (V 44%nat) + i < 1309752 + 8) /\ ~ (1309760 <= (V 44%nat) + i < 1309760 + 4)) ->
  (V 41%nat) + (V 43%nat) <= (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 44%nat) + (V 56%nat)) <= bv_unsigned a < (V 44%nat) + ((V 41%nat) + (V 43%nat))) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ (((V 44%nat) + (V 56%nat)) <= i < (V 44%nat) + ((V 41%nat) + (V 43%nat))) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ msteps RSEGS (st fx R 0xb5c54 M) (st fx' R' 0xb5cb8 M')
    /\ (forall x, In x KS_avaGLoop -> getr R' (reg x) = getr R (reg x))
    /\ getr R' (reg 1) = Z_to_bv 64 743616
    /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
    /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
    /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 64)
    /\ getr R' (reg 13) = Z_to_bv 64 ((V 44%nat) + ((V 41%nat) + (V 43%nat)))
    /\ getr R' (reg 16) = Z_to_bv 64 ((V 41%nat) + ((V 43%nat) + (V 44%nat)))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((V 41%nat) + ((V 43%nat) + (V 44%nat)))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 743604
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 44%nat) + (V 46%nat))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 41%nat) + (V 44%nat))
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 44%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 37%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 37%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 51%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 52%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 53%nat)
    /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 54%nat)
    /\ (forall i, (V 56%nat) <= i < (V 41%nat) + (V 43%nat) -> L5.u8_at RSEGS M' ((V 44%nat) + i) 0).

Proof.
  intros p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 pS pX pD.
  destruct (loopG_gen V (stepG_ok V) (conj p0 (conj p1 (conj p2 (conj p3 (conj p4 (conj p5 (conj p6 (conj p7 (conj p8 (conj p9 (conj p10 (conj p11 (conj p12 (conj p42 (conj p43 (conj p45 (conj p46 (conj p47 (conj p50 (conj p51 (conj p52 (conj p53 (conj p54 (conj p56 (conj p57 (conj p58 (conj p59 pD))))))))))))))))))))))))))) (Z.to_nat ((V 41%nat) + (V 43%nat) - (V 56%nat))) (V 56%nat) fx R M
    ltac:(rewrite Z2Nat.id; [reflexivity | clear - p73; lia]) (conj p14 (conj p15 (conj p16 (conj p17 (conj p18 (conj p19 (conj p20 (conj p21 (conj p22 (conj p23 (conj p24 (conj p25 (conj p26 (conj p27 (conj p28 (conj p29 (conj p30 (conj p31 (conj p32 (conj p33 (conj p34 (conj p35 (conj p36 (conj p37 (conj p38 (conj p39 (conj p40 (conj p41 (conj p44 (conj p48 (conj p49 (conj p55 (conj p60 (conj p61 (conj p62 (conj p63 (conj p64 (conj p65 (conj p66 (conj p67 (conj p68 (conj p69 (conj p70 (conj p71 (conj p72 (conj p73 p74)))))))))))))))))))))))))))))))))))))))))))))) pS pX)
    as (fx' & R' & M' & G & F & MS & KP & r1 & r2 & r10 & r11 & r13 & r16 & e48 & e72 & e40 & e56 & e64 & e8 & e16 & e24 & e32 & e80 & e88 & e96 & e104 & e112 & e120 & Zs).
  exists fx', R', M'.
  split; [exact G|]. split; [exact F|].
  split; [intros i Hi Ha Hb; apply F; rewrite L5.unsigned_lit by exact Hi; assumption|].
  split; [exact MS|]. split; [exact KP|]. split; [exact r1|]. split; [exact r2|]. split; [exact r10|]. split; [exact r11|].
  split; [exact r13|]. split; [exact r16|]. split; [exact e48|].
  split; [exact e72|]. split; [exact e40|]. split; [exact e56|]. split; [exact e64|]. split; [exact e8|]. split; [exact e16|]. split; [exact e24|]. split; [exact e32|]. split; [exact e80|]. split; [exact e88|]. split; [exact e96|]. split; [exact e104|]. split; [exact e112|]. split; [exact e120|].
  exact Zs.
Qed.

End PMAVLP.
