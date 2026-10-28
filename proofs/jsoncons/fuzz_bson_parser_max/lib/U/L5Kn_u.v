(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan AsanPlanCore BigLinkBase. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import BigLinkGlue_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zpoly (V : nat -> Z) (e : expr) : option Z :=
  match e with
  | ELit z => Some z
  | EVar n => Some (V n)
  | EAlu ALU_ADD a b => match zpoly V a, zpoly V b with Some x, Some y => Some (x + y) | _, _ => None end
  | EAlu ALU_SUB a b => match zpoly V a, zpoly V b with Some x, Some y => Some (x - y) | _, _ => None end
  | EMd M_MUL a b => match zpoly V a, zpoly V b with Some x, Some y => Some (x * y) | _, _ => None end
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint zagree (E : env) (V : nat -> Z) (e : expr) : Prop :=
  match e with
  | ELit _ => True
  | EVar n => bv_unsigned (ev E n) = V n
  | EAlu _ a b | EMd _ a b => zagree E V a /\ zagree E V b
  | _ => True
  end.

Lemma MMpos : 0 < BL.MM. Proof. unfold BL.MM. lia. Qed.

Lemma zpoly_sound E V e : forall zz, zagree E V e -> zpoly V e = Some zz -> bv_unsigned (edenot E e) = zz mod BL.MM.
Proof.
  induction e; intros zz HA HZ; cbn [zpoly zagree] in HA, HZ; try discriminate; cbn [edenot].
  - inversion HZ; subst. rewrite Z_to_bv_unsigned. reflexivity.
  - inversion HZ; subst. rewrite <- HA. symmetry. apply Z.mod_small. apply (BL.bvu_range (ev E n)).
  - destruct HA as [Ha Hb].
    destruct op; try discriminate;
      destruct (zpoly V e1) as [x|] eqn:E1; try discriminate; destruct (zpoly V e2) as [y|] eqn:E2; try discriminate;
      inversion HZ; subst; cbn [alu64 alu];
      [ rewrite bv_add_unsigned | rewrite bv_sub_unsigned ];
      unfold bv_wrap; change (bv_modulus 64) with BL.MM;
      rewrite (IHe1 x Ha eq_refl), (IHe2 y Hb eq_refl).
    + rewrite <- Z.add_mod by (unfold BL.MM; lia). reflexivity.
    + rewrite <- Zminus_mod. reflexivity.
  - destruct HA as [Ha Hb].
    destruct op; try discriminate.
    destruct (zpoly V e1) as [x|] eqn:E1; try discriminate; destruct (zpoly V e2) as [y|] eqn:E2; try discriminate.
    inversion HZ; subst. cbn [mul_div]. rewrite bv_mul_unsigned. unfold bv_wrap; change (bv_modulus 64) with BL.MM.
    rewrite (IHe1 x Ha eq_refl), (IHe2 y Hb eq_refl). rewrite <- Z.mul_mod by (unfold BL.MM; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zpoly_val E V e z v : zagree E V e -> zpoly V e = Some z -> z mod BL.MM = v -> bv_unsigned (edenot E e) = v.
Proof. intros HA HZ Hv. rewrite (zpoly_sound E V e z HA HZ). exact Hv. Qed.
Lemma zpoly_word E V e z v : zagree E V e -> zpoly V e = Some z -> z mod BL.MM = v -> edenot E e = Z_to_bv 64 v.
Proof. intros HA HZ Hv. apply BG.word_of_unsigned. eapply zpoly_val; eauto. Qed.

(* [comment removed for export] *)
Lemma zagree_all E V e : (forall n, bv_unsigned (ev E n) = V n) -> zagree E V e.
Proof. intros H. induction e; cbn [zagree]; auto. Qed.
(* [comment removed for export] *)
Lemma zagree_lt E E' V b e : env_agree b E E' -> zagree E V e -> expr_vars_lt b e = true -> zagree E' V e.
Proof.
  intros HA. induction e; cbn [zagree expr_vars_lt]; intros HZ HV; auto.
  - apply Nat.ltb_lt in HV. rewrite <- (proj1 HA n HV). exact HZ.
  - apply andb_prop in HV. destruct HV, HZ. split; auto.
  - apply andb_prop in HV. destruct HV, HZ. split; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

Lemma estart_e E b off : estart E (SA b off) = bv_unsigned (edenot E b) + off.
Proof. reflexivity. Qed.
Lemma adenot_e E b off : adenot E (SA b off) = Z_to_bv 64 (bv_unsigned (edenot E b) + off).
Proof. reflexivity. Qed.

Lemma kentry_KRange E M e lo hi v : bv_unsigned (edenot E e) = v -> lo <= v <= hi -> kentry_ok segs E M (KRange e lo hi).
Proof. intros Hv Hr. cbn [kentry_ok]. rewrite Hv. lia. Qed.

(* [comment removed for export] *)
Lemma and_lit_val (x : word) m : 0 <= m < 2 ^ 64 -> bv_unsigned (alu64 ALU_AND x (Z_to_bv 64 m)) = Z.land (bv_unsigned x) m.
Proof. intros Hm. cbn [alu64 alu]. rewrite bv_and_unsigned, BG.unsigned_lit by lia. reflexivity. Qed.
Lemma kentry_KRange_andlit E M e m lo hi v :
  bv_unsigned (edenot E e) = v -> 0 <= m < 2 ^ 64 -> lo <= Z.land v m <= hi -> kentry_ok segs E M (KRange (EAlu ALU_AND e (ELit m)) lo hi).
Proof. intros Hv Hm Hr. cbn [kentry_ok edenot]. rewrite and_lit_val by exact Hm. rewrite Hv. lia. Qed.
Lemma land1_bit0_false fb : 0 <= fb -> Z.testbit fb 0 = false -> Z.land fb 1 = 0.
Proof.
  intros Hfb B0. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec i 0) as [->|Hi0]. rewrite B0. reflexivity.
  replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). apply Bool.andb_false_r.
Qed.
Lemma land1_bit0_true fb : 0 <= fb -> Z.testbit fb 0 = true -> Z.land fb 1 = 1.
Proof.
  intros Hfb B0. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hi0]. rewrite B0. reflexivity.
  replace (Z.testbit 1 i) with false by (symmetry; apply Z.bits_above_log2; cbn; lia). rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma land2_bit1_false fb : 0 <= fb -> Z.testbit fb 1 = false -> Z.land fb 2 = 0.
Proof.
  intros Hfb B1. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec i 1) as [->|Hi1]. rewrite B1. reflexivity.
  replace (Z.testbit 2 i) with false. apply Bool.andb_false_r.
  destruct (Z.eq_dec i 0) as [->|Hi0]. reflexivity. symmetry. apply Z.bits_above_log2; cbn; lia.
Qed.
Lemma land2_bit1_true fb : 0 <= fb -> Z.testbit fb 1 = true -> Z.land fb 2 = 2.
Proof.
  intros Hfb B1. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 1) as [->|Hi1]. rewrite B1. reflexivity.
  replace (Z.testbit 2 i) with false. rewrite Bool.andb_false_r. reflexivity.
  destruct (Z.eq_dec i 0) as [->|Hi0]. reflexivity. symmetry. apply Z.bits_above_log2; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma land_le_r a m : 0 <= a -> 0 <= m -> 0 <= Z.land a m <= m.
Proof.
  intros Ha Hm. split. apply Z.land_nonneg. left; exact Ha.
  pose proof (Z.lor_ldiff_and m a) as E1. pose proof (Z.add_lor_land (Z.ldiff m a) (Z.land m a)) as E2.
  assert (Z0: Z.land (Z.ldiff m a) (Z.land m a) = 0).
  { rewrite (Z.land_comm m a). rewrite Z.land_assoc. rewrite Z.land_ldiff. apply Z.land_0_l. }
  assert (D0: 0 <= Z.ldiff m a). { apply Z.ldiff_nonneg. left; exact Hm. }
  rewrite Z.land_comm. lia.
Qed.
Lemma land_even_bit0 a m : Z.testbit m 0 = false -> Z.testbit (Z.land a m) 0 = false.
Proof. intros H. rewrite Z.land_spec, H. apply Bool.andb_false_r. Qed.

Lemma kentry_KAlign E M e m v : bv_unsigned (edenot E e) = v -> 0 < m -> v mod m = 0 -> kentry_ok segs E M (KAlign e m).
Proof. intros Hv Hm H0. cbn [kentry_ok]. rewrite Hv. auto. Qed.

Lemma kentry_KWr E M b off ne a n :
  bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E ne) = n ->
  0 <= a + off -> 0 < n -> a + off + n <= 2 ^ 64 ->
  L5.writable segs M (a + off) n -> kentry_ok segs E M (KWr (SA b off) ne).
Proof.
  intros Ha Hn H1 H2 H3 Hw. cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_e, Ha, Hn.
  split. lia. intros d m Hd Hm. apply Hw; lia.
Qed.

Lemma kentry_KUnk E M b off ne a n :
  bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E ne) = n ->
  0 <= a + off -> 0 < n -> a + off + n <= 2 ^ 64 ->
  L5.defined M (a + off) n -> kentry_ok segs E M (KUnk (SA b off) ne).
Proof.
  intros Ha Hn H1 H2 H3 Hd. cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_e, Ha, Hn.
  split. lia. intros i Hi. apply Hd. lia.
Qed.

Lemma kentry_KDisj E M b1 off1 n1e b2 off2 n2e a1 n1 a2 n2 :
  bv_unsigned (edenot E b1) = a1 -> bv_unsigned (edenot E n1e) = n1 ->
  bv_unsigned (edenot E b2) = a2 -> bv_unsigned (edenot E n2e) = n2 ->
  (a1 + off1 + n1 <= a2 + off2 \/ a2 + off2 + n2 <= a1 + off1) ->
  kentry_ok segs E M (KDisj (SA b1 off1) n1e (SA b2 off2) n2e).
Proof.
  intros Ha1 Hn1 Ha2 Hn2 Hd. cbn [kentry_ok]. unfold elenZ. rewrite !estart_e, Ha1, Ha2, Hn1, Hn2. exact Hd.
Qed.

Lemma kentry_KWord8 E M b off e a v :
  bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E e) = v ->
  0 <= a + off -> a + off + 8 <= 2 ^ 64 ->
  L5.u64_at segs M (a + off) v -> kentry_ok segs E M (KWord (SA b off) 8 e).
Proof.
  intros Ha Hv H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
  - unfold flat. rewrite estart_e, Ha. lia.
  - rewrite adenot_e, Ha. rewrite (BG.word_of_unsigned _ _ Hv). exact Hu.
Qed.

Lemma kentry_KWord1 E M b off e a v :
  bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E e) = v ->
  0 <= a + off -> a + off + 1 <= 2 ^ 64 -> 0 <= v < 256 ->
  L5.u8_at segs M (a + off) v -> kentry_ok segs E M (KWord (SA b off) 1 e).
Proof.
  intros Ha Hv H1 H2 Hr Hu. cbn [kentry_ok]. split. lia. split.
  - unfold flat. rewrite estart_e, Ha. lia.
  - rewrite adenot_e, Ha. rewrite (BG.word_of_unsigned _ _ Hv). rewrite BG.word_to_le_bytes_1 by exact Hr. exact Hu.
Qed.

Lemma kentry_KWord4 E M b off e a v :
  bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E e) = v ->
  0 <= a + off -> a + off + 4 <= 2 ^ 64 ->
  L5.u32_at segs M (a + off) v -> kentry_ok segs E M (KWord (SA b off) 4 e).
Proof.
  intros Ha Hv H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
  - unfold flat. rewrite estart_e, Ha. lia.
  - rewrite adenot_e, Ha. rewrite (BG.word_of_unsigned _ _ Hv). exact Hu.
Qed.

Lemma kentry_KImg E M lo hi : 0 <= lo -> hi <= 2 ^ 64 -> L5.img_clear M lo hi -> kentry_ok segs E M (KImg lo hi).
Proof. intros H1 H2 H. cbn [kentry_ok]. repeat split; auto. Qed.

(* [comment removed for export] *)
Lemma u64_of_KWord8 E M b off e a v :
  kentry_ok segs E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E e) = v ->
  L5.u64_at segs M (a + off) v.
Proof.
  intros K Ha Hv. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd). unfold L5.u64_at.
  rewrite adenot_e, Ha in Rd. rewrite <- (BG.word_of_unsigned _ _ Hv). exact Rd.
Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8_ex E M b off e a :
  kentry_ok segs E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at segs M (a + off) v.
Proof.
  intros K Ha. exists (bv_unsigned (edenot E e)). split. apply (BL.bvu_range (edenot E e)).
  eapply u64_of_KWord8; eauto.
Qed.
Lemma u32_of_KWord4 E M b off e a v :
  kentry_ok segs E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E e) = v ->
  L5.u32_at segs M (a + off) v.
Proof.
  intros K Ha Hv. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd). unfold L5.u32_at.
  rewrite adenot_e, Ha in Rd. rewrite <- (BG.word_of_unsigned _ _ Hv). exact Rd.
Qed.
Lemma u8_of_KWord1 E M b off e a v :
  kentry_ok segs E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E e) = v -> 0 <= v < 256 ->
  L5.u8_at segs M (a + off) v.
Proof.
  intros K Ha Hv Hr. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd). unfold L5.u8_at.
  rewrite adenot_e, Ha in Rd. rewrite (BG.word_of_unsigned _ _ Hv) in Rd. rewrite BG.word_to_le_bytes_1 in Rd by exact Hr. exact Rd.
Qed.
Lemma defined_of_KUnk E M b off ne a n :
  kentry_ok segs E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E ne) = n ->
  L5.defined M (a + off) n.
Proof.
  intros K Ha Hn. cbn [kentry_ok] in K. destruct K as [_ D]. unfold elenZ in D. rewrite estart_e, Ha, Hn in D.
  intros i Hi. apply D. exact Hi.
Qed.

Lemma range_of_KRange E M e lo hi v :
  kentry_ok segs E M (KRange e lo hi) -> bv_unsigned (edenot E e) = v -> lo <= v <= hi.
Proof. intros K Hv. cbn [kentry_ok] in K. rewrite Hv in K. exact K. Qed.

(* [comment removed for export] *)
Lemma u64_at_keep M M' lo hi a v :
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> M' x = M x) ->
  (a + 8 <= lo \/ hi <= a \/ hi <= lo) -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at segs M a v -> L5.u64_at segs M' a v.
Proof.
  intros HF Hap Ha H8 Hu. eapply (L5.u64_at_frame segs M M' [(lo, hi - lo)]). 2: exact Ha. 2: exact H8. 3: exact Hu.
  - intros x Hx. apply HF. intros Hin. apply (Hx (lo, hi - lo)). left; reflexivity. unfold L5.in_rng. cbn. lia.
  - intros i Hi r [<-|[]]. unfold L5.in_rng. cbn. lia.
Qed.
Lemma u8_at_keep M M' lo hi a v :
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> M' x = M x) ->
  (a + 1 <= lo \/ hi <= a \/ hi <= lo) -> 0 <= a -> a + 1 <= 2 ^ 64 -> L5.u8_at segs M a v -> L5.u8_at segs M' a v.
Proof.
  intros HF Hap Ha H1 Hu. eapply (L5.u8_at_frame segs M M' [(lo, hi - lo)]). 2: exact Ha. 2: exact H1. 3: exact Hu.
  - intros x Hx. apply HF. intros Hin. apply (Hx (lo, hi - lo)). left; reflexivity. unfold L5.in_rng. cbn. lia.
  - intros r [<-|[]]. unfold L5.in_rng. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma outside_cons_e E b off ne F (x : word) a n :
  bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E ne) = n ->
  ~ (a + off <= bv_unsigned x < a + off + n) -> SGP.outside E F x -> SGP.outside E ((b, off, ne) :: F) x.
Proof.
  intros Ha Hn Hx HF. constructor. 2: exact HF. unfold estart, elenZ. cbn [a_base a_off]. rewrite Ha, Hn. lia.
Qed.
Lemma outside_nil_e E (x : word) : SGP.outside E [] x.
Proof. constructor. Qed.

End WithSegs.

(* [comment removed for export] *)
Lemma In_of_existsb (i : nat) (l : list nat) : existsb (Nat.eqb i) l = true -> In i l.
Proof. induction l as [|x l IH]; cbn; intros H. discriminate. apply Bool.orb_prop in H. destruct H as [H|H]. left. apply Nat.eqb_eq in H. lia. right. apply IH. exact H. Qed.
Lemma incl_b (l1 l2 : list nat) : forallb (fun i => existsb (Nat.eqb i) l2) l1 = true -> forall i, In i l1 -> In i l2.
Proof. intros H i Hi. rewrite forallb_forall in H. apply In_of_existsb. apply H. exact Hi. Qed.
Lemma in_b (i : nat) (l : list nat) : existsb (Nat.eqb i) l = true -> In i l.
Proof. apply In_of_existsb. Qed.

(* [comment removed for export] *)
Lemma nth_error_single {A} (x y : A) i : nth_error [x] i = Some y -> y = x.
Proof. intros H. destruct i as [|i]; cbn in H; [inversion H; auto | destruct i; discriminate]. Qed.
Lemma nth_error_pair {A} (x y z : A) i : nth_error [x; y] i = Some z -> (i = 0%nat /\ z = x) \/ (i = 1%nat /\ z = y).
Proof. intros H. destruct i as [|[|i]]; cbn in H; [inversion H; auto | inversion H; auto | destruct i; discriminate]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zrange_tac :=
  first [ apply BL.bvu_range | unfold BL.MM; lia
        | lazymatch goal with
          | |- context [getr] => fail
          | |- context [bv_unsigned] => fail
          | |- 0 <= ?z < _ => let v := eval vm_compute in z in
                              lazymatch v with Z0 => idtac | Zpos _ => idtac end;
                              change z with v; unfold BL.MM; lia
          end ].
Ltac mod_small_tac := rewrite Z.mod_small; [| zrange_tac ].
(* [comment removed for export] *)
Ltac solve_mod :=
  first [ mod_small_tac; first [reflexivity | lia]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); unfold BL.MM; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac norm_expr :=
  lazymatch goal with
  | |- bv_unsigned (edenot _ ?e) = _ => let e' := eval vm_compute in e in change e with e'
  | |- edenot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
  | _ => idtac
  end.
Ltac evalE ZA :=
  norm_expr; eapply zpoly_val;
  [ apply (zagree_all _ _ _ ZA) | cbn [zpoly]; reflexivity | solve_mod ].
(* [comment removed for export] *)
Ltac evalE' ZA AG :=
  norm_expr; eapply zpoly_val;
  [ eapply (zagree_lt _ _ _ _ _ AG); [apply (zagree_all _ _ _ ZA) | vm_compute; reflexivity]
  | cbn [zpoly]; reflexivity | solve_mod ].
(* [comment removed for export] *)
Ltac wordE ZA := apply BG.word_of_unsigned; evalE ZA.
Ltac wordE' ZA AG := apply BG.word_of_unsigned; evalE' ZA AG.

(* [comment removed for export] *)
Ltac slot ZA := first [ assumption | reflexivity | (etransitivity; [eassumption|]; symmetry; wordE ZA) ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kn_mem :=
  rewrite ?Z.add_0_r;
  first [ eassumption
        | match goal with H : L5.u64_at _ ?M ?a' ?v' |- L5.u64_at _ ?M ?a ?v =>
            replace a with a' by lia; replace v with v' by lia; exact H end
        | match goal with H : L5.u8_at _ ?M ?a' ?v' |- L5.u8_at _ ?M ?a ?v =>
            replace a with a' by lia; replace v with v' by lia; exact H end
        | match goal with H : L5.u32_at _ ?M ?a' ?v' |- L5.u32_at _ ?M ?a ?v =>
            replace a with a' by lia; replace v with v' by lia; exact H end
        | match goal with H : L5.defined ?M ?a' ?n' |- L5.defined ?M ?a ?n =>
            apply (L5.defined_sub M a' n' a n H); lia end
        | match goal with H : L5.writable _ ?M ?a' ?n' |- L5.writable _ ?M ?a ?n =>
            apply (L5.writable_sub _ M a' n' a n H); lia end
        | idtac ].
Ltac kn1 ZA :=
  lazymatch goal with
  | |- kentry_ok _ _ _ (KRange (EAlu ALU_AND _ (ELit _)) _ _) =>
        eapply kentry_KRange_andlit; [evalE ZA | lia | first [lia | rewrite land1_bit0_false by (first [assumption|lia]); lia
                                                         | rewrite land1_bit0_true by (first [assumption|lia]); lia
                                                         | rewrite land2_bit1_false by (first [assumption|lia]); lia
                                                         | rewrite land2_bit1_true by (first [assumption|lia]); lia | idtac] ]
  | |- kentry_ok _ _ _ (KRange _ _ _) => eapply kentry_KRange; [evalE ZA | lia]
  | |- kentry_ok _ _ _ (KAlign _ _) => eapply kentry_KAlign; [evalE ZA | lia | first [assumption | lia | idtac]]
  | |- kentry_ok _ _ _ (KWr _ _) => eapply kentry_KWr; [evalE ZA | evalE ZA | lia | lia | lia | kn_mem]
  | |- kentry_ok _ _ _ (KUnk _ _) => eapply kentry_KUnk; [evalE ZA | evalE ZA | lia | lia | lia | kn_mem]
  | |- kentry_ok _ _ _ (KDisj _ _ _ _) => eapply kentry_KDisj; [evalE ZA | evalE ZA | evalE ZA | evalE ZA | lia]
  | |- kentry_ok _ _ _ (KWord _ 8 _) => eapply kentry_KWord8; [evalE ZA | evalE ZA | lia | lia | kn_mem]
  | |- kentry_ok _ _ _ (KWord _ 1 _) => eapply kentry_KWord1; [evalE ZA | evalE ZA | lia | lia | lia | kn_mem]
  | |- kentry_ok _ _ _ (KWord _ 4 _) => eapply kentry_KWord4; [evalE ZA | evalE ZA | lia | lia | kn_mem]
  | |- kentry_ok _ _ _ (KImg _ _) => eapply kentry_KImg; [lia | lia | first [eassumption | idtac]]
  end.
Ltac kn_all ZA :=
  lazymatch goal with
  | |- Forall _ (_ :: _) => apply Forall_cons; [kn1 ZA | kn_all ZA]
  | |- Forall _ [] => apply Forall_nil
  | |- Forall _ _ => idtac
  end.

(* [comment removed for export] *)
Lemma zc_sound E e t v : BL.zcomp e = Some t -> BL.zden (BL.uv E) t = v -> bv_unsigned (edenot E e) = v.
Proof. intros Ht Hv. rewrite (BL.zcomp_sound E e t Ht). exact Hv. Qed.
Lemma zc_sound' b E E' e t v : env_agree b E E' -> evars_lt b e = true -> BL.zcomp e = Some t ->
  BL.zden (BL.uv E) t = v -> bv_unsigned (edenot E' e) = v.
Proof.
  intros AG Hb Ht Hv. rewrite (BL.zcomp_sound E' e t Ht). rewrite <- (BL.zden_agree b (BL.uv E) (BL.uv E') e t). exact Hv.
  intros n Hn. unfold BL.uv. rewrite (proj1 AG n Hn). reflexivity. exact Hb. exact Ht.
Qed.
(* [comment removed for export] *)
Ltac evalB ZA :=
  lazymatch goal with |- bv_unsigned (edenot _ ?e) = _ =>
    let t := eval vm_compute in (BL.zc e) in
    eapply (zc_sound _ e t); [vm_compute; reflexivity | cbn [BL.zden]; unfold BL.uv; rewrite ?ZA; unfold BL.MM] end.
Ltac evalB' ZA AG :=
  lazymatch goal with |- bv_unsigned (edenot _ ?e) = _ =>
    let t := eval vm_compute in (BL.zc e) in
    eapply (zc_sound' _ _ _ e t _ AG); [vm_compute; reflexivity | vm_compute; reflexivity | cbn [BL.zden]; unfold BL.uv; rewrite ?ZA; unfold BL.MM] end.
(* [comment removed for export] *)
Ltac wordB ZA := apply BG.word_of_unsigned; evalB ZA.
Ltac wordB' ZA AG := apply BG.word_of_unsigned; evalB' ZA AG.

(* [comment removed for export] *)
Ltac outsideF ZA AG := repeat (eapply outside_cons_e; [evalE' ZA AG | evalE' ZA AG | lia |]); apply outside_nil_e.

End L5K.
