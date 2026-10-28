(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec SeqExec StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun BigLinkBase.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BG.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition E_R (R : bvmap 5 word) (rest : nat -> word) (ebs : nat -> list byte) : env := Env (reg_ev R rest) ebs.

Lemma E_R_reg R rest ebs i : (i < 32)%nat -> ev (E_R R rest ebs) i = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof. intros. unfold E_R, reg_ev. cbn [ev]. destruct (Nat.ltb_spec i 32); auto. lia. Qed.
Lemma E_R_rest R rest ebs i : (32 <= i)%nat -> ev (E_R R rest ebs) i = rest i.
Proof. intros. unfold E_R, reg_ev. cbn [ev]. destruct (Nat.ltb_spec i 32); auto. lia. Qed.

(* [comment removed for export] *)
Fixpoint slots_ok (E : env) (R : bvmap 5 word) (sr : list expr) (i : nat) : Prop :=
  match sr with
  | [] => True
  | e :: t => (match e with EVar j => (j = i)%nat \/ getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E e
                           | _ => getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E e end) /\ slots_ok E R t (S i)
  end.

Lemma slots_ok_nth E R sr : forall i0, slots_ok E R sr i0 ->
  forall i, (i < length sr)%nat -> nth i sr (ELit 0) = EVar (i0 + i) \/ getr R (Z_to_bv 5 (Z.of_nat (i0 + i))) = edenot E (nth i sr (ELit 0)).
Proof.
  induction sr as [|e t IH]; intros i0 H i Hi. exfalso; simpl in Hi; lia.
  simpl in H. destruct H as [He Ht]. destruct i.
  - rewrite Nat.add_0_r. cbn [nth]. destruct e; try (right; exact He). destruct He as [He|He]. left; subst; reflexivity. right; exact He.
  - replace (i0 + S i)%nat with (S i0 + i)%nat by lia. cbn [nth]. apply IH; auto. simpl in Hi; lia.
Qed.

Lemma regs_ok_slots R rest ebs sr :
  length sr = 32%nat -> slots_ok (E_R R rest ebs) R sr 0 -> regs_ok (E_R R rest ebs) sr R.
Proof.
  intros Hl Hs r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. apply getr_zero.
  - pose proof (ridx_range r) as Hr.
    destruct (slots_ok_nth _ _ _ 0 Hs (ridx r) ltac:(lia)) as [E|E]; simpl in E.
    + rewrite E. cbn [edenot]. rewrite E_R_reg by auto. rewrite ridx_roundtrip. reflexivity.
    + rewrite ridx_roundtrip in E. exact E.
Qed.

(* [comment removed for export] *)
Fixpoint slots (E : env) (R : bvmap 5 word) (sr : list expr) (i : nat) : Prop :=
  match sr with
  | [] => True
  | e :: t => getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E e /\ slots E R t (S i)
  end.

Lemma slots_nth E R sr : forall i0, slots E R sr i0 ->
  forall i, (i < length sr)%nat -> getr R (Z_to_bv 5 (Z.of_nat (i0 + i))) = edenot E (nth i sr (ELit 0)).
Proof.
  induction sr as [|e t IH]; intros i0 H i Hi. exfalso; simpl in Hi; lia.
  simpl in H. destruct H as [He Ht]. destruct i.
  - rewrite Nat.add_0_r. exact He.
  - replace (i0 + S i)%nat with (S i0 + i)%nat by lia. cbn [nth]. apply IH; auto. simpl in Hi; lia.
Qed.

Lemma regs_ok_of_slots E R sr : length sr = 32%nat -> slots E R (tl sr) 1 -> regs_ok E sr R.
Proof.
  intros Hl Hs r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. apply getr_zero.
  - pose proof (ridx_range r) as Hr.
    assert (Hnz: ridx r <> 0%nat).
    { intros Z0. assert (r = 0%bv). { rewrite <- (ridx_roundtrip r). rewrite Z0. apply bv_eq. reflexivity. } subst r.
      unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate. }
    destruct sr as [|e0 t]. simpl in Hl; lia. simpl in Hl. cbn [tl] in Hs.
    pose proof (slots_nth E R t 1 Hs (ridx r - 1) ltac:(simpl; lia)) as X.
    replace (1 + (ridx r - 1))%nat with (ridx r) in X by lia. rewrite ridx_roundtrip in X.
    rewrite X. destruct (ridx r) eqn:E0. lia. replace (S n - 1)%nat with n by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma reg_out (ps_regs : list (nat * expr)) (R' : bvmap 5 word) (E' : env) i e :
  (forall i e, In (i, e) ps_regs -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e) ->
  In (i, e) ps_regs -> getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e.
Proof. intros H Hin. apply (H i e Hin). Qed.

Lemma edenot_kept b E E' e : env_agree b E E' -> expr_vars_lt b e = true -> edenot E' e = edenot E e.
Proof. intros. symmetry. eapply edenot_agree; eauto. Qed.

(* [comment removed for export] *)
Lemma sr_get_reg sr i : (0 < i < 32)%nat -> sr_get sr (Z_to_bv 5 (Z.of_nat i)) = nth i sr (ELit 0).
Proof.
  intros Hi. unfold sr_get.
  assert (R: ridx (Z_to_bv 5 (Z.of_nat i)) = i).
  { unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
  destruct (bv_eqb (Z_to_bv 5 (Z.of_nat i)) 0) eqn:E.
  - exfalso. unfold bv_eqb in E. apply Z.eqb_eq in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E.
    change (bv_modulus 5) with 32 in E. rewrite Z.mod_small in E by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in E. lia.
  - rewrite R. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kept_reg E E' R R' (sr ro : list expr) b i :
  regs_ok E sr R -> env_agree b E E' -> (0 < i < 32)%nat ->
  expr_eqb (nth i ro (ELit 0)) (nth i sr (ELit 0)) = true -> expr_vars_lt b (nth i sr (ELit 0)) = true ->
  getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' (nth i ro (ELit 0)) ->
  getr R' (Z_to_bv 5 (Z.of_nat i)) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof.
  intros HR HA Hi He Hv HG. apply expr_eqb_eq in He. rewrite HG, He.
  rewrite (edenot_kept b E E') by auto. rewrite (HR (Z_to_bv 5 (Z.of_nat i))). rewrite sr_get_reg by auto. reflexivity.
Qed.

(* [comment removed for export] *)
Definition kept_ok (b : nat) (sr ro : list expr) (ks : list nat) : bool :=
  forallb (fun i => (0 <? i)%nat && (i <? 32)%nat && expr_eqb (nth i ro (ELit 0)) (nth i sr (ELit 0)) && expr_vars_lt b (nth i sr (ELit 0)))%bool ks.
(* [comment removed for export] *)
Definition kept_list (b : nat) (sr ro : list expr) : list nat :=
  List.filter (fun i => expr_eqb (nth i ro (ELit 0)) (nth i sr (ELit 0)) && expr_vars_lt b (nth i sr (ELit 0)))%bool (seq 1 31).

Lemma in_psregs (ro : list expr) i : (0 < i < 32)%nat -> In (i, nth i ro (ELit 0)) (map (fun i => (i, nth i ro (ELit 0))) (seq 1 31)).
Proof. intros Hi. apply in_map_iff. exists i. split; auto. apply in_seq. lia. Qed.

Lemma kept_regs E E' R R' (sr ro : list expr) b ks :
  kept_ok b sr ro ks = true ->
  regs_ok E sr R -> env_agree b E E' ->
  (forall i e, In (i, e) (map (fun i => (i, nth i ro (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e) ->
  forall i, In i ks -> getr R' (Z_to_bv 5 (Z.of_nat i)) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof.
  intros HK HR HA HO i Hi. unfold kept_ok in HK. rewrite forallb_forall in HK. specialize (HK i Hi).
  apply andb_prop in HK. destruct HK as [HK Hv]. apply andb_prop in HK. destruct HK as [HK He].
  apply andb_prop in HK. destruct HK as [H0 H32]. apply Nat.ltb_lt in H0. apply Nat.ltb_lt in H32.
  assert (Hi1 : (0 < i < 32)%nat) by (split; assumption).
  exact (kept_reg E E' R R' sr ro b i HR HA Hi1 He Hv (proj2 (HO i (nth i ro (ELit 0)) (in_psregs ro i Hi1)))).
Qed.

(* [comment removed for export] *)
Lemma out_reg (ro : list expr) E' R' i :
  (forall i e, In (i, e) (map (fun i => (i, nth i ro (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e) ->
  (0 < i < 32)%nat -> getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' (nth i ro (ELit 0)).
Proof.
  intros HO Hi. exact (proj2 (HO i (nth i ro (ELit 0)) (in_psregs ro i Hi))).
Qed.

(* [comment removed for export] *)

Lemma zeval_kept b E E' e z : env_agree b E E' -> evars_lt b e = true ->
  BL.zeval (BL.uv E) e = Some z -> bv_unsigned (edenot E' e) = z.
Proof.
  intros HA Hv Hz. apply BL.zeval_sound. rewrite <- Hz. apply BL.zeval_agree with (b := b); auto.
  intros n Hn. unfold BL.uv. destruct HA as [HA _]. rewrite HA; auto.
Qed.

Lemma word_of_unsigned (w : word) z : bv_unsigned w = z -> w = Z_to_bv 64 z.
Proof. intros H. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite <- H. symmetry. apply bv_wrap_bv_unsigned. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition u64_at (M : word -> option byte) (a : Z) (v : Z) : Prop :=
  rdn RSEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).
Definition writable (M : word -> option byte) (a n : Z) : Prop :=
  forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok RSEGS M (Z_to_bv 64 (a + d)) k = true.
Definition defined (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None.

Lemma estart_var E j off : estart E (SA (EVar j) off) = bv_unsigned (ev E j) + off.
Proof. reflexivity. Qed.

Lemma kentry_KRange E M e lo hi z : BL.zeval (BL.uv E) e = Some z -> lo <= z <= hi -> kentry_ok RSEGS E M (KRange e lo hi).
Proof. intros Hz Hr. cbn [kentry_ok]. rewrite (BL.zeval_sound E e z Hz). lia. Qed.

Lemma adenot_var E j off : adenot E (SA (EVar j) off) = Z_to_bv 64 (bv_unsigned (ev E j) + off).
Proof. reflexivity. Qed.

Lemma kentry_KRange_var E M j lo hi a : bv_unsigned (ev E j) = a -> lo <= a <= hi -> kentry_ok RSEGS E M (KRange (EVar j) lo hi).
Proof. intros Ha Hr. cbn [kentry_ok edenot]. rewrite Ha. lia. Qed.

Lemma kentry_KRange_z E M e t lo hi z : BL.zcomp e = Some t -> BL.zden (BL.uv E) t = z -> lo <= z <= hi -> kentry_ok RSEGS E M (KRange e lo hi).
Proof. intros Ht Hz Hr. cbn [kentry_ok]. rewrite (BL.zcomp_sound E e t Ht), Hz. lia. Qed.

Lemma kentry_KAlign_var E M j m a : bv_unsigned (ev E j) = a -> 0 < m -> a mod m = 0 -> kentry_ok RSEGS E M (KAlign (EVar j) m).
Proof. intros Ha Hm H0. cbn [kentry_ok edenot]. rewrite Ha. auto. Qed.

(* [comment removed for export] *)
Lemma kentry_KWr_z E M j off (a : Z) ne t n :
  bv_unsigned (ev E j) = a -> BL.zcomp ne = Some t -> BL.zden (BL.uv E) t = n ->
  0 <= a + off -> 0 < n < 2 ^ 64 -> a + off + n <= 2 ^ 64 ->
  writable M (a + off) n -> kentry_ok RSEGS E M (KWr (SA (EVar j) off) ne).
Proof.
  intros Ha Ht Hn H1 H2 H3 Hw. cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_var, Ha.
  rewrite (BL.zcomp_sound E ne t Ht), Hn. split. lia. intros d m Hd Hm. apply Hw; lia.
Qed.

Lemma kentry_KDisj_z E M j1 off1 n1e t1 n1 j2 off2 n2e t2 n2 (a1 a2 : Z) :
  bv_unsigned (ev E j1) = a1 -> bv_unsigned (ev E j2) = a2 ->
  BL.zcomp n1e = Some t1 -> BL.zden (BL.uv E) t1 = n1 -> BL.zcomp n2e = Some t2 -> BL.zden (BL.uv E) t2 = n2 ->
  (a1 + off1 + n1 <= a2 + off2 \/ a2 + off2 + n2 <= a1 + off1) ->
  kentry_ok RSEGS E M (KDisj (SA (EVar j1) off1) n1e (SA (EVar j2) off2) n2e).
Proof.
  intros Ha1 Ha2 Ht1 Hn1 Ht2 Hn2 Hd. cbn [kentry_ok]. unfold elenZ. rewrite !estart_var, Ha1, Ha2.
  rewrite (BL.zcomp_sound E n1e t1 Ht1), Hn1, (BL.zcomp_sound E n2e t2 Ht2), Hn2. exact Hd.
Qed.

(* [comment removed for export] *)
Definition u8_at (M : word -> option byte) (a : Z) (b : Z) : Prop :=
  rdn RSEGS M (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 b].

Lemma word_to_le_bytes_1 z : 0 <= z < 256 -> word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros Hz. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small z (2^64)) by lia. reflexivity.
Qed.

Lemma kentry_KWord1_lit E M j off (a b : Z) :
  bv_unsigned (ev E j) = a -> 0 <= a + off -> a + off + 1 <= 2 ^ 64 -> 0 <= b < 256 ->
  u8_at M (a + off) b -> kentry_ok RSEGS E M (KWord (SA (EVar j) off) 1 (ELit b)).
Proof.
  intros Ha H1 H2 Hb Hu. cbn [kentry_ok]. split. lia. split.
  - unfold flat. rewrite estart_var, Ha. lia.
  - rewrite adenot_var, Ha. cbn [edenot]. rewrite word_to_le_bytes_1 by auto. exact Hu.
Qed.

Lemma kentry_KWord_lit E M j off (a v : Z) :
  bv_unsigned (ev E j) = a -> 0 <= a + off -> a + off + 8 <= 2 ^ 64 ->
  u64_at M (a + off) v -> kentry_ok RSEGS E M (KWord (SA (EVar j) off) 8 (ELit v)).
Proof.
  intros Ha H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
  - unfold flat. rewrite estart_var, Ha. lia.
  - rewrite adenot_var, Ha. cbn [edenot]. exact Hu.
Qed.

(* [comment removed for export] *)
Lemma kentry_KWord_z E M j off e t (a v : Z) :
  bv_unsigned (ev E j) = a -> BL.zcomp e = Some t -> BL.zden (BL.uv E) t = v ->
  0 <= a + off -> a + off + 8 <= 2 ^ 64 ->
  u64_at M (a + off) v -> kentry_ok RSEGS E M (KWord (SA (EVar j) off) 8 e).
Proof.
  intros Ha Ht Hv H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
  - unfold flat. rewrite estart_var, Ha. lia.
  - rewrite adenot_var, Ha. pose proof (BL.zcomp_sound E e t Ht) as S. rewrite Hv in S.
    rewrite (word_of_unsigned _ _ S). exact Hu.
Qed.

Lemma u8_of_KWord1 E M j off (a b : Z) :
  kentry_ok RSEGS E M (KWord (SA (EVar j) off) 1 (ELit b)) -> bv_unsigned (ev E j) = a -> 0 <= b < 256 -> u8_at M (a + off) b.
Proof.
  intros K Ha Hb. cbn [kentry_ok] in K. destruct K as (_ & F & Rd). unfold u8_at.
  rewrite adenot_var, Ha in Rd. cbn [edenot] in Rd. rewrite word_to_le_bytes_1 in Rd by auto. exact Rd.
Qed.

(* [comment removed for export] *)
Lemma bv_add_lit (a : Z) (w : word) k : bv_unsigned w = a -> (w + Z_to_bv 64 k)%bv = Z_to_bv 64 (a + k).
Proof.
  intros Ha. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, Ha. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.


Lemma kentry_KWord_var E M j off k (a v : Z) :
  bv_unsigned (ev E j) = a -> bv_unsigned (ev E k) = v ->
  0 <= a + off -> a + off + 8 <= 2 ^ 64 ->
  u64_at M (a + off) v -> kentry_ok RSEGS E M (KWord (SA (EVar j) off) 8 (EVar k)).
Proof.
  intros Ha Hv H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
  - unfold flat. rewrite estart_var, Ha. lia.
  - rewrite adenot_var, Ha. cbn [edenot]. rewrite (word_of_unsigned (ev E k) v Hv). exact Hu.
Qed.

Lemma kentry_KWr_var E M j off (a n : Z) :
  bv_unsigned (ev E j) = a -> 0 <= a + off -> 0 < n < 2 ^ 64 -> a + off + n <= 2 ^ 64 ->
  writable M (a + off) n -> kentry_ok RSEGS E M (KWr (SA (EVar j) off) (ELit n)).
Proof.
  intros Ha H1 H2 H3 Hw. cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_var, Ha. cbn [edenot].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
  split. lia. intros d m Hd Hm. apply Hw; lia.
Qed.

Lemma kentry_KUnk_var E M j off (a n : Z) :
  bv_unsigned (ev E j) = a -> 0 <= a + off -> 0 < n < 2 ^ 64 -> a + off + n <= 2 ^ 64 ->
  defined M (a + off) n -> kentry_ok RSEGS E M (KUnk (SA (EVar j) off) (ELit n)).
Proof.
  intros Ha H1 H2 H3 Hd. cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_var, Ha. cbn [edenot].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
  split. lia. intros i Hi. apply Hd. lia.
Qed.

(* [comment removed for export] *)
Lemma u64_of_KWord E M j off e (a z : Z) :
  kentry_ok RSEGS E M (KWord (SA (EVar j) off) 8 e) ->
  bv_unsigned (ev E j) = a -> bv_unsigned (edenot E e) = z -> u64_at M (a + off) z.
Proof.
  intros K Ha Hz. cbn [kentry_ok] in K. destruct K as (_ & F & Rd). unfold u64_at.
  rewrite adenot_var, Ha in Rd. rewrite <- (word_of_unsigned _ _ Hz). exact Rd.
Qed.

(* [comment removed for export] *)
Lemma adenot_e E b off : adenot E (SA b off) = Z_to_bv 64 (bv_unsigned (edenot E b) + off).
Proof. reflexivity. Qed.

Lemma kentry_KWord_e E M b off e (a v : Z) :
  bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E e) = v ->
  0 <= a + off -> a + off + 8 <= 2 ^ 64 ->
  u64_at M (a + off) v -> kentry_ok RSEGS E M (KWord (SA b off) 8 e).
Proof.
  intros Ha Hv H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
  - unfold flat, estart. cbn [a_base a_off]. rewrite Ha. lia.
  - rewrite adenot_e, Ha. rewrite (word_of_unsigned _ _ Hv). exact Hu.
Qed.

Lemma u64_of_KWord_e E M b off e (a z : Z) :
  kentry_ok RSEGS E M (KWord (SA b off) 8 e) ->
  bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E e) = z -> u64_at M (a + off) z.
Proof.
  intros K Ha Hz. cbn [kentry_ok] in K. destruct K as (_ & F & Rd). unfold u64_at.
  rewrite adenot_e, Ha in Rd. rewrite <- (word_of_unsigned _ _ Hz). exact Rd.
Qed.

Lemma rdn_of_bytes (M : word -> option byte) (f : Z -> byte) : forall n (a : Z),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) = Some (f (a + i))) ->
  rdn RSEGS M (Z_to_bv 64 a) n = Some (map (fun k => f (a + Z.of_nat k)) (seq 0 n)).
Proof.
  induction n as [|n IH]; intros a Ha Hn H. reflexivity.
  cbn [rdn seq map]. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0.
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1%bv : bv 64)) with 1.
      unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite (IH (a + 1)); try lia.
  - rewrite Z.add_0_r. f_equal. f_equal. rewrite <- seq_shift, map_map. apply map_ext. intros k. f_equal. lia.
  - intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply H. lia.
Qed.

Lemma u64_of_KZero_e E M b off (a : Z) :
  kentry_ok RSEGS E M (KZero (SA b off) (ELit 8)) -> bv_unsigned (edenot E b) = a -> u64_at M (a + off) 0.
Proof.
  intros K Ha. cbn [kentry_ok] in K. destruct K as [F Z0]. unfold flat, estart, elenZ in *. cbn [a_base a_off edenot] in *.
  rewrite Ha in F, Z0. rewrite Z_to_bv_unsigned in F, Z0. change (bv_wrap 64 8) with 8 in F, Z0.
  unfold u64_at. rewrite (rdn_of_bytes M (fun _ => Z_to_bv 8 0) 8 (a + off)); try lia.
  - reflexivity.
  - intros i Hi. apply Z0. simpl in Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_ext (M M' : word -> option byte) : forall n a,
  (forall i, 0 <= i < Z.of_nat n -> M' (Z_to_bv 64 (bv_unsigned a + i)) = M (Z_to_bv 64 (bv_unsigned a + i))) ->
  rdn RSEGS M' a n = rdn RSEGS M a n.
Proof.
  induction n as [|n IH]; intros a H. reflexivity.
  cbn [rdn]. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  replace (Z_to_bv 64 (bv_unsigned a)) with a in H0. 2:{ apply bv_eq. rewrite Z_to_bv_unsigned. symmetry; apply bv_wrap_bv_unsigned. }
  rewrite H0. rewrite (IH (a + 1)%bv). reflexivity.
  intros i Hi. pose proof (H (i + 1)) as Hi1.
  assert (E1: forall m : word -> option byte, m (Z_to_bv 64 (bv_unsigned (a + 1)%bv + i)) = m (Z_to_bv 64 (bv_unsigned a + (i + 1)))).
  { intros m. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
    replace (bv_unsigned (a + 1)%bv) with ((bv_unsigned a + 1) mod 2^64)%Z by (rewrite bv_add_unsigned; reflexivity).
    unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. rewrite Zplus_mod_idemp_l. f_equal. lia. }
  rewrite !E1. apply Hi1. lia.
Qed.

Lemma u64_at_frame (M M' : word -> option byte) a v :
  0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> M' (Z_to_bv 64 (a + i)) = M (Z_to_bv 64 (a + i))) ->
  u64_at M a v -> u64_at M' a v.
Proof.
  intros Ha Hb H Hu. unfold u64_at in *. rewrite <- Hu. apply rdn_ext. intros i Hi.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia. apply H. simpl in Hi. lia.
Qed.

Lemma defined_grows (M M' : word -> option byte) a n : mem_grows M M' -> defined M a n -> defined M' a n.
Proof. intros G D i Hi. apply G. apply D. auto. Qed.


(* [comment removed for export] *)
Lemma alu_add_lit a k : alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a + k).
Proof. unfold alu64, alu. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Z.add_mod; [reflexivity|]. discriminate. Qed.

Lemma md_mul_lit a b : mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof. unfold mul_div. apply bv_eq. rewrite bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Z.mul_mod; [reflexivity|discriminate]. Qed.

Lemma unsigned_lit a : 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact H. Qed.

Lemma writable_grows (M M' : word -> option byte) a n : mem_grows M M' -> writable M a n -> writable M' a n.
Proof. intros G W d k Hd Hk. eapply store_ok_mono. exact G. apply W; auto. Qed.

Lemma u64_keep (M M' : word -> option byte) (lo hi a v : Z) :
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> M' x = M x) ->
  0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= lo \/ hi <= a) -> u64_at M a v -> u64_at M' a v.
Proof.
  intros HF Ha Hb Hd Hu. apply (u64_at_frame M M' a v Ha Hb). 2: exact Hu. intros i Hi. apply HF. rewrite unsigned_lit by lia. lia.
Qed.

Lemma u64_keep2 (M M' : word -> option byte) (lo1 hi1 lo2 hi2 a v : Z) :
  (forall x : word, ~ (lo1 <= bv_unsigned x < hi1) -> ~ (lo2 <= bv_unsigned x < hi2) -> M' x = M x) ->
  0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= lo1 \/ hi1 <= a) -> (a + 8 <= lo2 \/ hi2 <= a) -> u64_at M a v -> u64_at M' a v.
Proof.
  intros HF Ha Hb Hd1 Hd2 Hu. apply (u64_at_frame M M' a v Ha Hb). 2: exact Hu. intros i Hi. apply HF; rewrite unsigned_lit by lia; lia.
Qed.

Lemma u8_at_frame (M M' : word -> option byte) a b :
  M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) -> u8_at M a b -> u8_at M' a b.
Proof. unfold u8_at. cbn [rdn]. intros H Hu. rewrite H. exact Hu. Qed.

Lemma u8_keep (M M' : word -> option byte) (lo hi a b : Z) :
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> M' x = M x) ->
  0 <= a < 2 ^ 64 -> (a + 1 <= lo \/ hi <= a) -> u8_at M a b -> u8_at M' a b.
Proof. intros HF Ha Hd Hu. apply (u8_at_frame M M' a b). 2: exact Hu. apply HF. rewrite unsigned_lit by lia. lia. Qed.

Lemma u8_keep2 (M M' : word -> option byte) (lo1 hi1 lo2 hi2 a b : Z) :
  (forall x : word, ~ (lo1 <= bv_unsigned x < hi1) -> ~ (lo2 <= bv_unsigned x < hi2) -> M' x = M x) ->
  0 <= a < 2 ^ 64 -> (a + 1 <= lo1 \/ hi1 <= a) -> (a + 1 <= lo2 \/ hi2 <= a) -> u8_at M a b -> u8_at M' a b.
Proof. intros HF Ha Hd1 Hd2 Hu. apply (u8_at_frame M M' a b). 2: exact Hu. apply HF; rewrite unsigned_lit by lia; lia. Qed.


End BG.
