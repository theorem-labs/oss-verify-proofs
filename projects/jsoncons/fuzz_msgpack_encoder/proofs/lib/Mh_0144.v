(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase.
Module BigLinkGlue.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BG.

Abbreviation RSEGS := Plain.M.loaded_segments.

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

End BigLinkGlue.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
Module L5Kn.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.

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

End L5Kn.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound BigLinkBase.
Module L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5KA.

Fixpoint zpolyA (V : nat -> Z) (e : expr) : option Z :=
  match e with
  | ELit z => Some z
  | EVar n => Some (V n)
  | EAlu ALU_ADD a b => match zpolyA V a, zpolyA V b with Some x, Some y => Some (x + y) | _, _ => None end
  | EAlu ALU_SUB a b => match zpolyA V a, zpolyA V b with Some x, Some y => Some (x - y) | _, _ => None end
  | EAlu ALU_SRL a (ELit s) =>
      if (Z.leb 0 s && Z.ltb s 64)%bool then match zpolyA V a with Some x => Some (x mod 18446744073709551616 / 2 ^ s) | None => None end else None
  | EMd M_MUL a b => match zpolyA V a, zpolyA V b with Some x, Some y => Some (x * y) | _, _ => None end
  | _ => None
  end.

Lemma zpolyA_sound E V e : forall zz, L5K.zagree E V e -> zpolyA V e = Some zz -> bv_unsigned (edenot E e) = zz mod BL.MM.
Proof.
  induction e; intros zz HA HZ; cbn [zpolyA L5K.zagree] in HA, HZ; try discriminate; cbn [edenot].
  - inversion HZ; subst. rewrite Z_to_bv_unsigned. reflexivity.
  - inversion HZ; subst. rewrite <- HA. symmetry. apply Z.mod_small. apply (BL.bvu_range (ev E n)).
  - destruct HA as [HA1 HA2]. destruct op; try discriminate.
    + destruct (zpolyA V e1) as [x|] eqn:E1; destruct (zpolyA V e2) as [y|] eqn:E2; try discriminate. inversion HZ; subst.
      rewrite (BL.zalu_sound ALU_ADD _ _ ((bv_unsigned (edenot E e1) + bv_unsigned (edenot E e2)) mod BL.MM)) by reflexivity.
      rewrite (IHe1 x HA1 eq_refl), (IHe2 y HA2 eq_refl). rewrite <- Zplus_mod. reflexivity.
    + destruct (zpolyA V e1) as [x|] eqn:E1; destruct (zpolyA V e2) as [y|] eqn:E2; try discriminate. inversion HZ; subst.
      rewrite (BL.zalu_sound ALU_SUB _ _ ((bv_unsigned (edenot E e1) - bv_unsigned (edenot E e2)) mod BL.MM)) by reflexivity.
      rewrite (IHe1 x HA1 eq_refl), (IHe2 y HA2 eq_refl). rewrite <- Zminus_mod. reflexivity.
    + destruct e2 as [s| | | | | | |]; try discriminate.
      destruct (Z.leb 0 s && Z.ltb s 64)%bool eqn:Hs; try discriminate. apply andb_prop in Hs as [Hs0 Hs1]. apply Z.leb_le in Hs0. apply Z.ltb_lt in Hs1.
      destruct (zpolyA V e1) as [x|] eqn:E1; try discriminate. inversion HZ; subst.
      rewrite (BL.zalu_sound ALU_SRL _ _ (bv_unsigned (edenot E e1) / 2 ^ (bv_unsigned (edenot E (ELit s)) mod 64))) by reflexivity.
      rewrite (IHe1 x HA1 eq_refl). cbn [edenot]. rewrite BG.unsigned_lit by lia.
      rewrite (Z.mod_small s 64) by lia. rewrite BL.MM_val.
      symmetry. apply Z.mod_small. split. apply Z.div_pos. apply Z.mod_pos_bound. lia. lia.
      apply Z.div_lt_upper_bound. lia. assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
      pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)). nia.
  - destruct HA as [HA1 HA2]. destruct op; try discriminate.
    destruct (zpolyA V e1) as [x|] eqn:E1; destruct (zpolyA V e2) as [y|] eqn:E2; try discriminate. inversion HZ; subst.
    rewrite (BL.zmd_sound M_MUL _ _ ((bv_unsigned (edenot E e1) * bv_unsigned (edenot E e2)) mod BL.MM)) by reflexivity.
    rewrite (IHe1 x HA1 eq_refl), (IHe2 y HA2 eq_refl). rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma zpolyA_val E V e z v : L5K.zagree E V e -> zpolyA V e = Some z -> z mod BL.MM = v -> bv_unsigned (edenot E e) = v.
Proof. intros HA HZ Hv. rewrite (zpolyA_sound E V e z HA HZ). exact Hv. Qed.
Lemma zpolyA_word E V e z v : L5K.zagree E V e -> zpolyA V e = Some z -> z mod BL.MM = v -> edenot E e = Z_to_bv 64 v.
Proof. intros HA HZ Hv. apply BG.word_of_unsigned. eapply zpolyA_val; eauto. Qed.

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Definition zeros_at (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

Lemma kentry_KZero E M b off ne a n :
  bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E ne) = n ->
  0 <= a + off -> 0 < n -> a + off + n <= 2 ^ 64 ->
  zeros_at M (a + off) n -> kentry_ok segs E M (KZero (SA b off) ne).
Proof.
  intros Ha Hn H1 H2 H3 Hz. cbn [kentry_ok]. unfold flat, elenZ. rewrite L5K.estart_e, Ha, Hn.
  split. lia. intros i Hi. apply Hz. lia.
Qed.
Lemma zeros_of_KZero E M b off ne a n :
  kentry_ok segs E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E ne) = n -> zeros_at M (a + off) n.
Proof.
  intros (Hf & Hz) Ha Hn i Hi. unfold elenZ in Hz. rewrite L5K.estart_e, Ha, Hn in Hz. apply Hz. lia.
Qed.
Lemma zeros_at_sub M a n a' n' : zeros_at M a n -> a <= a' -> a' + n' <= a + n -> zeros_at M a' n'.
Proof. intros Hz H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply Hz. lia. Qed.
Lemma zeros_at_agree1 M M' a n : (forall i, a <= i < a + n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> zeros_at M a n -> zeros_at M' a n.
Proof. intros HA Hz i Hi. rewrite HA by lia. apply Hz. lia. Qed.
Lemma zeros_at_defined M a n : zeros_at M a n -> L5.defined M a n.
Proof. intros Hz i Hi. rewrite (Hz i Hi). discriminate. Qed.
(* [comment removed for export] *)
Lemma u8_of_zeros M a n i : zeros_at M a n -> 0 <= i < n -> 0 <= a + i < 2 ^ 64 -> L5.u8_at segs M (a + i) 0.
Proof.
  intros Hz Hi Hr. unfold L5.u8_at. cbn [rdn]. rewrite (Hz i Hi). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma word_to_le_bytes_1_mod z : 0 <= z < 2 ^ 64 -> word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 (z mod 256)].
Proof.
  intros Hz. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small z (2^64)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma u8_of_KWord1_mod E M b off e a v :
  kentry_ok segs E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E e) = v ->
  L5.u8_at segs M (a + off) (v mod 256).
Proof.
  intros K Ha Hv. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd). unfold L5.u8_at.
  rewrite L5K.adenot_e, Ha in Rd. rewrite (BG.word_of_unsigned _ _ Hv) in Rd.
  rewrite word_to_le_bytes_1_mod in Rd. exact Rd. rewrite <- Hv. apply (BL.bvu_range (edenot E e)).
Qed.
End WithSegs.
End L5KA.

End L5KnA.
