(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg MmapSim SymExec MemSplit RefMemcpyLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymExec2Sound SymRun SymDrive.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_nth : forall segs E M kn i K,
  know_ok segs E M kn -> nth_error kn i = Some K -> kentry_ok segs E M K.
Proof.
  intros segs E M kn i K HK Hn. unfold know_ok in HK.
  apply (proj1 (Forall_forall _ _) HK K). eapply nth_error_In. exact Hn.
Qed.
End VP1.

Section VP2. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_app : forall segs E M k1 k2,
  know_ok segs E M (k1 ++ k2) <-> know_ok segs E M k1 /\ know_ok segs E M k2.
Proof. intros. unfold know_ok. apply Forall_app. Qed.
End VP2.

Section VP3. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_cons : forall segs E M K kn,
  kentry_ok segs E M K -> know_ok segs E M kn -> know_ok segs E M (K :: kn).
Proof. intros. constructor; assumption. Qed.
End VP3.

(* [comment removed for export] *)
Fixpoint kindex (p : kentry -> bool) (kn : list kentry) (i : nat) : option nat :=
  match kn with
  | [] => None
  | K :: r => if p K then Some i else kindex p r (S i)
  end.

(* [comment removed for export] *)
Definition is_krange (e : expr) (K : kentry) : bool :=
  match K with KRange e' _ _ => expr_eqb e e' | _ => false end.
Definition is_kalign (e : expr) (K : kentry) : bool :=
  match K with KAlign e' _ => expr_eqb e e' | _ => false end.
Definition is_kdisj (b1 : expr) (b2 : expr) (K : kentry) : bool :=
  match K with
  | KDisj (SA c1 _) _ (SA c2 _) _ => expr_eqb b1 c1 && expr_eqb b2 c2
  | _ => false
  end.
(* [comment removed for export] *)
Definition is_kwr_cov (b : expr) (k m : Z) (K : kentry) : bool :=
  match K with
  | KWr (SA c kk) len => expr_eqb b c && Z.leb kk k && Z.leb (k + m) (kk + len)
  | _ => false
  end.
(* [comment removed for export] *)
Definition is_kimg_cov (a n : Z) (K : kentry) : bool :=
  match K with
  | KImg lo hi => Z.leb lo a && Z.leb (a + n) hi
  | _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP4. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma rdn_agree : forall segs M M' n (a : word),
  (forall j, (j < n)%nat -> M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = M' (Z_to_bv 64 (bv_unsigned a + Z.of_nat j))) ->
  rdn segs M a n = rdn segs M' a n.
Proof.
  intros segs M M' n. induction n as [|n IH]; intros a Hag; [reflexivity|].
  cbn [rdn].
  pose proof (Hag 0%nat ltac:(lia)) as H0.
  rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  rewrite (IH (a + 1)); [reflexivity|].
  intros j Hj. rewrite w_add_1.
  pose proof (u64_range a) as Ha.
  destruct (Z_lt_le_dec (bv_unsigned a + 1) (2 ^ 64)) as [Hlt | Hge].
  - rewrite u_small by lia.
    replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
    apply Hag. lia.
  - replace (Z_to_bv 64 (bv_unsigned a + 1)) with (Z_to_bv 64 0)
      by (apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; replace (bv_unsigned a + 1)%Z with (2^64)%Z by lia; reflexivity).
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    specialize (Hag (S j) ltac:(lia)).
    replace (bv_unsigned a + Z.of_nat (S j))%Z with (2 ^ 64 + Z.of_nat j)%Z in Hag by lia.
    replace (Z_to_bv 64 (2 ^ 64 + Z.of_nat j)) with (Z_to_bv 64 (0 + Z.of_nat j)) in Hag; [exact Hag|].
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite <- (Zplus_mod_idemp_l (2 ^ 64) (Z.of_nat j)), Z_mod_same_full. reflexivity.
Qed.
End VP4.

(* [comment removed for export] *)
Section VP5. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma rdn_untouched : forall segs M (a : Z) n,
  (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall i, (a <= i < a + Z.of_nat n)%Z -> M (Z_to_bv 64 i) = None) ->
  rdn segs M (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros segs M a n H0 Hnw Hnone. apply rdn_agree. intros j Hj.
  rewrite u_small by lia. rewrite Hnone by lia. reflexivity.
Qed.
End VP5.

Section VP6. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kimg_rdn : forall segs E M kn i lo hi (a : Z) n,
  know_ok segs E M kn -> nth_error kn i = Some (KImg lo hi) ->
  (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z ->
  rdn segs M (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros segs E M kn i lo hi a n HK Hn Hlo Hhi.
  pose proof (know_nth segs E M kn i _ HK Hn) as (H0 & H64 & Hnone).
  apply rdn_untouched; [lia | lia |]. intros j Hj. apply Hnone. lia.
Qed.
End VP6.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP7. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kwr_store_ok : forall segs E M kn i b kk len (k : Z) (m : nat),
  know_ok segs E M kn -> nth_error kn i = Some (KWr (SA b kk) len) ->
  (kk <= k)%Z -> (k + Z.of_nat m <= kk + len)%Z ->
  store_ok segs M (adenot E (SA b k)) m = true.
Proof.
  intros segs E M kn i b kk len k m HK Hn H1 H2.
  pose proof (know_nth segs E M kn i _ HK Hn) as (Hfl & Hst).
  unfold adenot. cbn [a_base a_off].
  destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
  specialize (Hst (k - kk)%Z m ltac:(lia) ltac:(lia)).
  replace (bv_unsigned (edenot E b) + kk + (k - kk))%Z with (bv_unsigned (edenot E b) + k)%Z in Hst by lia.
  unfold v_addi. exact Hst.
Qed.
End VP7.

(* [comment removed for export] *)
Section VP8. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kwr_store_ok_lit : forall segs E M kn i kk len (k : Z) (m : nat),
  know_ok segs E M kn -> nth_error kn i = Some (KWr (SA (ELit 0) kk) len) ->
  (kk <= k)%Z -> (k + Z.of_nat m <= kk + len)%Z -> (0 <= k < 2 ^ 64)%Z ->
  store_ok segs M (Z_to_bv 64 k) m = true.
Proof.
  intros segs E M kn i kk len k m HK Hn H1 H2 Hk.
  pose proof (kwr_store_ok segs E M kn i (ELit 0) kk len k m HK Hn H1 H2) as H.
  unfold adenot, v_addi in H. cbn [a_base a_off edenot] in H.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in H. rewrite Z.add_0_l in H. exact H.
Qed.
End VP8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition entry_below_b (spi : nat) (ihi : Z) (e : sentry) : bool :=
  match e with
  | SE (SA (EVar i) k) w _ => Nat.eqb i spi && Z.leb (k + Z.of_nat w) 0 && Z.leb (- 2 ^ 40) k
  | SE (SA (ELit 0) k) w _ => Z.leb 0 k && Z.leb (k + Z.of_nat w) ihi
  | _ => false
  end.

Definition log_below_b (spi : nat) (ihi : Z) (log : list sentry) : bool :=
  forallb (entry_below_b spi ihi) log.

Section VP9. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma entry_below_sound : forall E spi ihi b k w v (x : word),
  entry_below_b spi ihi (SE (SA b k) w v) = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z ->
  (bv_unsigned (adenot E (SA b k)) + Z.of_nat w <= bv_unsigned x)%Z.
Proof.
  intros E spi ihi b k w v x He Hsp Hx1 Hx2.
  unfold adenot, v_addi. cbn [a_base a_off]. pose proof (u64_range x) as Hxr.
  destruct b as [z|i| | | | | |]; cbn [entry_below_b] in He; try discriminate.
  - destruct z; try discriminate. apply andb_prop in He as [He1 He2].
    apply Z.leb_le in He1. apply Z.leb_le in He2. cbn [edenot].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l, u_small by lia. lia.
  - apply andb_prop in He as [He1 He3]. apply andb_prop in He1 as [He1 He2].
    apply Nat.eqb_eq in He1. subst i. apply Z.leb_le in He2. apply Z.leb_le in He3.
    cbn [edenot]. pose proof (u64_range (ev E spi)) as Hs. rewrite u_small by lia. lia.
Qed.
End VP9.

Section VP10. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma mem_denot_above : forall E M log spi ihi (x : word),
  log_below_b spi ihi log = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  (bv_unsigned (ev E spi) <= bv_unsigned x)%Z -> (ihi <= bv_unsigned x)%Z ->
  mem_denot E M log x = M x.
Proof.
  intros E M log spi ihi x Hb Hsp Hx1 Hx2.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_below_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  pose proof (entry_below_sound E spi ihi b k w v x He Hsp Hx1 Hx2) as Hbnd.
  pose proof (u64_range x) as Hxr.
  cbn [mem_denot]. rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. lia.
  - rewrite length_N_to_le_bytes. right. lia.
Qed.
End VP10.

Section VP11. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma rdn_mem_denot_above : forall segs E M log spi ihi (a : word) n,
  log_below_b spi ihi log = true ->
  (2 ^ 40 <= bv_unsigned (ev E spi))%Z ->
  (bv_unsigned (ev E spi) <= bv_unsigned a)%Z -> (ihi <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn segs (mem_denot E M log) a n = rdn segs M a n.
Proof.
  intros segs E M log spi ihi a n Hb Hsp H1 H2 Hnw.
  apply rdn_agree. intros j Hj. pose proof (u64_range a).
  apply (mem_denot_above E M log spi ihi); try assumption; rewrite u_small by lia; lia.
Qed.
End VP11.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint esub (f t : expr) (e : expr) : expr :=
  if expr_eqb e f then t else
  match e with
  | EAlu op a b => EAlu op (esub f t a) (esub f t b)
  | EAluw op a b => EAluw op (esub f t a) (esub f t b)
  | EMd op a b => EMd op (esub f t a) (esub f t b)
  | EMdw op a b => EMdw op (esub f t a) (esub f t b)
  | EExt sx lo n a => EExt sx lo n (esub f t a)
  | _ => e
  end.

Section VP12. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma esub_sound : forall E f t e,
  edenot E f = edenot E t -> edenot E (esub f t e) = edenot E e.
Proof.
  intros E f t e Hft. induction e; cbn [esub];
    (destruct (expr_eqb _ f) eqn:Eq;
     [apply expr_eqb_eq in Eq; rewrite <- Eq in Hft; symmetry; exact Hft|]);
    cbn [edenot]; try reflexivity;
    try (rewrite IHe1, IHe2; reflexivity);
    try (rewrite IHe; reflexivity).
Qed.
End VP12.

Definition asub (f t : expr) (a : saddr) : saddr := SA (esub f t (a_base a)) (a_off a).

Section VP13. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma asub_sound : forall E f t a,
  edenot E f = edenot E t -> adenot E (asub f t a) = adenot E a.
Proof. intros E f t [b k] H. unfold asub, adenot. cbn [a_base a_off]. rewrite esub_sound by exact H. reflexivity. Qed.
End VP13.

Section VP14. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma asub_estart : forall E f t a,
  edenot E f = edenot E t -> estart E (asub f t a) = estart E a.
Proof. intros E f t [b k] H. unfold asub, estart. cbn [a_base a_off]. rewrite esub_sound by exact H. reflexivity. Qed.
End VP14.

Definition ksub (f t : expr) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (asub f t a) w (esub f t v)
  | KZero a n => KZero (asub f t a) (esub f t n)
  | KBlob a n bk => KBlob (asub f t a) (esub f t n) bk
  | KImg lo hi => K
  | KAlign e m => KAlign (esub f t e) m
  | KRange e lo hi => KRange (esub f t e) lo hi
  | KWr a n => KWr (asub f t a) n
  | KDisj a1 n1 a2 n2 => KDisj (asub f t a1) n1 (asub f t a2) n2
  end.

Section VP15. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma flat_asub : forall E f t a n,
  edenot E f = edenot E t -> flat E (asub f t a) n <-> flat E a n.
Proof. intros E f t a n H. unfold flat. rewrite asub_estart by exact H. tauto. Qed.
End VP15.

Section VP16. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma ksub_sound : forall segs E M f t K,
  edenot E f = edenot E t -> kentry_ok segs E M K -> kentry_ok segs E M (ksub f t K).
Proof.
  intros segs E M f t K H HK. destruct K; cbn [ksub kentry_ok] in *.
  - rewrite (asub_sound E f t a H), (esub_sound E f t v H). rewrite (flat_asub E f t a _ H). exact HK.
  - unfold elenZ in *. rewrite (esub_sound E f t n H), (asub_estart E f t a H). rewrite (flat_asub E f t a _ H). exact HK.
  - unfold elenZ in *. rewrite (esub_sound E f t n H), (asub_estart E f t a H). rewrite (flat_asub E f t a _ H). exact HK.
  - exact HK.
  - rewrite (esub_sound E f t e H). exact HK.
  - rewrite (esub_sound E f t e H). exact HK.
  - rewrite (asub_estart E f t a H). rewrite (flat_asub E f t a _ H). exact HK.
  - rewrite (asub_estart E f t a1 H), (asub_estart E f t a2 H). exact HK.
Qed.
End VP16.

Section VP17. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_ksub : forall segs E M f t kn,
  edenot E f = edenot E t -> know_ok segs E M kn -> know_ok segs E M (map (ksub f t) kn).
Proof.
  intros segs E M f t kn H HK. unfold know_ok in *. apply Forall_map.
  eapply Forall_impl; [|exact HK]. intros K. apply ksub_sound. exact H.
Qed.
End VP17.

Section VP18. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma regs_ok_esub : forall E f t sr R,
  edenot E f = edenot E t -> regs_ok E sr R -> regs_ok E (map (esub f t) sr) R.
Proof.
  intros E f t sr R H HR r. rewrite (HR r). unfold sr_get.
  destruct (bv_eqb r 0); [reflexivity|].
  revert sr HR. generalize (ridx r) as i. intros i sr _.
  revert i. induction sr as [|e rest IH]; intros i.
  - destruct i; reflexivity.
  - destruct i as [|i]; cbn [map nth].
    + symmetry. apply esub_sound. exact H.
    + apply IH.
Qed.
End VP18.

(* [comment removed for export] *)
Section VP19. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma regs_ok_ext : forall E sr sr' R,
  length sr = length sr' ->
  (forall i, (i < length sr)%nat -> edenot E (nth i sr (ELit 0)) = edenot E (nth i sr' (ELit 0))) ->
  regs_ok E sr R -> regs_ok E sr' R.
Proof.
  intros E sr sr' R Hlen Heq HR r. rewrite (HR r). unfold sr_get.
  destruct (bv_eqb r 0); [reflexivity|].
  destruct (Nat.lt_ge_cases (ridx r) (length sr)) as [Hlt | Hge].
  - apply Heq. exact Hlt.
  - rewrite !nth_overflow by lia. reflexivity.
Qed.
End VP19.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP20. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma junk_vals_length : forall R, length (junk_vals R) = 32%nat.
Proof. intros R. unfold junk_vals. rewrite length_map, length_seq. reflexivity. Qed.
End VP20.

Section VP21. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vals_ev_app_l : forall vals extra n, (n < length vals)%nat ->
  vals_ev (vals ++ extra) n = vals_ev vals n.
Proof. intros. unfold vals_ev. rewrite app_nth1 by assumption. reflexivity. Qed.
End VP21.

Section VP22. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vals_ev_app_r : forall vals extra n,
  vals_ev (vals ++ extra) (length vals + n) = vals_ev extra n.
Proof. intros. unfold vals_ev. rewrite app_nth2_plus. reflexivity. Qed.
End VP22.

(* [comment removed for export] *)
Section VP23. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma env_app_know : forall segs vals extra ebs M kn,
  kn_vars_lt (length vals) kn = true ->
  know_ok segs (Env (vals_ev vals) ebs) M kn -> know_ok segs (Env (vals_ev (vals ++ extra)) ebs) M kn.
Proof. intros. eapply know_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.
End VP23.

Section VP24. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma env_app_regs : forall vals extra ebs sr R,
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R -> regs_ok (Env (vals_ev (vals ++ extra)) ebs) sr R.
Proof. intros. eapply regs_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.
End VP24.

Section VP25. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma env_app_edenot : forall vals extra ebs e,
  expr_vars_lt (length vals) e = true ->
  edenot (Env (vals_ev (vals ++ extra)) ebs) e = edenot (Env (vals_ev vals) ebs) e.
Proof. intros. symmetry. eapply edenot_agree; [apply vals_app_agree | assumption]. Qed.
End VP25.

(* [comment removed for export] *)
Section VP26. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma regs_after_keeps : forall vals ebs sr R R' (kept : list reg),
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  (forall r : reg, In r kept -> getr R' r = getr R r) ->
  ~ In 0%bv kept ->
  regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs)
          (sr_after_call_j sr (map ridx kept) (length vals)) R'.
Proof.
  intros vals ebs sr R R' kept Hlt HR Hk H0.
  apply (regs_after_call vals ebs sr R R' (map ridx kept) Hlt HR).
  - intros i Hi. apply in_map_iff in Hi as (r & <- & Hr). split; [apply ridx_range|].
    rewrite ridx_roundtrip. apply Hk. exact Hr.
  - intros Hin. apply in_map_iff in Hin as (r & Hr0 & Hr). apply H0.
    replace 0%bv with r; [exact Hr|]. apply ridx_inj. rewrite Hr0. reflexivity.
Qed.
End VP26.

(* [comment removed for export] *)
Section VP27. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_after_store : forall segs E M kn sa w v bs kn' scs hs,
  carry [SE sa w v] kn [] = (kn', scs, hs) -> scs = [] ->
  know_ok segs E M kn -> (w <= 8)%nat -> flat E sa (Z.of_nat w) ->
  bs = word_to_le_bytes w (edenot E v) ->
  know_ok segs E (wbytes M (adenot E sa) bs) kn'.
Proof.
  intros segs E M kn sa w v bs kn' scs hs Hc -> HK Hw Hfl ->.
  change (wbytes M (adenot E sa) (word_to_le_bytes w (edenot E v))) with (mem_denot E M [SE sa w v]).
  eapply carry_after; [exact Hc | | exact HK | constructor].
  cbn [log_flat]. auto.
Qed.
End VP27.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP28. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma Z_to_bv_lit : forall z (w : word), bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof. intros z w <-. apply Z_to_bv_bv_unsigned. Qed.
End VP28.

(* [comment removed for export] *)
Section VP29. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma flat_intro : forall E b k n,
  (0 <= bv_unsigned (edenot E b) + k)%Z -> (0 <= n)%Z ->
  (bv_unsigned (edenot E b) + k < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k + n <= 2 ^ 64)%Z ->
  flat E (SA b k) n.
Proof. intros. unfold flat, estart. cbn [a_base a_off]. lia. Qed.
End VP29.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ECALLW : bv 32 := Z_to_bv 32 0x73.
Section VP30. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma is_ecall_ECALLW : is_ecall ECALLW = true. Proof. reflexivity. Qed.
End VP30.

(* [comment removed for export] *)
Section VP31. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma adenot_lit0 : forall E a, adenot E (SA (ELit 0) a) = Z_to_bv 64 a.
Proof. intros. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l. reflexivity. Qed.
End VP31.

Section VP32. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma edenot_add_lit : forall E b k, edenot E (EAlu ALU_ADD b (ELit k)) = adenot E (SA b k).
Proof.
  intros. cbn [edenot]. rewrite alu_add. unfold adenot, v_addi, v_add. cbn [a_base a_off].
  apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. apply Zplus_mod_idemp_r.
Qed.
End VP32.

(* [comment removed for export] *)
Ltac split_foralls :=
  repeat lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| ]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac p6_body t :=
  first [ let b := eval cbv delta [t] in t in b | t ].

(* [comment removed for export] *)
Ltac p6_run HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T ssn scs scr' knn scs2 hs2 :=
  eapply (rz_run segs fuel stops scr pc sr kn NX ssn scs scr' knn scs2 hs2 E M rom R model T);
  [ vm_cast_no_check (@eq_refl _ (ssn, scs, scr'))
  | vm_cast_no_check (@eq_refl _ (knn, scs2, hs2))
  | exact HR | exact HK
  | split_foralls
  | split_foralls
  | try reflexivity; try assumption
  | try reflexivity; try assumption
  | clear HR HK;
    let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in
    intros R' M' HR HK EQM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
    lazymatch keep with
    | true => idtac
    | false => clear EQM; try clear R; try clear M;
               try rename R' into R; try rename M' into M
    end;
    tryif is_var kn then try clear kn else idtac;
    tryif is_var sr then try clear sr else idtac ].

Ltac run_block_with HR HK fuel stops scr NX keep :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (SS ?pc' ?sr' ?log' ?kn0 ?nx', ?scs, ?scr') =>
          let c := eval vm_compute in (carry log' kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            let SRn := fresh "P6_SR" in
            pose (SRn := sr');
            let ssn := constr:(SS pc' SRn log' kn nx') in
            let knb := p6_body kn in
            tryif constr_eq knb kn'
            then p6_run HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T ssn scs scr' kn scs2 hs2
            else (let KNn := fresh "P6_KN" in
                  pose (KNn := kn');
                  p6_run HR HK fuel stops scr NX keep segs E sr R M kn pc rom model T ssn scs scr' KNn scs2 hs2)
          end
        end
      end
    end
  end.

Tactic Notation "run_block_gen" constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_block_with HR HK fuel stops scr NX keep
  end.

(* [comment removed for export] *)
Ltac regv HR r :=
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e;
    lazymatch e with ELit _ => cbn [edenot] | _ => idtac end
  end.

(* [comment removed for export] *)
Ltac krd HK a n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (ELit 0) a n) in
    lazymatch r with
    | Some ?v =>
        pose proof (kread_rdn segs E M kn (ELit 0) a n v HK
                      ltac:(vm_cast_no_check (@eq_refl _ (Some v))) ltac:(lia) ltac:(lia)
                      ltac:(unfold flat, estart; cbn [a_base a_off edenot];
                            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia)) as H;
        rewrite adenot_lit0 in H; cbn [edenot] in H
    | None => fail "krd: knowledge does not determine this read"
    end
  end.

(* [comment removed for export] *)
Ltac krdv HK i k n H :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    let r := eval vm_compute in (kread segs kn (EVar i) k n) in
    lazymatch r with
    | Some ?v =>
        let Hf := fresh "Hflat" in
        assert (Hf : flat E (SA (EVar i) k) (Z.of_nat n));
        [ | pose proof (kread_rdn segs E M kn (EVar i) k n v HK
                          ltac:(vm_cast_no_check (@eq_refl _ (Some v))) ltac:(lia) ltac:(lia) Hf) as H;
            clear Hf; cbn [edenot] in H ]
    | None => fail "krdv: knowledge does not determine this read"
    end
  end.

(* [comment removed for export] *)
Ltac kidx kn p :=
  let r := eval vm_compute in (kindex p kn 0) in
  lazymatch r with Some ?i => i | None => fail "kidx: no such entry" end.

(* [comment removed for export] *)
Ltac krd_solve HK :=
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some _ =>
      let H := fresh "Hrd" in
      krd HK a n H; rewrite H; clear H;
      first [ reflexivity | rewrite ?Z_to_bv_bv_unsigned; reflexivity | idtac ]
  end.

Section VP33. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma callee_kept_no0 : ~ In (0%bv : reg) callee_kept.
Proof.
  unfold callee_kept. intros Hin.
  repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]).
  exact Hin.
Qed.
End VP33.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_apart_b (allkn : list kentry) (ub : expr) (uk un : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => ranges_apart allkn ub uk un b k (Z.of_nat w)
  | KZero (SA b k) (ELit l) => Z.leb 0 l && Z.ltb l (2 ^ 64) && ranges_apart allkn ub uk un b k l
  | KBlob (SA b k) (ELit l) _ => Z.leb 0 l && Z.ltb l (2 ^ 64) && ranges_apart allkn ub uk un b k l
  | KImg _ _ => true
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart allkn ub uk un b k n
  | _ => false
  end.

Definition kn_unfill (kn : list kentry) (ub : expr) (uk un : Z) : list kentry :=
  List.filter (kentry_apart_b kn ub uk un) kn.

Section VP34. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma unfill_outside : forall (a n : word) M (x : word),
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
  unfill a n M x = M x.
Proof.
  intros a n M x H. unfold unfill.
  destruct H as [H|H].
  - rewrite (proj2 (Z.leb_gt _ _) H). reflexivity.
  - destruct (bv_unsigned a <=? bv_unsigned x)%Z; [|reflexivity].
    rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
Qed.
End VP34.

Section VP35. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma unfill_none : forall (a n : word) M (x : word), M x = None -> unfill a n M x = None.
Proof. intros a n M x H. unfold unfill. rewrite H. destruct (_ && _)%bool; reflexivity. Qed.
End VP35.

Section VP36. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma wview_ext : forall segs M M' (x : word), M' x = M x -> wview segs M' x = wview segs M x.
Proof. intros segs M M' x H. unfold wview. rewrite H. reflexivity. Qed.
End VP36.

Section VP37. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma store_ok_agree : forall segs M M' (a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n)%Z -> M' x = M x) ->
  store_ok segs M a n = true -> store_ok segs M' a n = true.
Proof.
  intros segs M M' a n Hnw Hag Hs. apply store_ok_of_all; [exact Hnw|].
  intros x Hx. rewrite (wview_ext segs M M' x (Hag x Hx)). exact (store_ok_all segs M n a Hnw Hs x Hx).
Qed.
End VP37.

Section VP38. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_unfill : forall segs E M kn ub uk un,
  know_ok segs E M kn -> flat E (SA ub uk) un -> (un < 2 ^ 64)%Z ->
  know_ok segs E (unfill (adenot E (SA ub uk)) (Z_to_bv 64 un) M) (kn_unfill kn ub uk un).
Proof.
  intros segs E M kn ub uk un HK Hfl Hun.
  pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  set (a := adenot E (SA ub uk)) in *. set (nw := Z_to_bv 64 un).
  assert (Hn : bv_unsigned nw = un) by (subst nw; apply u_small; lia).
  (* [comment removed for export] *)
  assert (OUT : forall x : word,
            (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + un <= bv_unsigned x)%Z ->
            unfill a nw M x = M x).
  { intros x Hx. apply unfill_outside. rewrite Hu, Hn. exact Hx. }
  unfold know_ok, kn_unfill. apply Forall_forall. intros K HinF.
  apply filter_In in HinF as [Hin Hb].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  assert (APART : forall b k n, ranges_apart kn ub uk un b k n = true ->
            ((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z)).
  { intros b k n H. eapply ranges_apart_sound; [exact HK | exact H]. }
  destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
    cbn [kentry_apart_b] in Hb; cbn [kentry_ok] in HKK |- *; try exact HKK.
  - (* [comment removed for export] *)
    destruct HKK as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
    rewrite <- Hr. apply rdn_agree. intros j Hj.
    pose proof (flat_u E _ _ Hf) as Hub. destruct Hf as (G1 & G2 & G3 & G4).
    apply OUT. rewrite u_small by lia. destruct (APART b k (Z.of_nat w) Hb); lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | |]; try discriminate.
    apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    destruct HKK as (Hf & Hz). split; [exact Hf|].
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. destruct Hf as (G1 & G2 & G3 & G4).
    intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
    rewrite u_small by lia. destruct (APART b k l Hap); lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | |]; try discriminate.
    apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    destruct HKK as (Hf & Hlen & Hz). split; [exact Hf|]. split; [exact Hlen|].
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. destruct Hf as (G1 & G2 & G3 & G4).
    intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
    rewrite u_small by lia. destruct (APART b k l Hap); lia.
  - (* [comment removed for export] *)
    destruct HKK as (H0 & H1 & Hnone). split; [exact H0|]. split; [exact H1|].
    intros i Hi. apply unfill_none. apply Hnone. exact Hi.
  - (* [comment removed for export] *)
    destruct HKK as (Hf & Hst). split; [exact Hf|].
    destruct Hf as (G1 & G2 & G3 & G4).
    intros d m Hd Hm. destruct m as [|m]; [reflexivity|].
    apply (store_ok_agree segs M); [rewrite u_small by lia; lia | | apply Hst; assumption].
    intros x Hx. rewrite u_small in Hx by lia. apply OUT. destruct (APART b k n Hb); lia.
Qed.
End VP38.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Ltac p6_sr_body sr k := tryif is_var sr then (let b := eval cbv delta [sr] in sr in k b) else k sr.
