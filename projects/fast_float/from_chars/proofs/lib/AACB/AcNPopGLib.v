(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf AXG_gp AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA AcPri AcNPop AcPriStep AcNPopG.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma tcls_spec : forall nd, 1 <= nd <= 65536 -> 1 <= tcls nd <= 30 /\ sz_tbl (tcls nd - 1) < nd <= sz_tbl (tcls nd).
Proof.
  intros nd H.
  assert (A : allb (fun x => (65536 <? x) || ((1 <=? tcls x) && (tcls x <=? 30) && (sz_tbl (tcls x - 1) <? x) && (x <=? sz_tbl (tcls x)))) 1 17 = true)
    by (vm_cast_no_check (eq_refl true)).
  pose proof (allb_ok _ _ _ A nd ltac:(change (2 ^ Z.of_nat 17) with 131072; lia)) as B. cbv beta in B.
  apply orb_prop in B as [B|B]; [apply Z.ltb_lt in B; lia|].
  apply andb_prop in B as [B B4]. apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2].
  apply Z.leb_le in B1, B2, B4. apply Z.ltb_lt in B3. lia.
Qed.
Lemma tcls_cls_of : forall nd, 1 <= nd <= 65536 -> cls_of nd = tcls nd.
Proof. intros nd H. destruct (tcls_spec nd H) as [H1 H2]. exact (cls_of_tbl (tcls nd) nd H1 H2). Qed.
Lemma tcls_step : forall nd, 1 <= nd < 65536 -> tcls nd <= tcls (nd + 1).
Proof.
  intros nd H.
  assert (A : allb (fun x => (65536 <=? x) || (tcls x <=? tcls (x + 1))) 1 17 = true) by (vm_cast_no_check (eq_refl true)).
  pose proof (allb_ok _ _ _ A nd ltac:(change (2 ^ Z.of_nat 17) with 131072; lia)) as B. cbv beta in B.
  apply orb_prop in B as [B|B]; [apply Z.leb_le in B; lia | apply Z.leb_le in B; exact B].
Qed.
Lemma tcls_mono : forall a b, 1 <= a -> a <= b -> b <= 65536 -> tcls a <= tcls b.
Proof.
  intros a b Ha Hab Hb. replace b with (a + Z.of_nat (Z.to_nat (b - a))) in * by lia. generalize dependent (Z.to_nat (b - a)). intros n.
  induction n as [|n IH]; intros Hab Hb; [rewrite Z.add_0_r; lia|].
  rewrite Nat2Z.inj_succ in *. specialize (IH ltac:(lia) ltac:(lia)).
  pose proof (tcls_step (a + Z.of_nat n) ltac:(lia)) as X. replace (a + Z.succ (Z.of_nat n)) with (a + Z.of_nat n + 1) by lia. lia.
Qed.
Lemma in_crange : forall clo chi c, clo <= c <= chi -> In c (crange clo chi).
Proof. intros clo chi c H. unfold crange. apply in_map_iff. exists (Z.to_nat (c - clo)). split; [lia | apply in_seq; lia]. Qed.
Lemma crange_rng : forall clo chi c, In c (crange clo chi) -> clo <= c <= chi.
Proof. intros clo chi c H. unfold crange in H. apply in_map_iff in H as (i & <- & Hi). apply in_seq in Hi. lia. Qed.
Lemma rng_in_cls : forall c, 1 <= c <= 30 -> In c CLS.
Proof. intros c H. cls30_go c H; unfold CLS; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ]. Qed.

(* [comment removed for export] *)
Fixpoint ext_cls (E : valu) (vj : positive) (cs : list Z) (f : Z -> Z * Z) : valu :=
  match cs with [] => E | c :: r => ext_cls (upd (upd E vj (wa (fst (f c)))) (vj + 1) (wa (snd (f c)))) (vj + 2) r f end.
Lemma ext_cls_lt : forall cs E vj f x, (x < vj)%positive -> ext_cls E vj cs f x = E x.
Proof.
  induction cs as [|c r IH]; intros E vj f x Hx; [reflexivity|]. cbn [ext_cls]. rewrite IH by lia. unfold upd.
  replace (Pos.eqb x (vj + 1)) with false by (symmetry; apply Pos.eqb_neq; lia).
  replace (Pos.eqb x vj) with false by (symmetry; apply Pos.eqb_neq; lia). reflexivity.
Qed.
Fixpoint cvals_ok (E : valu) (vj : positive) (cs : list Z) (f : Z -> Z * Z) : Prop :=
  match cs with [] => True | c :: r => E vj = wa (fst (f c)) /\ E (vj + 1)%positive = wa (snd (f c)) /\ cvals_ok E (vj + 2) r f end.
Lemma ext_cls_ok : forall cs E vj f, cvals_ok (ext_cls E vj cs f) vj cs f.
Proof.
  induction cs as [|c r IH]; intros E vj f; [exact I|]. cbn [ext_cls cvals_ok]. split; [|split; [|apply IH]].
  - rewrite ext_cls_lt by lia. unfold upd. replace (Pos.eqb vj (vj + 1)) with false by (symmetry; apply Pos.eqb_neq; lia). rewrite Pos.eqb_refl. reflexivity.
  - rewrite ext_cls_lt by lia. unfold upd. rewrite Pos.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fT (T : list Z) (c : Z) : Z * Z := (nth (5 + 2 * cidx c) T 0, nth (6 + 2 * cidx c) T 0).
Fixpoint setz (cs : list Z) (T pz : list Z) : list Z :=
  match cs with [] => pz | c :: r => setz r T (set_nth (6 + 2 * cidx c) (nth (6 + 2 * cidx c) T 0) (set_nth (5 + 2 * cidx c) (nth (5 + 2 * cidx c) T 0) pz)) end.
Lemma uE_lvar_wa : forall E x v, E x = wa v -> 0 <= v < 2^64 -> uE E (lvar x) = v.
Proof. intros E x v H Hv. unfold uE. rewrite lden_lvar, H. apply u_wa_small. exact Hv. Qed.
Lemma map_set_classes : forall cs E vj pri T, cvals_ok E vj cs (fT T) -> (forall k, 0 <= nth k T 0 < 2^64) ->
  List.map (uE E) (set_classes vj cs pri) = setz cs T (List.map (uE E) pri).
Proof.
  induction cs as [|c r IH]; intros E vj pri T Hc HT; [reflexivity|]. cbn [set_classes setz]. destruct Hc as (H1 & H2 & H3).
  rewrite (IH E (vj + 2)%positive _ T H3 HT). rewrite !map_set_nth.
  rewrite (uE_lvar_wa E vj _ H1 (HT _)), (uE_lvar_wa E (vj + 1)%positive _ H2 (HT _)). reflexivity.
Qed.
Definition hitk (k : nat) (cs : list Z) : bool := existsb (fun c => Nat.eqb k (5 + 2 * cidx c) || Nat.eqb k (6 + 2 * cidx c))%bool cs.
Lemma setz_length : forall cs T pz, List.length (setz cs T pz) = List.length pz.
Proof. induction cs as [|c r IH]; intros T pz; [reflexivity|]. cbn [setz]. rewrite IH, !set_nth_length. reflexivity. Qed.
Lemma nth_setz : forall cs T pz k, List.length pz = PRI_LEN -> (forall c, In c cs -> 1 <= c <= 30) ->
  nth k (setz cs T pz) 0 = if hitk k cs then nth k T 0 else nth k pz 0.
Proof.
  induction cs as [|c r IH]; intros T pz k Hl Hr; [reflexivity|]. cbn [setz]. unfold hitk. cbn [existsb]. fold (hitk k r).
  pose proof (cidx_rng c (Hr c (or_introl eq_refl))) as Hi.
  set (pz1 := set_nth (6 + 2 * cidx c) (nth (6 + 2 * cidx c) T 0) (set_nth (5 + 2 * cidx c) (nth (5 + 2 * cidx c) T 0) pz)).
  assert (Hl1 : List.length pz1 = PRI_LEN) by (unfold pz1; rewrite !set_nth_length; exact Hl).
  rewrite (IH T pz1 k Hl1 (fun c' Hc' => Hr c' (or_intror Hc'))). unfold pz1.
  destruct (hitk k r); [rewrite orb_true_r; reflexivity|]. rewrite orb_false_r.
  rewrite nth_set_nth by (rewrite set_nth_length, Hl; unfold PRI_LEN; lia).
  rewrite nth_set_nth by (rewrite Hl; unfold PRI_LEN; lia).
  destruct (Nat.eqb k (6 + 2 * cidx c)) eqn:E6; [apply Nat.eqb_eq in E6; subst k; rewrite orb_true_r; reflexivity|].
  destruct (Nat.eqb k (5 + 2 * cidx c)) eqn:E5; [apply Nat.eqb_eq in E5; subst k; reflexivity | reflexivity].
Qed.
Lemma setz_step : forall cs pz c, List.length pz = PRI_LEN -> (forall c', In c' cs -> 1 <= c' <= 30) -> In c cs ->
  setz cs (pz_step pz c) pz = pz_step pz c.
Proof.
  intros cs pz c Hl Hr Hc. pose proof (Hr c Hc) as Hcr.
  apply (nth_ext _ _ 0 0); [rewrite setz_length, (step_len pz c Hl); exact Hl|].
  intros k _. rewrite (nth_setz cs _ pz k Hl Hr). destruct (hitk k cs) eqn:Eh; [reflexivity|].
  change (nth k pz 0) with (zn pz k). change (nth k (pz_step pz c) 0) with (zn (pz_step pz c) k). rewrite (zn_step pz c Hl Hcr k).
  unfold hitk in Eh. rewrite <- not_true_iff_false in Eh.
  destruct (Nat.eqb k (6 + 2 * cidx c)) eqn:E6; [exfalso; apply Eh; apply existsb_exists; exists c; split; [exact Hc | rewrite E6; apply orb_true_r]|].
  destruct (Nat.eqb k (5 + 2 * cidx c)) eqn:E5; [exfalso; apply Eh; apply existsb_exists; exists c; split; [exact Hc | rewrite E5; reflexivity]|].
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma class_facts_ok : forall cs E fs a vj T, cvals_ok E vj cs (fT T) -> (forall k, 0 <= nth k T 0 < 2^64) ->
  (forall c, In c cs -> fst (irange fs (p_j a c)) <= nth (5 + 2 * cidx c) T 0 <= snd (irange fs (p_j a c)) + 1 /\ 0 <= nth (6 + 2 * cidx c) T 0 <= 262144 /\
                        0 <= nth (5 + 2 * cidx c) T 0 - uE E (p_j a c) <= 1) ->     (* [comment removed for export] *)
  Forall (fact_ok E) (class_facts fs a vj cs).
Proof.
  induction cs as [|c r IH]; intros E fs a vj T Hc HT Hb; [constructor|]. cbn [class_facts]. destruct Hc as (H1 & H2 & H3).
  destruct (Hb c (or_introl eq_refl)) as (B1 & B2 & B3).
  constructor; [|constructor; [|constructor; [|exact (IH E fs a (vj + 2)%positive T H3 HT (fun c' Hc' => Hb c' (or_intror Hc')))]]].
  - cbn [fact_ok]. fold (uE E (lvar vj)). rewrite (uE_lvar_wa E vj _ H1 (HT _)). exact B1.
  - cbn [fact_ok]. fold (uE E (lvar (vj + 1))). rewrite (uE_lvar_wa E (vj + 1)%positive _ H2 (HT _)). exact B2.
  - cbn [fact_ok]. rewrite lden_lsub, bv_sub_unsigned. fold (uE E (lvar vj)) (uE E (p_j a c)). rewrite (uE_lvar_wa E vj _ H1 (HT _)).
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. change (fst (fT T c)) with (nth (5 + 2 * cidx c) T 0).
    rewrite Z.mod_small by (unfold two64; clear - B3; lia). exact B3.
Qed.

(* [comment removed for export] *)
Lemma HA_on_ext_add : forall E M a m0 b z, HA_on E M a m0 -> (a_pri a <> [] -> ext_sem (pden E a) (uE E b) (uE E z)) ->
  (* [comment removed for export] *)
  (a_pri a <> [] -> forall q, In q (x_rngs E a) -> forall x, ~ (uE E b <= x < uE E b + uE E z /\ in_rg q x)) ->
  HA_on E M (ext_add a b z) m0.
Proof.
  intros E M a m0 b z [Hdep Hown Hownx Hhi HgD HgB Hpri] Hx Hnew. constructor; try assumption.
  intros Hne. change (a_pri (ext_add a b z)) with (a_pri a) in Hne. destruct (Hpri Hne) as [Hi Ho Hp Ht Hz Hs Hxt Hlv]. constructor; try assumption.
  - intros p Hp'. rewrite a_ext_add in Hp'. destruct Hp' as [<-|Hp']; [exact (Hx Hne) | exact (Hxt p Hp')].
  - exact (lv_inv_ext_add E a m0 b z (Hnew Hne) Hlv).
Qed.

(* [comment removed for export] *)
Lemma ldiv8_wf : forall n l l', ldiv8 l = Some l' -> lwf n l = true -> lwf n l' = true.
Proof.
  intros n [c t] l' H Hw. unfold ldiv8 in H. cbn [l_c l_t] in H.
  destruct (Z.eqb (Z.rem (sgn64 c) 8) 0 && forallb (fun '(_, k) => Z.eqb (Z.rem (sgn64 k) 8) 0) t)%bool; [|discriminate].
  injection H as <-. unfold lwf in *. cbn [l_t] in *. clear - Hw. induction t as [|[x k] t IH]; [reflexivity|].
  cbn [List.map forallb] in *. apply andb_prop in Hw as [H1 H2]. rewrite H1, (IH H2). reflexivity.
Qed.
Lemma uE_ldiv8 : forall E l l', ldiv8 l = Some l' -> 8 * uE E l' < two64 -> uE E l = 8 * uE E l'.
Proof.
  intros E l l' H Hb. pose proof (ldiv8_eqm E l l' H) as Hq. unfold eqm in Hq. unfold uE, lden in *. rewrite !u_Z_to_bv in *.
  rewrite Hq. pose proof (Z.mod_pos_bound (lz E l') two64 ltac:(unfold two64; lia)) as B.
  rewrite <- (Z.mod_small (8 * (lz E l' mod two64)) two64) by lia.
  rewrite <- Zmult_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma set_classes_length : forall cs vj pri, List.length (set_classes vj cs pri) = List.length pri.
Proof. induction cs as [|c r IH]; intros vj pri; [reflexivity|]. cbn [set_classes]. rewrite IH, !set_nth_length. reflexivity. Qed.
Lemma set_classes_base : forall cs vj pri k, (k < 5)%nat -> (forall c, In c cs -> 1 <= c <= 30) -> List.length pri = PRI_LEN ->
  nth k (set_classes vj cs pri) lc0 = nth k pri lc0.
Proof.
  induction cs as [|c r IH]; intros vj pri k Hk Hr Hl; [reflexivity|]. cbn [set_classes].
  pose proof (cidx_rng c (Hr c (or_introl eq_refl))) as Hi.
  rewrite IH; [| exact Hk | intros c' Hc'; apply Hr; right; exact Hc' | rewrite !set_nth_length; exact Hl].
  rewrite nth_set_nth by (rewrite set_nth_length, Hl; unfold PRI_LEN; lia).
  replace (Nat.eqb k (6 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite nth_set_nth by (rewrite Hl; unfold PRI_LEN; lia).
  replace (Nat.eqb k (5 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

Lemma cvals_ok_agree : forall cs E E3 vj f n, cvals_ok E vj cs f -> agree n E E3 -> (Pos.to_nat vj + 2 * List.length cs <= Pos.to_nat n)%nat ->
  cvals_ok E3 vj cs f.
Proof.
  induction cs as [|c r IH]; intros E E3 vj f n Hc Ha Hn; [exact I|]. cbn [cvals_ok List.length] in *. destruct Hc as (H1 & H2 & H3).
  split; [rewrite <- (Ha vj ltac:(lia)); exact H1|]. split; [rewrite <- (Ha (vj + 1)%positive ltac:(lia)); exact H2|].
  apply (IH E E3 (vj + 2)%positive f n H3 Ha). lia.
Qed.
Lemma sz_tbl_mod32 : forall c, 1 <= c <= 30 -> sz_tbl c mod 32 = 0.
Proof. intros c H. cls30_go c H; reflexivity. Qed.
Lemma pden_nth_rng : forall E a k, 0 <= nth k (pden E a) 0 < 2^64.
Proof.
  intros E a k. unfold pden. destruct (Nat.lt_ge_cases k (List.length (a_pri a))) as [Hk|Hk].
  - rewrite (nth_indep _ 0 (uE E lc0)) by (rewrite length_map; exact Hk). rewrite map_nth. pose proof (uE_range E (nth k (a_pri a) lc0)) as U. unfold two64 in U. exact U.
  - rewrite nth_overflow by (rewrite length_map; exact Hk). lia.
Qed.
Lemma pz_step_nth_rng : forall E a c, List.length (a_pri a) = PRI_LEN -> 1 <= c <= 30 -> 0 <= z_j (pden E a) c + 1 < 2^64 ->
  forall k, 0 <= nth k (pz_step (pden E a) c) 0 < 2^64.
Proof.
  intros E a c Hl Hc Hj k. assert (Hlz : List.length (pden E a) = PRI_LEN) by (unfold pden; rewrite length_map; exact Hl).
  change (nth k (pz_step (pden E a) c) 0) with (zn (pz_step (pden E a) c) k). rewrite (zn_step (pden E a) c Hlz Hc k).
  destruct (Nat.eqb k (6 + 2 * cidx c)); [lia|]. destruct (Nat.eqb k (5 + 2 * cidx c)); [exact Hj|]. exact (pden_nth_rng E a k).
Qed.
(* [comment removed for export] *)
