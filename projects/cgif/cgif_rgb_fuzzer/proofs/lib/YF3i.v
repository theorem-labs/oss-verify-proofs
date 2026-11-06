(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG0h YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3v YF8g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tblr (i : Z) (cs : list YQ0b.chunk) : YQ0b.region :=
YQ0b.mkRegion (Some rT) (212 + 80 * i) (224 + 80 * i) (212 + 80 * i) (224 + 80 * i) cs.
Definition tblF (i : Z) : YQ0b.region :=
tblr i [YQ0b.mkChunk (216 + 80 * i) (CVal 8 (SLit (class_size i))); YQ0b.mkChunk (212 + 80 * i) (CVal 4 (SLit (max_cached i)))].
Definition TBLS0 : smem := Eval vm_compute in map (fun k => tblr (Z.of_nat k) []) (seq 1 31).
Definition TBLSF : smem := Eval vm_compute in map (fun k => tblF (Z.of_nat k)) (seq 1 31).
Lemma TBLS0_eq : TBLS0 = map (fun k => tblr (Z.of_nat k) []) (seq 1 31). Proof. img_refl. Qed.
Lemma TBLSF_eq : TBLSF = map (fun k => tblF (Z.of_nat k)) (seq 1 31). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.


Lemma In_TBLS0 : forall r, In r TBLS0 -> exists i, 1 <= i <= 31 /\ r = tblr i [].
Proof.
intros r Hr. rewrite TBLS0_eq in Hr. apply in_map_iff in Hr as (k & <- & Hk). apply in_seq in Hk.
exists (Z.of_nat k). split; [img_lia | img_refl].
Qed.


Lemma TBLSF_In : forall i, 1 <= i <= 31 -> In (tblF i) TBLSF.
Proof.
intros i Hi. rewrite TBLSF_eq. img_apply in_map_iff. exists (Z.to_nat i). rewrite Z2Nat.id by img_lia. split; [img_refl|]. img_apply in_seq. img_lia.
Qed.
Lemma TBLS0_Forall : forall (P : YQ0b.region -> Prop), (forall i, 1 <= i <= 31 -> P (tblr i [])) -> Forall P TBLS0.
Proof. intros P HP. img_apply Forall_forall. intros r Hr. destruct (In_TBLS0 r Hr) as (i & Hi & ->). img_exact (HP i Hi). Qed.
Definition headc0 : YQ0b.region := YQ0b.mkRegion (Some rP) 0 16 0 0 [YQ0b.mkChunk 0 (CVal 4 (SLit 0)); YQ0b.mkChunk 4 (CVal 4 (SLit 0)); YQ0b.mkChunk 8 (CVal 8 (SLit 0))].
Definition headcnt : YQ0b.region := YQ0b.mkRegion (Some rP) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SLit 0))].
Definition headcJ : YQ0b.region := YQ0b.mkRegion (Some rP) 0 16 0 16 [YQ0b.mkChunk 0 (CVal 4 (SLit 0)); YQ0b.mkChunk 4 (CVal 4 (SOff rMAX 0)); YQ0b.mkChunk 8 (CVal 8 (SOff rCSZ 0))].
Definition dropAt {A} (i : nat) (m : list A) : list A := firstn i m ++ skipn (S i) m.
Definition insAt {A} (i : nat) (r : A) (m : list A) : list A := firstn i m ++ r :: skipn i m.
Definition replAt {A} (i : nat) (r : A) (m : list A) : list A := firstn i m ++ r :: skipn (S i) m.
Definition TABW (T a : Z) : Prop := exists i, 1 <= i <= 31 /\ T + 212 + 80 * i <= a < T + 224 + 80 * i.
Definition tabwb (T a : Z) : bool := existsb (fun k => (T + 212 + 80 * Z.of_nat k <=? a) && (a <? T + 224 + 80 * Z.of_nat k)) (seq 1 31).
Lemma tabwb_spec : forall T a, tabwb T a = true <-> TABW T a.
Proof.
intros T a. unfold tabwb, TABW. rewrite existsb_exists. split.
- intros (k & Hk & Hb). apply in_seq in Hk. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
exists (Z.of_nat k). img_lia.
- intros (i & Hi & Hr). exists (Z.to_nat i). split; [img_try (img_apply in_seq; img_lia)|]. rewrite Z2Nat.id by img_lia.
img_apply andb_true_intro. split; [img_try (img_apply Z.leb_le) | img_try (img_apply Z.ltb_lt)]; img_lia.
Qed.
Lemma tabwb_false : forall T a, tabwb T a = false <-> ~ TABW T a.
Proof.
intros T a. split.
- intros Hf Hw. apply tabwb_spec in Hw. rewrite Hw in Hf. discriminate.
- intros Hn. destruct (tabwb T a) eqn:Eb; [|img_refl]. exfalso. img_apply Hn. img_apply tabwb_spec. img_exact Eb.
Qed.
Lemma TABW_dec : forall T a, {TABW T a} + {~ TABW T a}.
Proof. intros T a. destruct (tabwb T a) eqn:Eb; [img_try (left; img_apply tabwb_spec; img_exact Eb) | img_try (right; img_apply tabwb_false; img_exact Eb)]. Qed.
Lemma TABW_range : forall T a, TABW T a -> T + 292 <= a < T + 2704.
Proof. intros T a (i & Hi & Hr). img_lia. Qed.
Lemma TABW_not_count : forall T a i, 1 <= i <= 31 -> T + 208 + 80 * i <= a < T + 212 + 80 * i -> ~ TABW T a.
Proof. intros T a i Hi Ha (j & Hj & Hr). assert (i = j \/ i < j \/ j < i) by img_lia. img_lia. Qed.


Lemma in_wrange_app : forall E l1 l2 a, in_wrange E (l1 ++ l2) a -> in_wrange E l1 a \/ in_wrange E l2 a.
Proof.
intros E l1 l2 a (r & Hin & Hr). apply in_app_iff in Hin as [Hin|Hin]; [img_try (left)|img_try (right)]; exists r; split; assumption.
Qed.
Lemma in_wrange_TBLS0 : forall E a, in_wrange E TBLS0 a -> TABW (base_val E (Some rT)) a.
Proof.
intros E a (r & Hin & Hr). destruct (In_TBLS0 r Hin) as (i & Hi & ->). cbn [tblr YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi] in Hr.
exists i. img_lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ext3 (r : YQ0b.region) : option nat * Z * Z := (YQ0b.r_base r, YQ0b.r_lo r, YQ0b.r_hi r).
Lemma extent_disjoint_sym : forall E r r', extent_disjoint E r r' -> extent_disjoint E r' r.
Proof. intros E r r' H. unfold extent_disjoint in *. img_lia. Qed.
Lemma extent_disjoint_ext3 : forall E r r1 r2, ext3 r1 = ext3 r2 -> extent_disjoint E r r1 -> extent_disjoint E r r2.
Proof.
intros E r r1 r2 He H. unfold ext3 in He. injection He as Hb Hl Hh. unfold extent_disjoint in *. rewrite <- Hb, <- Hl, <- Hh. img_exact H.
Qed.
Lemma all_disjoint_ext3 : forall E r l l', map ext3 l = map ext3 l' -> all_disjoint E r l -> all_disjoint E r l'.
Proof.
intros E r l. induction l as [|x l IH]; intros l' Hm H; destruct l' as [|y l']; cbn in Hm; try discriminate; [img_try (img_exact I)|].
cbn in H |- *. destruct H as [D1 D2].
assert (Hxy : ext3 x = ext3 y) by (img_try (injection Hm; intros; unfold ext3; congruence)).
assert (Hll : map ext3 l = map ext3 l') by (img_try (injection Hm; intros; assumption)).
split; [img_try (img_exact (extent_disjoint_ext3 E r x y Hxy D1)) | img_try (img_exact (IH l' Hll D2))].
Qed.
Lemma all_disjoint_head_ext3 : forall E r r' l, ext3 r = ext3 r' -> all_disjoint E r l -> all_disjoint E r' l.
Proof.
intros E r r' l He. unfold ext3 in He. injection He as Hb Hl Hh. induction l as [|x l IH]; cbn; intros H; [img_try (img_exact I)|].
destruct H as [H1 H2]. split; [|img_try (img_exact (IH H2))]. unfold extent_disjoint in *. rewrite <- Hb, <- Hl, <- Hh. img_exact H1.
Qed.
Lemma all_disjoint_shrink : forall E r r' l, YQ0b.r_base r' = YQ0b.r_base r -> YQ0b.r_lo r <= YQ0b.r_lo r' -> YQ0b.r_hi r' <= YQ0b.r_hi r ->
YQ0b.r_lo r' <= YQ0b.r_hi r' -> all_disjoint E r l -> all_disjoint E r' l.
Proof.
intros E r r' l Hb Hlo Hhi Hwf. induction l as [|x l IH]; cbn; intros H; [img_try (img_exact I)|].
destruct H as [H1 H2]. split; [|img_try (img_exact (IH H2))]. unfold extent_disjoint in *. rewrite Hb. img_lia.
Qed.
Lemma all_disjoint_app : forall E r l1 l2, all_disjoint E r (l1 ++ l2) <-> all_disjoint E r l1 /\ all_disjoint E r l2.
Proof.
intros E r l1 l2. induction l1 as [|x l1 IH]; cbn; [img_try (tauto)|]. rewrite IH. tauto.
Qed.
Lemma all_disjoint_In : forall E r l x, all_disjoint E r l -> In x l -> extent_disjoint E r x.
Proof.
intros E r l x. induction l as [|y l IH]; cbn; intros H Hin; [img_try (destruct Hin)|].
destruct H as [H1 H2]. destruct Hin as [<-|Hin]; [img_try (img_exact H1) | img_try (img_exact (IH H2 Hin))].
Qed.
Lemma all_disjoint_of_In : forall E r l, (forall x, In x l -> extent_disjoint E r x) -> all_disjoint E r l.
Proof.
intros E r l. induction l as [|y l IH]; cbn; intros H; [img_try (img_exact I)|]. split; [img_try (img_apply H; left; img_refl) | img_try (img_apply IH; intros x Hx; img_apply H; right; img_exact Hx)].
Qed.
Lemma pairwise_disjoint_app : forall E l1 l2,
pairwise_disjoint E (l1 ++ l2) <-> pairwise_disjoint E l1 /\ pairwise_disjoint E l2 /\ (forall r, In r l2 -> all_disjoint E r l1).
Proof.
intros E l1 l2. induction l1 as [|x l1 IH]; cbn.
- split; [img_try (intros H; split; [img_exact I|]; split; [img_exact H|]; intros r0 Hr0; img_exact I) | img_try (intros (_ & H & _); img_exact H)].
- rewrite all_disjoint_app, IH. split.
+ intros ([A1 A2] & P1 & P2 & P3). split; [img_try (split; assumption)|]. split; [img_try (assumption)|]. intros r Hr. split; [|img_try (img_exact (P3 r Hr))].
img_apply extent_disjoint_sym. img_exact (all_disjoint_In E x l2 r A2 Hr).
+ intros ([A1 P1] & P2 & P3). split; [img_try (split; [img_exact A1|])|].
* img_apply all_disjoint_of_In. intros r Hr. img_apply extent_disjoint_sym. img_exact (proj1 (P3 r Hr)).
* split; [img_try (img_exact P1)|]. split; [img_try (img_exact P2)|]. intros r Hr. img_exact (proj2 (P3 r Hr)).
Qed.
Lemma pairwise_disjoint_ext3 : forall E l l', map ext3 l = map ext3 l' -> pairwise_disjoint E l -> pairwise_disjoint E l'.
Proof.
intros E l. induction l as [|x l IH]; intros l' Hm H; destruct l' as [|y l']; cbn in Hm; try discriminate; [img_try (img_exact I)|].
cbn in H |- *. destruct H as [A P].
assert (Hxy : ext3 x = ext3 y) by (img_try (injection Hm; intros; unfold ext3; congruence)).
assert (Hll : map ext3 l = map ext3 l') by (img_try (injection Hm; intros; assumption)).
split; [| img_try (img_exact (IH l' Hll P))]. img_apply (all_disjoint_head_ext3 E x y _ Hxy). img_exact (all_disjoint_ext3 E x l l' Hll A).
Qed.
Lemma pairwise_disjoint_pick : forall E l i r, pairwise_disjoint E l -> nth_error l i = Some r -> all_disjoint E r (dropAt i l).
Proof.
intros E l. induction l as [|x l IH]; intros i r HP Hn; [img_try (destruct i; discriminate)|].
destruct i as [|i]; cbn in Hn.
- injection Hn as ->. unfold dropAt. cbn. img_exact (proj1 HP).
- cbn in HP. destruct HP as [A P]. unfold dropAt. cbn [firstn skipn app]. split.
+ img_apply extent_disjoint_sym. img_exact (all_disjoint_In E x l r A (nth_error_In _ _ Hn)).
+ img_exact (IH i r P Hn).
Qed.
Lemma firstn_In {A} : forall n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros n l x H. rewrite <- (firstn_skipn n l). img_apply in_app_iff. left. img_exact H. Qed.
Lemma skipn_In {A} : forall n (l : list A) x, In x (skipn n l) -> In x l.
Proof. intros n l x H. rewrite <- (firstn_skipn n l). img_apply in_app_iff. right. img_exact H. Qed.
Lemma regions_wf_app : forall l1 l2, regions_wf (l1 ++ l2) = regions_wf l1 && regions_wf l2.
Proof. intros l1 l2. induction l1 as [|x l1 IH]; cbn; [img_refl|]. rewrite IH, andb_assoc. img_refl. Qed.
Lemma regions_wf_forallb : forall l, regions_wf l = forallb YQ0b.region_wf l.
Proof. induction l as [|x l IH]; cbn; [img_refl|]. rewrite IH. img_refl. Qed.
Lemma regions_wf_incl : forall l l', incl l' l -> regions_wf l = true -> regions_wf l' = true.
Proof.
intros l l' Hi Hw. rewrite regions_wf_forallb in *. img_apply forallb_forall. intros x Hx. img_exact (proj1 (forallb_forall _ _) Hw x (Hi x Hx)).
Qed.
Lemma incl_dropAt {A} : forall i (l : list A), incl (dropAt i l) l.
Proof.
intros i l x Hx. unfold dropAt in Hx. apply in_app_iff in Hx as [Hx|Hx].
- img_exact (firstn_In _ _ _ Hx).
- img_exact (skipn_In _ _ _ Hx).
Unshelve. all: try img_exact 0%nat.
Qed.
Lemma submem_refl : forall l, submem l l.
Proof.
induction l as [|x l IH]; [img_try (constructor)|]. img_apply submem_keep; [|img_try (img_exact IH)].
unfold subregion. split; [img_refl|]. split; [img_lia|]. split; [img_lia|]. split; [img_try (right; img_lia)|]. intros c Hc; img_exact Hc.
Qed.
Lemma submem_dropAt : forall i l, submem (dropAt i l) l.
Proof.
intros i l. revert i. induction l as [|x l IH]; intros i.
- unfold dropAt. rewrite firstn_nil, skipn_nil. constructor.
- destruct i as [|i]; unfold dropAt; cbn [firstn skipn app].
+ img_apply submem_drop. img_apply submem_refl.
+ img_apply submem_keep; [|img_try (img_exact (IH i))]. unfold subregion. split; [img_refl|]. split; [img_lia|]. split; [img_lia|]. split; [img_try (right; img_lia)|]. intros c Hc; img_exact Hc.
Qed.
Lemma submem_replAt : forall i l r r', nth_error l i = Some r -> subregion r' r -> submem (replAt i r' l) l.
Proof.
intros i l. revert i. induction l as [|x l IH]; intros i r r' Hn Hs; [img_try (destruct i; discriminate)|].
destruct i as [|i]; cbn in Hn; unfold replAt; cbn [firstn skipn app].
- injection Hn as ->. img_apply submem_keep; [img_try (img_exact Hs) | img_try (img_apply submem_refl)].
- img_apply submem_keep; [|img_try (img_exact (IH i r r' Hn Hs))]. unfold subregion. split; [img_refl|]. split; [img_lia|]. split; [img_lia|]. split; [img_try (right; img_lia)|]. intros c Hc; img_exact Hc.
Qed.
Lemma mem_ok_dropAt {imgk : img} : forall E m rs i, mem_ok tfxsegs E m rs -> mem_ok tfxsegs E m (dropAt i rs).
Proof.
intros E m rs i HM. eapply mem_ok_sub; [img_try (img_apply submem_dropAt) | | img_try (img_exact HM)].
img_apply (regions_wf_incl rs); [img_try (img_apply incl_dropAt) | img_try (img_exact (proj1 HM))].
Qed.
Lemma mem_ok_replAt {imgk : img} : forall E m rs i r r', mem_ok tfxsegs E m rs -> nth_error rs i = Some r -> subregion r' r -> YQ0b.region_wf r' = true ->
mem_ok tfxsegs E m (replAt i r' rs).
Proof.
intros E m rs i r r' HM Hn Hs Hwf. eapply mem_ok_sub; [img_try (img_exact (submem_replAt i rs r r' Hn Hs)) | | img_try (img_exact HM)].
unfold replAt. rewrite regions_wf_app. cbn [regions_wf]. rewrite Hwf. cbn [andb].
rewrite (regions_wf_incl rs (firstn i rs)); [| img_try (intros x Hx; img_exact (firstn_In _ _ _ Hx)) | img_try (img_exact (proj1 HM))].
rewrite (regions_wf_incl rs (skipn (S i) rs)); [img_refl | img_try (intros x Hx; img_exact (skipn_In _ _ _ Hx)) | img_try (img_exact (proj1 HM))].
Qed.
Lemma mem_ok_app_l {imgk : img} : forall E m l1 l2, mem_ok tfxsegs E m (l1 ++ l2) -> mem_ok tfxsegs E m l1.
Proof.
intros E m l1 l2 (W & F & P). rewrite regions_wf_app in W. apply andb_prop in W as [W1 W2]. apply Forall_app in F as [F1 F2].
apply pairwise_disjoint_app in P as (P1 & _). split; [img_try (img_exact W1) | img_try (split; [img_exact F1 | img_exact P1])].
Qed.
Lemma mem_ok_app_r {imgk : img} : forall E m l1 l2, mem_ok tfxsegs E m (l1 ++ l2) -> mem_ok tfxsegs E m l2.
Proof.
intros E m l1 l2 (W & F & P). rewrite regions_wf_app in W. apply andb_prop in W as [W1 W2]. apply Forall_app in F as [F1 F2].
apply pairwise_disjoint_app in P as (_ & P2 & _). split; [img_try (img_exact W2) | img_try (split; [img_exact F2 | img_exact P2])].
Qed.
Lemma mem_ok_app {imgk : img} : forall E m l1 l2, mem_ok tfxsegs E m l1 -> regions_wf l2 = true -> Forall (region_ok tfxsegs E m) l2 -> pairwise_disjoint E l2 ->
(forall r, In r l2 -> all_disjoint E r l1) -> mem_ok tfxsegs E m (l1 ++ l2).
Proof.
intros E m l1 l2 (W & F & P) W2 F2 P2 D. split; [img_try (rewrite regions_wf_app, W, W2; img_refl)|].
split; [img_try (img_apply Forall_app; split; assumption)|]. img_apply pairwise_disjoint_app. repeat split; assumption.
Qed.
Lemma pairwise_disjoint_insAt : forall E i r l, pairwise_disjoint E l -> all_disjoint E r l -> pairwise_disjoint E (insAt i r l).
Proof.
intros E i r l. revert i. induction l as [|x l IH]; intros i HP HA.
- unfold insAt. rewrite firstn_nil, skipn_nil. cbn. split; img_exact I.
- destruct i as [|i]; unfold insAt; cbn [firstn skipn app].
+ cbn. split; [img_try (img_exact HA) | img_try (img_exact HP)].
+ cbn in HP, HA |- *. destruct HP as [A P]. destruct HA as [D A']. split; [|img_try (img_exact (IH i P A'))].
change (all_disjoint E x (insAt i r l)). unfold insAt. img_apply all_disjoint_app. split.
* img_apply all_disjoint_of_In. intros y Hy. img_exact (all_disjoint_In E x l y A (firstn_In _ _ _ Hy)).
* cbn. split; [img_try (img_apply extent_disjoint_sym; img_exact D)|]. img_apply all_disjoint_of_In. intros y Hy. img_exact (all_disjoint_In E x l y A (skipn_In _ _ _ Hy)).
Qed.
Lemma mem_ok_insAt {imgk : img} : forall E m rs i r, mem_ok tfxsegs E m rs -> YQ0b.region_wf r = true -> region_ok tfxsegs E m r -> all_disjoint E r rs ->
mem_ok tfxsegs E m (insAt i r rs).
Proof.
intros E m rs i r (W & F & P) Hwf Hr HA. split; [|img_try (split)].
- unfold insAt. rewrite regions_wf_app. cbn [regions_wf]. rewrite Hwf. cbn [andb].
rewrite (regions_wf_incl rs (firstn i rs)); [| img_try (intros x Hx; img_exact (firstn_In _ _ _ Hx)) | img_try (img_exact W)].
rewrite (regions_wf_incl rs (skipn i rs)); [img_refl | img_try (intros x Hx; img_exact (skipn_In _ _ _ Hx)) | img_try (img_exact W)].
- unfold insAt. img_apply Forall_app. split; [|img_try (img_apply Forall_cons; [img_exact Hr|])]; img_apply Forall_forall; intros x Hx; img_apply (proj1 (Forall_forall _ _) F);
[img_try (img_exact (firstn_In _ _ _ Hx)) | img_try (img_exact (skipn_In _ _ _ Hx))].
- img_exact (pairwise_disjoint_insAt E i r rs P HA).
Qed.
Lemma all_disjoint_insAt : forall E r i x l, extent_disjoint E r x -> all_disjoint E r l -> all_disjoint E r (insAt i x l).
Proof.
intros E r i x l Hx Hl. unfold insAt. img_apply all_disjoint_app. split.
- img_apply all_disjoint_of_In. intros y Hy. img_exact (all_disjoint_In E r l y Hl (firstn_In _ _ _ Hy)).
- cbn. split; [img_try (img_exact Hx)|]. img_apply all_disjoint_of_In. intros y Hy. img_exact (all_disjoint_In E r l y Hl (skipn_In _ _ _ Hy)).
Qed.
Lemma replAt_insAt {A} : forall i (x : A) l, (i < length l)%nat -> replAt i x l = insAt i x (dropAt i l).
Proof.
intros i x l Hi. unfold replAt, insAt, dropAt.
rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn, (Nat.min_l i (length l)) by img_lia. rewrite Nat.sub_diag, firstn_0, app_nil_r.
rewrite skipn_app, length_firstn, (Nat.min_l i (length l)) by img_lia. rewrite Nat.sub_diag, skipn_0.
rewrite (skipn_all2 (firstn i l)); [img_refl|]. rewrite length_firstn. img_lia.
Qed.
Lemma all_disjoint_replAt : forall E r i x l, (i < length l)%nat -> extent_disjoint E r x -> all_disjoint E r (dropAt i l) -> all_disjoint E r (replAt i x l).
Proof. intros E r i x l Hi Hx Hl. rewrite (replAt_insAt i x l Hi). img_exact (all_disjoint_insAt E r i x _ Hx Hl). Qed.
Lemma st_ok_mem_surgery {imgk : img} : forall E ss ms rs',
st_ok tfxsegs E ss ms -> (mem_ok tfxsegs E (ms_mem ms) (ss_mem ss) -> mem_ok tfxsegs E (ms_mem ms) rs') ->
st_ok tfxsegs E (mkSS (ss_pc ss) (ss_regs ss) rs' (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms rs' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HM.
unfold st_ok; cbn. repeat (split; [img_try (assumption)|]). split; [img_try (img_exact (HM H8)) | img_try (img_exact H9)].
Qed.
Definition tbl_facts {imgk : img} (m : word -> option byte) (T : Z) (i : Z) : Prop :=
val_mem tfxsegs m (T + 212 + 80 * i) 4 (max_cached i) /\ val_mem tfxsegs m (T + 216 + 80 * i) 8 (class_size i).
Lemma max_cached_range : forall i, 1 <= i <= 31 -> 0 <= max_cached i < 2 ^ 32.
Proof. intros i Hi. pose proof (class_ok i Hi) as (_ & _ & _ & K4 & _). img_lia. Qed.
Lemma region_ok_tblF {imgk : img} : forall E m i, 1 <= i <= 31 -> region_ok tfxsegs E m (tblF i) ->
tbl_facts m (bv_unsigned (ew E rT)) i /\ (forall o, 0 <= o < 12 -> writable_at tfxsegs m (bv_unsigned (ew E rT) + 212 + 80 * i + o)).
Proof.
intros E m i Hi (_ & _ & Hw & Hcs). cbn [tblF tblr YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val] in Hw, Hcs.
apply Forall_cons_iff in Hcs as [C8 Hcs]. apply Forall_cons_iff in Hcs as [C4 _].
pose proof (class_ok i Hi) as (K1 & K2 & K3 & K4 & K5). pose proof (max_cached_range i Hi) as MR.
split; [img_try (split)|].
- replace (bv_unsigned (ew E rT) + 212 + 80 * i) with (bv_unsigned (ew E rT) + (212 + 80 * i)) by img_lia.
img_apply (val_of_chunk_ok tfxsegs E m _ _ 4 (SLit (max_cached i)) (max_cached i) C4); [| img_try (cbn; img_lia) | img_try (cbn; img_lia)].
cbn. img_apply bv_eq. rewrite !Z_to_bv_unsigned. img_refl.
- replace (bv_unsigned (ew E rT) + 216 + 80 * i) with (bv_unsigned (ew E rT) + (216 + 80 * i)) by img_lia.
img_apply (val_of_chunk_ok tfxsegs E m _ _ 8 (SLit (class_size i)) (class_size i) C8); [| img_try (cbn; unfold kMaxSize in *; img_lia) | img_try (cbn; img_lia)].
cbn. img_apply bv_eq. rewrite !Z_to_bv_unsigned. img_refl.
- intros o Ho. replace (bv_unsigned (ew E rT) + 212 + 80 * i + o) with (bv_unsigned (ew E rT) + (212 + 80 * i + o)) by img_lia. img_apply Hw. img_lia.
Qed.
Lemma mem_ok_TBLSF {imgk : img} : forall E m l, mem_ok tfxsegs E m (l ++ TBLSF) ->
forall i, 1 <= i <= 31 -> tbl_facts m (bv_unsigned (ew E rT)) i /\ (forall o, 0 <= o < 12 -> writable_at tfxsegs m (bv_unsigned (ew E rT) + 212 + 80 * i + o)).
Proof.
intros E m l HM i Hi. pose proof (mem_ok_app_r E m l TBLSF HM) as (_ & F & _).
img_apply (region_ok_tblF E m i Hi). img_exact (proj1 (Forall_forall _ _) F _ (TBLSF_In i Hi)).
Qed.
Lemma TBLS0_ok {imgk : img} : forall E m, 0 <= bv_unsigned (ew E rT) -> bv_unsigned (ew E rT) + 4096 <= 2 ^ 64 ->
(forall a, bv_unsigned (ew E rT) + 292 <= a < bv_unsigned (ew E rT) + 2704 -> writable_at tfxsegs m a) ->
Forall (region_ok tfxsegs E m) TBLS0.
Proof.
intros E m T0 T1 Hw. img_apply TBLS0_Forall. intros i Hi. unfold region_ok. cbn [tblr YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [|img_try (img_apply Forall_nil)]. intros o Ho. img_apply Hw. img_lia.
Qed.
Lemma TBLS0_wf : regions_wf TBLS0 = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma TBLS0_pairwise : forall E, pairwise_disjoint E TBLS0.
Proof.
intros E. img_apply pairwise_disjoint_of_extents. unfold TBLS0. unfold extent_of_region. cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi].
set (b := base_val E (Some 32%nat)). clearbody b. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
Qed.
Lemma TBLS0_disjoint : forall E r l, In r TBLS0 ->
all_disjoint E (YQ0b.mkRegion (Some rT) 292 2704 0 0 []) l -> all_disjoint E r l.
Proof.
intros E r l Hr HA. destruct (In_TBLS0 r Hr) as (i & Hi & ->).
eapply all_disjoint_shrink; [| | | | img_try (img_exact HA)]; cbn [tblr YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]; [img_refl | img_lia | img_lia | img_lia].
Qed.
End d.
