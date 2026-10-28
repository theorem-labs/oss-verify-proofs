(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG0f YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhy AFkp.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tblr (i : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some rT) (212 + 80 * i) (224 + 80 * i) (212 + 80 * i) (224 + 80 * i) cs.
Definition tblF (i : Z) : YP09.region :=
tblr i [YP09.mkChunk (216 + 80 * i) (CVal 8 (SLit (class_size i))); YP09.mkChunk (212 + 80 * i) (CVal 4 (SLit (max_cached i)))].
Definition TBLS0 : smem := Eval vm_compute in map (fun k => tblr (Z.of_nat k) []) (seq 1 31).
Definition TBLSF : smem := Eval vm_compute in map (fun k => tblF (Z.of_nat k)) (seq 1 31).
Lemma TBLS0_eq : TBLS0 = map (fun k => tblr (Z.of_nat k) []) (seq 1 31). Proof. reflexivity. Qed.
Lemma TBLSF_eq : TBLSF = map (fun k => tblF (Z.of_nat k)) (seq 1 31). Proof. vm_compute. reflexivity. Qed.
Lemma TBLS0_length : length TBLS0 = 31%nat. Proof. reflexivity. Qed.
Lemma TBLSF_length : length TBLSF = 31%nat. Proof. reflexivity. Qed.
Lemma In_TBLS0 : forall r, In r TBLS0 -> exists i, 1 <= i <= 31 /\ r = tblr i [].
Proof.
intros r Hr. rewrite TBLS0_eq in Hr. apply in_map_iff in Hr as (k & <- & Hk). apply in_seq in Hk.
exists (Z.of_nat k). split; [lia | reflexivity].
Qed.
Lemma In_TBLSF : forall r, In r TBLSF -> exists i, 1 <= i <= 31 /\ r = tblF i.
Proof.
intros r Hr. rewrite TBLSF_eq in Hr. apply in_map_iff in Hr as (k & <- & Hk). apply in_seq in Hk.
exists (Z.of_nat k). split; [lia | reflexivity].
Qed.
Lemma TBLS0_In : forall i, 1 <= i <= 31 -> In (tblr i []) TBLS0.
Proof.
intros i Hi. rewrite TBLS0_eq. apply in_map_iff. exists (Z.to_nat i). rewrite Z2Nat.id by lia. split; [reflexivity|]. apply in_seq. lia.
Qed.
Lemma TBLSF_In : forall i, 1 <= i <= 31 -> In (tblF i) TBLSF.
Proof.
intros i Hi. rewrite TBLSF_eq. apply in_map_iff. exists (Z.to_nat i). rewrite Z2Nat.id by lia. split; [reflexivity|]. apply in_seq. lia.
Qed.
Lemma TBLS0_Forall : forall (P : YP09.region -> Prop), (forall i, 1 <= i <= 31 -> P (tblr i [])) -> Forall P TBLS0.
Proof. intros P HP. apply Forall_forall. intros r Hr. destruct (In_TBLS0 r Hr) as (i & Hi & ->). exact (HP i Hi). Qed.
Definition headc0 : YP09.region := YP09.mkRegion (Some rP) 0 16 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))].
Definition headcnt : YP09.region := YP09.mkRegion (Some rP) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 0))].
Definition headcJ : YP09.region := YP09.mkRegion (Some rP) 0 16 0 16 [YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SOff rMAX 0)); YP09.mkChunk 8 (CVal 8 (SOff rCSZ 0))].
Definition dropAt {A} (i : nat) (m : list A) : list A := firstn i m ++ skipn (S i) m.
Definition insAt {A} (i : nat) (r : A) (m : list A) : list A := firstn i m ++ r :: skipn i m.
Definition replAt {A} (i : nat) (r : A) (m : list A) : list A := firstn i m ++ r :: skipn (S i) m.
Definition TABW (T a : Z) : Prop := exists i, 1 <= i <= 31 /\ T + 212 + 80 * i <= a < T + 224 + 80 * i.
Definition tabwb (T a : Z) : bool := existsb (fun k => (T + 212 + 80 * Z.of_nat k <=? a) && (a <? T + 224 + 80 * Z.of_nat k)) (seq 1 31).
Lemma tabwb_spec : forall T a, tabwb T a = true <-> TABW T a.
Proof.
intros T a. unfold tabwb, TABW. rewrite existsb_exists. split.
- intros (k & Hk & Hb). apply in_seq in Hk. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
exists (Z.of_nat k). lia.
- intros (i & Hi & Hr). exists (Z.to_nat i). split; [apply in_seq; lia|]. rewrite Z2Nat.id by lia.
apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma tabwb_false : forall T a, tabwb T a = false <-> ~ TABW T a.
Proof.
intros T a. split.
- intros Hf Hw. apply tabwb_spec in Hw. rewrite Hw in Hf. discriminate.
- intros Hn. destruct (tabwb T a) eqn:Eb; [|reflexivity]. exfalso. apply Hn. apply tabwb_spec. exact Eb.
Qed.
Lemma TABW_dec : forall T a, {TABW T a} + {~ TABW T a}.
Proof. intros T a. destruct (tabwb T a) eqn:Eb; [left; apply tabwb_spec; exact Eb | right; apply tabwb_false; exact Eb]. Qed.
Lemma TABW_range : forall T a, TABW T a -> T + 292 <= a < T + 2704.
Proof. intros T a (i & Hi & Hr). lia. Qed.
Lemma TABW_not_count : forall T a i, 1 <= i <= 31 -> T + 208 + 80 * i <= a < T + 212 + 80 * i -> ~ TABW T a.
Proof. intros T a i Hi Ha (j & Hj & Hr). assert (i = j \/ i < j \/ j < i) by lia. lia. Qed.
Lemma TABW_not_slots : forall T a i, 0 <= i <= 31 -> T + 224 + 80 * i <= a < T + 288 + 80 * i -> ~ TABW T a.
Proof. intros T a i Hi Ha (j & Hj & Hr). assert (i = j \/ i < j \/ j < i) by lia. lia. Qed.
Lemma TABW_other : forall T a c, 1 <= c <= 31 -> TABW T a -> ~ (T + 212 + 80 * c <= a < T + 224 + 80 * c) ->
~ (T + 208 + 80 * c <= a < T + 224 + 80 * c).
Proof. intros T a c Hc (j & Hj & Hr) Hn Hh. assert (c = j \/ c < j \/ j < c) by lia. lia. Qed.
Lemma in_wrange_app : forall E l1 l2 a, in_wrange E (l1 ++ l2) a -> in_wrange E l1 a \/ in_wrange E l2 a.
Proof.
intros E l1 l2 a (r & Hin & Hr). apply in_app_iff in Hin as [Hin|Hin]; [left|right]; exists r; split; assumption.
Qed.
Lemma in_wrange_TBLS0 : forall E a, in_wrange E TBLS0 a -> TABW (base_val E (Some rT)) a.
Proof.
intros E a (r & Hin & Hr). destruct (In_TBLS0 r Hin) as (i & Hi & ->). cbn [tblr YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
exists i. lia.
Qed.
Lemma in_wrange_TBLSF : forall E a, in_wrange E TBLSF a -> TABW (base_val E (Some rT)) a.
Proof.
intros E a (r & Hin & Hr). destruct (In_TBLSF r Hin) as (i & Hi & ->). cbn [tblF tblr YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
exists i. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ext3 (r : YP09.region) : option nat * Z * Z := (YP09.r_base r, YP09.r_lo r, YP09.r_hi r).
Lemma extent_disjoint_sym : forall E r r', extent_disjoint E r r' -> extent_disjoint E r' r.
Proof. intros E r r' H. unfold extent_disjoint in *. lia. Qed.
Lemma extent_disjoint_ext3 : forall E r r1 r2, ext3 r1 = ext3 r2 -> extent_disjoint E r r1 -> extent_disjoint E r r2.
Proof.
intros E r r1 r2 He H. unfold ext3 in He. injection He as Hb Hl Hh. unfold extent_disjoint in *. rewrite <- Hb, <- Hl, <- Hh. exact H.
Qed.
Lemma all_disjoint_ext3 : forall E r l l', map ext3 l = map ext3 l' -> all_disjoint E r l -> all_disjoint E r l'.
Proof.
intros E r l. induction l as [|x l IH]; intros l' Hm H; destruct l' as [|y l']; cbn in Hm; try discriminate; [exact I|].
cbn in H |- *. destruct H as [D1 D2].
assert (Hxy : ext3 x = ext3 y) by (injection Hm; intros; unfold ext3; congruence).
assert (Hll : map ext3 l = map ext3 l') by (injection Hm; intros; assumption).
split; [exact (extent_disjoint_ext3 E r x y Hxy D1) | exact (IH l' Hll D2)].
Qed.
Lemma all_disjoint_head_ext3 : forall E r r' l, ext3 r = ext3 r' -> all_disjoint E r l -> all_disjoint E r' l.
Proof.
intros E r r' l He. unfold ext3 in He. injection He as Hb Hl Hh. induction l as [|x l IH]; cbn; intros H; [exact I|].
destruct H as [H1 H2]. split; [|exact (IH H2)]. unfold extent_disjoint in *. rewrite <- Hb, <- Hl, <- Hh. exact H1.
Qed.
Lemma all_disjoint_shrink : forall E r r' l, YP09.r_base r' = YP09.r_base r -> YP09.r_lo r <= YP09.r_lo r' -> YP09.r_hi r' <= YP09.r_hi r ->
YP09.r_lo r' <= YP09.r_hi r' -> all_disjoint E r l -> all_disjoint E r' l.
Proof.
intros E r r' l Hb Hlo Hhi Hwf. induction l as [|x l IH]; cbn; intros H; [exact I|].
destruct H as [H1 H2]. split; [|exact (IH H2)]. unfold extent_disjoint in *. rewrite Hb. lia.
Qed.
Lemma all_disjoint_app : forall E r l1 l2, all_disjoint E r (l1 ++ l2) <-> all_disjoint E r l1 /\ all_disjoint E r l2.
Proof.
intros E r l1 l2. induction l1 as [|x l1 IH]; cbn; [tauto|]. rewrite IH. tauto.
Qed.
Lemma all_disjoint_In : forall E r l x, all_disjoint E r l -> In x l -> extent_disjoint E r x.
Proof.
intros E r l x. induction l as [|y l IH]; cbn; intros H Hin; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [<-|Hin]; [exact H1 | exact (IH H2 Hin)].
Qed.
Lemma all_disjoint_of_In : forall E r l, (forall x, In x l -> extent_disjoint E r x) -> all_disjoint E r l.
Proof.
intros E r l. induction l as [|y l IH]; cbn; intros H; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx].
Qed.
Lemma pairwise_disjoint_app : forall E l1 l2,
pairwise_disjoint E (l1 ++ l2) <-> pairwise_disjoint E l1 /\ pairwise_disjoint E l2 /\ (forall r, In r l2 -> all_disjoint E r l1).
Proof.
intros E l1 l2. induction l1 as [|x l1 IH]; cbn.
- split; [intros H; split; [exact I|]; split; [exact H|]; intros r0 Hr0; exact I | intros (_ & H & _); exact H].
- rewrite all_disjoint_app, IH. split.
+ intros ([A1 A2] & P1 & P2 & P3). split; [split; assumption|]. split; [assumption|]. intros r Hr. split; [|exact (P3 r Hr)].
apply extent_disjoint_sym. exact (all_disjoint_In E x l2 r A2 Hr).
+ intros ([A1 P1] & P2 & P3). split; [split; [exact A1|]|].
* apply all_disjoint_of_In. intros r Hr. apply extent_disjoint_sym. exact (proj1 (P3 r Hr)).
* split; [exact P1|]. split; [exact P2|]. intros r Hr. exact (proj2 (P3 r Hr)).
Qed.
Lemma pairwise_disjoint_ext3 : forall E l l', map ext3 l = map ext3 l' -> pairwise_disjoint E l -> pairwise_disjoint E l'.
Proof.
intros E l. induction l as [|x l IH]; intros l' Hm H; destruct l' as [|y l']; cbn in Hm; try discriminate; [exact I|].
cbn in H |- *. destruct H as [A P].
assert (Hxy : ext3 x = ext3 y) by (injection Hm; intros; unfold ext3; congruence).
assert (Hll : map ext3 l = map ext3 l') by (injection Hm; intros; assumption).
split; [| exact (IH l' Hll P)]. apply (all_disjoint_head_ext3 E x y _ Hxy). exact (all_disjoint_ext3 E x l l' Hll A).
Qed.
Lemma pairwise_disjoint_pick : forall E l i r, pairwise_disjoint E l -> nth_error l i = Some r -> all_disjoint E r (dropAt i l).
Proof.
intros E l. induction l as [|x l IH]; intros i r HP Hn; [destruct i; discriminate|].
destruct i as [|i]; cbn in Hn.
- injection Hn as ->. unfold dropAt. cbn. exact (proj1 HP).
- cbn in HP. destruct HP as [A P]. unfold dropAt. cbn [firstn skipn app]. split.
+ apply extent_disjoint_sym. exact (all_disjoint_In E x l r A (nth_error_In _ _ Hn)).
+ exact (IH i r P Hn).
Qed.
Lemma firstn_In {A} : forall n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros n l x H. rewrite <- (firstn_skipn n l). apply in_app_iff. left. exact H. Qed.
Lemma skipn_In {A} : forall n (l : list A) x, In x (skipn n l) -> In x l.
Proof. intros n l x H. rewrite <- (firstn_skipn n l). apply in_app_iff. right. exact H. Qed.
Lemma regions_wf_app : forall l1 l2, regions_wf (l1 ++ l2) = regions_wf l1 && regions_wf l2.
Proof. intros l1 l2. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.
Lemma regions_wf_forallb : forall l, regions_wf l = forallb YP09.region_wf l.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma regions_wf_incl : forall l l', incl l' l -> regions_wf l = true -> regions_wf l' = true.
Proof.
intros l l' Hi Hw. rewrite regions_wf_forallb in *. apply forallb_forall. intros x Hx. exact (proj1 (forallb_forall _ _) Hw x (Hi x Hx)).
Qed.
Lemma incl_dropAt {A} : forall i (l : list A), incl (dropAt i l) l.
Proof.
intros i l x Hx. unfold dropAt in Hx. apply in_app_iff in Hx as [Hx|Hx].
- exact (firstn_In _ _ _ Hx).
- exact (skipn_In _ _ _ Hx).
Unshelve. all: try exact 0%nat.
Qed.
Lemma submem_refl : forall l, submem l l.
Proof.
induction l as [|x l IH]; [constructor|]. apply submem_keep; [|exact IH].
unfold subregion. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia|]. intros c Hc; exact Hc.
Qed.
Lemma submem_dropAt : forall i l, submem (dropAt i l) l.
Proof.
intros i l. revert i. induction l as [|x l IH]; intros i.
- unfold dropAt. rewrite firstn_nil, skipn_nil. constructor.
- destruct i as [|i]; unfold dropAt; cbn [firstn skipn app].
+ apply submem_drop. apply submem_refl.
+ apply submem_keep; [|exact (IH i)]. unfold subregion. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia|]. intros c Hc; exact Hc.
Qed.
Lemma submem_replAt : forall i l r r', nth_error l i = Some r -> subregion r' r -> submem (replAt i r' l) l.
Proof.
intros i l. revert i. induction l as [|x l IH]; intros i r r' Hn Hs; [destruct i; discriminate|].
destruct i as [|i]; cbn in Hn; unfold replAt; cbn [firstn skipn app].
- injection Hn as ->. apply submem_keep; [exact Hs | apply submem_refl].
- apply submem_keep; [|exact (IH i r r' Hn Hs)]. unfold subregion. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia|]. intros c Hc; exact Hc.
Qed.
Lemma mem_ok_dropAt : forall E m rs i, mem_ok tfibsegs E m rs -> mem_ok tfibsegs E m (dropAt i rs).
Proof.
intros E m rs i HM. eapply mem_ok_sub; [apply submem_dropAt | | exact HM].
apply (regions_wf_incl rs); [apply incl_dropAt | exact (proj1 HM)].
Qed.
Lemma mem_ok_replAt : forall E m rs i r r', mem_ok tfibsegs E m rs -> nth_error rs i = Some r -> subregion r' r -> YP09.region_wf r' = true ->
mem_ok tfibsegs E m (replAt i r' rs).
Proof.
intros E m rs i r r' HM Hn Hs Hwf. eapply mem_ok_sub; [exact (submem_replAt i rs r r' Hn Hs) | | exact HM].
unfold replAt. rewrite regions_wf_app. cbn [regions_wf]. rewrite Hwf. cbn [andb].
rewrite (regions_wf_incl rs (firstn i rs)); [| intros x Hx; exact (firstn_In _ _ _ Hx) | exact (proj1 HM)].
rewrite (regions_wf_incl rs (skipn (S i) rs)); [reflexivity | intros x Hx; exact (skipn_In _ _ _ Hx) | exact (proj1 HM)].
Qed.
Lemma mem_ok_app_l : forall E m l1 l2, mem_ok tfibsegs E m (l1 ++ l2) -> mem_ok tfibsegs E m l1.
Proof.
intros E m l1 l2 (W & F & P). rewrite regions_wf_app in W. apply andb_prop in W as [W1 W2]. apply Forall_app in F as [F1 F2].
apply pairwise_disjoint_app in P as (P1 & _). split; [exact W1 | split; [exact F1 | exact P1]].
Qed.
Lemma mem_ok_app_r : forall E m l1 l2, mem_ok tfibsegs E m (l1 ++ l2) -> mem_ok tfibsegs E m l2.
Proof.
intros E m l1 l2 (W & F & P). rewrite regions_wf_app in W. apply andb_prop in W as [W1 W2]. apply Forall_app in F as [F1 F2].
apply pairwise_disjoint_app in P as (_ & P2 & _). split; [exact W2 | split; [exact F2 | exact P2]].
Qed.
Lemma mem_ok_app : forall E m l1 l2, mem_ok tfibsegs E m l1 -> regions_wf l2 = true -> Forall (region_ok tfibsegs E m) l2 -> pairwise_disjoint E l2 ->
(forall r, In r l2 -> all_disjoint E r l1) -> mem_ok tfibsegs E m (l1 ++ l2).
Proof.
intros E m l1 l2 (W & F & P) W2 F2 P2 D. split; [rewrite regions_wf_app, W, W2; reflexivity|].
split; [apply Forall_app; split; assumption|]. apply pairwise_disjoint_app. repeat split; assumption.
Qed.
Lemma pairwise_disjoint_insAt : forall E i r l, pairwise_disjoint E l -> all_disjoint E r l -> pairwise_disjoint E (insAt i r l).
Proof.
intros E i r l. revert i. induction l as [|x l IH]; intros i HP HA.
- unfold insAt. rewrite firstn_nil, skipn_nil. cbn. split; exact I.
- destruct i as [|i]; unfold insAt; cbn [firstn skipn app].
+ cbn. split; [exact HA | exact HP].
+ cbn in HP, HA |- *. destruct HP as [A P]. destruct HA as [D A']. split; [|exact (IH i P A')].
change (all_disjoint E x (insAt i r l)). unfold insAt. apply all_disjoint_app. split.
* apply all_disjoint_of_In. intros y Hy. exact (all_disjoint_In E x l y A (firstn_In _ _ _ Hy)).
* cbn. split; [apply extent_disjoint_sym; exact D|]. apply all_disjoint_of_In. intros y Hy. exact (all_disjoint_In E x l y A (skipn_In _ _ _ Hy)).
Qed.
Lemma mem_ok_insAt : forall E m rs i r, mem_ok tfibsegs E m rs -> YP09.region_wf r = true -> region_ok tfibsegs E m r -> all_disjoint E r rs ->
mem_ok tfibsegs E m (insAt i r rs).
Proof.
intros E m rs i r (W & F & P) Hwf Hr HA. split; [|split].
- unfold insAt. rewrite regions_wf_app. cbn [regions_wf]. rewrite Hwf. cbn [andb].
rewrite (regions_wf_incl rs (firstn i rs)); [| intros x Hx; exact (firstn_In _ _ _ Hx) | exact W].
rewrite (regions_wf_incl rs (skipn i rs)); [reflexivity | intros x Hx; exact (skipn_In _ _ _ Hx) | exact W].
- unfold insAt. apply Forall_app. split; [|apply Forall_cons; [exact Hr|]]; apply Forall_forall; intros x Hx; apply (proj1 (Forall_forall _ _) F);
[exact (firstn_In _ _ _ Hx) | exact (skipn_In _ _ _ Hx)].
- exact (pairwise_disjoint_insAt E i r rs P HA).
Qed.
Lemma all_disjoint_insAt : forall E r i x l, extent_disjoint E r x -> all_disjoint E r l -> all_disjoint E r (insAt i x l).
Proof.
intros E r i x l Hx Hl. unfold insAt. apply all_disjoint_app. split.
- apply all_disjoint_of_In. intros y Hy. exact (all_disjoint_In E r l y Hl (firstn_In _ _ _ Hy)).
- cbn. split; [exact Hx|]. apply all_disjoint_of_In. intros y Hy. exact (all_disjoint_In E r l y Hl (skipn_In _ _ _ Hy)).
Qed.
Lemma replAt_insAt {A} : forall i (x : A) l, (i < length l)%nat -> replAt i x l = insAt i x (dropAt i l).
Proof.
intros i x l Hi. unfold replAt, insAt, dropAt.
rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn, (Nat.min_l i (length l)) by lia. rewrite Nat.sub_diag, firstn_0, app_nil_r.
rewrite skipn_app, length_firstn, (Nat.min_l i (length l)) by lia. rewrite Nat.sub_diag, skipn_0.
rewrite (skipn_all2 (firstn i l)); [reflexivity|]. rewrite length_firstn. lia.
Qed.
Lemma all_disjoint_replAt : forall E r i x l, (i < length l)%nat -> extent_disjoint E r x -> all_disjoint E r (dropAt i l) -> all_disjoint E r (replAt i x l).
Proof. intros E r i x l Hi Hx Hl. rewrite (replAt_insAt i x l Hi). exact (all_disjoint_insAt E r i x _ Hx Hl). Qed.
Lemma st_ok_mem_surgery : forall E ss ms rs',
st_ok tfibsegs E ss ms -> (mem_ok tfibsegs E (ms_mem ms) (ss_mem ss) -> mem_ok tfibsegs E (ms_mem ms) rs') ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) rs' (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms rs' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HM.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [exact (HM H8) | exact H9].
Qed.
Definition tbl_facts (m : word -> option byte) (T : Z) (i : Z) : Prop :=
val_mem tfibsegs m (T + 212 + 80 * i) 4 (max_cached i) /\ val_mem tfibsegs m (T + 216 + 80 * i) 8 (class_size i).
Lemma max_cached_range : forall i, 1 <= i <= 31 -> 0 <= max_cached i < 2 ^ 32.
Proof. intros i Hi. pose proof (class_ok i Hi) as (_ & _ & _ & K4 & _). lia. Qed.
Lemma region_ok_tblF : forall E m i, 1 <= i <= 31 -> region_ok tfibsegs E m (tblF i) ->
tbl_facts m (bv_unsigned (ew E rT)) i /\ (forall o, 0 <= o < 12 -> writable_at tfibsegs m (bv_unsigned (ew E rT) + 212 + 80 * i + o)).
Proof.
intros E m i Hi (_ & _ & Hw & Hcs). cbn [tblF tblr YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in Hw, Hcs.
apply Forall_cons_iff in Hcs as [C8 Hcs]. apply Forall_cons_iff in Hcs as [C4 _].
pose proof (class_ok i Hi) as (K1 & K2 & K3 & K4 & K5). pose proof (max_cached_range i Hi) as MR.
split; [split|].
- replace (bv_unsigned (ew E rT) + 212 + 80 * i) with (bv_unsigned (ew E rT) + (212 + 80 * i)) by lia.
apply (val_of_chunk_ok tfibsegs E m _ _ 4 (SLit (max_cached i)) (max_cached i) C4); [| cbn; lia | cbn; lia].
cbn. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
- replace (bv_unsigned (ew E rT) + 216 + 80 * i) with (bv_unsigned (ew E rT) + (216 + 80 * i)) by lia.
apply (val_of_chunk_ok tfibsegs E m _ _ 8 (SLit (class_size i)) (class_size i) C8); [| cbn; unfold kMaxSize in *; lia | cbn; lia].
cbn. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
- intros o Ho. replace (bv_unsigned (ew E rT) + 212 + 80 * i + o) with (bv_unsigned (ew E rT) + (212 + 80 * i + o)) by lia. apply Hw. lia.
Qed.
Lemma mem_ok_TBLSF : forall E m l, mem_ok tfibsegs E m (l ++ TBLSF) ->
forall i, 1 <= i <= 31 -> tbl_facts m (bv_unsigned (ew E rT)) i /\ (forall o, 0 <= o < 12 -> writable_at tfibsegs m (bv_unsigned (ew E rT) + 212 + 80 * i + o)).
Proof.
intros E m l HM i Hi. pose proof (mem_ok_app_r E m l TBLSF HM) as (_ & F & _).
apply (region_ok_tblF E m i Hi). exact (proj1 (Forall_forall _ _) F _ (TBLSF_In i Hi)).
Qed.
Lemma TBLS0_ok : forall E m, 0 <= bv_unsigned (ew E rT) -> bv_unsigned (ew E rT) + 4096 <= 2 ^ 64 ->
(forall a, bv_unsigned (ew E rT) + 292 <= a < bv_unsigned (ew E rT) + 2704 -> writable_at tfibsegs m a) ->
Forall (region_ok tfibsegs E m) TBLS0.
Proof.
intros E m T0 T1 Hw. apply TBLS0_Forall. intros i Hi. unfold region_ok. cbn [tblr YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hw. lia.
Qed.
Lemma TBLS0_wf : regions_wf TBLS0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma TBLS0_pairwise : forall E, pairwise_disjoint E TBLS0.
Proof.
intros E. apply pairwise_disjoint_of_extents. unfold TBLS0. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
set (b := base_val E (Some 32%nat)). clearbody b. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
Qed.
Lemma TBLS0_disjoint : forall E r l, In r TBLS0 ->
all_disjoint E (YP09.mkRegion (Some rT) 292 2704 0 0 []) l -> all_disjoint E r l.
Proof.
intros E r l Hr HA. destruct (In_TBLS0 r Hr) as (i & Hi & ->).
eapply all_disjoint_shrink; [| | | | exact HA]; cbn [tblr YP09.r_base YP09.r_lo YP09.r_hi]; [reflexivity | lia | lia | lia].
Qed.
End d.
