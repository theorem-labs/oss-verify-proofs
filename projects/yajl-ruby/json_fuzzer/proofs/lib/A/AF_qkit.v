(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Export AF_free_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Export AsanConsts AsanSizeClass AsanState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Notation bcnt b := (Z.of_nat (length (b_items b))).
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition bhd_or (l : list batch) (n : Z) : Z := match l with [] => n | b :: _ => b_addr b end.
End RC__1.
Notation bhd l := (bhd_or l 0).
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Fixpoint blast (l : list batch) : Z := match l with [] => 0 | [b] => b_addr b | _ :: rest => blast rest end.
End RC__2.
Notation blen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Fixpoint bcellsn (m : word -> option byte) (l : list batch) (n : Z) : Prop :=
  match l with
  | [] => True
  | b :: rest => rw_cells asegs m (b_addr b) [C8 (Z_to_bv 64 (bhd_or rest n)); C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (bcnt b))] /\ bcellsn m rest n
  end.
End RC__3.
Notation bcells m l := (bcellsn m l 0).
(* [comment removed for export] *)
Section RC__4.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition bitems (m : word -> option byte) (b : batch) : Prop :=
  exists junk, u64arr asegs m (b_addr b + 24) (map (fun z => Z_to_bv 64 z) (b_items b) ++ junk) /\ (length (b_items b) + length junk = 1021)%nat.
Fixpoint bitemsl (m : word -> option byte) (l : list batch) : Prop :=
  match l with [] => True | b :: rest => bitems m b /\ bitemsl m rest end.

(* [comment removed for export] *)
Definition bok (lo T : Z) (b : batch) : Prop :=
  0x10007fff8000 (* [comment removed for export] *) <= b_addr b /\ b_addr b + 8192 <= lo /\ (b_addr b + 8192 <= T \/ T + 4096 <= b_addr b)
  /\ 8192 <= b_size b /\ bcnt b <= 1021.
(* [comment removed for export] *)
Definition far (x y : Z) : Prop := x + 8192 <= y \/ y + 8192 <= x.
Fixpoint apl (xs : list Z) : Prop := match xs with [] => True | x :: r => Forall (far x) r /\ apl r end.
Definition bapart (l : list batch) : Prop := apl (map b_addr l).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qbytes_cons : forall b l, qbytes (b :: l) = b_size b + qbytes l. Proof. reflexivity. Qed.
Lemma qbytes_nil : qbytes [] = 0. Proof. reflexivity. Qed.
Lemma qbytes_app : forall l1 l2, qbytes (l1 ++ l2) = qbytes l1 + qbytes l2.
Proof. aceil. induction l1; intros; [reflexivity|]. cbn [app]. rewrite !qbytes_cons, IHl1. lia. Qed.
Lemma qbytes_lb : forall lo T l, Forall (bok lo T) l -> 8192 * blen l <= qbytes l.
Proof. aceil. induction l; intros H; [cbn; lia|]. inversion H; subst. unfold bok in *. specialize (IHl ltac:(assumption)). rewrite qbytes_cons. cbn [length]. lia. Qed.
Lemma qbytes_nonneg : forall lo T l, Forall (bok lo T) l -> 0 <= qbytes l.
Proof. aceil. intros lo T l H. pose proof (qbytes_lb lo T l H). lia. Qed.
Lemma blast_app1 : forall l b, blast (l ++ [b]) = b_addr b.
Proof. aceil. induction l as [|x l IH]; cbn; intros; [reflexivity|]. rewrite IH. destruct (l ++ [b]) eqn:E; [| reflexivity]. destruct l; discriminate. Qed.
Lemma blast_app : forall l1 l2, l2 <> [] -> blast (l1 ++ l2) = blast l2.
Proof. aceil.
  induction l1 as [|x l1 IH]; cbn; intros l2 H; [reflexivity|]. rewrite IH by exact H.
  destruct (l1 ++ l2) eqn:E; [| reflexivity]. apply app_eq_nil in E. tauto.
Qed.
Lemma blast_cons : forall b l, l <> [] -> blast (b :: l) = blast l.
Proof. aceil. intros b [|x l] H; [congruence| reflexivity]. Qed.
Lemma blast_in : forall l, l <> [] -> exists b, In b l /\ blast l = b_addr b.
Proof. aceil.
  induction l as [|b l IH]; intros NE; [congruence|]. destruct l as [|b2 l2]; [exists b; split; [left; reflexivity| reflexivity]|].
  destruct (IH ltac:(discriminate)) as (b' & Hin & E). exists b'. split; [right; exact Hin| exact E].
Qed.
Lemma bhd_or_app : forall l1 l2 n, l1 <> [] -> bhd_or (l1 ++ l2) n = bhd_or l1 n.
Proof. aceil. intros [|b l1] l2 n H; [congruence| reflexivity]. Qed.
Lemma bhd_or_indep : forall l n n', l <> [] -> bhd_or l n = bhd_or l n'.
Proof. aceil. intros [|b l] n n' H; [congruence| reflexivity]. Qed.

Lemma far_sym : forall x y, far x y -> far y x. Proof. unfold far; intros; lia. Qed.
Lemma apl_app : forall xs ys, apl (xs ++ ys) <-> apl xs /\ apl ys /\ forall x y, In x xs -> In y ys -> far x y.
Proof. aceil.
  induction xs as [|x xs IH]; cbn; intros ys.
  - intuition.
  - rewrite IH, Forall_app, !Forall_forall. split.
    + intros ([F1 F2] & A1 & A2 & CR). repeat split; auto. intros x0 y [<-|Hx] Hy; auto.
    + intros ((F1 & A1) & A2 & CR). repeat split; auto.
Qed.
Lemma apl_perm : forall xs ys, Permutation.Permutation xs ys -> apl xs -> apl ys.
Proof. aceil.
  intros xs ys HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn; intros A.
  - exact I.
  - destruct A as [F A]. split; [| apply IH; exact A]. apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) F).
    eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HP| exact Hz].
  - destruct A as (F1 & F2 & A). inversion F1; subst. repeat split; auto. constructor; [apply far_sym; assumption| assumption].
  - auto.
Qed.
Lemma apl_in_cases : forall xs x y, apl xs -> In x xs -> In y xs -> x = y \/ far x y.
Proof. aceil.
  induction xs as [|z xs IH]; cbn; intros x y A Hx Hy; [tauto|]. destruct A as [F A].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - left; reflexivity.
  - right. exact (proj1 (Forall_forall _ _) F y Hy).
  - right. apply far_sym. exact (proj1 (Forall_forall _ _) F x Hx).
  - exact (IH x y A Hx Hy).
Qed.
Lemma blast_cases : forall l, l = [] /\ blast l = 0 \/ exists b, In b l /\ blast l = b_addr b.
Proof. aceil. intros l. destruct l as [|b l'] eqn:E; [left; split; reflexivity| right; rewrite <- E; apply blast_in; rewrite E; discriminate]. Qed.
Lemma bapart_perm : forall l l', Permutation.Permutation (map b_addr l) (map b_addr l') -> bapart l -> bapart l'.
Proof. aceil. intros l l' HP H. unfold bapart in *. eapply apl_perm; eauto. Qed.
Lemma bapart_tl : forall b l, bapart (b :: l) -> bapart l.
Proof. aceil. intros b l [_ H]. exact H. Qed.
Lemma bapart_hd : forall b l b', bapart (b :: l) -> In b' l -> b_addr b + 8192 <= b_addr b' \/ b_addr b' + 8192 <= b_addr b.
Proof. aceil. intros b l b' [F _] Hin. apply (proj1 (Forall_forall _ _) F). apply in_map. exact Hin. Qed.
Lemma bapart_app : forall l1 l2, bapart (l1 ++ l2) <-> bapart l1 /\ bapart l2 /\ forall x y, In x l1 -> In y l2 -> far (b_addr x) (b_addr y).
Proof. aceil.
  intros l1 l2. unfold bapart. rewrite map_app, apl_app. split.
  - intros (A1 & A2 & CR). repeat split; auto. intros x y Hx Hy. apply CR; apply in_map; assumption.
  - intros (A1 & A2 & CR). repeat split; auto. intros x y Hx Hy. apply in_map_iff in Hx as (x0 & <- & Hx). apply in_map_iff in Hy as (y0 & <- & Hy). auto.
Qed.
Lemma bapart_app_inv : forall l1 l2, bapart (l1 ++ l2) -> bapart l2.
Proof. aceil. intros l1 l2 H. apply bapart_app in H. tauto. Qed.
Lemma bapart_app_l : forall l1 l2, bapart (l1 ++ l2) -> bapart l1.
Proof. aceil. intros l1 l2 H. apply bapart_app in H. tauto. Qed.
Lemma bapart_drop : forall l1 x l2, bapart (l1 ++ x :: l2) -> bapart (l1 ++ l2).
Proof. aceil.
  intros l1 x l2 H. apply bapart_app in H. destruct H as (A1 & [_ A2] & CR). apply bapart_app. repeat split; auto.
  intros a b Ha Hb. apply CR; [exact Ha| right; exact Hb].
Qed.
Lemma blast_cons_addr : forall x y l, b_addr x = b_addr y -> blast (x :: l) = blast (y :: l).
Proof. aceil. intros x y [|z l] E; cbn; [exact E| reflexivity]. Qed.
Lemma bapart_app_cross : forall l1 l2 b1 b2, bapart (l1 ++ l2) -> In b1 l1 -> In b2 l2 -> b_addr b1 + 8192 <= b_addr b2 \/ b_addr b2 + 8192 <= b_addr b1.
Proof. aceil. intros l1 l2 b1 b2 H H1 H2. apply bapart_app in H. destruct H as (_ & _ & CR). exact (CR b1 b2 H1 H2). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bcellsn_app : forall m l1 l2 n, bcellsn m (l1 ++ l2) n <-> bcellsn m l1 (bhd_or l2 n) /\ bcellsn m l2 n.
Proof. aceil.
  induction l1 as [|b l1 IH]; cbn; intros l2 n; [tauto|].
  rewrite IH. destruct l1; cbn; tauto.
Qed.
Lemma bcellsn_transport : forall W m m' l n,
  bcellsn m l n -> munch W m m' -> wmono asegs m m' -> Forall (fun b => disjoint_from W (b_addr b) 24) l -> bcellsn m' l n.
Proof. aceil.
  induction l as [|b l IH]; cbn; intros n QCx MU WM HF; [exact I|].
  inversion HF; subst. destruct QCx as [Hb Hl]. split; [| apply IH; assumption].
  eapply rw_cells_transport; [exact Hb| exact MU| exact WM| cbn; assumption].
Qed.
Lemma bcellsn_frame : forall m l nx a bs,
  bcellsn m l nx -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  Forall (fun b => b_addr b + 24 <= a \/ a + Z.of_nat (length bs) <= b_addr b) l ->
  bcellsn (write_to_mem m (wa a) bs) l nx.
Proof. aceil.
  induction l as [|b l IH]; cbn; intros nx a0 bs0 QCx Ha Hl HF; [exact I|].
  inversion HF; subst. destruct QCx as [Hb Hr]. split; [| apply IH; assumption].
  apply rw_cells_frame; [exact Hb| lia| lia| cbn [cells_size csize Nat.add]; lia].
Qed.
Lemma bitems_transport : forall W m m' b,
  bitems m b -> munch W m m' -> wmono asegs m m' -> disjoint_from W (b_addr b + 24) 8168 -> bitems m' b.
Proof. aceil.
  intros W m m' b (junk & ARR & LEN) MU WM DJ. exists junk. split; [| exact LEN].
  eapply u64arr_transport; [exact ARR| exact MU| exact WM|]. rewrite length_app, length_map.
  replace (8 * Z.of_nat (length (b_items b) + length junk)) with 8168 by lia. exact DJ.
Qed.
Lemma bitemsl_transport : forall W m m' l,
  bitemsl m l -> munch W m m' -> wmono asegs m m' -> Forall (fun b => disjoint_from W (b_addr b + 24) 8168) l -> bitemsl m' l.
Proof. aceil.
  induction l as [|b l IH]; cbn; intros BI MU WM HF; [exact I|]. inversion HF; subst. destruct BI as [X1 X2].
  split; [eapply bitems_transport; eassumption| apply IH; assumption].
Qed.
Lemma bitems_frame : forall m b a bs,
  bitems m b -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (b_addr b + 8192 <= a \/ a + Z.of_nat (length bs) <= b_addr b + 24) -> bitems (write_to_mem m (wa a) bs) b.
Proof. aceil.
  intros m b a bs (junk & ARR & LEN) Ha Hl DJ. exists junk. split; [| exact LEN].
  apply u64arr_frame; [exact ARR| lia| lia|]. rewrite length_app, length_map. lia.
Qed.
Lemma bitemsl_frame : forall m l a bs,
  bitemsl m l -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  Forall (fun b => b_addr b + 8192 <= a \/ a + Z.of_nat (length bs) <= b_addr b + 24) l -> bitemsl (write_to_mem m (wa a) bs) l.
Proof. aceil.
  intros m l; induction l as [|b l IH]; cbn; intros a0 bs0 BI Ha Hl HF; [exact I|]. inversion HF; subst. destruct BI as [X1 X2].
  split; [apply bitems_frame; assumption| apply IH; assumption].
Qed.
Lemma bitemsl_app : forall m l1 l2, bitemsl m (l1 ++ l2) <-> bitemsl m l1 /\ bitemsl m l2.
Proof. aceil. induction l1; cbn; intros; [tauto|]. rewrite IHl1. tauto. Qed.
Lemma bitemsl_In : forall m l b, bitemsl m l -> In b l -> bitems m b.
Proof. aceil. induction l; cbn; intros b H Hin; [tauto|]. destruct Hin as [<-|Hin]; [tauto| apply IHl; tauto]. Qed.

(* [comment removed for export] *)
Lemma inside_app_r : forall W1 W2 a n, inside W2 a n -> inside (W1 ++ W2) a n.
Proof. aceil. induction W1 as [|[u v] W1 IH]; cbn; intros; [assumption| right; apply IH; assumption]. Qed.
Lemma inside_app_l : forall W1 W2 a n, inside W1 a n -> inside (W1 ++ W2) a n.
Proof. aceil. induction W1 as [|[u v] W1 IH]; cbn; intros; [contradiction|]. destruct H; [left; assumption| right; apply IH; assumption]. Qed.
Lemma inside_bmap : forall (l : list batch) (off k : Z) b a n,
  In b l -> b_addr b + off <= a -> a + n <= b_addr b + off + k -> inside (map (fun b => (b_addr b + off, b_addr b + off + k)) l) a n.
Proof. aceil.
  induction l as [|x l IH]; cbn; intros off k b a n Hin H1 H2; [tauto|].
  destruct Hin as [->|Hin]; [left; lia| right; eapply IH; eauto].
Qed.
Lemma inside_amap : forall (l : list Z) (off k : Z) a0 a n,
  In a0 l -> a0 + off <= a -> a + n <= a0 + off + k -> inside (map (fun x => (x + off, x + off + k)) l) a n.
Proof. aceil.
  induction l as [|x l IH]; cbn; intros off k a0 a n Hin H1 H2; [tauto|].
  destruct Hin as [->|Hin]; [left; lia| right; eapply IH; eauto].
Qed.
Lemma disjoint_amap : forall (l : list Z) (off k : Z) a n,
  (forall x, In x l -> a + n <= x + off \/ x + off + k <= a) -> disjoint_from (map (fun x => (x + off, x + off + k)) l) a n.
Proof. aceil. induction l as [|x l IH]; cbn; intros off k a n H; [exact I|]. split; [apply H; auto| apply IH; intros; apply H; auto]. Qed.
Lemma outside_amap : forall (l : list Z) (off k : Z) x,
  (forall a0, In a0 l -> ~ (a0 + off <= x < a0 + off + k)) -> outside (map (fun a0 => (a0 + off, a0 + off + k)) l) x.
Proof. aceil. induction l as [|y l IH]; cbn; intros off k x H; [exact I|]. split; [apply H; auto| apply IH; intros; apply H; auto]. Qed.
Lemma disjoint_bmap : forall (l : list batch) (off k : Z) a n,
  (forall b, In b l -> a + n <= b_addr b + off \/ b_addr b + off + k <= a) -> disjoint_from (map (fun b => (b_addr b + off, b_addr b + off + k)) l) a n.
Proof. aceil. induction l as [|x l IH]; cbn; intros off k a n H; [exact I|]. split; [apply H; auto| apply IH; intros; apply H; auto]. Qed.
Lemma munch_write_inside : forall W m0 m a bs,
  munch W m0 m -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> inside W a (Z.of_nat (length bs)) -> munch W m0 (write_to_mem m (wa a) bs).
Proof. aceil. intros. apply munch_write; assumption. Qed.

(* [comment removed for export] *)
Lemma outside_forall : forall W x, outside W x <-> forall lo hi, In (lo, hi) W -> ~ (lo <= x < hi).
Proof. aceil.
  induction W as [|[lo hi] W IH]; cbn; intros x.
  - split; [intros _ lo hi []| intros; exact I].
  - rewrite IH. split.
    + intros [H1 H2] lo' hi' [E|Hin]; [injection E as <- <-; exact H1| exact (H2 _ _ Hin)].
    + intros H. split; [apply H; left; reflexivity| intros lo' hi' Hin; apply H; right; exact Hin].
Qed.
Definition covers (W1 W2 : list (Z * Z)) : Prop :=
  forall lo hi, In (lo, hi) W1 -> exists lo' hi', In (lo', hi') W2 /\ lo' <= lo /\ hi <= hi'.
Lemma munch_cover : forall W1 W2 m m', munch W1 m m' -> covers W1 W2 -> munch W2 m m'.
Proof. aceil.
  intros W1 W2 m m' MU CV x Hx. apply MU. apply (proj2 (outside_forall _ _)). intros lo hi Hin.
  destruct (CV lo hi Hin) as (lo' & hi' & Hin' & H1 & H2). pose proof (proj1 (outside_forall _ _) Hx lo' hi' Hin'). lia.
Qed.
Lemma covers_app_l : forall W1 W2 W, covers W1 W2 -> covers W1 (W2 ++ W).
Proof. aceil. intros W1 W2 W CV lo hi Hin. destruct (CV lo hi Hin) as (lo' & hi' & H & H1 & H2). exists lo', hi'. split; [apply in_app_iff; left; exact H| lia]. Qed.
Lemma covers_app_split : forall W1 W2 V, covers W1 V -> covers W2 V -> covers (W1 ++ W2) V.
Proof. aceil. intros W1 W2 V C1 C2 lo hi Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (C1 _ _ Hin)| exact (C2 _ _ Hin)]. Qed.
Lemma covers_self_r : forall W V, covers W (V ++ W).
Proof. aceil. intros W V lo hi Hin. exists lo, hi. split; [apply in_app_iff; right; exact Hin| lia]. Qed.
Lemma covers_self : forall W, covers W W.
Proof. aceil. intros W lo hi Hin. exists lo, hi. split; [exact Hin| lia]. Qed.
(* [comment removed for export] *)
End RC__4.
Ltac cover_member :=
  (left; reflexivity)
  + (right; cover_member)
  + (apply in_map_iff; eexists; split; [reflexivity|]; multimatch goal with H : In _ _ |- _ => exact H end)
  + (apply in_app_iff; ((left; cover_member) + (right; cover_member))).
Ltac solve_covers :=
  let lo := fresh "lo" in let hi := fresh "hi" in let Hin := fresh "Hin" in
  intros lo hi Hin; cbn [In app] in Hin;
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <-; do 2 eexists; split; [cover_member| cbn [fst snd b_addr]; lia] |]
  | _ = _ => injection Hin as <- <-; do 2 eexists; split; [cover_member| cbn [fst snd b_addr]; lia]
  | False => contradiction
  end.

(* [comment removed for export] *)
Section RC__5.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition hidden (X : Prop) : Prop := X.
Lemma hide : forall X : Prop, X -> hidden X. Proof. intros X H; exact H. Qed.
Lemma unhide : forall X : Prop, hidden X -> X. Proof. intros X H; exact H. Qed.

(* [comment removed for export] *)
End RC__5.
Ltac solve_inside_tail :=
  first [ slia
        | lazymatch goal with
          | |- inside (map _ _) _ _ =>
              first [ eapply inside_amap; [multimatch goal with H : In _ _ |- _ => exact H end | slia | slia]
                    | eapply inside_bmap; [multimatch goal with H : In _ _ |- _ => exact H end | cbn [b_addr b_size b_items]; slia | cbn [b_addr b_size b_items]; slia] ]
          | |- _ \/ _ => first [left; slia | right; solve_inside_tail]
          | |- inside (_ ++ _) _ _ => first [apply inside_app_l; cbn [inside]; solve_inside_tail | apply inside_app_r; cbn [inside]; solve_inside_tail]
          | |- False => fail
          end ].
Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside app]; simpl_sizes; solve_inside_tail ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac solve_bforall :=
  cbn [disjoint_from length]; rewrite ?length_le8, ?length_le4;
  first [ apply Forall_nil
        | match goal with
          | F : Forall _ ?l |- Forall _ ?l =>
              refine (Forall_impl _ _ F); cbv beta;
              let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; unfold bok in Hb;
              decompose [and] Hb; repeat split; try exact I; lia
          end ].

(* [comment removed for export] *)
Ltac transport_chunks segs m a bs ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : bcellsn m ?l ?nx |- _ =>
      first [ apply (bcellsn_frame m l nx a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; solve_bforall ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : bitemsl m ?l |- _ =>
      first [ apply (bitemsl_frame m l a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; solve_bforall ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : bitems m ?b |- _ =>
      first [ apply (bitems_frame m b a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : DR ?D ?ds m |- _ =>
      first [ apply (DR_store D ds m a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; solve_sep1 ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  | H : bcellsn m ?l ?nx |- _ =>
      first [ apply (bcellsn_transport W m m' l nx) in H; [ | exact MU | exact WM | solve_bforall ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : bitemsl m ?l |- _ =>
      first [ apply (bitemsl_transport W m m' l) in H; [ | exact MU | exact WM | solve_bforall ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : bitems m ?b |- _ =>
      first [ apply (bitems_transport W m m' b) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : DR ?D ?ds m |- _ =>
      first [ apply (dr_frame D ds m m' W) in H; [ | exact MU | exact WM | solve_seps ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  end.
