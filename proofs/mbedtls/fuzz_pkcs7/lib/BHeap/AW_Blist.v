(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_Blist () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "ARUN_1.bn_addr"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "ARUN_1.bn_size"; "ARUN_1.bn_count"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Stdlib.ZArith.BinInt.Z.add"; "ARUN_1.bn_elems"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "ARUN_1.bnode"; "Corelib.Init.Datatypes.list"; "ARUN_1.bwf"; "ARUN_1.bn_ok"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.app"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Lists.ListDef.map"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "ARUN_1.bnode_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "ARUN_1.blistT"; "ARUN_1.hd_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Record bnode := BN { bn_addr : Z; bn_size : Z; bn_elems : list word }.
Definition bn_count (b : bnode) : Z := Z.of_nat (length (bn_elems b)).
(* [comment removed for export] *)
Definition hd_addrT (bs : list bnode) (t : Z) : Z := match bs with [] => t | b :: _ => bn_addr b end.
Definition hd_addr (bs : list bnode) : Z := hd_addrT bs 0.
Fixpoint last_addr (d : Z) (bs : list bnode) : Z := match bs with [] => d | b :: r => last_addr (bn_addr b) r end.
Fixpoint bsum (bs : list bnode) : Z := match bs with [] => 0 | b :: r => bn_size b + bsum r end.

(* [comment removed for export] *)
Definition bnode_at (m : mem) (b : bnode) (nx : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Blist ()) "(0.(1.$2.O3.(3.O2.)(4.$5.(6.(7.&40.O1.))(4.$5.(6.(7.&40.(8.O2.)))(4.$5.(6.(7.&40.(9.O2.)))(:.$5.)))))(0.(;.$2.O3.(<.(3.O2.)+18.)(=.O2.))(>.$2.O3.(3.O2.)+2000.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Fixpoint blistT (m : mem) (bs : list bnode) (t : Z) : Prop :=
  match bs with
  | [] => True
  | b :: r => bnode_at m b (hd_addrT r t) /\ blistT m r t
  end.
Definition blist (m : mem) (bs : list bnode) : Prop := blistT m bs 0.

(* [comment removed for export] *)
Definition bn_ok (b : bnode) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Blist ()) "(0.(?.+65?000.(3.O1.))(0.(?.(<.(3.O1.)+2000.)(10.VhAR,))(0.(11.$12.(13.(3.O1.)+8.)=)(0.(0.(?.+2000.(8.O1.))(14.(8.O1.)(15.+2.+3<.)))(?.(9.O1.)+3?=.)))))")
(* [comment removed for export] *).
Definition aapart (l : list Z) : Prop :=
  List.NoDup l /\ forall x y, In x l -> In y l -> x <> y -> x + 8192 <= y \/ y + 8192 <= x.
Definition bapart (bs : list bnode) : Prop := aapart (map bn_addr bs).
Definition bwf (bs : list bnode) : Prop := Forall bn_ok bs /\ bapart bs.

#[using="Type"] Lemma bsum_app : forall a b, bsum (a ++ b) = bsum a + bsum b.
Proof. induction a; intros; cbn; [lia|]. rewrite IHa. lia. Qed.
#[using="Type"] Lemma bsum_nonneg : forall bs, Forall bn_ok bs -> 0 <= bsum bs.
Proof. induction bs; intros H; cbn; [lia|]. inversion H; subst. unfold bn_ok in *. specialize (IHbs ltac:(assumption)). lia. Qed.
#[using="Type"] Lemma bsum_ge : forall bs, Forall bn_ok bs -> 8192 * Z.of_nat (length bs) <= bsum bs.
Proof. induction bs; intros H; cbn [bsum length]; [lia|]. inversion H; subst. unfold bn_ok in *. specialize (IHbs ltac:(assumption)). lia. Qed.
#[using="Type"] Lemma last_addr_app : forall d a b, last_addr d (a ++ b) = last_addr (last_addr d a) b.
Proof. intros d a; revert d; induction a; intros; cbn; [reflexivity|]. apply IHa. Qed.
#[using="Type"] Lemma last_addr_snoc : forall d a x, last_addr d (a ++ [x]) = bn_addr x.
Proof. intros. rewrite last_addr_app. reflexivity. Qed.
#[using="Type"] Lemma last_addr_cons_ne : forall d d' b r, last_addr d (b :: r) = last_addr d' (b :: r).
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma hd_addrT_app : forall a b t, hd_addrT (a ++ b) t = hd_addrT a (hd_addrT b t).
Proof. intros [|x a] b t; reflexivity. Qed.
#[using="Type"] Lemma hd_addr_app_ne : forall (a b : list bnode), a <> [] -> hd_addr (a ++ b) = hd_addr a.
Proof. intros [|x a] b H; [congruence| reflexivity]. Qed.
#[using="Type"] Lemma zlen_app1 : forall (A : Type) (l : list A) (x : A), Z.of_nat (length (l ++ [x])) = Z.of_nat (length l) + 1.
Proof. intros. rewrite app_length. cbn. lia. Qed.
#[using="Type"] Lemma snoc_or_nil : forall (l : list bnode), l = [] \/ exists l0 x, l = l0 ++ [x].
Proof.
  intros l. destruct l as [|a r] eqn:E; [left; reflexivity| right].
  destruct (exists_last (l:=a :: r) ltac:(discriminate)) as [l0 [x H]]. dexists l0, x. exact H.
Qed.

#[using="Type"] Lemma blistT_app : forall m a b t, blistT m (a ++ b) t <-> blistT m a (hd_addrT b t) /\ blistT m b t.
Proof.
  intros m a; induction a as [|x a IH]; intros b t; cbn [app blistT].
  - tauto.
  - rewrite hd_addrT_app. rewrite IH. tauto.
Qed.
#[using="Type"] Lemma blistT_snoc : forall m a x t, blistT m (a ++ [x]) t <-> blistT m a (bn_addr x) /\ bnode_at m x t.
Proof. intros. rewrite blistT_app. cbn. tauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aapart_perm : forall l1 l2, Permutation l1 l2 -> aapart l1 -> aapart l2.
Proof.
  intros l1 l2 P [N A]. split; [eapply Permutation_NoDup; [exact P| exact N]|].
  intros x y Hx Hy. apply A; eapply Permutation_in; try eassumption; apply Permutation_sym; exact P.
Qed.
#[using="Type"] Lemma aapart_app_l : forall a b, aapart (a ++ b) -> aapart a.
Proof.
  intros a b [N A]. split; [exact (NoDup_app_remove_r _ _ N)|]. intros x y Hx Hy. apply A; apply in_or_app; left; assumption.
Qed.
#[using="Type"] Lemma aapart_app_r : forall a b, aapart (a ++ b) -> aapart b.
Proof.
  intros a b [N A]. split; [exact (NoDup_app_remove_l _ _ N)|]. intros x y Hx Hy. apply A; apply in_or_app; right; assumption.
Qed.
#[using="Type"] Lemma aapart_app_ne : forall a b x y, aapart (a ++ b) -> In x a -> In y b -> x <> y.
Proof.
  intros a b x y [N _] Hx Hy ->. induction a as [|z a IH]; [exact Hx|].
  cbn in N. inversion N; subst. destruct Hx as [->|Hx]; [| exact (IH ltac:(assumption) Hx)].
  match goal with H : ~ In y (a ++ b) |- _ => apply H end. apply in_or_app. right. exact Hy.
Qed.

#[using="Type"] Lemma bwf_cons_inv : ltac2:(CDefT.buildp (gd_tbl_AW_Blist ()) "Pb,$16.Pbs,(17.$16.)P,(18.(4.$16.R2.R1.))(0.(19.R3.)(0.(18.R2.)Pbj,$16.P,(1:.$16.R1.R3.)(1;.(?.(<.(3.R5.)+2000.)(3.R2.))(?.(<.(3.R2.)+2000.)(3.R5.)))))")
(* [comment removed for export] *).
Proof.
  intros b bs [F A]. inversion F; subst. split; [assumption|]. unfold bapart in A. cbn [map] in A. split.
  - split; [assumption|]. exact (aapart_app_r [bn_addr b] _ A).
  - intros bj Hj. pose proof A as [N A']. apply A'; [left; reflexivity| right; apply in_map; exact Hj|].
    apply (aapart_app_ne [bn_addr b] (map bn_addr bs) _ _ A); [left; reflexivity| apply in_map; exact Hj].
Qed.
#[using="Type"] Lemma bwf_tail : forall b bs, bwf (b :: bs) -> bwf bs.
Proof. intros b bs H. apply bwf_cons_inv in H. tauto. Qed.
#[using="Type"] Lemma bwf_app_l : forall a b, bwf (a ++ b) -> bwf a.
Proof.
  intros a b [F A]. split. { apply Forall_app in F. tauto. } unfold bapart in *. rewrite map_app in A. exact (aapart_app_l _ _ A).
Qed.
#[using="Type"] Lemma bwf_app_r : forall a b, bwf (a ++ b) -> bwf b.
Proof.
  intros a b [F A]. split. { apply Forall_app in F. tauto. } unfold bapart in *. rewrite map_app in A. exact (aapart_app_r _ _ A).
Qed.
#[using="Type"] Lemma bapart_in : ltac2:(CDefT.buildp (gd_tbl_AW_Blist ()) "Pbs,(17.$16.)Pb,$16.Pb',$16.P,(18.R3.)P,(1:.$16.R3.R4.)P,(1:.$16.R3.R5.)P,(1<.(11.$12.(3.R5.)(3.R4.)))(1;.(?.(<.(3.R6.)+2000.)(3.R5.))(?.(<.(3.R5.)+2000.)(3.R6.)))")
(* [comment removed for export] *).
Proof. intros bs b b' [F [N A]] Hb Hb' NE. apply A; [apply in_map; exact Hb| apply in_map; exact Hb'| exact NE]. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma bwf_app_apart : ltac2:(CDefT.buildp (gd_tbl_AW_Blist ()) "Pl1,(17.$16.)Pl2,(17.$16.)Px,$16.Py,$16.P,(18.(1=.$16.R4.R3.))P,(1:.$16.R3.R5.)P,(1:.$16.R3.R5.)(1;.(?.(<.(3.R5.)+2000.)(3.R4.))(?.(<.(3.R4.)+2000.)(3.R5.)))")
(* [comment removed for export] *).
Proof.
  intros l1 l2 x y WF Hx Hy. pose proof WF as [F A]. unfold bapart in A. rewrite map_app in A.
  apply (bapart_in (l1 ++ l2) x y WF); [apply in_or_app; left; exact Hx| apply in_or_app; right; exact Hy|].
  eapply aapart_app_ne; [exact A| apply in_map; exact Hx| apply in_map; exact Hy].
Qed.
#[using="Type"] Lemma bwf_ok_in : forall bs b, bwf bs -> In b bs -> bn_ok b.
Proof. intros bs b [F _] H. rewrite Forall_forall in F. apply F, H. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma bwf_in_split : forall bs b, bwf bs -> In b bs -> exists l r, bs = l ++ b :: r /\ ~ In b l /\ ~ In b r.
Proof.
  intros bs b WF Hb. destruct (in_split _ _ Hb) as (l & r & ->). dexists l, r. split; [reflexivity|].
  split; intros H.
  - exact (aapart_app_ne _ _ _ _ ltac:(pose proof WF as [_ A]; unfold bapart in A; rewrite map_app in A; exact A)
             (in_map bn_addr _ _ H) ltac:(left; reflexivity) eq_refl).
  - pose proof (bwf_app_r _ _ WF) as WF'. pose proof WF' as [_ [N _]]. cbn [map] in N. inversion N; subst.
    match goal with X : ~ In _ _ |- _ => apply X end. apply in_map. exact H.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma bwf_of_perm : ltac2:(CDefT.buildp (gd_tbl_AW_Blist ()) "Pbs,(17.$16.)Pbs',(17.$16.)P,(18.R2.)P,(1>.$12.(1?.$16.$12.$3.R3.)(1?.$16.$12.$3.R2.))P,(20.$16.$19.R3.)(18.R4.)")
(* [comment removed for export] *).
Proof. intros bs bs' [F A] P F'. split; [exact F'|]. exact (aapart_perm _ _ P A). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma disjoint_sub : forall W A N a n, disjoint_from W A N -> A <= a -> a + n <= A + N -> disjoint_from W a n.
Proof.
  intros W A N a n D Ha Hn. induction W as [|[u v] W IH]; cbn in *; [exact I|]. destruct D as [D1 D2]. split; [lia| apply IH; exact D2].
Qed.
#[using="Type"] Lemma bnode_at_transport : ltac2:(CDefT.buildp (gd_tbl_AW_Blist ()) "PW,(17.$21.)Pm,P,(22.&40.)(23.(22.&8.))Pm',P,(22.&40.)(23.(22.&8.))Pb,$16.Pnx,$12.P,(24.R4.R2.R1.)P,(25.R6.R5.R4.)P,(26.$2.R6.R5.)P,(27.R8.(3.R5.)+2000.)P,(?.(9.R6.)+3?=.)(24.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  (intros W m m' b nx dd_H; ddestruct dd_H as (H1 & H2 & H3); intros MU WM DJ CNT). unfold bn_count in CNT. split; [|split].
  - eapply rw_cells_transport; [exact H1| exact MU| exact WM| eapply disjoint_sub; [exact DJ| lia| cbn; lia]].
  - eapply u64arr_transport; [exact H2| exact MU| exact WM| eapply disjoint_sub; [exact DJ| lia| lia]].
  - eapply wr_at_transport; [exact H3| exact WM].
Qed.
#[using="Type"] Lemma blistT_transport : ltac2:(CDefT.buildp (gd_tbl_AW_Blist ()) "PW,(17.$21.)Pm,P,(22.&40.)(23.(22.&8.))Pm',P,(22.&40.)(23.(22.&8.))Pbs,(17.$16.)Pt,$12.P,(28.R4.R2.R1.)P,(20.$16.$19.R3.)P,(25.R7.R6.R5.)P,(26.$2.R7.R6.)P,Pb,$16.P,(1:.$16.R1.R7.)(27.R;.(3.R2.)+2000.)(28.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  induction bs as [|b r IH]; intros t BL F MU WM DJ; [exact I|].
  destruct BL as [N BL]. inversion F; subst. split.
  - eapply bnode_at_transport; [exact N| exact MU| exact WM| apply DJ; left; reflexivity| unfold bn_ok in *; lia].
  - apply IH; auto. intros b' Hb'. apply DJ. right. exact Hb'.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma last_addr_bound : forall d l, Forall bn_ok l -> 0 <= d < 2^64 -> 0 <= last_addr d l < 2^64.
Proof.
  intros d l; revert d; induction l as [|b l IHl]; intros d F Hd; cbn; [exact Hd|].
  inversion F; subst. apply IHl; [assumption|]. unfold bn_ok in *; lia.
Qed.

#[using="Type"] Lemma blistT_map_nodes : ltac2:(CDefT.buildp (gd_tbl_AW_Blist ()) "Pm,P,(22.&40.)(23.(22.&8.))Pm',P,(22.&40.)(23.(22.&8.))Pl,(17.$16.)Pt,$12.P,Pb,$16.Pnx,$12.P,(1:.$16.R2.R4.)P,(24.R7.R3.R2.)(24.R7.R4.R3.)P,(28.R5.R3.R2.)(28.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m m' l; induction l as [|b l IH]; intros t H B; [exact I|]. destruct B as [N B]. split.
  - apply H; [left; reflexivity| exact N].
  - apply IH; [| exact B]. intros b' nx Hb' N'. apply H; [right; exact Hb'| exact N'].
Qed.

#[using="Type"] Lemma hd_addr_app_same : ltac2:(CDefT.buildp (gd_tbl_AW_Blist ()) "Pdone,(17.$16.)Pa,$16.Pb,$16.Pl1,(17.$16.)Pl2,(17.$16.)P,(11.$12.(3.R4.)(3.R3.))(11.$12.(29.(1=.$16.R6.(4.$16.R5.R3.)))(29.(1=.$16.R6.(4.$16.R4.R2.))))")
(* [comment removed for export] *).
Proof. intros [|d done] a b l1 l2 E; cbn; [exact E| reflexivity]. Qed.

#[using="Type"] Lemma last_addr_mid : forall d l b r, last_addr d (l ++ b :: r) = last_addr (bn_addr b) r.
Proof. intros. rewrite last_addr_app. reflexivity. Qed.

#[using="Type"] Lemma last_addr_in : forall d l, l <> [] -> exists b, In b l /\ last_addr d l = bn_addr b.
Proof.
  intros d l; revert d; induction l as [|b l IH]; intros d NE; [congruence|].
  destruct l as [|b2 l2]; [exists b; split; [left; reflexivity| reflexivity]|].
  ddestruct (IH (bn_addr b) ltac:(discriminate)) as (b0 & H0 & E0). exists b0. split; [right; exact H0| exact E0].
Qed.

#[using="Type"] Lemma u64arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u64arr asegs m A [].
Proof. intros m A H0 H1. split; (split; [lia|]); cbn; (split; [lia|]); intros i Hi; exfalso; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma munch_restrict : ltac2:(CDefT.buildp (gd_tbl_AW_Blist ()) "PW,(17.$21.)Pm,P,(22.&40.)(23.(22.&8.))Pm',P,(22.&40.)(23.(22.&8.))PA,$12.Pn,$12.P,(25.R5.R4.R3.)P,Py,$12.P,(0.(?.R4.R1.)(14.R1.(<.R4.R3.)))(2:.R8.R2.)(25.(4.(2;.$12.$12.)(2<.$12.$12.=R4.)(4.(2;.$12.$12.)(2<.$12.$12.(<.R4.R3.)(15.+2.+40.))(:.(2;.$12.$12.))))R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' A n MU H x Ox. cbn in Ox. pose proof (bv_unsigned_in_range 64 x). change (bv_modulus 64) with (2^64) in *. apply MU. apply H. lia.
Qed.


End ARUN_1.
