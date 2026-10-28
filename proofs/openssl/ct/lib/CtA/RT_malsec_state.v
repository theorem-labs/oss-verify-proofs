(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface R_depot_defs RT_state RT_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sec_new (P n : Z) : secst := mkSec P n false.

(* [comment removed for export] *)
Definition shw (P n : Z) : Z * Z := (pg_dn (shad P), pg_up (shad (P + smsz n))).

Definition sgΣ (Σ : rtsA) (P n : Z) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ ++ [sec_new P n]) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ)
         (fs0 Σ) (fs2 Σ) (fs4 Σ) (fs1 Σ) (fs3 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

Definition saΣ (Σ : rtsA) (P n : Z) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ ++ [sec_new P n]) (sec_nres Σ) (shw P n :: aw Σ) (ql Σ) (qg Σ) (dep Σ)
         (fs0 Σ) (fs2 Σ) (fs4 Σ) (fs1 Σ) (fs3 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

Definition spΣ (Σ : rtsA) (P n : Z) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ ++ [sec_new P n]) 0x4000 (shw P n :: aw Σ) (ql Σ) (qg Σ) (dep Σ)
         (fs0 Σ) (fs2 Σ) (fs4 Σ) (fs1 Σ) (fs3 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

(* [comment removed for export] *)
Definition mal_sec (Σ : rtsA) (P n : Z) (D' : depot) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ ++ [sec_new P n]) 0x4000 (shw P n :: aw Σ) (ql Σ) (qg Σ) D'
         (fs0 Σ) (fs2 Σ) (fs4 Σ) (fs1 Σ) (fs3 Σ) (ia_init Σ) (credit Σ - mcost n) ((s_ubeg (sec_new P n), n) :: live Σ) (frames Σ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fold_smsz_app : forall l s, fold_right (fun s acc => smsz (s_n s) + acc) 0 (l ++ [s])
  = fold_right (fun s acc => smsz (s_n s) + acc) 0 l + smsz (s_n s).
Proof. induction l as [|x l IH]; intros s; cbn [app fold_right]; [lia| rewrite IH; lia]. Qed.

Section Proj.
Variables (Σ : rtsA) (P n : Z) (D' : depot).

Lemma rt_maps_sg : rt_maps (sgΣ Σ P n) = secmap (sec_new P n) :: rt_maps Σ.
Proof. unfold rt_maps, sgΣ. cbn [sec lay]. rewrite rev_app_distr. reflexivity. Qed.
Lemma rt_maps_sa : rt_maps (saΣ Σ P n) = secmap (sec_new P n) :: rt_maps Σ.
Proof. unfold rt_maps, saΣ. cbn [sec lay]. rewrite rev_app_distr. reflexivity. Qed.
Lemma rt_maps_sp : rt_maps (spΣ Σ P n) = secmap (sec_new P n) :: rt_maps Σ.
Proof. unfold rt_maps, spΣ. cbn [sec lay]. rewrite rev_app_distr. reflexivity. Qed.
Lemma rt_maps_mal : rt_maps (mal_sec Σ P n D') = secmap (sec_new P n) :: rt_maps Σ.
Proof. unfold rt_maps, mal_sec. cbn [sec lay]. rewrite rev_app_distr. reflexivity. Qed.

Lemma rt_eager_sg : rt_eager (sgΣ Σ P n) = rt_eager Σ + smsz n.
Proof. unfold rt_eager, sgΣ. cbn [pr sec sec_nres]. rewrite fold_smsz_app. cbn [sec_new s_n]. lia. Qed.
Lemma rt_eager_sa : rt_eager (saΣ Σ P n) = rt_eager Σ + smsz n.
Proof. unfold rt_eager, saΣ. cbn [pr sec sec_nres]. rewrite fold_smsz_app. cbn [sec_new s_n]. lia. Qed.
Lemma rt_eager_sp : rt_eager (spΣ Σ P n) = rt_eager Σ + smsz n + 8 * (0x4000 - sec_nres Σ).
Proof. unfold rt_eager, spΣ. cbn [pr sec sec_nres]. rewrite fold_smsz_app. cbn [sec_new s_n]. lia. Qed.
Lemma rt_eager_mal : rt_eager (mal_sec Σ P n D') = rt_eager (spΣ Σ P n).
Proof. reflexivity. Qed.

Lemma rtA_allow_sg : rtA_allow (sgΣ Σ P n) = rtA_allow Σ.
Proof. reflexivity. Qed.
Lemma rtA_allow_sa : rtA_allow (saΣ Σ P n) = shw P n :: rtA_allow Σ.
Proof. reflexivity. Qed.
Lemma rtA_allow_sp : rtA_allow (spΣ Σ P n) = shw P n :: rtA_allow Σ.
Proof. reflexivity. Qed.
Lemma rtA_allow_mal : rtA_allow (mal_sec Σ P n D') = shw P n :: rtA_allow Σ.
Proof. reflexivity. Qed.
End Proj.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sum_cls_le : forall f k B, (forall c, 1 <= c <= Z.of_nat k -> 0 <= f c <= B) -> 0 <= sum_cls f k <= Z.of_nat k * B.
Proof.
  intros f k B. induction k as [|k IH]; intros H; cbn [sum_cls]; [lia|].
  pose proof (H (Z.of_nat (Datatypes.S k)) ltac:(lia)). specialize (IH ltac:(intros c Hc; apply H; lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma prim_eager_bound : forall Σ, regs_wf Σ ->
  0 <= sum_cls (fun c => r_muser (pr Σ c) + r_mfa (pr Σ c)) 31 <= 31 * (kUserCap + kFaCap).
Proof.
  intros Σ (R1 & _). apply (sum_cls_le _ 31 (kUserCap + kFaCap)). intros c Hc.
  destruct (R1 c ltac:(lia)) as ((M1 & M2) & _ & _ & _ & (F1 & F2) & _). lia.
Qed.

(* [comment removed for export] *)
Lemma sec_eager_room : forall Σ n, rt_wf Σ -> 64512 < n -> mcost n <= credit Σ ->
  smsz n <= mcost n /\ rt_eager Σ + smsz n + 8 * (0x4000 - sec_nres Σ) <= 2 ^ 38.
Proof.
  intros Σ n HW Hn Hc. pose proof HW as (_ & HR & _ & (_ & HN & _) & _ & _ & (B1 & _ & B3 & _ & B5) & _).
  pose proof (prim_eager_bound Σ HR) as Hp.
  assert (Hsm : smsz n <= mcost n).
  { unfold smsz, pg_up, needed, rounded, mcost. rewrite (proj2 (Z.leb_gt n 64512)) by lia.
    unfold rz_size, rz_log. rewrite !(proj2 (Z.leb_gt n _)) by lia. cbn.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  split; [exact Hsm|].
  unfold rt_eager. unfold secsum in B5. unfold kUserCap, kFaCap, CREDIT0 in *. destruct HN as [E|E]; rewrite E in *; lia.
Qed.
