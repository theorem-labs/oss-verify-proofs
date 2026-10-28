(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface R_cache_defs R_prim_defs R_depot_defs R_fs_defs RT_state RT_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition updf {A : Type} (f : Z -> A) (c : Z) (x : A) : Z -> A := fun c' => if c' =? c then x else f c'.

Lemma updf_same : forall {A} (f : Z -> A) c x, updf f c x c = x.
Proof. intros A f c x. unfold updf. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma updf_other : forall {A} (f : Z -> A) c x c', c' <> c -> updf f c x c' = f c'.
Proof. intros A f c x c' H. unfold updf. destruct (Z.eqb_spec c' c); [congruence | reflexivity]. Qed.

(* [comment removed for export] *)
Definition ureg (r : regst) (i : nat) (st : ckst) : regst := mkReg (r_muser r) (r_mfa r) (upd (r_st r) i st) (r_fl r).

Lemma nth_upd_ck : forall (l : list ckst) i j x,
  nth_error (upd l i x) j = if Nat.eqb i j then (if Nat.ltb j (length l) then Some x else None) else nth_error l j.
Proof.
  intros l i j x. destruct (Nat.eqb_spec i j) as [->|Hne].
  - destruct (Nat.ltb_spec j (length l)) as [L|L]; [apply nth_error_upd_same; exact L|]. apply nth_error_None. rewrite upd_length. lia.
  - apply nth_error_upd_other. exact Hne.
Qed.

Definition set_st (Σ : rtsA) (c : Z) (i : nat) (st : ckst) : rtsA :=
  mkRtsA (lay Σ) (updf (pr Σ) c (ureg (pr Σ c) i st)) (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ)
    (fs0 Σ) (fs2 Σ) (fs1 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

(* [comment removed for export] *)
Definition set_sec (Σ : rtsA) (l : list secst) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) l (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ)
    (fs0 Σ) (fs2 Σ) (fs1 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

(* [comment removed for export] *)
Definition set_q (Σ : rtsA) (l g : list batch) : rtsA :=
  mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) l g (dep Σ)
    (fs0 Σ) (fs2 Σ) (fs1 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dh_keep (c : Z) : nat := Z.to_nat (MaxCount c - MaxCount c / 2).
Definition dh_nf (c : Z) (r : regst) : Z := Z.of_nat (length (r_fl r)) + MaxCount c / 2.
Definition dh_grow (c : Z) (r : regst) : bool := r_mfa r <? 4 * dh_nf c r.
Definition dh_mfa (c : Z) (r : regst) : Z := if dh_grow c r then round_fa (4 * dh_nf c r) else r_mfa r.
Definition cdeal_full (c : Z) (l : list Z) : bool := MaxCount c <=? Z.of_nat (length l).

Definition cdeal_reg (c : Z) (r : regst) (l : list Z) : regst :=
  if cdeal_full c l then mkReg (r_muser r) (dh_mfa c r) (r_st r) (r_fl r ++ skipn (dh_keep c) l) else r.
Definition cdeal_ca (c : Z) (i : nat) (l : list Z) : list Z :=
  (if cdeal_full c l then firstn (dh_keep c) l else l) ++ [Z.of_nat i].

(* [comment removed for export] *)
Definition cdealΣ (Σ : rtsA) (c : Z) (i : nat) : rtsA :=
  mkRtsA (lay Σ) (updf (pr Σ) c (cdeal_reg c (pr Σ c) (ca Σ c))) (updf (ca Σ) c (cdeal_ca c i (ca Σ c))) (ca_init Σ) (sec Σ)
    (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ) (fs0 Σ) (fs2 Σ) (fs1 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).

(* [comment removed for export] *)
Definition recp (Σ : rtsA) (c : Z) (i : nat) : rtsA := cdealΣ (set_st Σ c i CkIdle) c i.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition swap_remove {X : Type} (k : nat) (l : list X) : list X :=
  match l with
  | [] => []
  | x :: _ => if Nat.eqb (S k) (length l) then removelast l else upd (removelast l) k (last l x)
  end.

Definition recs (Σ : rtsA) (k : nat) : rtsA := set_sec Σ (swap_remove k (sec Σ)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition qallP (Σ : rtsA) (P : list batch) : list batch := ql Σ ++ qg Σ ++ P.
Definition qentsP (Σ : rtsA) (P : list batch) : list (Z * Z) := flat_map snd (qallP Σ P).

Definition quar_wfP (Σ : rtsA) (P : list batch) : Prop :=
  qbytes (ql Σ) <= QMAX_L + 0x10000 /\ qbytes (qg Σ) <= QMAX_G + 0x10000 /\ qbytes P <= 2 ^ 40
  /\ Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) (qallP Σ P)
  /\ NoDup (map fst (qallP Σ P))
  /\ Forall (fun b => (length (snd b) <= 1021)%nat) (qallP Σ P)
  /\ Forall (qent_ok Σ) (qentsP Σ P) /\ NoDup (map fst (qentsP Σ P))
  /\ (forall c i, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some CkBatch ->
        c = 24 /\ In (p_abeg (l_SB (lay Σ)) 24 i) (map fst (qallP Σ P))).

Definition rt_countP (Σ : rtsA) (P : list batch) : Prop :=
  (forall c i n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkQuar n) ->
     In (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n) (qentsP Σ P))
  /\ (forall s, In s (sec Σ) -> s_quar s = true -> In (s_mb s + 6128, s_n s) (qentsP Σ P)).

Definition rt_wfP (Σ : rtsA) (P : list batch) : Prop :=
  layout_ok (lay Σ) /\ regs_wf Σ /\ live_wf Σ /\ sec_wf Σ /\ quar_wfP Σ P /\ fs_wf Σ /\ budget_wf Σ
  /\ depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ))
  /\ d_n (dep Σ) + 2 < 2 ^ 16 /\ d_tot (dep Σ) + 255 < 2 ^ 20 /\ dep_inv (l_cg (lay Σ)) (dep Σ) /\ rt_countP Σ P.

Lemma qallP_nil : forall Σ, qallP Σ [] = ql Σ ++ qg Σ.
Proof. intros Σ. unfold qallP. rewrite app_nil_r. reflexivity. Qed.
Lemma qentsP_nil : forall Σ, qentsP Σ [] = qents Σ.
Proof. intros Σ. unfold qentsP, qents. rewrite qallP_nil. reflexivity. Qed.

Lemma rt_wfP_nil : forall Σ, rt_wfP Σ [] -> rt_wf Σ.
Proof.
  intros Σ (H1 & H2 & H3 & H4 & (Q1 & Q2 & _ & Q4 & Q5 & Q6 & Q7 & Q8 & Q9) & H6 & H7 & H8 & H9 & H10 & H11 & (C1 & C2)).
  rewrite qallP_nil in Q4, Q5, Q6, Q9. rewrite qentsP_nil in Q7, Q8, C1, C2.
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 _))))))))))).
  - exact (conj Q1 (conj Q2 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 Q9))))))).
  - exact (conj C1 C2).
Qed.
