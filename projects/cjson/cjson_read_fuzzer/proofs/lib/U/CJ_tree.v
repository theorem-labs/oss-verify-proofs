(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition wb (z : Z) : byte := Z_to_bv 8 z.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma alloc_ceiling_eq : alloc_ceiling = alloc_ceiling.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac unfold_pconsts :=
  unfold PMALLOC, PFREE, PREALLOC, PTP, PERRNO, PHOOKS, PGERROR, PLCONV, PDOTSTR, PEMPTY,
         PIMG_LO, PIMG_HI, PDATA_LO, PLIBC, PCTX_END, PSSP, PGOT_SSP, RMALLOC_STACK in *.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition node_cells (nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z) : list cell :=
  [C8 (wz nx); C8 pv; C8 (wz ch); C4 (wz ty); C4 p1; C8 (wz vs); C4 vi; C4 p2; C8 vd; C8 (wz ky)].

Lemma node_cells_size : forall nx pv ch ty p1 vs vi p2 vd ky,
  cells_size (node_cells nx pv ch ty p1 vs vi p2 vd ky) = 64%nat.
Proof. reflexivity. Qed.

Lemma node_bound : forall m p nx pv ch ty p1 vs vi p2 vd ky,
  rw_cells usegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> 0 <= p /\ p + 64 <= 2^64.
Proof. intros. pose proof (rw_cells_bound usegs _ _ _ H) as HB. rewrite node_cells_size in HB. lia. Qed.

(* [comment removed for export] *)
Definition CJ_ANY : Z -> Prop := fun _ => True.
Definition CJ_PRINTABLE : Z -> Prop := fun ty => In ty [1; 2; 4; 8; 16; 32; 64].

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition magree (P : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2^64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).

Lemma magree_refl : forall P m, magree P m m.
Proof. intros P m a _ _. auto. Qed.

Lemma magree_trans : forall P m1 m2 m3, magree P m1 m2 -> magree P m2 m3 -> magree P m1 m3.
Proof.
  intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma magree_mono : forall (P P' : Z -> Prop) m m', magree P m m' -> (forall a, P' a -> P a) -> magree P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

Lemma bytes_at_magree : forall P m m' A bs,
  magree P m m' -> bytes_at usegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at usegs m' A bs.
Proof.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma wr_at_magree : forall P m m' A n,
  magree P m m' -> wr_at usegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at usegs m' A n.
Proof.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Lemma rw_cells_magree : forall P m m' A cs,
  magree P m m' -> rw_cells usegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells usegs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_magree; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_magree; eauto.
Qed.

(* [comment removed for export] *)
Lemma magree_of_munch : forall (P : Z -> Prop) W m m',
  munch W m m' -> wmono usegs m m' -> (forall a, 0 <= a < 2^64 -> P a -> outside W a) -> magree P m m'.
Proof.
  intros P W m m' MU WM HO a Ha HP. split.
  - apply MU. rewrite wa_unsigned by exact Ha. apply HO; assumption.
  - apply WM.
Qed.

Lemma magree_of_cj_pres : forall (P : Z -> Prop) LB SP m m',
  cj_pres LB SP m m' -> (forall a, 0 <= a < 2^64 -> P a -> cj_client_addr LB SP a) -> magree P m m'.
Proof. intros P LB SP m m' H HO a Ha HP. apply H; auto. Qed.

Lemma cj_pres_magree : forall LB SP m m', cj_pres LB SP m m' <-> magree (cj_client_addr LB SP) m m'.
Proof. intros; split; intros H a Ha HP; apply H; auto. Qed.

(* [comment removed for export] *)
Lemma in_cblock_app : forall B1 B2 a, in_cblock (B1 ++ B2) a <-> in_cblock B1 a \/ in_cblock B2 a.
Proof.
  intros B1 B2 a. unfold in_cblock. split.
  - intros (A & n & Hin & R). apply in_app_or in Hin. destruct Hin; [left|right]; exists A, n; auto.
  - intros [(A & n & Hin & R)|(A & n & Hin & R)]; exists A, n; split; auto; apply in_or_app; auto.
Qed.

Lemma in_cblock_cons : forall A n B a, in_cblock ((A, n) :: B) a <-> (A <= a < A + n) \/ in_cblock B a.
Proof.
  intros A n B a. change ((A, n) :: B) with ([(A, n)] ++ B). rewrite in_cblock_app. unfold in_cblock at 1.
  split.
  - intros [(A' & n' & [E|[]] & R)|H]; [inversion E; subst; left; exact R| right; exact H].
  - intros [R|H]; [left; exists A, n; split; [left; reflexivity| exact R]| right; exact H].
Qed.

Lemma in_cblock_nil : forall a, ~ in_cblock [] a.
Proof. intros a (A & n & H & _). exact H. Qed.

Lemma in_cblock_mono : forall B1 B2 a, (forall b, In b B1 -> In b B2) -> in_cblock B1 a -> in_cblock B2 a.
Proof. intros B1 B2 a H (A & n & Hin & R). exists A, n. auto. Qed.

(* [comment removed for export] *)
Lemma magree_blocks_of_cj_pres : forall B LB SP m m',
  cj_pres LB SP m m' -> (forall b, In b B -> In b LB) -> magree (in_cblock B) m m'.
Proof.
  intros B LB SP m m' H HB. eapply magree_of_cj_pres; [exact H|].
  intros a _ Ha. right; right. eapply in_cblock_mono; eauto.
Qed.

(* [comment removed for export] *)
Lemma magree_blocks_of_munch : forall B W m m',
  munch W m m' -> wmono usegs m m' ->
  (forall A n, In (A, n) B -> disjoint_from W A n) ->
  magree (in_cblock B) m m'.
Proof.
  intros B W m m' MU WM HD. eapply magree_of_munch; [exact MU| exact WM|].
  intros a _ (A & n & Hin & R). eapply disjoint_outside; [apply HD; exact Hin| exact R].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cj_str (m : word -> option byte) (s : Z) (B : list cblock) : Prop :=
  (s = 0 /\ B = [])
  \/ (exists (n : Z) (str tail : list byte),
        s <> 0 /\ B = [(s, n)]
        /\ bytes_at usegs m s (str ++ wb 0 :: tail)
        /\ ~ In (wb 0) str
        /\ Z.of_nat (length str) + 1 + Z.of_nat (length tail) = n).

Lemma cj_str_null : forall m, cj_str m 0 [].
Proof. intros m. left. auto. Qed.

Lemma cj_str_intro : forall m s n str tail,
  s <> 0 -> bytes_at usegs m s (str ++ wb 0 :: tail) -> ~ In (wb 0) str ->
  Z.of_nat (length str) + 1 + Z.of_nat (length tail) = n ->
  cj_str m s [(s, n)].
Proof. intros. right. exists n, str, tail. auto 10. Qed.

Lemma cj_str_magree : forall P m m' s B,
  magree P m m' -> cj_str m s B -> (forall a, in_cblock B a -> P a) -> cj_str m' s B.
Proof.
  intros P m m' s B HP [H|(n & str & tail & NZ & -> & BY & NN & LEN)] HB; [left; exact H|].
  right. exists n, str, tail. split; [exact NZ|]. split; [reflexivity|]. split; [|split; [exact NN| exact LEN]].
  eapply bytes_at_magree; [exact HP| exact BY|]. intros a Ha. apply HB. exists s, n. split; [left; reflexivity|].
  rewrite length_app in Ha. cbn [length] in Ha. lia.
Qed.

Lemma cj_str_nil_inv : forall m s, cj_str m s [] -> s = 0.
Proof. intros m s [[H _]|(n & str & tail & _ & E & _)]; [exact H| discriminate]. Qed.

Lemma cj_str_zero_inv : forall m B, cj_str m 0 B -> B = [].
Proof. intros m B [[_ H]|(n & str & tail & NZ & _)]; [exact H| exfalso; apply NZ; reflexivity]. Qed.

Lemma cj_str_nonzero_inv : forall m s B, cj_str m s B -> s <> 0 ->
  exists n str tail, B = [(s, n)] /\ bytes_at usegs m s (str ++ wb 0 :: tail) /\ ~ In (wb 0) str
    /\ Z.of_nat (length str) + 1 + Z.of_nat (length tail) = n.
Proof.
  intros m s B [[H _]|(n & str & tail & _ & E & BY & NN & LEN)] NZ; [exfalso; exact (NZ H)|].
  exists n, str, tail. auto.
Qed.

Lemma cj_str_blocks : forall m s B, cj_str m s B -> B = [] \/ (exists n, B = [(s, n)] /\ s <> 0 /\ 1 <= n).
Proof.
  intros m s B [[_ ->]|(n & str & tail & NZ & -> & _ & _ & LEN)]; [left; reflexivity| right]. exists n. split; [reflexivity| lia].
Qed.

Lemma cj_str_range : forall m s B, cj_str m s B -> 0 <= s < 2^64.
Proof.
  intros m s B [[-> _]|(n & str & tail & NZ & _ & BY & _ & LEN)]; [lia|].
  pose proof (bytes_at_bound _ _ _ _ BY) as HB. rewrite length_app in HB. cbn [length] in HB. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive cj_chain (T : Z -> Prop) (m : word -> option byte) : nat -> Z -> list cblock -> Prop :=
| cj_chain_nil : forall d, cj_chain T m d 0 []
| cj_chain_cons : forall d p nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn,
    p <> 0 ->
    rw_cells usegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    0 <= ty < 256 -> T ty ->
    cj_str m vs Bv ->
    cj_str m ky Bk ->
    cj_chain T m d ch Bc ->
    cj_chain T m (S d) nx Bn ->
    cj_chain T m (S d) p ((p, 64) :: Bv ++ Bk ++ Bc ++ Bn).

(* [comment removed for export] *)
Inductive cj_lseg (T : Z -> Prop) (m : word -> option byte) (d : nat) : Z -> Z -> list cblock -> Prop :=
| cj_lseg_nil : forall p, cj_lseg T m d p p []
| cj_lseg_cons : forall p q nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn,
    p <> 0 ->
    rw_cells usegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
    0 <= ty < 256 -> T ty ->
    cj_str m vs Bv ->
    cj_str m ky Bk ->
    cj_chain T m d ch Bc ->
    cj_lseg T m d nx q Bn ->
    cj_lseg T m d p q ((p, 64) :: Bv ++ Bk ++ Bc ++ Bn).

(* [comment removed for export] *)
Lemma cj_chain_zero_budget : forall T m p B, cj_chain T m 0 p B -> p = 0 /\ B = [].
Proof. intros T m p B H. inversion H; subst; auto. Qed.

Lemma cj_chain_null_inv : forall T m d B, cj_chain T m d 0 B -> B = [].
Proof. intros T m d B H. inversion H; subst; [reflexivity|]. exfalso. auto. Qed.

Lemma cj_chain_cons_inv : forall T m d p B, cj_chain T m d p B -> p <> 0 ->
  exists d' nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn,
    d = S d'
    /\ rw_cells usegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky)
    /\ 0 <= ty < 256 /\ T ty
    /\ cj_str m vs Bv /\ cj_str m ky Bk
    /\ cj_chain T m d' ch Bc
    /\ cj_chain T m (S d') nx Bn
    /\ B = (p, 64) :: Bv ++ Bk ++ Bc ++ Bn.
Proof.
  intros T m d p B H NZ. inversion H; subst; [exfalso; apply NZ; reflexivity|].
  do 15 eexists. repeat (split; [first [reflexivity | eassumption] |]). reflexivity.
Qed.

Lemma cj_chain_nil_blocks : forall T m d p, cj_chain T m d p [] -> p = 0.
Proof. intros T m d p H. inversion H; subst; reflexivity. Qed.

(* [comment removed for export] *)
Lemma cj_chain_ptr_range : forall T m d p B, cj_chain T m d p B -> 0 <= p /\ (p <> 0 -> p + 64 <= 2^64) /\ p < 2^64.
Proof.
  intros T m d p B H. inversion H; subst; [lia|].
  match goal with HN : rw_cells _ _ _ (node_cells _ _ _ _ _ _ _ _ _ _) |- _ => pose proof (node_bound _ _ _ _ _ _ _ _ _ _ _ _ HN) end. lia.
Qed.

Lemma cj_chain_head_block : forall T m d p B, cj_chain T m d p B -> p <> 0 -> In (p, 64) B.
Proof. intros T m d p B H NZ. inversion H; subst; [exfalso; auto| left; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma cj_chain_mono : forall (T T' : Z -> Prop) m d d' p B,
  cj_chain T m d p B -> (forall ty, T ty -> T' ty) -> (d <= d')%nat -> cj_chain T' m d' p B.
Proof.
  intros T T' m d d' p B H HT. revert d'. induction H as [d0 | d0 p0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn NZ ND TY HT0 SV SK CHc IHc CHn IHn]; intros d' Hd.
  - apply cj_chain_nil.
  - destruct d' as [|d'']; [lia|]. eapply cj_chain_cons; eauto; first [apply IHc; lia | apply IHn; lia].
Qed.

Lemma cj_chain_mono_d : forall T m d d' p B, cj_chain T m d p B -> (d <= d')%nat -> cj_chain T m d' p B.
Proof. intros. eapply cj_chain_mono; eauto. Qed.

Lemma cj_chain_mono_T : forall (T T' : Z -> Prop) m d p B,
  cj_chain T m d p B -> (forall ty, T ty -> T' ty) -> cj_chain T' m d p B.
Proof. intros. eapply cj_chain_mono; eauto. Qed.

Lemma cj_chain_any : forall T m d p B, cj_chain T m d p B -> cj_chain CJ_ANY m d p B.
Proof. intros. eapply cj_chain_mono_T; eauto. intros; exact I. Qed.

Lemma cj_lseg_mono : forall (T T' : Z -> Prop) m d d' p q B,
  cj_lseg T m d p q B -> (forall ty, T ty -> T' ty) -> (d <= d')%nat -> cj_lseg T' m d' p q B.
Proof.
  intros T T' m d d' p q B H HT Hd. induction H as [p0 | p0 q0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn NZ ND TY HT0 SV SK CHc SEG IHs].
  - apply cj_lseg_nil.
  - eapply cj_lseg_cons; eauto; eapply cj_chain_mono; eauto.
Qed.

(* [comment removed for export] *)
Lemma cj_chain_magree : forall T m d p B, cj_chain T m d p B ->
  forall P m', magree P m m' -> (forall a, in_cblock B a -> P a) -> cj_chain T m' d p B.
Proof.
  intros T m d p B H. induction H as [d0 | d0 p0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn NZ ND TY HT0 SV SK CHc IHc CHn IHn]; intros P m' HP HB.
  - apply cj_chain_nil.
  - eapply cj_chain_cons; eauto.
    + eapply rw_cells_magree; [exact HP| eassumption|]. rewrite node_cells_size. intros a Ha. apply HB.
      rewrite in_cblock_cons. left. lia.
    + eapply cj_str_magree; [exact HP| eassumption|]. intros a Ha. apply HB.
      rewrite in_cblock_cons, !in_cblock_app. tauto.
    + eapply cj_str_magree; [exact HP| eassumption|]. intros a Ha. apply HB.
      rewrite in_cblock_cons, !in_cblock_app. tauto.
    + eapply IHc; [exact HP|]. intros a Ha. apply HB. rewrite in_cblock_cons, !in_cblock_app. tauto.
    + eapply IHn; [exact HP|]. intros a Ha. apply HB. rewrite in_cblock_cons, !in_cblock_app. tauto.
Qed.

Lemma cj_lseg_magree : forall T m d p q B, cj_lseg T m d p q B ->
  forall P m', magree P m m' -> (forall a, in_cblock B a -> P a) -> cj_lseg T m' d p q B.
Proof.
  intros T m d p q B H. induction H as [p0 | p0 q0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn NZ ND TY HT0 SV SK CHc SEG IHs]; intros P m' HP HB.
  - apply cj_lseg_nil.
  - eapply cj_lseg_cons; eauto.
    + eapply rw_cells_magree; [exact HP| eassumption|]. rewrite node_cells_size. intros a Ha. apply HB.
      rewrite in_cblock_cons. left. lia.
    + eapply cj_str_magree; [exact HP| eassumption|]. intros a Ha. apply HB.
      rewrite in_cblock_cons, !in_cblock_app. tauto.
    + eapply cj_str_magree; [exact HP| eassumption|]. intros a Ha. apply HB.
      rewrite in_cblock_cons, !in_cblock_app. tauto.
    + eapply cj_chain_magree; [eassumption| exact HP|]. intros a Ha. apply HB. rewrite in_cblock_cons, !in_cblock_app. tauto.
    + eapply IHs; [exact HP|]. intros a Ha. apply HB. rewrite in_cblock_cons, !in_cblock_app. tauto.
Qed.

(* [comment removed for export] *)
Lemma cj_chain_frame : forall T m m' d p B W,
  cj_chain T m d p B -> munch W m m' -> wmono usegs m m' ->
  (forall A n, In (A, n) B -> disjoint_from W A n) ->
  cj_chain T m' d p B.
Proof.
  intros T m m' d p B W H MU WM HD. eapply cj_chain_magree; [exact H| |intros a Ha; exact Ha].
  eapply magree_blocks_of_munch; eauto.
Qed.

Lemma cj_chain_pres : forall T m m' d p B LB SP,
  cj_chain T m d p B -> cj_pres LB SP m m' -> (forall b, In b B -> In b LB) ->
  cj_chain T m' d p B.
Proof.
  intros T m m' d p B LB SP H HP HB. eapply cj_chain_magree; [exact H| |intros a Ha; exact Ha].
  eapply magree_blocks_of_cj_pres; eauto.
Qed.

Lemma cj_lseg_frame : forall T m m' d p q B W,
  cj_lseg T m d p q B -> munch W m m' -> wmono usegs m m' ->
  (forall A n, In (A, n) B -> disjoint_from W A n) ->
  cj_lseg T m' d p q B.
Proof.
  intros T m m' d p q B W H MU WM HD. eapply cj_lseg_magree; [exact H| |intros a Ha; exact Ha].
  eapply magree_blocks_of_munch; eauto.
Qed.

Lemma cj_lseg_pres : forall T m m' d p q B LB SP,
  cj_lseg T m d p q B -> cj_pres LB SP m m' -> (forall b, In b B -> In b LB) ->
  cj_lseg T m' d p q B.
Proof.
  intros T m m' d p q B LB SP H HP HB. eapply cj_lseg_magree; [exact H| |intros a Ha; exact Ha].
  eapply magree_blocks_of_cj_pres; eauto.
Qed.

Lemma cj_str_frame : forall m m' s B W,
  cj_str m s B -> munch W m m' -> wmono usegs m m' ->
  (forall A n, In (A, n) B -> disjoint_from W A n) -> cj_str m' s B.
Proof.
  intros m m' s B W H MU WM HD. eapply cj_str_magree; [| exact H| intros a Ha; exact Ha].
  eapply magree_blocks_of_munch; eauto.
Qed.

Lemma cj_str_pres : forall m m' s B LB SP,
  cj_str m s B -> cj_pres LB SP m m' -> (forall b, In b B -> In b LB) -> cj_str m' s B.
Proof.
  intros m m' s B LB SP H HP HB. eapply cj_str_magree; [| exact H| intros a Ha; exact Ha].
  eapply magree_blocks_of_cj_pres; eauto.
Qed.

(* [comment removed for export] *)
Lemma cj_lseg_snoc : forall T m d p q B nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc,
  cj_lseg T m d p q B ->
  q <> 0 ->
  rw_cells usegs m q (node_cells nx pv ch ty p1 vs vi p2 vd ky) ->
  0 <= ty < 256 -> T ty ->
  cj_str m vs Bv -> cj_str m ky Bk -> cj_chain T m d ch Bc ->
  cj_lseg T m d p nx (B ++ (q, 64) :: Bv ++ Bk ++ Bc).
Proof.
  intros T m d p q B nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc H NZ ND TY HT SV SK CH.
  induction H as [p0 | p0 q0 nx0 pv0 ch0 ty0 p10 vs0 vi0 p20 vd0 ky0 Bv0 Bk0 Bc0 Bn0 NZ0 ND0 TY0 HT0 SV0 SK0 CHc0 SEG IHs].
  - cbn [app]. replace (Bv ++ Bk ++ Bc) with (Bv ++ Bk ++ Bc ++ []) by (rewrite app_nil_r; reflexivity).
    eapply cj_lseg_cons; eauto using cj_lseg_nil.
  - cbn [app]. specialize (IHs NZ ND). rewrite <- !app_assoc. rewrite <- ?app_assoc in IHs.
    eapply cj_lseg_cons; eauto.
Qed.

(* [comment removed for export] *)
Lemma cj_lseg_chain : forall T m d p q B1 B2,
  cj_lseg T m d p q B1 -> cj_chain T m (S d) q B2 -> cj_chain T m (S d) p (B1 ++ B2).
Proof.
  intros T m d p q B1 B2 H CH. induction H as [p0 | p0 q0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn NZ ND TY HT0 SV SK CHc SEG IHs]; [exact CH|].
  specialize (IHs CH). cbn [app]. rewrite <- ?app_assoc. rewrite <- ?app_assoc in IHs. eapply cj_chain_cons; eauto.
Qed.

(* [comment removed for export] *)
Lemma cj_lseg_chain0 : forall T m d p B, cj_lseg T m d p 0 B -> cj_chain T m (S d) p B.
Proof. intros. rewrite <- (app_nil_r B). eapply cj_lseg_chain; eauto. apply cj_chain_nil. Qed.

(* [comment removed for export] *)
Lemma cj_chain_one : forall T m d p pv ch ty p1 vs vi p2 vd ky Bv Bk Bc,
  p <> 0 ->
  rw_cells usegs m p (node_cells 0 pv ch ty p1 vs vi p2 vd ky) ->
  0 <= ty < 256 -> T ty ->
  cj_str m vs Bv -> cj_str m ky Bk -> cj_chain T m d ch Bc ->
  cj_chain T m (S d) p ((p, 64) :: Bv ++ Bk ++ Bc).
Proof.
  intros. replace (Bv ++ Bk ++ Bc) with (Bv ++ Bk ++ Bc ++ []) by (rewrite app_nil_r; reflexivity).
  eapply cj_chain_cons; eauto. apply cj_chain_nil.
Qed.

(* [comment removed for export] *)
Lemma cj_chain_blocks_pos : forall T m d p B, cj_chain T m d p B -> forall A n, In (A, n) B -> A <> 0 /\ 1 <= n.
Proof.
  intros T m d p B H. induction H as [d0 | d0 p0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn NZ ND TY HT0 SV SK CHc IHc CHn IHn]; intros A n Hin; [destruct Hin|].
  destruct Hin as [E|Hin]; [inversion E; subst; split; [assumption| lia]|].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  { destruct (cj_str_blocks _ _ _ SV) as [->|(n' & -> & NZ' & Hn)]; [destruct Hin|]. destruct Hin as [E|[]]. inversion E; subst. split; [exact NZ'| lia]. }
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  { destruct (cj_str_blocks _ _ _ SK) as [->|(n' & -> & NZ' & Hn)]; [destruct Hin|]. destruct Hin as [E|[]]. inversion E; subst. split; [exact NZ'| lia]. }
  apply in_app_or in Hin. destruct Hin as [Hin|Hin]; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cb_remove_notin : forall A L, ~ In A (map fst L) -> cb_remove A L = L.
Proof.
  induction L as [|[B n] L IH]; intros H; [reflexivity|]. cbn. cbn in H.
  destruct (Z.eqb_spec B A); [exfalso; apply H; left; assumption|]. rewrite IH; [reflexivity|]. tauto.
Qed.

Lemma cb_remove_app : forall A L1 L2, ~ In A (map fst L1) -> cb_remove A (L1 ++ L2) = L1 ++ cb_remove A L2.
Proof.
  induction L1 as [|[B n] L1 IH]; intros L2 H; [reflexivity|]. cbn. cbn in H.
  destruct (Z.eqb_spec B A); [exfalso; apply H; left; assumption|]. rewrite IH; [reflexivity| tauto].
Qed.

Lemma NoDup_map_fst_perm : forall (L L' : list cblock), Permutation L L' -> NoDup (map fst L) -> NoDup (map fst L').
Proof.
  intros L L' HP HN. rewrite NoDup_ListNoDup in *. eapply Permutation_NoDup; [apply Permutation_map; exact HP| exact HN].
Qed.

(* [comment removed for export] *)
Lemma perm_cb_remove : forall A n (R LB : list cblock),
  Permutation ((A, n) :: R) LB -> NoDup (map fst LB) -> Permutation R (cb_remove A LB).
Proof.
  intros A n R LB HP ND.
  assert (HIn : In (A, n) LB) by (eapply Permutation_in; [exact HP| left; reflexivity]).
  apply in_split in HIn. destruct HIn as (L1 & L2 & ->).
  assert (ND' : NoDup (map fst ((A, n) :: L1 ++ L2))).
  { eapply NoDup_map_fst_perm; [| exact ND]. apply Permutation_sym, Permutation_middle. }
  rewrite NoDup_ListNoDup in ND'. cbn in ND'. inversion ND'; subst. rewrite map_app in H1.
  rewrite cb_remove_app by (intros Hc; apply H1; apply in_or_app; left; exact Hc).
  cbn. rewrite Z.eqb_refl. eapply Permutation_cons_inv. eapply Permutation_trans; [exact HP|].
  apply Permutation_sym, Permutation_middle.
Qed.

Lemma perm_in_head : forall (b : cblock) R LB, Permutation (b :: R) LB -> In b LB.
Proof. intros b R LB HP. eapply Permutation_in; [exact HP| left; reflexivity]. Qed.

Lemma perm_incl : forall (B R LB : list cblock) b, Permutation (B ++ R) LB -> In b B -> In b LB.
Proof. intros B R LB b HP Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. left. exact Hb. Qed.

Section HeapFacts.
  Variable HI : cj_heap_iface.

  (* [comment removed for export] *)
  Lemma lheap_perm_apart : forall SPB LB m mo A n R,
    LHEAP HI SPB LB m mo -> Permutation ((A, n) :: R) LB ->
    forall A' n', In (A', n') R -> A' <> A /\ (A' + n' <= A \/ A + n <= A').
  Proof.
    intros SPB LB m mo A n R HL HP A' n' Hin.
    pose proof (lh_nodup HI _ _ _ _ HL) as ND.
    assert (ND' : NoDup (map fst ((A, n) :: R))) by (eapply NoDup_map_fst_perm; [apply Permutation_sym; exact HP| exact ND]).
    rewrite NoDup_ListNoDup in ND'. cbn in ND'. inversion ND'; subst.
    assert (NE : A' <> A). { intros ->. apply H1. apply (in_map fst) in Hin. exact Hin. }
    split; [exact NE|].
    pose proof (lh_blocks_disjoint HI _ _ _ _ _ _ _ _ HL
                  ltac:(eapply Permutation_in; [exact HP| right; exact Hin])
                  ltac:(eapply Permutation_in; [exact HP| left; reflexivity]) NE). lia.
  Qed.

  Lemma lheap_perm_range : forall SPB LB m mo B R,
    LHEAP HI SPB LB m mo -> Permutation (B ++ R) LB -> forall A n, In (A, n) B -> cblock_range A n.
  Proof. intros SPB LB m mo B R HL HP A n Hin. eapply (lh_block_range HI); [exact HL|]. eapply perm_incl; eauto. Qed.

  Lemma lheap_in_range : forall SPB LB m mo A n,
    LHEAP HI SPB LB m mo -> In (A, n) LB -> cblock_range A n.
  Proof. intros. eapply (lh_block_range HI); eauto. Qed.

  (* [comment removed for export] *)
  Lemma lheap_block_disjoint_from : forall SPB LB m mo A n R lo hi,
    LHEAP HI SPB LB m mo -> Permutation ((A, n) :: R) LB -> A <= lo -> hi <= A + n ->
    forall A' n', In (A', n') R -> disjoint_from [(lo, hi)] A' n'.
  Proof.
    intros SPB LB m mo A n R lo hi HL HP Hlo Hhi A' n' Hin. cbn. split; [|exact I].
    destruct (lheap_perm_apart _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lheap_stack_disjoint_from : forall SPB LB m mo lo hi,
    LHEAP HI SPB LB m mo -> alloc_ceiling <= lo ->
    forall A' n', In (A', n') LB -> disjoint_from [(lo, hi)] A' n'.
  Proof.
    intros SPB LB m mo lo hi HL Hlo A' n' Hin. cbn. split; [|exact I].
    destruct (lh_block_range HI _ _ _ _ _ _ HL Hin) as (_ & _ & _ & R & _). lia.
  Qed.
End HeapFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_ty_256 : forall ty, 0 <= ty < 256 -> Z.land ty 256 = 0.
Proof.
  intros ty Hty. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  change 256 with (2^8). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 8 n); [subst; cbn [andb]| apply andb_false_r].
  rewrite andb_true_r. apply Z.bits_above_log2; [lia|]. 
  destruct (Z.eq_dec ty 0) as [->|]; [cbn; lia|]. apply (Z.lt_le_trans _ 8); [apply Z.log2_lt_pow2; lia| lia].
Qed.

Lemma land_ty_512 : forall ty, 0 <= ty < 256 -> Z.land ty 512 = 0.
Proof.
  intros ty Hty. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  change 512 with (2^9). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 9 n); [subst; cbn [andb]| apply andb_false_r].
  rewrite andb_true_r. apply Z.bits_above_log2; [lia|].
  destruct (Z.eq_dec ty 0) as [->|]; [cbn; lia|]. apply (Z.lt_le_trans _ 8); [apply Z.log2_lt_pow2; lia| lia].
Qed.

Lemma sx32_lit : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap.
  change (bv_swrap 32 (e mod 2^64)) with (((e mod 2^64) + 2^31) mod 2^32 - 2^31).
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Lemma zx32_lit : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite (unsigned_lit z) by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma scps_step_evt : forall (P : machine_state -> Model -> Prop) ms mo,
  MOK mo -> evt usegs (fun ms' => SCPS usegs P ms' mo) ms -> SCPS usegs P ms mo.
Proof. intros P ms mo HM He. eapply scps_evt_then; [exact HM| exact He|]. intros ms' H. exact H. Qed.

(* [comment removed for export] *)
Lemma CJST_pres : forall LB SP m m', cj_pres LB SP m m' -> CJST m -> CJST m'.
Proof.
  intros LB SP m m' HP (HK & (e1 & e2 & GE) & LC). split; [|split; [exists e1, e2|]].
  all: eapply cj_pres_rw_cells; [exact HP| eassumption|].
  all: right; left; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
       unfold PHOOKS, PGERROR, PLCONV, PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP; lia.
Qed.

(* [comment removed for export] *)
Lemma disjoint_from_data : forall W A n,
  (forall lo hi, In (lo, hi) W -> hi <= PDATA_LO \/ PIMG_HI <= lo) ->
  PDATA_LO <= A -> A + n <= PIMG_HI -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros A n HW HA Hn; [exact I|]. cbn. split.
  - destruct (HW lo hi ltac:(left; reflexivity)); lia.
  - apply IH; [| exact HA| exact Hn]. intros lo' hi' Hin. apply HW. right. exact Hin.
Qed.

Lemma CJST_frame : forall W m m',
  CJST m -> munch W m m' -> wmono usegs m m' ->
  (forall lo hi, In (lo, hi) W -> hi <= PDATA_LO \/ PIMG_HI <= lo) -> CJST m'.
Proof.
  intros W m m' (HK & (e1 & e2 & GE) & LC) MU WM HW.
  split; [|split; [exists e1, e2|]].
  all: eapply rw_cells_transport; [eassumption| exact MU| exact WM|].
  all: apply disjoint_from_data; [exact HW| |]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
       unfold PHOOKS, PGERROR, PLCONV, PDATA_LO, PIMG_HI; lia.
Qed.



End CeilWrap.
(* [comment removed for export] *)
Ltac unfold_pconsts :=
  unfold PMALLOC, PFREE, PREALLOC, PTP, PERRNO, PHOOKS, PGERROR, PLCONV, PDOTSTR, PEMPTY,
         PIMG_LO, PIMG_HI, PDATA_LO, PLIBC, PCTX_END, PSSP, PGOT_SSP, RMALLOC_STACK in *.
