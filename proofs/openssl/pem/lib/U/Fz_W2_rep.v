(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W1_defs Fz_W1_sync Fz_W3_iface.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Definition mbio_fp (LBall : list block) (K : mbk) (a : Z) : Prop :=
  exists b, In b LBall /\ mbio_T K (blk_id b) /\ blk_addr b <= a < blk_addr b + blk_size b.

Lemma cown_fp : forall LBall L K p A n nm a, cown LBall L p A n nm -> mbio_T K p -> A <= a < A + n -> mbio_fp LBall K a.
Proof. intros LBall L K p A n nm a [IN _] T R. exists (p, A, n). split; [exact IN|]. split; [exact T|]. unfold blk_addr, blk_size. cbn [fst snd]. exact R. Qed.

Lemma cells_fp : forall (m m' : mem) LBall L K p A n nm B cs,
  agree_on (mbio_fp LBall K) m m' -> cown LBall L p A n nm -> mbio_T K p -> A <= B -> B + Z.of_nat (cells_size cs) <= A + n ->
  rw_cells usegs m B cs -> rw_cells usegs m' B cs.
Proof.
  intros m m' LBall L K p A n nm B cs AG OWN T H1 H2 C. eapply rw_cells_agree; [exact AG| exact C|].
  intros a Ha. eapply cown_fp; [exact OWN| exact T| lia].
Qed.

Lemma mb_inner_agree : forall (m m' : mem) LBall L K BB BM RP len max off flw blw,
  mb_inner m LBall L K BB BM RP len max off flw blw -> agree_on (mbio_fp LBall K) m m' -> mb_inner m' LBall L K BB BM RP len max off flw blw.
Proof.
  intros m m' LBall L K BB BM RP len max off flw blw (rmaxw & OWNbb & BBC & OWNbm & OWNrp & OFF & LEN & MAX & D) AG.
  exists rmaxw. split; [exact OWNbb|]. split; [eapply (cells_fp m m' _ _ K _ _ _ _ _ _ AG OWNbb); [right; left; reflexivity| lia| cbn; lia| exact BBC]|].
  split; [exact OWNbm|]. split; [exact OWNrp|]. split; [exact OFF|]. split; [exact LEN|]. split; [exact MAX|].
  destruct (k_d K) as [pd|] eqn:KD.
  - destruct D as (Dd & nm & junk & OWNd & MAXP & BMC & RPC & LJ & DC). exists Dd, nm, junk. split; [exact OWNd|]. split; [exact MAXP|].
    split; [eapply (cells_fp m m' _ _ K _ _ _ _ _ _ AG OWNbm); [do 2 right; left; reflexivity| lia| cbn; lia| exact BMC]|].
    split; [eapply (cells_fp m m' _ _ K _ _ _ _ _ _ AG OWNrp); [do 3 right; left; reflexivity| lia| cbn; lia| exact RPC]|].
    split; [exact LJ|]. eapply (cells_fp m m' _ _ K _ _ _ _ _ _ AG OWNd); [do 4 right; exact KD| lia| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia| exact DC].
  - destruct D as (MAX0 & BMC & RPC). split; [exact MAX0|].
    split; [eapply (cells_fp m m' _ _ K _ _ _ _ _ _ AG OWNbm); [do 2 right; left; reflexivity| lia| cbn; lia| exact BMC]|].
    eapply (cells_fp m m' _ _ K _ _ _ _ _ _ AG OWNrp); [do 3 right; left; reflexivity| lia| cbn; lia| exact RPC].
Qed.

Lemma mbio_repx_agree : forall (m m' : mem) LBall L K BI BM blw meth len max off,
  mbio_repx m LBall L K BI BM blw meth len max off -> agree_on (mbio_fp LBall K) m m' -> mbio_repx m' LBall L K BI BM blw meth len max off.
Proof.
  intros m m' LBall L K BI BM blw meth len max off (BB & RP & fl & rrw & padw & nr & nw & OWNB & ND & METH & HEAD & W1C & FLOK & TAIL & INNER) AG.
  exists BB, RP, fl, rrw, padw, nr, nw. split; [exact OWNB|]. split; [exact ND|]. split; [exact METH|].
  split; [eapply (cells_fp m m' _ _ K _ _ _ _ _ _ AG OWNB); [left; reflexivity| lia| cbn; lia| exact HEAD]|].
  split; [eapply (cells_fp m m' _ _ K _ _ _ _ _ _ AG OWNB); [left; reflexivity| lia| cbn; lia| exact W1C]|].
  split; [exact FLOK|]. split; [eapply (cells_fp m m' _ _ K _ _ _ _ _ _ AG OWNB); [left; reflexivity| lia| cbn; lia| exact TAIL]|].
  eapply mb_inner_agree; [exact INNER| exact AG].
Qed.

Lemma mbio_rep_agree : forall (m m' : mem) LBall L K BI meth len max off,
  mbio_rep m LBall L K BI meth len max off -> agree_on (mbio_fp LBall K) m m' -> mbio_rep m' LBall L K BI meth len max off.
Proof. intros m m' LBall L K BI meth len max off [BM MB] AG. exists BM. eapply mbio_repx_agree; [exact MB| exact AG]. Qed.

(* [comment removed for export] *)
Lemma cfr_mbio_fp : forall T W SP LBall K m m', cfr T W SP LBall m m' -> (forall q, mbio_T K q -> ~ T q) -> agree_on (mbio_fp LBall K) m m'.
Proof.
  intros T W SP LBall K m m' CFR NT. eapply agree_on_mono; [exact CFR|]. intros a (b & IN & Tb & R). right; left. exists b. split; [exact IN|]. split; [exact (NT _ Tb)| exact R].
Qed.

(* [comment removed for export] *)
Lemma munch_mbio_fp : forall Wseg s LBall LB L m m' sp tp lo B K,
  cstate s LBall LB L m sp tp lo B -> munch Wseg m m' -> wmono usegs m m' ->
  (forall b, In b LBall -> mbio_T K (blk_id b) -> disjoint_from Wseg (blk_addr b) (blk_size b)) -> agree_on (mbio_fp LBall K) m m'.
Proof.
  intros Wseg s LBall LB L m m' sp tp lo B K CST MU WM HD. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|].
  intros a (b & IN & Tb & R). cbv beta. eapply disjoint_outside; [exact (HD b IN Tb)| exact R].
Qed.

(* [comment removed for export] *)
Lemma mbio_repx_keep : forall (m : mem) LBall LBall' L L' K BI BM blw meth len max off,
  mbio_repx m LBall L K BI BM blw meth len max off ->
  (forall b, In b LBall -> mbio_T K (blk_id b) -> In b LBall') -> (forall p nm, In (p, nm) L -> mbio_T K p -> In (p, nm) L') ->
  mbio_repx m LBall' L' K BI BM blw meth len max off.
Proof.
  intros m LBall LBall' L L' K BI BM blw meth len max off (BB & RP & fl & rrw & padw & nr & nw & OWNB & ND & METH & HEAD & W1C & FLOK & TAIL & INNER) KB KL.
  assert (OWNK : forall p A n nm, cown LBall L p A n nm -> mbio_T K p -> cown LBall' L' p A n nm).
  { intros p A n nm [I1 I2] T. split; [exact (KB _ I1 T)| exact (KL _ _ I2 T)]. }
  exists BB, RP, fl, rrw, padw, nr, nw. split; [apply OWNK; [exact OWNB| left; reflexivity]|]. split; [exact ND|]. split; [exact METH|].
  split; [exact HEAD|]. split; [exact W1C|]. split; [exact FLOK|]. split; [exact TAIL|].
  destruct INNER as (rmaxw & OWNbb & BBC & OWNbm & OWNrp & OFF & LEN & MAX & D). exists rmaxw.
  split; [apply OWNK; [exact OWNbb| right; left; reflexivity]|]. split; [exact BBC|]. split; [apply OWNK; [exact OWNbm| do 2 right; left; reflexivity]|].
  split; [apply OWNK; [exact OWNrp| do 3 right; left; reflexivity]|]. split; [exact OFF|]. split; [exact LEN|]. split; [exact MAX|].
  destruct (k_d K) as [pd|] eqn:KD; [| exact D].
  destruct D as (Dd & nm & junk & OWNd & REST). exists Dd, nm, junk. split; [apply OWNK; [exact OWNd| do 4 right; exact KD]| exact REST].
Qed.

Lemma mbio_rep_keep : forall (m : mem) LBall LBall' L L' K BI meth len max off,
  mbio_rep m LBall L K BI meth len max off ->
  (forall b, In b LBall -> mbio_T K (blk_id b) -> In b LBall') -> (forall p nm, In (p, nm) L -> mbio_T K p -> In (p, nm) L') ->
  mbio_rep m LBall' L' K BI meth len max off.
Proof. intros m LBall LBall' L L' K BI meth len max off [BM MB] KB KL. exists BM. eapply mbio_repx_keep; [exact MB| exact KB| exact KL]. Qed.

Lemma mbio_repx_cfr : forall (m m' : mem) T W SP LBall L K BI BM blw meth len max off,
  mbio_repx m LBall L K BI BM blw meth len max off -> cfr T W SP LBall m m' -> (forall q, mbio_T K q -> ~ T q) -> mbio_repx m' LBall L K BI BM blw meth len max off.
Proof. intros m m' T W SP LBall L K BI BM blw meth len max off MB CFR NT. eapply mbio_repx_agree; [exact MB| eapply cfr_mbio_fp; [exact CFR| exact NT]]. Qed.

Lemma mbio_rep_cfr : forall (m m' : mem) T W SP LBall L K BI meth len max off,
  mbio_rep m LBall L K BI meth len max off -> cfr T W SP LBall m m' -> (forall q, mbio_T K q -> ~ T q) -> mbio_rep m' LBall L K BI meth len max off.
Proof. intros m m' T W SP LBall L K BI meth len max off MB CFR NT. eapply mbio_rep_agree; [exact MB| eapply cfr_mbio_fp; [exact CFR| exact NT]]. Qed.
End WithCeiling0.
