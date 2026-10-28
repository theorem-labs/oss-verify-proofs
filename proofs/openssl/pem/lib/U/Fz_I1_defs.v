(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Export LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Seg.
Variable DV : Z -> Prop.            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_cells (m : mem) (A : Z) : Prop :=
  exists d (h : word), rw_cells usegs m A [C8 (wz d)] /\ DV d /\ rw_cells usegs m (A + 16) [C8 h].

(* [comment removed for export] *)
Fixpoint lseg (m : mem) (LBall : list block) (L : @clist bptr) (c : Z) (ns : list (bptr * Z)) (c' : Z) : Prop :=
  match ns with
  | [] => c = c'
  | (p, A) :: ns' => rw_cells usegs m c [C8 (wz A)] /\ cown LBall L p A 24 24 /\ (0 < A /\ A + 24 <= alloc_ceiling) /\ node_cells m A /\ lseg m LBall L (A + 8) ns' c'
  end.

Definition chain (m : mem) (LBall : list block) (L : @clist bptr) (c : Z) (ns : list (bptr * Z)) : Prop :=
  exists c', lseg m LBall L c ns c' /\ rw_cells usegs m c' [C8 (wz 0)].

Lemma lseg_app : forall m LBall L ns1 ns2 c c1 c2, lseg m LBall L c ns1 c1 -> lseg m LBall L c1 ns2 c2 -> lseg m LBall L c (ns1 ++ ns2) c2.
Proof.
  intros m LBall L ns1. induction ns1 as [|[p A] ns1 IH]; intros ns2 c c1 c2 H1 H2; cbn [lseg app] in *.
  - subst c1. exact H2.
  - destruct H1 as (C & O & RG & N & R). split; [exact C|]. split; [exact O|]. split; [exact RG|]. split; [exact N|]. eapply IH; eassumption.
Qed.

Lemma lseg_split : forall m LBall L ns1 ns2 c c2, lseg m LBall L c (ns1 ++ ns2) c2 -> exists c1, lseg m LBall L c ns1 c1 /\ lseg m LBall L c1 ns2 c2.
Proof.
  intros m LBall L ns1. induction ns1 as [|[p A] ns1 IH]; intros ns2 c c2 H; cbn [lseg app] in *.
  - exists c. auto.
  - destruct H as (C & O & RG & N & R). destruct (IH _ _ _ R) as (c1 & R1 & R2). exists c1. split; [| exact R2]. split; [exact C|]. split; [exact O|]. split; [exact RG|]. split; [exact N| exact R1].
Qed.

(* [comment removed for export] *)
Fixpoint lseg_fp (c : Z) (ns : list (bptr * Z)) (a : Z) : Prop :=
  match ns with
  | [] => False
  | (p, A) :: ns' => (c <= a < c + 8) \/ (A <= a < A + 8) \/ (A + 16 <= a < A + 24) \/ lseg_fp (A + 8) ns' a
  end.

Lemma lseg_agree : forall m m' LBall L LBall' L' ns c c',
  lseg m LBall L c ns c' -> agree_on (lseg_fp c ns) m m' ->
  (forall p A, In (p, A) ns -> cown LBall L p A 24 24 -> cown LBall' L' p A 24 24) ->
  lseg m' LBall' L' c ns c'.
Proof.
  intros m m' LBall L LBall' L' ns. induction ns as [|[p A] ns IH]; intros c c' H AG HO; cbn [lseg] in *; [exact H|].
  destruct H as (C & O & RG & (d & h & N1 & ND & N2) & R).
  split. { eapply rw_cells_agree; [exact AG| exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. cbn [lseg_fp]. left. lia. }
  split. { apply HO; [left; reflexivity| exact O]. }
  split; [exact RG|].
  split. { exists d, h. split; [| split; [exact ND|]].
    - eapply rw_cells_agree; [exact AG| exact N1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. cbn [lseg_fp]. right; left. lia.
    - eapply rw_cells_agree; [exact AG| exact N2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. cbn [lseg_fp]. right; right; left. lia. }
  apply IH; [exact R| | intros q B Hq; apply HO; right; exact Hq].
  eapply agree_on_mono; [exact AG|]. intros a Ha. cbn [lseg_fp]. do 3 right. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma lseg_fp_where : forall ns c a, lseg_fp c ns a -> (c <= a < c + 8) \/ exists p A, In (p, A) ns /\ A <= a < A + 24.
Proof.
  induction ns as [|[p A] ns IH]; intros c a H; cbn [lseg_fp] in H; [destruct H|].
  destruct H as [H|[H|[H|H]]]; [left; exact H| right; exists p, A; split; [left; reflexivity| lia]| right; exists p, A; split; [left; reflexivity| lia]|].
  destruct (IH _ _ H) as [H1|(q & B & Hq & H1)]; [right; exists p, A; split; [left; reflexivity| lia]| right; exists q, B; split; [right; exact Hq| exact H1]].
Qed.

Lemma chain_agree : forall m m' LBall L LBall' L' ns c,
  chain m LBall L c ns -> agree_on (fun a => (c <= a < c + 8) \/ exists p A, In (p, A) ns /\ A <= a < A + 24) m m' ->
  (forall p A, In (p, A) ns -> cown LBall L p A 24 24 -> cown LBall' L' p A 24 24) ->
  chain m' LBall' L' c ns.
Proof.
  intros m m' LBall L LBall' L' ns c (c' & S & Z0) AG HO. exists c'. split.
  - eapply lseg_agree; [exact S| | exact HO]. eapply agree_on_mono; [exact AG|]. intros a Ha. exact (lseg_fp_where _ _ _ Ha).
  - eapply rw_cells_agree; [exact AG| exact Z0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha.
    (* [comment removed for export] *)
    clear - S Ha. revert c S. induction ns as [|[p A] ns IH]; intros c S; cbn [lseg] in S.
    + subst c'. left. exact Ha.
    + destruct S as (_ & _ & _ & _ & R). destruct (IH _ R) as [H|(q & B & Hq & H)].
      * right. exists p, A. split; [left; reflexivity| lia].
      * right. exists q, B. split; [right; exact Hq| exact H].
Qed.
(* [comment removed for export] *)
Lemma lseg_ranges : forall m LBall L ns c c', lseg m LBall L c ns c' -> forall p A, In (p, A) ns -> 0 < A /\ A + 24 <= alloc_ceiling.
Proof.
  intros m LBall L ns. induction ns as [|[q B] ns IH]; intros c c' H p A Hin; [destruct Hin|]. cbn [lseg] in H. destruct H as (_ & _ & RG & _ & R).
  destruct Hin as [E|Hin]; [inversion E; subst; exact RG| exact (IH _ _ R p A Hin)].
Qed.

Lemma lseg_end_range : forall m LBall L ns c c', lseg m LBall L c ns c' -> 0 <= c /\ c + 8 <= alloc_ceiling -> 0 <= c' /\ c' + 8 <= alloc_ceiling.
Proof.
  intros m LBall L ns. induction ns as [|[q B] ns IH]; intros c c' H HC; cbn [lseg] in H; [subst; exact HC|].
  destruct H as (_ & _ & RG & _ & R). apply (IH _ _ R). lia.
Qed.

Lemma lseg_munch : forall W m m' LBall L ns c c', lseg m LBall L c ns c' -> munch W m m' -> wmono usegs m m' ->
  (forall a, 0 <= a < alloc_ceiling -> outside W a) -> 0 <= c /\ c + 8 <= alloc_ceiling -> lseg m' LBall L c ns c'.
Proof.
  intros W m m' LBall L ns c c' H MU WM HW HC. eapply lseg_agree; [exact H| | intros p A _ X; exact X].
  eapply agree_on_mono; [exact (agree_on_of_munch W m m' MU WM)|]. intros a Ha. apply HW.
  destruct (lseg_fp_where _ _ _ Ha) as [X|(p & A & Hp & X)]; [lia|]. pose proof (lseg_ranges _ _ _ _ _ _ H p A Hp). lia.
Qed.

Lemma chain_munch : forall W m m' LBall L ns c, chain m LBall L c ns -> munch W m m' -> wmono usegs m m' ->
  (forall a, 0 <= a < alloc_ceiling -> outside W a) -> 0 <= c /\ c + 8 <= alloc_ceiling -> chain m' LBall L c ns.
Proof.
  intros W m m' LBall L ns c (c' & S & Z0) MU WM HW HC. exists c'. split; [eapply lseg_munch; eassumption|].
  pose proof (lseg_end_range _ _ _ _ _ _ S HC) as HC'.
  eapply rw_cells_agree; [exact (agree_on_of_munch W m m' MU WM)| exact Z0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HW. lia.
Qed.
(* [comment removed for export] *)
Fixpoint chainv (m : mem) (LBall : list block) (L : @clist bptr) (v : Z) (ns : list (bptr * Z)) : Prop :=
  match ns with
  | [] => v = 0
  | (p, A) :: ns' => v = A /\ cown LBall L p A 24 24 /\ (0 < A /\ A + 24 <= alloc_ceiling) /\ node_cells m A
                     /\ exists nx, rw_cells usegs m (A + 8) [C8 (wz nx)] /\ chainv m LBall L nx ns'
  end.

Lemma chain_chainv : forall m LBall L ns c, chain m LBall L c ns -> exists v, rw_cells usegs m c [C8 (wz v)] /\ chainv m LBall L v ns.
Proof.
  intros m LBall L ns. induction ns as [|[p A] ns IH]; intros c (c' & S & Z0); cbn [lseg] in S.
  - subst c'. exists 0. split; [exact Z0| reflexivity].
  - destruct S as (C & O & RG & N & R). exists A. split; [exact C|]. cbn [chainv]. split; [reflexivity|]. split; [exact O|]. split; [exact RG|]. split; [exact N|].
    destruct (IH (A + 8) (ex_intro _ c' (conj R Z0))) as (nx & CX & CV). exists nx. auto.
Qed.

Lemma chainv_chain : forall m LBall L ns c v, rw_cells usegs m c [C8 (wz v)] -> chainv m LBall L v ns -> chain m LBall L c ns.
Proof.
  intros m LBall L ns. induction ns as [|[p A] ns IH]; intros c v C CV; cbn [chainv] in CV.
  - subst v. exists c. split; [reflexivity| exact C].
  - destruct CV as (-> & O & RG & N & nx & CX & CV). destruct (IH (A + 8) nx CX CV) as (c' & S & Z0).
    exists c'. split; [| exact Z0]. cbn [lseg]. auto.
Qed.

Lemma chainv_agree : forall m m' LBall L ns v,
  chainv m LBall L v ns -> agree_on (fun a => exists p A, In (p, A) ns /\ A <= a < A + 24) m m' -> chainv m' LBall L v ns.
Proof.
  intros m m' LBall L ns. induction ns as [|[p A] ns IH]; intros v CV AG; cbn [chainv] in *; [exact CV|].
  destruct CV as (-> & O & RG & (d & h & N1 & ND & N2) & nx & CX & CV).
  assert (IN : In (p, A) ((p, A) :: ns)) by (left; reflexivity).
  split; [reflexivity|]. split; [exact O|]. split; [exact RG|].
  split. { exists d, h. split; [| split; [exact ND|]].
    - eapply rw_cells_agree; [exact AG| exact N1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. exists p, A. split; [exact IN| lia].
    - eapply rw_cells_agree; [exact AG| exact N2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. exists p, A. split; [exact IN| lia]. }
  exists nx. split.
  - eapply rw_cells_agree; [exact AG| exact CX|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. exists p, A. split; [exact IN| lia].
  - apply IH; [exact CV|]. eapply agree_on_mono; [exact AG|]. intros a (q & Bq & Hq & Ha). exists q, Bq. split; [right; exact Hq| exact Ha].
Qed.

Lemma chainv_ranges : forall m LBall L ns v, chainv m LBall L v ns -> forall p A, In (p, A) ns -> 0 < A /\ A + 24 <= alloc_ceiling.
Proof.
  intros m LBall L ns. induction ns as [|[q B] ns IH]; intros v H p A Hin; [destruct Hin|]. cbn [chainv] in H. destruct H as (_ & _ & RG & _ & nx & _ & R).
  destruct Hin as [E|Hin]; [inversion E; subst; exact RG| exact (IH _ R p A Hin)].
Qed.
End Seg.

(* [comment removed for export] *)
(* [comment removed for export] *)



(* [comment removed for export] *)


(* [comment removed for export] *)
Definition lh_cells (f : lh_fns) (B : Z) (g : lh_geo) (x40 x48 err pad : word) : list cell :=
  [C8 (wz B); C8 (wz (lf_comp f)); C8 (wz (lf_hash f)); C8 (wz (lf_hashw f)); C8 (wz (lf_compw f)); C8 x40; C8 x48;
   C4 (wz (g_nn g)); C4 (wz (g_na g)); C4 (wz (g_p g)); C4 (wz (g_pmax g)); C8 (wz 512); C8 (wz 256); C8 (wz (g_items g)); C4 err; C4 pad].

(* [comment removed for export] *)

Definition lh_rep (DV : Z -> Prop) (m : mem) (LBall : list block) (L : @clist bptr) (f : lh_fns) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo)
    (bks : list (list (bptr * Z))) : Prop :=
  lh_geo_ok g
  /\ cown LBall L pl lh 104 104 /\ (0 < lh /\ lh + 104 <= alloc_ceiling) /\ (exists x40 x48 err pad, rw_cells usegs m lh (lh_cells f B g x40 x48 err pad))
  /\ cown LBall L pb B (8 * g_na g) nmb /\ (0 < B /\ B + 8 * g_na g <= alloc_ceiling)
  /\ Z.of_nat (length bks) = g_na g
  /\ (forall i, 0 <= i < g_na g -> chain DV m LBall L (B + 8 * i) (nth (Z.to_nat i) bks []))
  /\ (forall i, g_nn g <= i < g_na g -> nth (Z.to_nat i) bks [] = [])
  /\ List.NoDup (pl :: pb :: map fst (concat bks)).

(* [comment removed for export] *)
Definition lh_fp (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (a : Z) : Prop :=
  (lh <= a < lh + 104) \/ (B <= a < B + 8 * g_na g) \/ exists p A, In (p, A) (concat bks) /\ A <= a < A + 24.


Lemma lh_rep_agree : forall DV m m' LBall L LBall' L' f lh pl pb B nmb g bks,
  lh_rep DV m LBall L f lh pl pb B nmb g bks -> agree_on (lh_fp lh B g bks) m m' ->
  (forall q A n nm, lh_T pl pb bks q -> cown LBall L q A n nm -> cown LBall' L' q A n nm) ->
  lh_rep DV m' LBall' L' f lh pl pb B nmb g bks.
Proof.
  intros DV m m' LBall L LBall' L' f lh pl pb B nmb g bks (G & OL & RL & (x40 & x48 & err & pad & SC) & OB & RB & LEN & CH & EMP & ND) AG HO.
  pose proof (lh_geo_bounds g G) as GB.
  split; [exact G|]. split; [apply HO; [left; reflexivity| exact OL]|]. split; [exact RL|].
  split. { exists x40, x48, err, pad. eapply rw_cells_agree; [exact AG| exact SC|]. intros a Ha. left. cbn in Ha. lia. }
  split; [apply HO; [right; left; reflexivity| exact OB]|]. split; [exact RB|]. split; [exact LEN|].
  split; [| split; [exact EMP| exact ND]].
  intros i Hi. eapply chain_agree; [exact (CH i Hi)| |].
  - eapply agree_on_mono; [exact AG|]. intros a [Ha|(p & A & Hp & Ha)].
    + right; left. lia.
    + right; right. exists p, A. split; [| exact Ha]. eapply in_concat_nth; [| exact Hp]. lia.
  - intros p A Hp. apply HO. right; right. apply in_map_iff. exists (p, A). split; [reflexivity|]. eapply in_concat_nth; [| exact Hp]. lia.
Qed.
End WithCeiling0.
