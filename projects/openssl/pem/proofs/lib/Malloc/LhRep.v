(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks MallocRep Malloc_iface ClientOwn.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Export LhPure.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

(* [comment removed for export] *)
Lemma lhg_wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma lhg_rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite lhg_wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma lhg_rw_cells_CB_split_at : forall segs m A n bs k, (k <= n)%nat ->
  rw_cells segs m A [CB n bs] ->
  rw_cells segs m A [CB k (firstn k bs)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k)%nat (skipn k bs)].
Proof.
  intros segs m A n bs k Hk H.
  pose proof (rw_cells_CB_length segs m A n bs H) as L.
  pose proof (rw_cells_split_CB segs m A [] n bs [] [k; (n - k)%nat] H ltac:(cbn; lia)) as H2.
  cbn [mk_CB_cells app] in H2.
  apply (proj1 (lhg_rw_cells_app segs m A [_] _)) in H2. destruct H2 as [Ha Hb].
  cbn [cells_size csize Nat.add] in Hb. rewrite Nat.add_0_r in Hb.
  split; [exact Ha|].
  replace (skipn k bs) with (firstn (n - k) (skipn k bs)); [exact Hb|].
  apply firstn_all2. rewrite skipn_length. lia.
Qed.

Lemma lhg_rw_cells_CB_join : forall segs m A k1 bs1 k2 bs2,
  rw_cells segs m A [CB k1 bs1] -> rw_cells segs m (A + Z.of_nat k1) [CB k2 bs2] ->
  rw_cells segs m A [CB (k1 + k2)%nat (bs1 ++ bs2)].
Proof.
  intros segs m A k1 bs1 k2 bs2 H1 H2.
  pose proof (rw_cells_CB_length segs m A k1 bs1 H1) as L1.
  pose proof (rw_cells_CB_length segs m _ k2 bs2 H2) as L2.
  assert (H : rw_cells segs m A ([CB k1 bs1] ++ [CB k2 bs2])).
  { apply (proj2 (lhg_rw_cells_app segs m A [_] [_])). split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  pose proof (rw_cells_merge segs m A [] ([CB k1 bs1] ++ [CB k2 bs2]) []) as M.
  rewrite app_nil_r in M. cbn [app cells_size cells_bytes csize cbytes] in M.
  rewrite app_nil_r, Nat.add_0_r in M. apply M. exact H.
Qed.

Section LhRep.
Variable segs : list Segment.
Variable CEIL : Z.

Definition own_t : Type := bptr -> Z -> Z -> Z -> Prop.
Definition own_apart (OWN : own_t) : Prop :=
  forall (p1 : bptr) A1 n1 nm1 (p2 : bptr) A2 n2 nm2, OWN p1 A1 n1 nm1 -> OWN p2 A2 n2 nm2 -> p1 <> p2 -> A1 + n1 <= A2 \/ A2 + n2 <= A1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition agree_on (P : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

Lemma agree_on_refl : forall P m, agree_on P m m.
Proof. intros P m a _ _. auto. Qed.
Lemma agree_on_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma agree_on_mono : forall (P P' : Z -> Prop) m m', agree_on P m m' -> (forall a, P' a -> P a) -> agree_on P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.
Lemma agree_on_of_munch : forall W m m', munch W m m' -> wmono segs m m' -> agree_on (fun a => outside W a) m m'.
Proof.
  intros W m m' MU WM a Ha Ho. split; [| intros H; apply WM; exact H].
  apply MU. unfold wa. rewrite unsigned_lit by lia. exact Ho.
Qed.
Lemma bytes_at_agree : forall P m m' A bs,
  agree_on P m m' -> bytes_at segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at segs m' A bs.
Proof.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.
Lemma wr_at_agree : forall P m m' A n,
  agree_on P m m' -> wr_at segs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at segs m' A n.
Proof.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.
Lemma rw_cells_agree : forall P m m' A cs,
  agree_on P m m' -> rw_cells segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells segs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_agree; eauto.
Qed.

Lemma rw_cells_recast : forall m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells segs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma rw_cells_CB0 : forall m A, 0 <= A <= 2^64 -> rw_cells segs m A [CB 0 []].
Proof.
  intros m A HA. split; [split|].
  - cbn. split; reflexivity || exact I.
  - cbn [cells_bytes cbytes app]. apply bytes_at_nil. exact HA.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.
Lemma bytes_at_inj : forall m a bs1 bs2, bytes_at segs m a bs1 -> bytes_at segs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
  intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) LEN. apply List.nth_error_ext. intros i.
  destruct (Nat.ltb_spec0 i (length bs1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i)) by lia. rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section Seg.
Variable DV : Z -> Prop.            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_cells (m : mem) (A : Z) : Prop :=
  exists d (h : word), rw_cells segs m A [C8 (wz d)] /\ DV d /\ rw_cells segs m (A + 16) [C8 h].

(* [comment removed for export] *)
Fixpoint lseg (m : mem) (OWN : own_t) (c : Z) (ns : list (bptr * Z)) (c' : Z) : Prop :=
  match ns with
  | [] => c = c'
  | (p, A) :: ns' => rw_cells segs m c [C8 (wz A)] /\ OWN p A 24 24 /\ (0 < A /\ A + 24 <= CEIL) /\ node_cells m A /\ lseg m OWN (A + 8) ns' c'
  end.

Definition chain (m : mem) (OWN : own_t) (c : Z) (ns : list (bptr * Z)) : Prop :=
  exists c', lseg m OWN c ns c' /\ rw_cells segs m c' [C8 (wz 0)].

Lemma lseg_app : forall m OWN ns1 ns2 c c1 c2, lseg m OWN c ns1 c1 -> lseg m OWN c1 ns2 c2 -> lseg m OWN c (ns1 ++ ns2) c2.
Proof.
  intros m OWN ns1. induction ns1 as [|[p A] ns1 IH]; intros ns2 c c1 c2 H1 H2; cbn [lseg app] in *.
  - subst c1. exact H2.
  - destruct H1 as (C & O & RG & N & R). split; [exact C|]. split; [exact O|]. split; [exact RG|]. split; [exact N|]. eapply IH; eassumption.
Qed.

Lemma lseg_split : forall m OWN ns1 ns2 c c2, lseg m OWN c (ns1 ++ ns2) c2 -> exists c1, lseg m OWN c ns1 c1 /\ lseg m OWN c1 ns2 c2.
Proof.
  intros m OWN ns1. induction ns1 as [|[p A] ns1 IH]; intros ns2 c c2 H; cbn [lseg app] in *.
  - exists c. auto.
  - destruct H as (C & O & RG & N & R). destruct (IH _ _ _ R) as (c1 & R1 & R2). exists c1. split; [| exact R2]. split; [exact C|]. split; [exact O|]. split; [exact RG|]. split; [exact N| exact R1].
Qed.

(* [comment removed for export] *)
Fixpoint lseg_fp (c : Z) (ns : list (bptr * Z)) (a : Z) : Prop :=
  match ns with
  | [] => False
  | (p, A) :: ns' => (c <= a < c + 8) \/ (A <= a < A + 8) \/ (A + 16 <= a < A + 24) \/ lseg_fp (A + 8) ns' a
  end.

Lemma lseg_agree : forall m m' OWN OWN' ns c c',
  lseg m OWN c ns c' -> agree_on (lseg_fp c ns) m m' ->
  (forall p A, In (p, A) ns -> OWN p A 24 24 -> OWN' p A 24 24) ->
  lseg m' OWN' c ns c'.
Proof.
  intros m m' OWN OWN' ns. induction ns as [|[p A] ns IH]; intros c c' H AG HO; cbn [lseg] in *; [exact H|].
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

Lemma chain_agree : forall m m' OWN OWN' ns c,
  chain m OWN c ns -> agree_on (fun a => (c <= a < c + 8) \/ exists p A, In (p, A) ns /\ A <= a < A + 24) m m' ->
  (forall p A, In (p, A) ns -> OWN p A 24 24 -> OWN' p A 24 24) ->
  chain m' OWN' c ns.
Proof.
  intros m m' OWN OWN' ns c (c' & S & Z0) AG HO. exists c'. split.
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
Lemma lseg_ranges : forall m OWN ns c c', lseg m OWN c ns c' -> forall p A, In (p, A) ns -> 0 < A /\ A + 24 <= CEIL.
Proof.
  intros m OWN ns. induction ns as [|[q B] ns IH]; intros c c' H p A Hin; [destruct Hin|]. cbn [lseg] in H. destruct H as (_ & _ & RG & _ & R).
  destruct Hin as [E|Hin]; [inversion E; subst; exact RG| exact (IH _ _ R p A Hin)].
Qed.

Lemma lseg_end_range : forall m OWN ns c c', lseg m OWN c ns c' -> 0 <= c /\ c + 8 <= CEIL -> 0 <= c' /\ c' + 8 <= CEIL.
Proof.
  intros m OWN ns. induction ns as [|[q B] ns IH]; intros c c' H HC; cbn [lseg] in H; [subst; exact HC|].
  destruct H as (_ & _ & RG & _ & R). apply (IH _ _ R). lia.
Qed.

Lemma lseg_munch : forall W m m' OWN ns c c', lseg m OWN c ns c' -> munch W m m' -> wmono segs m m' ->
  (forall a, 0 <= a < CEIL -> outside W a) -> 0 <= c /\ c + 8 <= CEIL -> lseg m' OWN c ns c'.
Proof.
  intros W m m' OWN ns c c' H MU WM HW HC. eapply lseg_agree; [exact H| | intros p A _ X; exact X].
  eapply agree_on_mono; [exact (agree_on_of_munch W m m' MU WM)|]. intros a Ha. apply HW.
  destruct (lseg_fp_where _ _ _ Ha) as [X|(p & A & Hp & X)]; [lia|]. pose proof (lseg_ranges _ _ _ _ _ H p A Hp). lia.
Qed.

Lemma chain_munch : forall W m m' OWN ns c, chain m OWN c ns -> munch W m m' -> wmono segs m m' ->
  (forall a, 0 <= a < CEIL -> outside W a) -> 0 <= c /\ c + 8 <= CEIL -> chain m' OWN c ns.
Proof.
  intros W m m' OWN ns c (c' & S & Z0) MU WM HW HC. exists c'. split; [eapply lseg_munch; eassumption|].
  pose proof (lseg_end_range _ _ _ _ _ S HC) as HC'.
  eapply rw_cells_agree; [exact (agree_on_of_munch W m m' MU WM)| exact Z0|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HW. lia.
Qed.
(* [comment removed for export] *)
Fixpoint chainv (m : mem) (OWN : own_t) (v : Z) (ns : list (bptr * Z)) : Prop :=
  match ns with
  | [] => v = 0
  | (p, A) :: ns' => v = A /\ OWN p A 24 24 /\ (0 < A /\ A + 24 <= CEIL) /\ node_cells m A
                     /\ exists nx, rw_cells segs m (A + 8) [C8 (wz nx)] /\ chainv m OWN nx ns'
  end.

Lemma chain_chainv : forall m OWN ns c, chain m OWN c ns -> exists v, rw_cells segs m c [C8 (wz v)] /\ chainv m OWN v ns.
Proof.
  intros m OWN ns. induction ns as [|[p A] ns IH]; intros c (c' & S & Z0); cbn [lseg] in S.
  - subst c'. exists 0. split; [exact Z0| reflexivity].
  - destruct S as (C & O & RG & N & R). exists A. split; [exact C|]. cbn [chainv]. split; [reflexivity|]. split; [exact O|]. split; [exact RG|]. split; [exact N|].
    destruct (IH (A + 8) (ex_intro _ c' (conj R Z0))) as (nx & CX & CV). exists nx. auto.
Qed.

Lemma chainv_chain : forall m OWN ns c v, rw_cells segs m c [C8 (wz v)] -> chainv m OWN v ns -> chain m OWN c ns.
Proof.
  intros m OWN ns. induction ns as [|[p A] ns IH]; intros c v C CV; cbn [chainv] in CV.
  - subst v. exists c. split; [reflexivity| exact C].
  - destruct CV as (-> & O & RG & N & nx & CX & CV). destruct (IH (A + 8) nx CX CV) as (c' & S & Z0).
    exists c'. split; [| exact Z0]. cbn [lseg]. auto.
Qed.

Lemma chainv_agree : forall m m' OWN ns v,
  chainv m OWN v ns -> agree_on (fun a => exists p A, In (p, A) ns /\ A <= a < A + 24) m m' -> chainv m' OWN v ns.
Proof.
  intros m m' OWN ns. induction ns as [|[p A] ns IH]; intros v CV AG; cbn [chainv] in *; [exact CV|].
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

Lemma chainv_ranges : forall m OWN ns v, chainv m OWN v ns -> forall p A, In (p, A) ns -> 0 < A /\ A + 24 <= CEIL.
Proof.
  intros m OWN ns. induction ns as [|[q B] ns IH]; intros v H p A Hin; [destruct Hin|]. cbn [chainv] in H. destruct H as (_ & _ & RG & _ & nx & _ & R).
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

Definition lh_rep (DV : Z -> Prop) (m : mem) (OWN : own_t) (f : lh_fns) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo)
    (bks : list (list (bptr * Z))) : Prop :=
  lh_geo_ok g
  /\ OWN pl lh 104 104 /\ (0 < lh /\ lh + 104 <= CEIL) /\ (exists x40 x48 err pad, rw_cells segs m lh (lh_cells f B g x40 x48 err pad))
  /\ OWN pb B (8 * g_na g) nmb /\ (0 < B /\ B + 8 * g_na g <= CEIL)
  /\ Z.of_nat (length bks) = g_na g
  /\ (forall i, 0 <= i < g_na g -> chain DV m OWN (B + 8 * i) (nth (Z.to_nat i) bks []))
  /\ (forall i, g_nn g <= i < g_na g -> nth (Z.to_nat i) bks [] = [])
  /\ List.NoDup (pl :: pb :: map fst (concat bks)).

(* [comment removed for export] *)
Definition lh_fp (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (a : Z) : Prop :=
  (lh <= a < lh + 104) \/ (B <= a < B + 8 * g_na g) \/ exists p A, In (p, A) (concat bks) /\ A <= a < A + 24.


Lemma lh_rep_agree : forall DV m m' OWN OWN' f lh pl pb B nmb g bks,
  lh_rep DV m OWN f lh pl pb B nmb g bks -> agree_on (lh_fp lh B g bks) m m' ->
  (forall q A n nm, lh_T pl pb bks q -> OWN q A n nm -> OWN' q A n nm) ->
  lh_rep DV m' OWN' f lh pl pb B nmb g bks.
Proof.
  intros DV m m' OWN OWN' f lh pl pb B nmb g bks (G & OL & RL & (x40 & x48 & err & pad & SC) & OB & RB & LEN & CH & EMP & ND) AG HO.
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


(* [comment removed for export] *)
(* [comment removed for export] *)








(* [comment removed for export] *)






(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma lseg_owns : forall DV m OWN ns c c', lseg DV m OWN c ns c' -> forall p A, In (p, A) ns -> OWN p A 24 24.
Proof.
  intros DV m OWN ns. induction ns as [|[q B] ns IH]; intros c c' H p A Hin; [destruct Hin|]. cbn [lseg] in H. destruct H as (_ & O & _ & _ & R).
  destruct Hin as [E|Hin]; [inversion E; subst; exact O| exact (IH _ _ R p A Hin)].
Qed.
Lemma chain_owns : forall DV m OWN ns c, chain DV m OWN c ns -> forall p A, In (p, A) ns -> OWN p A 24 24.
Proof. intros DV m OWN ns c (c' & S & _). exact (lseg_owns _ _ _ _ _ _ S). Qed.

Lemma nodes_fop : forall (OWN : own_t) (ns : list (bptr * Z)), own_apart OWN -> (forall p A, In (p, A) ns -> OWN p A 24 24) -> List.NoDup (map fst ns) ->
  ForallOrdPairs apart24 (map snd ns).
Proof.
  intros OWN ns HP. induction ns as [|[p A] ns IH]; intros OW ND; cbn [map snd]; [constructor|]. cbn [map fst] in ND. inversion ND as [|x l NI ND']; subst.
  constructor; [| apply IH; [intros q Bq Hq; apply OW; right; exact Hq| exact ND']].
  apply Forall_forall. intros X HX. apply in_map_iff in HX. destruct HX as ([q Bq] & E & Hq). cbn [snd] in E. subst X.
  unfold apart24. eapply (HP p A 24 24 q Bq 24 24); [apply OW; left; reflexivity| apply OW; right; exact Hq|].
  intros E. apply NI. subst q. apply in_map_iff. exists (p, Bq). auto.
Qed.

(* [comment removed for export] *)
Lemma lh_sep : forall DV m OWN f lh pl pb B nmb g bks, own_apart OWN -> lh_rep DV m OWN f lh pl pb B nmb g bks ->
  (lh + 104 <= B \/ B + 8 * g_na g <= lh)
  /\ (forall i p A, (i < length bks)%nat -> In (p, A) (nth i bks []) -> (A + 24 <= lh \/ lh + 104 <= A) /\ (A + 24 <= B \/ B + 8 * g_na g <= A))
  /\ (forall i j x y, (i < length bks)%nat -> (j < length bks)%nat -> i <> j -> In x (nth i bks []) -> In y (nth j bks []) -> apart24 (snd x) (snd y))
  /\ (forall i, (i < length bks)%nat -> ForallOrdPairs apart24 (map snd (nth i bks []))).
Proof.
  intros DV m OWN f lh pl pb B nmb g bks HP (G & OL & RL & SC & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB.
  inversion ND as [|x l NI1 ND1]; subst. inversion ND1 as [|x l NI2 ND2]; subst.
  assert (OWNED : forall i p A, (i < length bks)%nat -> In (p, A) (nth i bks []) -> OWN p A 24 24).
  { intros i p A Hi Hin. assert (IR : 0 <= Z.of_nat i < g_na g) by lia. pose proof (CH (Z.of_nat i) IR) as C. rewrite Nat2Z.id in C.
    exact (chain_owns _ _ _ _ _ C p A Hin). }
  assert (IDS : forall i p A, In (p, A) (nth i bks []) -> In p (map fst (concat bks))).
  { intros i p A Hin. apply in_map_iff. exists (p, A). split; [reflexivity| eapply in_nth_concat; exact Hin]. }
  split. { eapply (HP pl lh 104 104 pb B (8 * g_na g) nmb); [exact OL| exact OB|]. intros E. apply NI1. left. symmetry. exact E. }
  split. { intros i p A Hi Hin. split.
    - eapply (HP p A 24 24 pl lh 104 104); [exact (OWNED i p A Hi Hin)| exact OL|]. intros E. apply NI1. right. subst p. exact (IDS i pl A Hin).
    - eapply (HP p A 24 24 pb B (8 * g_na g) nmb); [exact (OWNED i p A Hi Hin)| exact OB|]. intros E. apply NI2. subst p. exact (IDS i pb A Hin). }
  split. { intros i j [p A] [q Bq] Hi Hj NE Hx Hy. cbn [snd]. unfold apart24.
    eapply (HP p A 24 24 q Bq 24 24); [exact (OWNED i p A Hi Hx)| exact (OWNED j q Bq Hj Hy)|].
    exact (nodup_concat_ne bks i j (p, A) (q, Bq) ND2 NE Hx Hy). }
  intros i Hi. eapply (nodes_fop OWN); [exact HP| intros p A Hin; exact (OWNED i p A Hi Hin)| exact (nodup_concat_nth bks i ND2)].
Qed.

(* [comment removed for export] *)
Lemma bucket_nsep : forall DV m OWN f lh pl pb B nmb g bks i j, own_apart OWN -> lh_rep DV m OWN f lh pl pb B nmb g bks ->
  0 <= i < g_na g -> 0 <= j < g_na g -> i <> j -> nsep (nth (Z.to_nat i) bks []) (B + 8 * i) (B + 8 * j).
Proof.
  intros DV m OWN f lh pl pb B nmb g bks i j HP REP Hi Hj NE.
  destruct (lh_sep _ _ _ _ _ _ _ _ _ _ _ HP REP) as (_ & SN & _ & SF). destruct REP as (G & _ & _ & _ & _ & _ & LEN & _).
  assert (LI : (Z.to_nat i < length bks)%nat) by lia.
  split; [exact (SF _ LI)|]. split; [| lia].
  apply Forall_forall. intros X HX. apply in_map_iff in HX. destruct HX as ([p A] & E & Hin). cbn [snd] in E. subst X.
  destruct (SN _ p A LI Hin) as [_ SB]. unfold apartc. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lseg_end_loc : forall DV m OWN ns c c', lseg DV m OWN c ns c' ->
  (ns = [] /\ c' = c) \/ (exists pre p A, ns = pre ++ [(p, A)] /\ c' = A + 8).
Proof.
  intros DV m OWN ns. induction ns as [|[q Bq] ns IH]; intros c c' H; cbn [lseg] in H; [left; auto|].
  destruct H as (_ & _ & _ & _ & R). right. destruct (IH _ _ R) as [[-> ->]|(pre & p & A & -> & ->)].
  - exists [], q, Bq. auto.
  - exists ((q, Bq) :: pre), p, A. auto.
Qed.

(* [comment removed for export] *)

Lemma lh_rep_owned : forall DV m OWN f lh pl pb B nmb g bks, lh_rep DV m OWN f lh pl pb B nmb g bks ->
  forall p A, In (p, A) (concat bks) -> OWN p A 24 24.
Proof.
  intros DV m OWN f lh pl pb B nmb g bks (G & _ & _ & _ & _ & _ & LEN & CH & _) p A Hin.
  apply in_concat in Hin. destruct Hin as (ns & Hns & Hin). destruct (In_nth _ _ [] Hns) as (i & Hi & E). subst ns.
  assert (IR : 0 <= Z.of_nat i < g_na g) by lia. pose proof (CH (Z.of_nat i) IR) as C. rewrite Nat2Z.id in C. exact (chain_owns _ _ _ _ _ C p A Hin).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bucket_fp (B : Z) (bks : list (list (bptr * Z))) (i : Z) (a : Z) : Prop :=
  (B + 8 * i <= a < B + 8 * i + 8) \/ exists p A, In (p, A) (nth (Z.to_nat i) bks []) /\ A <= a < A + 24.

Lemma lh_rep_upd : forall DV m m' OWN OWN' f lh pl pb B nmb g g' bks bks' (J : Z -> Prop),
  lh_rep DV m OWN f lh pl pb B nmb g bks -> (forall i, J i \/ ~ J i) ->
  g_na g' = g_na g -> lh_geo_ok g' ->
  (exists x40 x48 err pad, rw_cells segs m' lh (lh_cells f B g' x40 x48 err pad)) ->
  (forall q A n nm, lh_T pl pb bks q -> OWN q A n nm -> OWN' q A n nm) ->
  Z.of_nat (length bks') = g_na g ->
  (forall i, 0 <= i < g_na g -> J i -> chain DV m' OWN' (B + 8 * i) (nth (Z.to_nat i) bks' [])) ->
  (forall i, 0 <= i < g_na g -> ~ J i -> nth (Z.to_nat i) bks' [] = nth (Z.to_nat i) bks [] /\ agree_on (bucket_fp B bks i) m m') ->
  (forall i, g_nn g' <= i < g_na g -> nth (Z.to_nat i) bks' [] = []) ->
  List.NoDup (pl :: pb :: map fst (concat bks')) ->
  lh_rep DV m' OWN' f lh pl pb B nmb g' bks'.
Proof.
  intros DV m m' OWN OWN' f lh pl pb B nmb g g' bks bks' J (G & OL & RL & SC & OB & RB & LEN & CH & EMP & ND) JDEC ENA G' SC' HO LEN' CHJ CHO EMP' ND'.
  split; [exact G'|]. split; [apply HO; [left; reflexivity| exact OL]|]. split; [exact RL|]. split; [exact SC'|].
  rewrite ENA. split; [apply HO; [right; left; reflexivity| exact OB]|]. split; [exact RB|]. split; [exact LEN'|].
  split; [| split; [exact EMP'| exact ND']].
  intros i Hi. destruct (JDEC i) as [HJ|HJ]; [exact (CHJ i Hi HJ)|].
  destruct (CHO i Hi HJ) as [E AG]. rewrite E. eapply chain_agree; [exact (CH i Hi)| exact AG|].
  intros p A Hp. apply HO. right; right. apply in_map_iff. exists (p, A). split; [reflexivity|]. eapply in_nth_concat. exact Hp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cells_assemble : forall (n : nat) m B, 0 <= B -> B + 8 * Z.of_nat n <= 2^64 ->
  (forall i, (i < n)%nat -> exists w : word, rw_cells segs m (B + 8 * Z.of_nat i) [C8 w]) ->
  exists src, rw_cells segs m B [CB (8 * n) src].
Proof.
  induction n as [|n IH]; intros m B HB HH H.
  - exists []. apply rw_cells_CB0. lia.
  - destruct (IH m B HB ltac:(lia) (fun i Hi => H i ltac:(lia))) as [src HS]. destruct (H n ltac:(lia)) as [w C].
    exists (src ++ le8 w). replace (8 * S n)%nat with (8 * n + 8)%nat by lia.
    eapply lhg_rw_cells_CB_join; [exact HS|]. replace (B + Z.of_nat (8 * n)) with (B + 8 * Z.of_nat n) by lia.
    eapply rw_cells_recast; [exact C| change (length (le8 w) = 8%nat /\ True); split; [apply length_le8| exact I]| reflexivity| reflexivity].
Qed.

Lemma cells_read_back : forall m m' B A' (n N : nat) src tail (i : nat) (w : word),
  rw_cells segs m B [CB (8 * n) src] -> rw_cells segs m (B + 8 * Z.of_nat i) [C8 w] -> (i < n)%nat ->
  rw_cells segs m' A' [CB N (src ++ tail)] ->
  rw_cells segs m' (A' + 8 * Z.of_nat i) [C8 w].
Proof.
  intros m m' B A' n N src tail i w HS C Hi HS'.
  pose proof (rw_cells_CB_length segs m B _ _ HS) as LS. pose proof (rw_cells_CB_length segs m' A' _ _ HS') as LN. rewrite length_app in LN.
  (* [comment removed for export] *)
  assert (E : firstn 8 (skipn (8 * i) src) = le8 w).
  { pose proof (rw_cells_bytes_at segs m B _ HS) as BS. cbn [cells_bytes cbytes] in BS. rewrite app_nil_r in BS.
    pose proof (rw_cells_bytes_at segs m _ _ C) as BC. cbn [cells_bytes cbytes] in BC. rewrite app_nil_r in BC.
    rewrite <- (firstn_skipn (8 * i) src) in BS. apply bytes_at_app in BS. destruct BS as [_ BS]. rewrite firstn_length, Nat.min_l in BS by lia.
    rewrite <- (firstn_skipn 8 (skipn (8 * i) src)) in BS. apply bytes_at_app in BS. destruct BS as [BS _].
    replace (B + Z.of_nat (8 * i)) with (B + 8 * Z.of_nat i) in BS by lia.
    apply (bytes_at_inj m (B + 8 * Z.of_nat i)); [exact BS| exact BC|]. rewrite firstn_length, skipn_length, length_le8. lia. }
  destruct (lhg_rw_cells_CB_split_at segs m' A' N (src ++ tail) (8 * i) ltac:(lia) HS') as [_ S2].
  destruct (lhg_rw_cells_CB_split_at segs m' (A' + Z.of_nat (8 * i)) (N - 8 * i) (skipn (8 * i) (src ++ tail)) 8 ltac:(lia) S2) as [S3 _].
  replace (A' + Z.of_nat (8 * i)) with (A' + 8 * Z.of_nat i) in S3 by lia.
  eapply rw_cells_recast; [exact S3| cbn; auto| | reflexivity]. cbn [cells_bytes cbytes]. f_equal.
  rewrite skipn_app, firstn_app, skipn_length. replace (8 - (length src - 8 * i))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. symmetry. exact E.
Qed.



(* [comment removed for export] *)
Lemma cells_zero : forall m A (n i : nat), rw_cells segs m A [CB (8 * n) (repeat (Z_to_bv 8 0) (8 * n))] -> (i < n)%nat ->
  rw_cells segs m (A + 8 * Z.of_nat i) [C8 (Z_to_bv 64 0)].
Proof.
  intros m A n i HS Hi.
  destruct (lhg_rw_cells_CB_split_at segs m A (8 * n) (repeat (Z_to_bv 8 0) (8 * n)) (8 * i) ltac:(lia) HS) as [_ S2].
  destruct (lhg_rw_cells_CB_split_at segs m (A + Z.of_nat (8 * i)) (8 * n - 8 * i) (skipn (8 * i) (repeat (Z_to_bv 8 0) (8 * n))) 8 ltac:(lia) S2) as [S3 _].
  replace (A + Z.of_nat (8 * i)) with (A + 8 * Z.of_nat i) in S3 by lia.
  eapply rw_cells_recast; [exact S3| cbn; auto| | reflexivity]. cbn [cells_bytes cbytes]. f_equal.
  rewrite firstn_skipn_repeat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lh_raw (DV : Z -> Prop) (m : mem) (OWN : own_t) (lh : Z) (pl pb : bptr) (B nmb na : Z) (bks : list (list (bptr * Z))) : Prop :=
  OWN pl lh 104 104 /\ (0 < lh /\ lh + 104 <= CEIL)
  /\ OWN pb B (8 * na) nmb /\ (0 < B /\ B + 8 * na <= CEIL)
  /\ Z.of_nat (length bks) = na
  /\ (forall i, 0 <= i < na -> chain DV m OWN (B + 8 * i) (nth (Z.to_nat i) bks []))
  /\ List.NoDup (pl :: pb :: map fst (concat bks)).

Lemma lh_rep_raw : forall DV m OWN f lh pl pb B nmb g bks, lh_rep DV m OWN f lh pl pb B nmb g bks -> lh_raw DV m OWN lh pl pb B nmb (g_na g) bks.
Proof. intros DV m OWN f lh pl pb B nmb g bks (G & OL & RL & SC & OB & RB & LEN & CH & EMP & ND). unfold lh_raw. auto 10. Qed.

Lemma lh_rep_of_raw : forall DV m OWN f lh pl pb B nmb g bks, lh_raw DV m OWN lh pl pb B nmb (g_na g) bks -> lh_geo_ok g ->
  (exists x40 x48 err pad, rw_cells segs m lh (lh_cells f B g x40 x48 err pad)) ->
  (forall i, g_nn g <= i < g_na g -> nth (Z.to_nat i) bks [] = []) ->
  lh_rep DV m OWN f lh pl pb B nmb g bks.
Proof. intros DV m OWN f lh pl pb B nmb g bks (OL & RL & OB & RB & LEN & CH & ND) G SC EMP. unfold lh_rep. auto 12. Qed.

Lemma lh_raw_upd : forall DV m m' OWN OWN' lh pl pb B nmb na bks bks' (J : Z -> Prop),
  lh_raw DV m OWN lh pl pb B nmb na bks -> (forall i, J i \/ ~ J i) ->
  (forall q A n nm, lh_T pl pb bks q -> OWN q A n nm -> OWN' q A n nm) ->
  Z.of_nat (length bks') = na ->
  (forall i, 0 <= i < na -> J i -> chain DV m' OWN' (B + 8 * i) (nth (Z.to_nat i) bks' [])) ->
  (forall i, 0 <= i < na -> ~ J i -> nth (Z.to_nat i) bks' [] = nth (Z.to_nat i) bks [] /\ agree_on (bucket_fp B bks i) m m') ->
  List.NoDup (pl :: pb :: map fst (concat bks')) ->
  lh_raw DV m' OWN' lh pl pb B nmb na bks'.
Proof.
  intros DV m m' OWN OWN' lh pl pb B nmb na bks bks' J (OL & RL & OB & RB & LEN & CH & ND) JDEC HO LEN' CHJ CHO ND'.
  split; [apply HO; [left; reflexivity| exact OL]|]. split; [exact RL|]. split; [apply HO; [right; left; reflexivity| exact OB]|]. split; [exact RB|]. split; [exact LEN'|].
  split; [| exact ND'].
  intros i Hi. destruct (JDEC i) as [HJ|HJ]; [exact (CHJ i Hi HJ)|].
  destruct (CHO i Hi HJ) as [E AG]. rewrite E. eapply chain_agree; [exact (CH i Hi)| exact AG|].
  intros p A Hp. apply HO. right; right. apply in_map_iff. exists (p, A). split; [reflexivity|]. eapply in_nth_concat. exact Hp.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition split_ivs (cp cn : Z) (NS : list (bptr * Z)) : list (Z * Z) := (cp, cp + 8) :: (cn, cn + 8) :: map (fun x => (snd x + 8, snd x + 16)) NS.

Lemma split_ivs_outside : forall cp cn NS a, outside (split_ivs cp cn NS) a <-> ~ split_W cp cn NS a.
Proof.
  intros cp cn NS a. unfold split_ivs, split_W. cbn [outside]. induction NS as [|[p A] NS IH]; cbn [map outside snd].
  - split; [intros (H1 & H2 & _) [H|[H|(p & A & [] & _)]]; tauto| intros H; repeat split; intros X; apply H; tauto].
  - split.
    + intros (H1 & H2 & H3 & H4) [H|[H|(q & Bq & [E|Hq] & Ha)]]; [tauto| tauto| inversion E; subst; tauto|].
      apply (proj1 IH); [repeat split; assumption|]. right; right. exists q, Bq. auto.
    + intros H. split; [intros X; apply H; tauto|]. split; [intros X; apply H; tauto|]. split.
      * intros X. apply H. right; right. exists p, A. split; [left; reflexivity| exact X].
      * assert (H' : ~ ((cp <= a < cp + 8) \/ (cn <= a < cn + 8) \/ exists q Bq, In (q, Bq) NS /\ Bq + 8 <= a < Bq + 16)).
        { intros [X|[X|(q & Bq & Hq & X)]]; apply H; [tauto| tauto| right; right; exists q, Bq; split; [right; exact Hq| exact X]]. }
        exact (proj2 (proj2 (proj2 IH H'))).
Qed.

Lemma split_munch : forall cp cn NS m m', agree_on (fun a => ~ split_W cp cn NS a) m m' -> munch (split_ivs cp cn NS) m m'.
Proof.
  intros cp cn NS m m' AG x Hx. apply split_ivs_outside in Hx. pose proof (bv_unsigned_in_range _ x) as XR. change (bv_modulus 64) with (2^64) in XR.
  destruct (AG (bv_unsigned x) XR Hx) as [E _]. rewrite wa_unsigned_id in E. exact E.
Qed.
(* [comment removed for export] *)
Lemma lh_sep_raw : forall DV m OWN lh pl pb B nmb na bks, own_apart OWN -> lh_raw DV m OWN lh pl pb B nmb na bks ->
  (lh + 104 <= B \/ B + 8 * na <= lh)
  /\ (forall i p A, (i < length bks)%nat -> In (p, A) (nth i bks []) -> (A + 24 <= lh \/ lh + 104 <= A) /\ (A + 24 <= B \/ B + 8 * na <= A))
  /\ (forall i j x y, (i < length bks)%nat -> (j < length bks)%nat -> i <> j -> In x (nth i bks []) -> In y (nth j bks []) -> apart24 (snd x) (snd y))
  /\ (forall i, (i < length bks)%nat -> ForallOrdPairs apart24 (map snd (nth i bks []))).
Proof.
  intros DV m OWN lh pl pb B nmb na bks HP (OL & RL & OB & RB & LEN & CH & ND).
  inversion ND as [|x l NI1 ND1]; subst. inversion ND1 as [|x l NI2 ND2]; subst.
  assert (OWNED : forall i p A, (i < length bks)%nat -> In (p, A) (nth i bks []) -> OWN p A 24 24).
  { intros i p A Hi Hin. assert (IR : 0 <= Z.of_nat i < Z.of_nat (length bks)) by lia. pose proof (CH (Z.of_nat i) IR) as C. rewrite Nat2Z.id in C.
    exact (chain_owns _ _ _ _ _ C p A Hin). }
  assert (IDS : forall i p A, In (p, A) (nth i bks []) -> In p (map fst (concat bks))).
  { intros i p A Hin. apply in_map_iff. exists (p, A). split; [reflexivity| eapply in_nth_concat; exact Hin]. }
  split. { eapply (HP pl lh 104 104 pb B (8 * Z.of_nat (length bks)) nmb); [exact OL| exact OB|]. intros E. apply NI1. left. symmetry. exact E. }
  split. { intros i p A Hi Hin. split.
    - eapply (HP p A 24 24 pl lh 104 104); [exact (OWNED i p A Hi Hin)| exact OL|]. intros E. apply NI1. right. subst p. exact (IDS i pl A Hin).
    - eapply (HP p A 24 24 pb B (8 * Z.of_nat (length bks)) nmb); [exact (OWNED i p A Hi Hin)| exact OB|]. intros E. apply NI2. subst p. exact (IDS i pb A Hin). }
  split. { intros i j [p A] [q Bq] Hi Hj NE Hx Hy. cbn [snd]. unfold apart24.
    eapply (HP p A 24 24 q Bq 24 24); [exact (OWNED i p A Hi Hx)| exact (OWNED j q Bq Hj Hy)|].
    exact (nodup_concat_ne bks i j (p, A) (q, Bq) ND2 NE Hx Hy). }
  intros i Hi. eapply (nodes_fop OWN); [exact HP| intros p A Hin; exact (OWNED i p A Hi Hin)| exact (nodup_concat_nth bks i ND2)].
Qed.

Lemma bucket_nsep_raw : forall DV m OWN lh pl pb B nmb na bks i j, own_apart OWN -> lh_raw DV m OWN lh pl pb B nmb na bks ->
  0 <= i < na -> 0 <= j < na -> i <> j -> nsep (nth (Z.to_nat i) bks []) (B + 8 * i) (B + 8 * j).
Proof.
  intros DV m OWN lh pl pb B nmb na bks i j HP RAW Hi Hj NE.
  destruct (lh_sep_raw _ _ _ _ _ _ _ _ _ _ HP RAW) as (_ & SN & _ & SF). destruct RAW as (_ & _ & _ & _ & LEN & _).
  assert (LI : (Z.to_nat i < length bks)%nat) by lia.
  split; [exact (SF _ LI)|]. split; [| lia].
  apply Forall_forall. intros X HX. apply in_map_iff in HX. destruct HX as ([p A] & E & Hin). cbn [snd] in E. subst X.
  destruct (SN _ p A LI Hin) as [_ SB]. unfold apartc. lia.
Qed.

(* [comment removed for export] *)
Lemma split_raw : forall DV m m' OWN lh pl pb B nmb na bks (p nn : Z) stay' moved',
  own_apart OWN -> lh_raw DV m OWN lh pl pb B nmb na bks ->
  0 <= p < nn -> nn < na -> nth (Z.to_nat nn) bks [] = [] ->
  chain DV m' OWN (B + 8 * p) stay' -> chain DV m' OWN (B + 8 * nn) moved' ->
  Permutation (stay' ++ moved') (nth (Z.to_nat p) bks []) ->
  agree_on (fun a => ~ ((lh + 56 <= a < lh + 68) \/ split_W (B + 8 * p) (B + 8 * nn) (nth (Z.to_nat p) bks []) a)) m m' ->
  lh_raw DV m' OWN lh pl pb B nmb na (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' bks))
  /\ Permutation (concat (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' bks))) (concat bks).
Proof.
  intros DV m m' OWN lh pl pb B nmb na bks p nn stay' moved' HP RAW PR NNA EMP CS CM PM AG.
  destruct (lh_sep_raw _ _ _ _ _ _ _ _ _ _ HP RAW) as (S_LB & S_N & S_X & S_F).
  pose proof RAW as (OL & RL & OB & RB & LEN & CH & ND).
  assert (LP : (Z.to_nat p < length bks)%nat) by lia. assert (LN : (Z.to_nat nn < length bks)%nat) by lia. assert (NEpn : Z.to_nat p <> Z.to_nat nn) by lia.
  assert (PMC : Permutation (concat (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' bks))) (concat bks)) by (apply concat_lupd2_perm; assumption).
  split; [| exact PMC].
  eapply (lh_raw_upd DV m m' OWN OWN lh pl pb B nmb na bks _ (fun i => i = p \/ i = nn) RAW).
  - intros i. lia.
  - intros q A n nm _ X. exact X.
  - rewrite !lupd_length. exact LEN.
  - intros i Hi [-> | ->].
    + rewrite nth_lupd_eq by (rewrite lupd_length; exact LP). exact CS.
    + rewrite nth_lupd_ne by exact NEpn. rewrite nth_lupd_eq by exact LN. exact CM.
  - intros i Hi NJ. assert (LI : (Z.to_nat i < length bks)%nat) by lia.
    split; [rewrite !nth_lupd_ne by lia; reflexivity|].
    eapply agree_on_mono; [exact AG|]. intros a FP. unfold bucket_fp in FP. unfold split_W. intros BAD.
    assert (NP : forall q Aq, In (q, Aq) (nth (Z.to_nat p) bks []) -> (Aq + 24 <= lh \/ lh + 104 <= Aq) /\ (Aq + 24 <= B \/ B + 8 * na <= Aq)) by (intros q Aq Hq; exact (S_N _ q Aq LP Hq)).
    destruct FP as [FP|(q0 & A0 & H0 & FP)].
    + destruct BAD as [BAD|[BAD|[BAD|(q & Aq & Hq & BAD)]]]; try lia. destruct (NP q Aq Hq) as [_ X]. lia.
    + destruct (S_N _ q0 A0 LI H0) as [X1 X2].
      destruct BAD as [BAD|[BAD|[BAD|(q & Aq & Hq & BAD)]]]; try lia.
      assert (X : apart24 (snd (q0, A0)) (snd (q, Aq))) by (apply (S_X (Z.to_nat i) (Z.to_nat p)); try assumption; lia). unfold apart24 in X. cbn [snd] in X. lia.
  - inversion ND as [|x l NI1 ND1]; subst. inversion ND1 as [|x l NI2 ND2]; subst.
    assert (PMM : Permutation (map fst (concat (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' bks)))) (map fst (concat bks))) by (apply Permutation_map; exact PMC).
    constructor. { intros [E|X]; [apply NI1; left; exact E| apply NI1; right; eapply Permutation_in; [exact PMM| exact X]]. }
    constructor. { intros X. apply NI2. eapply Permutation_in; [exact PMM| exact X]. }
    eapply Permutation_NoDup; [apply Permutation_sym; exact PMM| exact ND2].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lseg_fp_end : forall DV m OWN ns c0 c', lseg DV m OWN c0 ns c' ->
  ForallOrdPairs apart24 (map snd ns) -> Forall (fun A => apartc A c0) (map snd ns) ->
  forall a, lseg_fp c0 ns a -> ~ (c' <= a < c' + 8).
Proof.
  intros DV m OWN ns. induction ns as [|[p1 A1] ns IH]; intros c0 c' S FO FC a Ha; cbn [lseg_fp] in Ha; [destruct Ha|].
  cbn [lseg] in S. destruct S as (_ & _ & RG & _ & R). cbn [map snd] in FO, FC. inversion FO as [|x l FA FO']; subst. inversion FC as [|x l AC0 FC']; subst.
  (* [comment removed for export] *)
  assert (LOC : c' = A1 + 8 \/ exists A, In A (map snd ns) /\ c' = A + 8).
  { clear - R. revert R. generalize (A1 + 8). induction ns as [|[q Bq] ns IHn]; intros z R; cbn [lseg] in R; [left; symmetry; exact R|].
    destruct R as (_ & _ & _ & _ & R). destruct (IHn _ R) as [E|(A & HA & E)]; right; [exists Bq; split; [left; reflexivity| exact E]| exists A; split; [right; exact HA| exact E]]. }
  unfold apartc in AC0.
  destruct Ha as [Ha|[Ha|[Ha|Ha]]].
  - destruct LOC as [->|(A & HA & ->)]; [lia|]. pose proof (proj1 (Forall_forall _ _) FC' A HA) as X. unfold apartc in X. lia.
  - destruct LOC as [->|(A & HA & ->)]; [lia|]. pose proof (proj1 (Forall_forall _ _) FA A HA) as X. unfold apart24 in X. lia.
  - destruct LOC as [->|(A & HA & ->)]; [lia|]. pose proof (proj1 (Forall_forall _ _) FA A HA) as X. unfold apart24 in X. lia.
  - apply (IH (A1 + 8) c' R FO'); [| exact Ha].
    apply Forall_forall. intros A HA. pose proof (proj1 (Forall_forall _ _) FA A HA) as X. unfold apart24, apartc in *. lia.
Qed.

Lemma chainv_own : forall DV m OWN OWN' ns v, chainv DV m OWN v ns ->
  (forall p A, In (p, A) ns -> OWN p A 24 24 -> OWN' p A 24 24) -> chainv DV m OWN' v ns.
Proof.
  intros DV m OWN OWN' ns. induction ns as [|[p A] ns IH]; intros v CV HO; cbn [chainv] in *; [exact CV|].
  destruct CV as (-> & O & RG & N & nx & CX & CV). split; [reflexivity|]. split; [apply HO; [left; reflexivity| exact O]|]. split; [exact RG|]. split; [exact N|].
  exists nx. split; [exact CX|]. apply IH; [exact CV|]. intros q Bq Hq. apply HO. right. exact Hq.
Qed.

End LhRep.
