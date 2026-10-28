(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzArrD BzCMem BzCStream BzCState BzCMtf BzCRebuildF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCutSM.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)

From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmas1 CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
Module CmpCutGSM.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSM.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.
(* [comment removed for export] *)
End CmpCutGSM.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sip0 (e : est) : sip := SIP (smA_len e) (smA_ng e) (sm_nmtf e) 0.
Definition sip_k (e : est) (k : nat) : sip := Nat.iter k (sm_init_iter (e_mtfFreq e) (smA_ng e) (sm_alpha e)) (sip0 e).
Lemma sip_k_S : forall e k, sip_k e (S k) = sm_init_iter (e_mtfFreq e) (smA_ng e) (sm_alpha e) (sip_k e k).
Proof. reflexivity. Qed.
(* [comment removed for export] *)

Lemma sm_nGroups_range : forall n, 2 <= sm_nGroups n <= 6.
Proof. intros n. unfold sm_nGroups. repeat (destruct (_ <? _)); lia. Qed.
Lemma sm_nGroups_6 : forall n, sm_nGroups n = 6 <-> 2400 <= n.
Proof.
  intros n. unfold sm_nGroups.
  destruct (Z.ltb_spec n 200); [split; intros; lia|]. destruct (Z.ltb_spec n 600); [split; intros; lia|].
  destruct (Z.ltb_spec n 1200); [split; intros; lia|]. destruct (Z.ltb_spec n 2400); split; intros; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition smA_facts (e : est) : Prop :=
  let mf := e_mtfFreq e in let A := sm_alpha e in let nG := smA_ng e in let nMTF := sm_nmtf e in
  1 <= e_nInUse e <= 256 /\ 1 <= nMTF <= NBLOCKMAX + 19 /\
  (forall v, 0 <= v < A -> zdef mf v = true /\ 0 <= zget mf v <= nMTF) /\
  (* [comment removed for export] *)
  (forall k, (Z.of_nat k < nG) -> let s := sip_k e k in
     ip_nPart s = nG - Z.of_nat k /\ 0 <= ip_gs s <= A /\
     ip_remF s = sumF (fun v => zget mf v) (ip_gs s) (Z.to_nat (A - ip_gs s)) /\ 0 <= ip_remF s <= nMTF) /\
  sm_init_tables 8%nat mf nG A (sip0 e) = sip_k e (Z.to_nat nG).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sumF_split : forall n m g j, sumF g j (n + m) = sumF g j n + sumF g (j + Z.of_nat n) m.
Proof.
  induction n as [|n IH]; intros m g j; cbn [sumF Nat.add].
  - replace (j + Z.of_nat 0) with j by lia. lia.
  - rewrite IH. replace (j + 1 + Z.of_nat n) with (j + Z.of_nat (S n)) by lia. lia.
Qed.
Lemma sumF_S_last : forall n g j, sumF g j (S n) = sumF g j n + g (j + Z.of_nat n).
Proof. intros n g j. replace (S n) with (n + 1)%nat by lia. rewrite sumF_split. cbn [sumF]. lia. Qed.
(* [comment removed for export] *)
Lemma sumF_prefix_le : forall n m g j, (n <= m)%nat -> (forall b, j <= b < j + Z.of_nat m -> 0 <= g b) ->
  0 <= sumF g j n <= sumF g j m.
Proof.
  intros n m g j Hnm Hg. replace m with (n + (m - n))%nat by lia. rewrite sumF_split.
  pose proof (sumF_nonneg n g j ltac:(intros; apply Hg; lia)).
  pose proof (sumF_nonneg (m - n) g (j + Z.of_nat n) ltac:(intros; apply Hg; lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_len_init_row_S : forall n len t v, sm_len_init_row (S n) len t v = sm_len_init_row n (zset len (258 * t + v) BZ_GREATER_ICOST) t (v + 1).
Proof. reflexivity. Qed.
Lemma sm_len_init_row_get : forall n len t v x,
  zget (sm_len_init_row n len t v) x = (if (258 * t + v <=? x) && (x <? 258 * t + v + Z.of_nat n) then BZ_GREATER_ICOST else zget len x).
Proof.
  induction n as [|n IH]; intros len t v x; cbn [sm_len_init_row].
  - destruct (Z.leb_spec (258 * t + v) x), (Z.ltb_spec x (258 * t + v + Z.of_nat 0)); cbn [andb]; try reflexivity; lia.
  - rewrite IH, zget_zset. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    destruct (Z.leb_spec (258 * t + (v + 1)) x), (Z.ltb_spec x (258 * t + (v + 1) + Z.of_nat n)), (Z.eqb_spec x (258 * t + v)),
      (Z.leb_spec (258 * t + v) x), (Z.ltb_spec x (258 * t + v + (Z.of_nat n + 1))); cbn [andb]; try reflexivity; lia.
Qed.
Lemma sm_len_init_row_def : forall n len t v x,
  zdef (sm_len_init_row n len t v) x = (((258 * t + v <=? x) && (x <? 258 * t + v + Z.of_nat n)) || zdef len x)%bool.
Proof.
  induction n as [|n IH]; intros len t v x; cbn [sm_len_init_row].
  - destruct (Z.leb_spec (258 * t + v) x), (Z.ltb_spec x (258 * t + v + Z.of_nat 0)); cbn [andb orb]; try reflexivity; lia.
  - rewrite IH, zdef_zset. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    destruct (Z.leb_spec (258 * t + (v + 1)) x), (Z.ltb_spec x (258 * t + (v + 1) + Z.of_nat n)), (Z.eqb_spec x (258 * t + v)),
      (Z.leb_spec (258 * t + v) x), (Z.ltb_spec x (258 * t + v + (Z.of_nat n + 1))), (zdef len x); cbn [andb orb]; try reflexivity; lia.
Qed.
Lemma sm_len_init_S : forall n len A t, sm_len_init (S n) len A t = sm_len_init n (sm_len_init_row (Z.to_nat A) len t 0) A (t + 1).
Proof. reflexivity. Qed.

Definition setrow_val (gs ge v : Z) : Z := if (gs <=? v) && (v <=? ge) then BZ_LESSER_ICOST else BZ_GREATER_ICOST.
Lemma sm_setrow_S : forall n len t gs ge v, sm_setrow (S n) len t gs ge v = sm_setrow n (zset len (258 * t + v) (setrow_val gs ge v)) t gs ge (v + 1).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sm_grow_S : forall f mf tF A ge aF,
  sm_grow (S f) mf tF A ge aF = (if (aF <? tF) && (ge <? A - 1) then sm_grow f mf tF A (ge + 1) (aF + zget mf (ge + 1)) else (ge, aF)).
Proof. reflexivity. Qed.
Lemma sm_grow_stop : forall f mf tF A ge aF, (tF <= aF \/ A - 1 <= ge) -> sm_grow f mf tF A ge aF = (ge, aF).
Proof.
  intros [|f] mf tF A ge aF H; [reflexivity|]. rewrite sm_grow_S.
  destruct (Z.ltb_spec aF tF), (Z.ltb_spec ge (A - 1)); cbn [andb]; try reflexivity. lia.
Qed.

(* [comment removed for export] *)
Definition ip_adj (nG : Z) (s : sip) (ge1 : Z) : bool :=
  (ip_gs s <? ge1) && negb (ip_nPart s =? nG) && negb (ip_nPart s =? 1) && ((nG - ip_nPart s) mod 2 =? 1).
Lemma sm_init_iter_spec : forall mf nG A s ge1 aF1,
  sm_grow 260%nat mf (ip_remF s / ip_nPart s) A (ip_gs s - 1) 0 = (ge1, aF1) ->
  let ge2 := if ip_adj nG s ge1 then ge1 - 1 else ge1 in
  let aF2 := if ip_adj nG s ge1 then aF1 - zget mf ge1 else aF1 in
  sm_init_iter mf nG A s = SIP (sm_setrow (Z.to_nat A) (ip_len s) (ip_nPart s - 1) (ip_gs s) ge2 0) (ip_nPart s - 1) (ip_remF s - aF2) (ge2 + 1).
Proof.
  intros mf nG A s ge1 aF1 H. cbv zeta. unfold sm_init_iter. rewrite H. fold (ip_adj nG s ge1).
  destruct (ip_adj nG s ge1); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_mask31 : forall d, 0 <= d < 2147483648 -> Z.land d 18446744071562067969 = d mod 2.
Proof.
  intros d Hd.
  rewrite <- (Z.mod_small d (2^31)) at 1 by lia. rewrite <- (Z.land_ones d 31) by lia.
  rewrite <- Z.land_assoc. replace (Z.land (Z.ones 31) 18446744071562067969) with (Z.ones 1) by reflexivity.
  change (d mod 2) with (d mod 2^1). apply Z.land_ones. lia.
Qed.

(* [comment removed for export] *)
Lemma sm_nGroups_lt200 : forall n, n < 200 -> sm_nGroups n = 2.
Proof. intros n H. unfold sm_nGroups. replace (n <? 200) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma sm_nGroups_lt600 : forall n, 200 <= n < 600 -> sm_nGroups n = 3.
Proof. intros n H. unfold sm_nGroups. replace (n <? 200) with false by (symmetry; apply Z.ltb_ge; lia). replace (n <? 600) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma sm_nGroups_lt1200 : forall n, 600 <= n < 1200 -> sm_nGroups n = 4.
Proof. intros n H. unfold sm_nGroups. replace (n <? 200) with false by (symmetry; apply Z.ltb_ge; lia). replace (n <? 600) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (n <? 1200) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma sm_nGroups_ge1200 : forall n, 1200 <= n -> sm_nGroups n = (if n <? 2400 then 5 else 6).
Proof. intros n H. unfold sm_nGroups. replace (n <? 200) with false by (symmetry; apply Z.ltb_ge; lia). replace (n <? 600) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (n <? 1200) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

End ACeilS1.
