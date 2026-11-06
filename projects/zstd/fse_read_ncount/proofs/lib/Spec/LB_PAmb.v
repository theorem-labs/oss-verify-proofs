(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Malloc MI_Inv MI_Cnt
LB_Tables LB_Inv LB_Sum LB_Bound LB_StmtA LB_Raw LB_PCaps LB_Hist.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition validc (c : Z) : bool := ((0 <=? c) && (c <? 48)) || (c =? 63).
Lemma validc_cls n : 0 <= n < MMAP_THRESHOLD -> validc (size_to_class n) = true.
Proof. intros Hn. pose proof (proj1 (size_to_class_ok n Hn)). unfold validc. apply orb_true_intro. left. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. Qed.
Lemma validc_63 : validc 63 = true. Proof. reflexivity. Qed.
Lemma PHI_mono P P' : (forall c, P c <= P' c) -> PHI P <= PHI P'.
Proof.
intros HP. unfold PHI.
assert (A : zsum (map (fun c => if std_nested c then 0 else std_len c * ((CAP P c + 32) / cmax c)) classes)
<= zsum (map (fun c => if std_nested c then 0 else std_len c * ((CAP P' c + 32) / cmax c)) classes)).
{ apply zsum_map_le. intros c Hc. apply In_classes in Hc. pose proof (tab_basic_ok c Hc) as (SS & CM & SL & _).
destruct (std_nested c); [lia|]. apply Z.mul_le_mono_nonneg_l; [unfold std_span, UNIT in SL; nia|].
apply Z.div_le_mono; [lia|]. pose proof (CAP_mono P P' c HP). lia. }
pose proof (NCAP_mono P P' HP) as B.
assert (C : 5 * NCAP P / 101 <= 5 * NCAP P' / 101) by (apply Z.div_le_mono; lia).
unfold PGSZ. lia.
Qed.
Definition Pamb (c : Z) : Z := if validc c then AMBC else 0.
Lemma Pamb_le_Pcap c : Pamb c <= Pcap c.
Proof.
unfold Pamb, Pcap, validc. destruct (Z.eqb_spec c 63) as [->|N63]; [cbn; lia|].
destruct (Z.leb_spec 0 c); destruct (Z.ltb_spec c 48); cbn [andb orb]; lia.
Qed.
Lemma Pamb_amb c : validc c = true -> AMBC <= Pamb c.
Proof. intros H. unfold Pamb. rewrite H. lia. Qed.
Lemma Pamb_nonneg c : 0 <= Pamb c.
Proof. unfold Pamb, AMBC. destruct (validc c); lia. Qed.
Lemma Pamb_ok : PQOK Pamb.
Proof. vm_compute. split; discriminate. Qed.
Lemma PHI_Pamb : PHI Pamb <= LBUDGET.
Proof. pose proof (PHI_mono Pamb Pcap Pamb_le_Pcap). pose proof PHI_Pcap. unfold RBIG, W in *. lia. Qed.
