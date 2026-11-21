(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (13 recorded proofs replaced by written proofs (CNT_nonneg, validc_cls, CNT_app and 10 more); Pamb_le_Pcap takes zstd_frame_info's proof, for this unit's Pcap). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Malloc MI_Inv MI_Cnt
  LB_Tables LB_Inv LB_Sum LB_Bound LB_StmtA LB_Raw LB_PCaps LB_Hist.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_PAmb () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6LB_Inv6zcountC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6LB_Sum=zcount_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_PAmb3CNTC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6MI_Cnt@size_to_class_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6ltb_ltK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes?andb_true_introK47Corelib4Init5Logic2or01C46Stdlib4Bool4Bool>orb_true_introc59OSSVerify5KrLib4Spec7LB_PAmb6validcC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec6LB_Sum:zcount_appC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec6LB_Sum;zcount_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6LB_Sum;zcount_consC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib4Spec7LB_PAmb>zcount_map_sndC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec6LB_Raw3LRXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z8eqb_reflC59OSSVerify5KrLib4Spec6LB_Raw4n63XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables:std_nestedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7std_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables4cmaxC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec9LB_Tables:In_classesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables<tab_basic_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables2S_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables8std_spanC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib4Spec6LB_Inv3CAPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz07C59OSSVerify5KrLib4Spec6LB_Raw8CAP_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;div_le_monoC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lC59OSSVerify5KrLib4Spec6LB_Sum;zsum_map_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MI_Inv4zsumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw9NCAP_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv4NCAPC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib4Spec6LB_Inv3PHIC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Tables7classesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z8ltb_specc59OSSVerify5KrLib4Spec7LB_PAmb4PambC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_PCaps4PcapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_PCaps4AMBCC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec6LB_Inv4PQOKC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib4Spec7LB_PAmb8PHI_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib4Spec7LB_PAmb<Pamb_le_PcapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_PCaps8PHI_PcapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_PCaps4RBIGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw7LBUDGETC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition CNT (c : Z) (S : list Z) : Z :=
  if c =? 63 then zcount (fun n => MMAP_THRESHOLD <=? n) S
  else zcount (fun n => negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? c)) S.

(* [comment removed for export] *)
Definition validc (c : Z) : bool := ((0 <=? c) && (c <? 48)) || (c =? 63).

Lemma CNT_nonneg c S : 0 <= CNT c S.
Proof. unfold CNT. destruct (c =? 63); apply zcount_nonneg. Qed.
Lemma validc_cls n : 0 <= n < MMAP_THRESHOLD -> validc (size_to_class n) = true.
Proof. intros Hn. pose proof (proj1 (size_to_class_ok n Hn)). unfold validc. apply orb_true_intro. left. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. Qed.
Lemma validc_63 : validc 63 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PAmb ()) [] "p;2g00EWj20Tg008Pg00ML'0o"). Qed.
Lemma CNT_app c A B : CNT c (A ++ B) = CNT c A + CNT c B.
Proof. unfold CNT. destruct (c =? 63); apply zcount_app. Qed.
Lemma CNT_perm c A B : Permutation A B -> CNT c A = CNT c B.
Proof. intros HP. unfold CNT. destruct (c =? 63); apply zcount_perm; exact HP. Qed.

(* [comment removed for export] *)
Lemma zcount_map_snd (p : Z -> bool) (X : list (bptr * Z)) : zcount (fun xb => p (snd xb)) X = zcount p (map snd X).
Proof. induction X as [|[b n] X IH]; [reflexivity|]. cbn [map snd]. rewrite !zcount_cons. cbn [snd]. rewrite IH. reflexivity. Qed.
Lemma LRX_CNT X c : 0 <= c < 48 -> LRX X c = CNT c (map snd X).
Proof.
  intros Hc. unfold LRX, CNT. replace (c =? 63) with false by (symmetry; apply Z.eqb_neq; lia).
  apply (zcount_map_snd (fun n => negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? c))).
Qed.
Lemma n63X_CNT X : n63X X = CNT 63 (map snd X).
Proof. unfold n63X, CNT. rewrite Z.eqb_refl. apply (zcount_map_snd (fun n => MMAP_THRESHOLD <=? n)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
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
Proof.
  pose proof (PHI_mono Pamb Pcap Pamb_le_Pcap) as M. pose proof PHI_Pcap as C.
  unfold RBIG, W in C. lia.
Qed.
