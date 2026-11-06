(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmStep PmKeep PnLayout PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNKP.

Section Agree.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable AN : PNL.pn_addrs.
Hypothesis WF : PNST.addrs_wf A AN.

(* [comment removed for export] *)
Definition edep (a : Z) : Prop :=
  (pa_errcat_guard A <= a < pa_errcat_guard A + 2) \/ (pa_atexit A <= a < pa_atexit A + 544)
  \/ (exists iv, In iv (PNL.pn_d128_foot AN) /\ fst iv <= a < snd iv).

Section MM.
Variables M M' : word -> option byte.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> edep a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).

Lemma clear_e lo hi : 0 <= lo -> hi < 2 ^ 47 -> (forall a, lo <= a < hi -> edep a) -> L5.img_clear M lo hi -> L5.img_clear M' lo hi.
Proof. intros Hlo Hhi D C i Hi. rewrite AG; [apply C; exact Hi| lia| apply D; exact Hi]. Qed.
Lemma u8_e a v : 0 <= a < 2 ^ 47 -> edep a -> L5.u8_at segs M a v -> L5.u8_at segs M' a v.
Proof. intros Ha D. apply (L5C.u8_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG; [lia|]. replace i with a by lia. exact D. Qed.
Lemma u32_e a v : 0 <= a < 2 ^ 47 -> (forall i, a <= i < a + 4 -> edep i) -> L5.u32_at segs M a v -> L5.u32_at segs M' a v.
Proof.
  intros Ha D H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat a); [exact H|lia|cbn; lia|].
  intros i Hi. apply AG; [cbn in Hi; lia|]. apply D. cbn in Hi. lia.
Qed.
Lemma u64_e a v : 0 <= a < 2 ^ 47 -> (forall i, a <= i < a + 8 -> edep i) -> L5.u64_at segs M a v -> L5.u64_at segs M' a v.
Proof. intros Ha D. apply (L5C.u64_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG; [lia|]. apply D. exact Hi. Qed.
Lemma vstr_e o s : 0 <= o < 2 ^ 40 -> (forall i, o <= i < o + 24 -> edep i) -> (exists n, s = PM.VShort n) ->
  PM.vstr_at segs (fun _ _ _ => True) M o s -> PM.vstr_at segs (fun _ _ _ => True) M' o s.
Proof.
  intros Ho D (n0 & E) H.
  apply (PMF.vstr_at_agree segs M M' o s); [lia|lia| |intros c n p E'; congruence| exact H].
  intros i Hi. apply AG; [lia| apply D; exact Hi].
Qed.

Local Ltac cde tac := lazymatch goal with |- L5.img_clear _ ?lo ?hi => apply (clear_e lo hi); [lia| lia| tac| try assumption] end.

Lemma slots_e X l : 0 <= X < 2 ^ 40 -> (forall a, X <= a < X + 544 -> edep a) ->
  forall i, 0 <= i -> i + Z.of_nat (length l) <= 32 -> PNST.slots_at segs M X i l -> PNST.slots_at segs M' X i l.
Proof.
  intros HX D. induction l as [|[f a] r IH]; intros i Hi Hl; cbn [PNST.slots_at]; [tauto|].
  cbn [length] in Hl. rewrite Nat2Z.inj_succ in Hl. intros (F & Ar & S). split; [|split].
  - apply u64_e; [lia| intros; apply D; lia| exact F].
  - apply u64_e; [lia| intros; apply D; lia| exact Ar].
  - apply (IH (i + 1)); [lia| lia| exact S].
Qed.

Lemma batexit_agree ax : PNST.batexit_st segs A AN M ax -> PNST.batexit_st segs A AN M' ax.
Proof.
  pose proof (PMST.aw_atexit A (PNST.aw_j A AN WF)) as HX.
  assert (D : forall a, pa_atexit A <= a < pa_atexit A + 544 -> edep a) by (intros; right; left; lia).
  unfold PNST.batexit_st. cbv zeta.
  (* [comment removed for export] *)
  assert (LEN : Z.of_nat (length (PNST.bax_drv AN :: PNST.bax_list A AN ax)) <= 4) by (destruct ax; cbn; lia).
  assert (LEN1 : 1 <= Z.of_nat (length (PNST.bax_drv AN :: PNST.bax_list A AN ax))) by (cbn [length]; lia).
  intros (C1 & S & C2 & H & C3 & SL & C4 & C5).
  split; [cde ltac:(intros; apply D; lia)|].
  split; [apply u32_e; [lia| intros; apply D; lia| exact S]|].
  split; [cde ltac:(intros; apply D; lia)|].
  split; [apply u64_e; [lia| intros; apply D; lia| exact H]|].
  split; [cde ltac:(intros; apply D; lia)|].
  split; [apply (slots_e (pa_atexit A) (PNST.bax_drv AN :: PNST.bax_list A AN ax)); [lia| exact D| lia| lia| exact SL]|].
  split; cde ltac:(intros; apply D; lia).
Qed.

Lemma in_d128 iv a : In iv (PNL.pn_d128_foot AN) -> fst iv <= a < snd iv -> edep a.
Proof. intros Hin H. right. right. exists iv. split; assumption. Qed.

Lemma bdec_agree d : PNST.bdec_ok segs AN M d -> PNST.bdec_ok segs AN M' d.
Proof.
  pose proof (PNST.aw_infg A AN WF). pose proof (PNST.aw_nang A AN WF). pose proof (PNST.aw_info A AN WF). pose proof (PNST.aw_nano A AN WF).
  assert (D1 : forall a, PNL.pn_inf_guard AN <= a < PNL.pn_inf_guard AN + 8 -> edep a).
  { intros a Ha. apply (in_d128 (PNL.pn_inf_guard AN, PNL.pn_inf_guard AN + 8)); [cbn; auto| cbn; lia]. }
  assert (D2 : forall a, PNL.pn_inf_obj AN <= a < PNL.pn_inf_obj AN + 24 -> edep a).
  { intros a Ha. apply (in_d128 (PNL.pn_inf_obj AN, PNL.pn_inf_obj AN + 24)); [cbn; auto| cbn; lia]. }
  assert (D3 : forall a, PNL.pn_nan_guard AN <= a < PNL.pn_nan_guard AN + 8 -> edep a).
  { intros a Ha. apply (in_d128 (PNL.pn_nan_guard AN, PNL.pn_nan_guard AN + 8)); [cbn; auto 6| cbn; lia]. }
  assert (D4 : forall a, PNL.pn_nan_obj AN <= a < PNL.pn_nan_obj AN + 24 -> edep a).
  { intros a Ha. apply (in_d128 (PNL.pn_nan_obj AN, PNL.pn_nan_obj AN + 24)); [cbn; auto 6| cbn; lia]. }
  unfold PNST.bdec_ok. destruct d.
  - intros (G1 & G2 & S1 & S2). split; [|split; [|split]].
    + apply u8_e; [lia| apply D1; lia| exact G1].
    + apply u8_e; [lia| apply D3; lia| exact G2].
    + destruct S1 as (S1a & S1b). split; [apply u8_e; [lia| apply D2; lia| exact S1a]|].
      apply (L5C.defined_agree M M'); [| exact S1b]. intros i Hi. apply AG; [lia| apply D2; lia].
    + destruct S2 as (S2a & S2b). split; [apply u8_e; [lia| apply D4; lia| exact S2a]|].
      apply (L5C.defined_agree M M'); [| exact S2b]. intros i Hi. apply AG; [lia| apply D4; lia].
  - intros (C1 & C2 & C3 & C4). split; [|split; [|split]].
    + cde ltac:(intros; apply D1; lia).
    + cde ltac:(intros; apply D3; lia).
    + cde ltac:(intros; apply D2; lia).
    + cde ltac:(intros; apply D4; lia).
Qed.

Lemma berr_agree ax : PNST.berr_ok segs A AN M ax -> PNST.berr_ok segs A AN M' ax.
Proof.
  pose proof (PMST.aw_errg A (PNST.aw_j A AN WF)) as Heg.
  intros (ERG & DEC & ATX). split; [|split; [apply bdec_agree; exact DEC| apply batexit_agree; exact ATX]].
  destruct (PNST.bax_cat ax).
  - apply u8_e; [lia| left; lia| exact ERG].
  - cde ltac:(intros; left; lia).
Qed.
End MM.
End Agree.

(* [comment removed for export] *)
Section Keep.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AN : PNL.pn_addrs.
Variable L : heap_layout.
Hypothesis KL : PMK.klayout segs L.
Hypothesis SF : PMKP.sfoot A L.
Hypothesis WF : PNST.addrs_wf A AN.
Hypothesis SFN : forall iv a, In iv (PNL.pn_d128_foot AN) -> fst iv <= a < snd iv -> PMKP.cstatic L a.

Lemma edep_cstatic a : edep A AN a -> PMKP.cstatic L a.
Proof.
  intros [H|[H|(iv & Hin & H)]].
  - apply (PMKP.sf_foot A L SF (pa_errcat_guard A, pa_errcat_guard A + 2)); [unfold pm_foot; cbn; auto| cbn; lia].
  - apply (PMKP.sf_foot A L SF (pa_atexit A, pa_atexit A + 544)); [|cbn; lia].
    unfold pm_foot. cbn [app]. right. right. apply in_or_app. right. cbn. auto.
  - apply (SFN iv a Hin H).
Qed.

Lemma berr_ok_keep LB sp scr W M M' ax : PMK.ek L LB sp scr W M M' ->
  (forall a, edep A AN a -> L5.outside W a) ->
  PNST.berr_ok segs A AN M ax -> PNST.berr_ok segs A AN M' ax.
Proof.
  intros E OW. apply (berr_agree segs A AN WF M M'). intros a Ha D.
  apply E. apply (PMKP.kept_cstatic segs L KL); [apply edep_cstatic; exact D| apply OW; exact D].
Qed.
End Keep.
End PNKP.
