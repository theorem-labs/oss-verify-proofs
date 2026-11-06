(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Exec Step Frame RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import Divembc SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Import ShapeAlg.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Definition srz_at (md : Model) (T : TSet) : machine_state -> Prop :=
  fun ms => srealizes segs (mkCfg ms md) T.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Hulled.
Variable A : hull.
Hypothesis HA : H_off_segments segs (hidc A).
Hypothesis Hwx : wx_segs_nowrap segs.

Let Hd := hidc A.

(* [comment removed for export] *)
Theorem acct_evt_restrict : forall (P : config -> Prop) AL E (Q : machine_state -> Prop) ms model,
  silent_closed segs P ->
  MInv A AL E model -> m_halted model = None ->
  evt segs Q (restrict Hd ms) ->
  (forall msr' model', Q msr' -> MInv A AL E model' -> same_but_materialized model model' ->
                       hclean Hd msr' ->
                       P (mkCfg (unrestrict Hd (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  (intros P AL E Q ms model HP HI Hh; (first [ intro dR_3; dex1 dR_3 as msr'; destruct dR_3 as [Hms HQ] | intro dR_3; dand3 dR_3 as msr' Hms HQ | intros (msr' & Hms & HQ) ]); intros K).
  eapply (acct_msteps_restrict_hull segs A HA Hwx P AL E ms msr' model HP HI Hh).
  - apply msteps_to_cat. exact Hms.
  - intros model' HI' Hsame Hcl. exact (K msr' model' HQ HI' Hsame Hcl).
Qed.

Theorem srz_evt_restrict : forall AL E (Q : machine_state -> Prop) ms model T,
  MInv A AL E model -> m_halted model = None ->
  evt segs Q (restrict Hd ms) ->
  (forall msr' model', Q msr' -> MInv A AL E model' -> same_but_materialized model model' ->
                       hclean Hd msr' ->
                       srealizes segs (mkCfg (unrestrict Hd (ms_mem ms) msr') model') T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
  intros AL E Q ms model T HI Hh Hev K.
  exact (acct_evt_restrict (fun c => srealizes segs c T) AL E Q ms model
           (silent_closed_srealizes segs T) HI Hh Hev K).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem ts_evt_restrict : forall AL E (Q : machine_state -> Prop) ms model,
  MInv A AL E model ->
  evt segs Q (restrict Hd ms) ->
  (forall msr' model', Q msr' -> MInv A AL E model' -> same_but_materialized model model' ->
                       hclean Hd msr' ->
                       to_spin segs (unrestrict Hd (ms_mem ms) msr') model') ->
  to_spin segs ms model.
Proof.
  (intros AL E Q ms model HI; (first [ intro dR_4; dex1 dR_4 as msr'; destruct dR_4 as [Hms HQ] | intro dR_4; dand3 dR_4 as msr' Hms HQ | intros (msr' & Hms & HQ) ]); intros K).
  eapply (ts_msteps_restrict_hull segs A HA Hwx AL E ms msr' model HI).
  - apply msteps_to_cat. exact Hms.
  - intros model' HI' Hsame Hcl. exact (K msr' model' HQ HI' Hsame Hcl).
Qed.

(* [comment removed for export] *)
Definition srz_at_r (AL : hull) (E : Z) (full : word -> option byte) (md : Model) (T : TSet)
    : machine_state -> Prop :=
  fun msr => forall model', MInv A AL E model' -> same_but_materialized md model' ->
             hclean Hd msr ->
             srealizes segs (mkCfg (unrestrict Hd full msr) model') T.

Lemma srz_go_restrict : forall AL E ms md T,
  MInv A AL E md -> m_halted md = None ->
  evt segs (srz_at_r AL E (ms_mem ms) md T) (restrict Hd ms) ->
  srealizes segs (mkCfg ms md) T.
Proof.
  intros AL E ms md T HI Hh Hev.
  eapply srz_evt_restrict; [exact HI | exact Hh | exact Hev |].
  intros msr' model' HQ HI' Hsame Hcl. exact (HQ model' HI' Hsame Hcl).
Qed.

Lemma srz_stop_restrict : forall AL E full md T msr,
  (forall model', MInv A AL E model' -> same_but_materialized md model' -> hclean Hd msr ->
             srealizes segs (mkCfg (unrestrict Hd full msr) model') T) ->
  evt segs (srz_at_r AL E full md T) msr.
Proof. intros AL E full md T msr H. apply evt_done. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End Hulled.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zrange_visible (H : word -> bool) (a n : Z) : Prop :=
  forall i, (0 <= i < n)%Z -> H (wa (a + i)) = false.

Lemma zrange_visible_hidc : forall (A : hull) lo hi a n,
  In (lo, hi) A -> (lo <= a)%Z -> (a + n <= hi)%Z -> (0 <= a)%Z -> (hi <= 2 ^ 64)%Z ->
  zrange_visible (hidc A) a n.
Proof.
  intros A lo hi a n Hin Hlo Hhi H0 Htop i Hi. unfold hidc. apply negb_false_iff.
  apply (in_hullb_intro A _ lo hi Hin). rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)

Section Seeding.
Variable H : word -> bool.

Lemma mrd_mrestrict_visible : forall m x,
  H x = false -> mrd segs (mrestrict H m) x = mrd segs m x.
Proof. intros m x Hx. unfold mrd, mrestrict. rewrite Hx. reflexivity. Qed.

(* [comment removed for export] *)

Lemma bytes_at_mrestrict : forall m a bs,
  zrange_visible H a (Z.of_nat (length bs)) ->
  bytes_at segs m a bs <-> bytes_at segs (mrestrict H m) a bs.
Proof.
  intros m a bs Hv. unfold bytes_at. split; ((first [ intro dR_5; dand3 dR_5 as H0 Htop Hb | intros (H0 & Htop & Hb) ])); (split; [exact H0|]); (split; [exact Htop|]);
    intros i Hi; specialize (Hb i Hi).
  - rewrite mrd_mrestrict_visible; [exact Hb | apply Hv; lia].
  - rewrite mrd_mrestrict_visible in Hb; [exact Hb | apply Hv; lia].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma munrestrict_visible : forall full m x,
  H x = false -> munrestrict H full m x = m x.
Proof. intros full m x Hx. unfold munrestrict. rewrite Hx. reflexivity. Qed.

Lemma munrestrict_hidden : forall full m x,
  H x = true -> munrestrict H full m x = full x.
Proof. intros full m x Hx. unfold munrestrict. rewrite Hx. reflexivity. Qed.

Lemma bytes_at_munrestrict : forall full m a bs,
  zrange_visible H a (Z.of_nat (length bs)) ->
  bytes_at segs m a bs <-> bytes_at segs (munrestrict H full m) a bs.
Proof.
  intros full m a bs Hv. unfold bytes_at, mrd. split; ((first [ intro dR_8; dand3 dR_8 as H0 Htop Hb | intros (H0 & Htop & Hb) ])); (split; [exact H0|]); (split; [exact Htop|]);
    intros i Hi; specialize (Hb i Hi).
  - rewrite munrestrict_visible; [exact Hb | apply Hv; lia].
  - rewrite munrestrict_visible in Hb; [exact Hb | apply Hv; lia].
Qed.

Lemma wr_at_munrestrict : forall full m a n,
  zrange_visible H a n ->
  wr_at segs m a n <-> wr_at segs (munrestrict H full m) a n.
Proof.
  intros full m a n Hv. unfold wr_at, wview. split; ((first [ intro dR_9; dand3 dR_9 as H0 Htop Hw | intros (H0 & Htop & Hw) ])); (split; [exact H0|]); (split; [exact Htop|]);
    intros i Hi; specialize (Hw i Hi).
  - rewrite munrestrict_visible; [exact Hw | apply Hv; lia].
  - rewrite munrestrict_visible in Hw; [exact Hw | apply Hv; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End Seeding.

(* [comment removed for export] *)
Section ReRestrict.
Variable H : word -> bool.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mrestrict_clean_id : forall m,
  (forall x, H x = true -> m x = None) -> mrestrict H m = m.
Proof.
  intros m Hc. apply functional_extensionality. intros x. unfold mrestrict.
  destruct (H x) eqn:Hx; [symmetry; exact (Hc x Hx) | reflexivity].
Qed.

Lemma mrestrict_munrestrict' : forall full m, mrestrict H (munrestrict H full m) = mrestrict H m.
Proof. intros. apply mrestrict_munrestrict. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End ReRestrict.

(* [comment removed for export] *)
Lemma restrict_MS : forall Hh R F pc fc rv m ro,
  restrict Hh (MS R F pc fc rv m ro) = MS R F pc fc rv (mrestrict Hh m) ro.
Proof. reflexivity. Qed.

Lemma unrestrict_MS : forall Hh full R F pc fc rv m ro,
  unrestrict Hh full (MS R F pc fc rv m ro) = MS R F pc fc rv (munrestrict Hh full m) ro.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma unrestrict_MSsvc : forall Hh full R F pc x8 fc rv m ro,
  unrestrict Hh full (MSsvc R F pc x8 fc rv m ro) = MSsvc R F pc x8 fc rv (munrestrict Hh full m) ro.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma advance_apply_MSsvc : forall R F pc x8 fc rv m ro r ws zs us cis,
  advance_past_svc (apply_effect (MSsvc R F pc x8 fc rv m ro) (mkEffectU r ws zs us [] cis))
  = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4) fc rv
       (apply_writes (apply_zeros (apply_unmaps m us) zs) ws) ro.
Proof. reflexivity. Qed.

Lemma advance_set_gpr0_MSsvc : forall R F pc x8 fc rv m ro r,
  advance_past_svc (set_gpr0 (MSsvc R F pc x8 fc rv m ro) r)
  = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4) fc rv m ro.
Proof. reflexivity. Qed.

Lemma ms_gpr_MSsvc : forall R F pc x8 fc rv m ro i,
  ms_gpr (MSsvc R F pc x8 fc rv m ro) i = reg_get R (Z_to_bv 5 (10 + Z.of_nat i)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

Arguments srz_at segs md T /.
Arguments srz_at_r segs A AL E full md T /.
