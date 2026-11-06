(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv.
From OSSVerify.Proofs.openssl.bignum.lib Require Import TopLevel Obligations TopLevelA TopE TopSides ProofBaseG.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim Driver Prog ModelInv Unforced LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section SidesG.
Context {LM : LibModel}.
Variable P : Z -> Z.
Variable T : list Z.
Variables NBLK BSZ : Z.
Variable linv : LS -> list (bptr * Z) -> Prop.
Hypothesis HP0 : forall c, 0 <= P c.
Hypothesis HC : caps_ok P T NBLK BSZ.
Hypothesis H_init : lwf (okT T) lib_init [] (fun ls Li => linv ls [] /\ subms (map snd Li) T).
Hypothesis H_one : forall ls d X, linv ls X -> zlength d <= MAX_INPUT ->
  lwf (okB NBLK BSZ) (lib_one ls d) X (fun r X' => linv (fst r) X').
Hypothesis H_rc : forall ls d, lleaves (lib_one ls d) (fun r => snd r = 0).

Theorem G_side : forall segs pc ph rstage lim,
  image_low segs -> KLIM + SMALLREQ <= lim -> implG_stmt segs pc ph rstage ->
  side_canon ncfg Tc (mkImage segs pc ph) lim.
Proof.
  intros segs pc ph rstage lim Hlow Hlim HI en inp He Hi.
  destruct (progG_model_ok_run P T NBLK BSZ linv HP0 HC H_init H_one H_rc segs rstage pc ph lim Hlow Hlim en inp He Hi) as [Hl Hs].
  destruct (run_of_tree segs pc ph lim (the_progG segs rstage inp en) (epost the_post) en inp (HI en inp He Hi) Hl Hs)
    as (Htr & Herr & _).
  split; [| exact Herr].
  intros tr. rewrite (Htr tr).
  exact (progG_det_gen P T NBLK BSZ linv HP0 HC H_init H_one H_rc segs rstage pc ph lim Hlow Hlim en inp He Hi tr).
Qed.

Corollary G_side_off : forall segs pc ph rstage lim,
  image_low segs -> KLIM + SMALLREQ <= lim -> implG_stmt segs pc ph rstage ->
  side_canon_off ncfg Tc (mkImage segs pc ph) lim.
Proof. intros. apply side_canon_off_of_either. eapply G_side; eassumption. Qed.

Section Pairs.
Variables (segsS : list Segment) (pcS : N) (phS : PhdrInfo) (rstageS : Z).
Hypothesis HlowS : image_low segsS.
Hypothesis HS : implG_stmt segsS pcS phS rstageS.

Section Same.
Variables (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (rstageT : Z).
Hypothesis HlowT : image_low segsT.
Hypothesis HT : implG_stmt segsT pcT phT rstageT.
Theorem pairG_scfg : strong_universal_error_free_T_scfg ncfg (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  exact (glue_scfg_e ncfg Tc _ _ (G_side segsS pcS phS rstageS _ HlowS lim_source_ok HS) (G_side segsT pcT phT rstageT _ HlowT lim_target_ok HT)).
Qed.
Theorem pairG_base : strong_universal_error_free_T_scfg_budgets ncfg ShippedBudgets.lim_source ShippedBudgets.lim_target
  (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  exact (glue_scfg_budgets_e ncfg Tc _ _ (G_side segsS pcS phS rstageS _ HlowS lim_source_ok HS) (G_side segsT pcT phT rstageT _ HlowT lim_target_ok HT)).
Qed.
End Same.

Section AsanFamily.
Variables (tsegs : list Segment) (tpc : N) (tph : PhdrInfo).
Hypothesis HA : S3s_stmt tsegs tpc tph.
Theorem pairGA_scfg : strong_universal_error_free_T_scfg ncfg (mkImage segsS pcS phS) (mkImage tsegs tpc tph).
Proof. exact (glue_scfg_e ncfg Tc _ _ (G_side segsS pcS phS rstageS _ HlowS lim_source_ok HS) (S_side _ _ _ HA)). Qed.
Theorem pairGA_base : strong_universal_error_free_T_scfg_budgets ncfg ShippedBudgets.lim_source ShippedBudgets.lim_target
  (mkImage segsS pcS phS) (mkImage tsegs tpc tph).
Proof. exact (glue_scfg_budgets_e ncfg Tc _ _ (G_side segsS pcS phS rstageS _ HlowS lim_source_ok HS) (S_side _ _ _ HA)). Qed.
End AsanFamily.
End Pairs.

End SidesG.
