(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg PropExec ShapeAlg SReach RegsEquivM.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import MState Frame.
(* [comment removed for export] *)
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section Eqv.
  Variable segs : list Segment.
  Context {SC : StepCfg}.

  Lemma cfg_eqv_refl : forall c, cfg_eqv c c.
  Proof. intros [ms mo]. split; [apply ms_eqv_refl | reflexivity]. Qed.

  Lemma cfg_eqv_trans : forall a b c, cfg_eqv a b -> cfg_eqv b c -> cfg_eqv a c.
  Proof. intros a b c [H1 H2] [H3 H4]. split; [eapply ms_eqv_trans; eassumption | congruence]. Qed.

  (* [comment removed for export] *)
  Theorem realizes_eqv : forall c T, realizes segs c T -> forall c', cfg_eqv c c' -> realizes segs c' T.
  Proof.
    intros c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros c' Heqv.
    - (* [comment removed for export] *)
      destruct Hnode as [N1 N2].
      set (I' := { p : I * config | sstep_cfg segs the_scfg c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
      assert (X0 : forall i, exists c2, sstep_cfg segs the_scfg c' (evs i) (SNext c2) /\ cfg_eqv (nx i) c2).
      { intros i. destruct (sstep_scfg_cfg_eqv segs the_scfg c c' (evs i) (SNext (nx i)) Heqv (N1 i)) as (X' & Hs & HX).
        destruct X' as [c2|]; cbn in HX; [|contradiction]. exists c2. auto. }
      destruct (X0 i0) as (c20 & Hs0 & He0).
      apply (rz_conseq segs _ (t_alt (fun p : I' => t_emit (evs (fst (proj1_sig p))) (T (fst (proj1_sig p)))))).
      + apply (rz_node segs c' I' (fun p => evs (fst (proj1_sig p))) (fun p => snd (proj1_sig p))
                 (fun p => T (fst (proj1_sig p))) (exist _ (i0, c20) (conj Hs0 He0))).
        * split.
          -- intros [[i c2] [Hs He]]. cbn. exact Hs.
          -- intros e st Hst.
             destruct (sstep_scfg_cfg_eqv segs the_scfg c' c e st (cfg_eqv_sym c c' Heqv) Hst) as (X' & Hs & HX).
             destruct (N2 e X' Hs) as (i & -> & ->).
             destruct st as [c2|]; cbn in HX; [|contradiction].
             exists (exist _ (i, c2) (conj Hst (cfg_eqv_sym _ _ HX))). cbn. auto.
        * intros [[i c2] [Hs He]]. cbn. apply (IH i). exact He.
      + (* [comment removed for export] *)
        intros tr. split.
        * intros [[[i c2] [Hs He]] Htr]. cbn in Htr. exists i. exact Htr.
        * intros [i Htr]. destruct (X0 i) as (c2 & Hs & He). exists (exist _ (i, c2) (conj Hs He)). cbn. exact Htr.
    - apply rz_halt. destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hh.
    - eapply rz_conseq; [apply IH; exact Heqv | exact Heq].
  Qed.

  (* [comment removed for export] *)
  Theorem sreach_eqv : forall (Q : config -> Prop) c, sreach segs Q c ->
    forall c', cfg_eqv c c' -> sreach segs (fun d => exists d0, Q d0 /\ cfg_eqv d0 d) c'.
  Proof.
    intros Q c H. induction H as [c HQ | c Hex Hsil Hk IH]; intros c' Heqv.
    - apply sr_done. exists c. auto.
    - apply sr_step.
      + destruct Hex as [c1 Hs]. destruct (sstep_scfg_cfg_eqv segs the_scfg c c' [] (SNext c1) Heqv Hs) as (X' & Hs' & HX).
        destruct X' as [c2|]; cbn in HX; [|contradiction]. exists c2. exact Hs'.
      + intros evs X Hst. destruct (sstep_scfg_cfg_eqv segs the_scfg c' c evs X (cfg_eqv_sym c c' Heqv) Hst) as (X' & Hs & HX).
        destruct (Hsil evs X' Hs) as [-> [c1 ->]]. split; [reflexivity|].
        destruct X as [c2|]; cbn in HX; [|contradiction]. exists c2. reflexivity.
      + intros evs c2 Hst. destruct (sstep_scfg_cfg_eqv segs the_scfg c' c evs (SNext c2) (cfg_eqv_sym c c' Heqv) Hst) as (X' & Hs & HX).
        destruct X' as [c1|]; cbn in HX; [|contradiction].
        apply (IH evs c1 Hs). apply cfg_eqv_sym. exact HX.
  Qed.

  (* [comment removed for export] *)
  Corollary sreach_eqv_closed : forall (Q : config -> Prop) c c',
    (forall d d', Q d -> cfg_eqv d d' -> Q d') ->
    cfg_eqv c c' -> sreach segs Q c -> sreach segs Q c'.
  Proof.
    intros Q c c' HQ Heqv H. eapply sreach_mono; [eapply sreach_eqv; eassumption|].
    intros d (d0 & H0 & He). eapply HQ; eassumption.
  Qed.
End Eqv.

(* [comment removed for export] *)
Lemma mkst_as_MS : forall R pc m rom,
  ms_eqv (mkst R pc m rom) (MS (mkR_of R) bvmap_empty pc (Z_to_bv 32 0) None m rom).
Proof.
  intros R pc m rom. unfold mkst, MS. split; [apply mkR_of_eqv|]. cbn. repeat split; try apply fregs_eqv_refl.
Qed.

Lemma getr_reg_get : forall R (r : reg), r <> 0%bv -> getr R r = reg_get R r.
Proof.
  intros R r Hr. unfold getr. destruct (bv_eqb r 0) eqn:E; [|reflexivity].
  exfalso. apply Hr. apply bv_eqb_eq. exact E.
Qed.

(* [comment removed for export] *)
Lemma mkR_of_getr : forall R,
  mkR_of R = mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
                 (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
                 (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31).
Proof. intros R. reflexivity. Qed.

(* [comment removed for export] *)
Lemma getr_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (r : reg),
  getr (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) r
  = nth (Z.to_nat (bv_unsigned r)) [Z_to_bv 64 0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20; x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31] (Z_to_bv 64 0).
Proof.
  intros. destruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.
