(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (cfg_eqv_refl, cfg_eqv_trans, silent_loop_eqv and 1 more); sys_rob_eqv added: RomBase.sys_rob carries over cfg_eqv, for srealizes_eqv's node case; imports RomBase). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import SimInv ShapeAlg DivergeSim SpinAlg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import RegsEqv0.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import RomBase.
Ltac2 kr_t_SrzEqv () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init6Specif9proj1_sigC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC59OSSVerify5KrLib2AS8RegsEqv07cfg_eqvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC59OSSVerify5KrLib2AS8RegsEqv06ms_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib2AS8RegsEqv0;ms_eqv_reflC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib2AS8RegsEqv0<ms_eqv_transC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C59OSSVerify5KrLib2AS8RegsEqv0Csstep_cfg_eqv0_scfgC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS8RegsEqv06to_eqvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02C59OSSVerify5KrLib2AS:DivergeSim;silent_loopC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC59OSSVerify5KrLib2AS8RegsEqv09regs_eqv0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC59OSSVerify5KrLib2AS8RegsEqv08regs_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib2AS8RegsEqv0Cmi_account_step_eqvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SpinAlgEsrealizes_of_realizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS6SrzEqv=srealizes_eqvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SpinAlgErealizes_of_srealizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib2AS8RegsEqv0=regs_eqv_reflC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Instance srz_fx_as : OSSVerify.Proofs.zstd.huf_decompress.lib.AS.PropExec.FPState := OSSVerify.Proofs.zstd.huf_decompress.lib.AS.PropExec.fx0.
Local Instance srz_fx_lib : OSSVerify.Proofs.zstd.huf_decompress.lib.Lib.PropExec.FPState := OSSVerify.Proofs.zstd.huf_decompress.lib.Lib.PropExec.fx0.
Import ListNotations.

Section WithSegs.
Variable segs : list Segment.

Lemma cfg_eqv_refl : forall c, cfg_eqv c c.
Proof. intros [ms mo]. split; [apply ms_eqv_refl | reflexivity]. Qed.

Lemma cfg_eqv_trans : forall a b c, cfg_eqv a b -> cfg_eqv b c -> cfg_eqv a c.
Proof.
  intros [? ?] [? ?] [? ?] [H1 H2] [G1 G2]; cbn in *. split; [eapply ms_eqv_trans; eassumption | etransitivity; eassumption].
Qed.

(* [comment removed for export] *)
Lemma sstep_next_eqv : forall c c' e c2,
  cfg_eqv c c' -> sstep_cfg segs ACFG c e (SNext c2) -> exists c2', sstep_cfg segs ACFG c' e (SNext c2') /\ cfg_eqv c2 c2'.
Proof.
  intros c c' e c2 Heqv Hss.
  destruct (sstep_cfg_eqv0_scfg segs ACFG c c' e (SNext c2) Heqv Hss) as (X' & Hss' & HX).
  destruct X' as [c2'| ]; cbn in HX; [|contradiction].
  exists c2'. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma silent_loop_eqv : forall P : config -> Prop,
  silent_loop segs P -> silent_loop segs (fun d => exists c, P c /\ cfg_eqv c d).
Proof.
  intros P HL d (c & HP & Heqv).
  destruct (HL c HP) as (Hh & Hsvc & ms1 & mo1 & Hacc & HP1).
  destruct c as [ms mo]; destruct d as [ms' mo']. destruct Heqv as [Hms Hmo]; cbn in *. subst mo'.
  pose proof Hms as (_ & _ & _ & Hsv & _ & _ & _ & _).
  split; [exact Hh|]. split; [congruence|].
  pose proof (mi_account_step_eqv segs ms ms' mo Hms) as K. rewrite Hacc in K.
  destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |]; try contradiction.
  destruct K as [Heq <-].
  exists ms1', mo1. split; [reflexivity|]. exists (mkCfg ms1 mo1). split; [exact HP1|]. split; [exact Heq | reflexivity].
Qed.
(* LPS 727298f3: [srz_node] asks [RomBase.sys_rob]; an equivalent configuration has the same
   memory, backing, pending call and model, and the same argument registers ([sys_input_eqv]) *)
#[using="Type"] Lemma sys_rob_eqv : forall c c', sys_rob segs c -> cfg_eqv c c' -> sys_rob segs c'.
Proof.
  intros [ms mo] [ms' mo'] Hrob [Hms Hmo] r x8 Hr Hs o. cbn [cfg_ms cfg_model] in *. subst mo'.
  pose proof Hms as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  assert (Hw : ms_eqv (wrom ms r) (wrom ms' r)) by (repeat split; first [assumption | reflexivity]).
  rewrite <- (sys_input_eqv segs _ _ x8 Hw), <- (sys_input_eqv segs _ _ x8 Hms).
  apply (Hrob r x8); [intros a b E; apply Hr; rewrite <- H8; exact E | exact (eq_trans H4 Hs)].
Qed.

Theorem srealizes_eqv : forall c T, srealizes segs c T -> forall c', cfg_eqv c c' -> srealizes segs c' T.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq]; intros c' Heqv.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct Hnode as [Hfwd Hexact].
    set (I' := { p : I * config | sstep_cfg segs ACFG c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
    destruct (sstep_next_eqv c c' (evs i0) (nx i0) Heqv (Hfwd i0)) as (c20 & Hs0 & He0).
    pose (q0 := (exist _ (i0, c20) (conj Hs0 He0) : I')).
    apply (srz_conseq segs c' (t_alt (fun q : I' => t_emit (evs (fst (proj1_sig q))) (T (fst (proj1_sig q)))))).
    + apply (srz_node segs c' I' (fun q => evs (fst (proj1_sig q))) (fun q => snd (proj1_sig q))
                      (fun q => T (fst (proj1_sig q))) q0).
      2:{ exact (sys_rob_eqv c c' Hrob Heqv). }
      * split.
        -- intros [[i c2] [Hs He]]. cbn. exact Hs.
        -- intros e st Hss.
           destruct (sstep_cfg_eqv0_scfg segs ACFG c' c e st (cfg_eqv_sym c c' Heqv) Hss) as (X & HssX & HX).
           destruct (Hexact e X HssX) as (j & -> & ->).
           destruct st as [c2|]; cbn in HX; [|contradiction].
           exists (exist _ (j, c2) (conj Hss (cfg_eqv_sym _ _ HX))). cbn. split; reflexivity.
      * intros [[i c2] [Hs He]]. cbn. exact (IH i c2 He).
    + (* [comment removed for export] *)
      intros tr. split.
      * intros [[[i c2] [Hs He]] Ht]. cbn in Ht. exists i. exact Ht.
      * intros [i Ht].
        destruct (sstep_next_eqv c c' (evs i) (nx i) Heqv (Hfwd i)) as (c2 & Hs & He).
        exists (exist _ (i, c2) (conj Hs He)). cbn. exact Ht.
  - (* [comment removed for export] *)
    apply srz_halt. destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hh.
  - (* [comment removed for export] *)
    eapply srz_conseq; [apply IH; exact Heqv | exact Heq].
Qed.

(* [comment removed for export] *)
Corollary realizes_eqv : forall c T, realizes segs c T -> forall c', cfg_eqv c c' -> realizes segs c' T.
Proof. intros c T H c' He. apply realizes_of_srealizes. exact (srealizes_eqv c T (srealizes_of_realizes segs c T H) c' He). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mkst_MS : forall R pc m ro,
  OSSVerify.Proofs.zstd.huf_decompress.lib.AS.PropExec.mkst R pc m ro = MS R bvmap_empty pc (Z_to_bv 32 0) None m ro.
Proof.
ltac2:(KReplay.run1 (kr_t_SrzEqv ()) ["WithSegs"] "h01Rh11mh22pch32rop;1p;2p;7g00ITj10Tg00e8j1:Tg00J9j11Tg00JWj12Tg003cj29Tg00K:j18Tg00e]j27Tg00fOj24Tg00K\j15Tg00g5j76Tg00:hj23Tg00^d#0R0#:#1R1%00#0R0#0#0R2#0#1#2R3'9%10#2#8\3R0g00<Rf31713f2%12g00gg'4%53f1f0F6'3X30W1X23W0o"). Qed.

Lemma cfg_eqv_regs : forall R R' F pc fc rv m ro mo,
  regs_eqv0 R R' -> cfg_eqv (mkCfg (MS R F pc fc rv m ro) mo) (mkCfg (MS R' F pc fc rv m ro) mo).
Proof.
  intros. split; [|reflexivity]. split; [assumption|]. split; [apply regs_eqv_refl|]. repeat split; reflexivity.
Qed.

End WithSegs.
