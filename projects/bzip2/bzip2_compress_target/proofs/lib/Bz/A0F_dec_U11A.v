(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzDU5 BzDUM BzDU11 DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decCutsE.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsE.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast FLiaA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecTac2.
Local Ltac AsanKit.a_norm ::= DecTac2.lit_store_fix.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.
  Hypothesis HFAST : A0F_cut_HFAST A Q F.
  Hypothesis HSMALL : A0F_cut_HSMALL A Q F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prep DM MU DP :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold_W14 MU; open_ash ASH AOK;
    lazymatch goal with H : sanchor (b_s _) (a_shs _) |- _ => pose proof (proj2 H : saddr (b_s (a_cx A)) (a_shs A)) as ANS0 end;
    open_dmemF DM; a0img.

  (* [comment removed for export] *)
  Lemma U11A_T : A0F_cut_T A Q F.
  Proof.
    unfold A0F_cut_T. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    prep DM MU DP. cps_destruct DI as (EOB & ORIG & CFP).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL. pose proof (dpureF_verb _ _ _ _ _ _ DP) as VERB.
    unfold r_of in DR. dr_open. hide_all_but_atF [S; S + 3152; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S, S + 68); (S + 3152, S + 3196)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro.
    (* [comment removed for export] *)
    arun_to 0xa6b40%Z. astep. rewrite ?VERB.
    arun. rewrite SMALL.
    cell_mod32 MIDc 32%nat. change ((-1) mod 2 ^ 32)%Z with crc_init in MIDc.
    destruct (act_small01 _ _ AOK) as [SM|SM]; rewrite SM; AsanKit.a_lit_branch.
    - (* [comment removed for export] *)
      assert (SM0 : d_small d = 0%Z) by (rewrite SMALL; exact SM).
      rewrite (K_T_fast F L d s SM0) in KQ. unfold dT in KQ.
      revive_all MUL WML AOK. enter_sameF HFAST DP.
      apply dinv_HFAST_T; [exact EOB | exact ORIG | exact CFP | exact SM0].
    - (* [comment removed for export] *)
      assert (SM1 : d_small d = 1%Z) by (rewrite SMALL; exact SM).
      rewrite (K_T_small F L d s) in KQ by (rewrite SM1; discriminate). unfold dT in KQ.
      revive_all MUL WML AOK. enter_sameF HSMALL DP.
      apply dinv_HSMALL_T; [exact EOB | exact ORIG | exact CFP | exact SM1].
  Qed.

  (* [comment removed for export] *)
  Lemma U11A_L25 : forall i, (1 <= i <= 256)%Z -> ((i < 256)%Z -> A0F_cut_L25 A Q F (i + 1)) -> A0F_cut_L25 A Q F i.
  Proof.
    intros i Hi NXT. unfold A0F_cut_L25. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    prep DM MU DP. cps_destruct DI as (EOB & ORIG & _ & CFP). cps_pose EOB as (NBR & NB9 & SYMB & HIST & HDR).
    pose proof (eobF_psum_range L d (i - 1) EOB ltac:(lia)) as PS0. pose proof (eobF_psum_range L d i EOB ltac:(lia)) as PS1.
    pose proof (psum_step_le (bsym d) (zget (d_unzftab d)) (Z.to_nat (sv_nblock L)) HIST (i - 1) ltac:(lia)) as MONO.
    replace (i - 1 + 1)%Z with i in MONO by lia.
    pose proof (CFP i ltac:(lia)) as CFi. pose proof (CFP (i - 1)%Z ltac:(lia)) as CFi1.
    unfold r_of in DR. dr_open. hide_all_but_atF [S + 1096; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro.
    arun_to 0xa6a74%Z.
    pose proof (zw32_read a0segs m (S + 1096) (d_cftab d) 257 (i - 1) _ CF ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    astep. clear RD. rewrite ?CFi1.
    arun_to 0xa6a7c%Z.
    pose proof (zw32_read a0segs m (S + 1096) (d_cftab d) 257 i _ CF ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    astep. clear RD. rewrite ?CFi.
    arun; if_cases K1; [ zify_cond_z K1; exfalso; lia | ].
    rewrite (K_L25_pass F L d s i) in KQ by first [lia | rewrite !CFP by lia; exact MONO].
    arun; if_cases K2; zify_cond_z K2.
    - pose proof (NXT ltac:(lia)) as NX. unfold A0F_cut_L25 in NX. revive_all MUL WML AOK.
      kq_fold. enter_cutF (NX L _ s JK_) DP. split; [exact EOB | split; [exact ORIG | split; [lia | exact CFP]]].
    - astep.
      rewrite (K_L25_exit F L d s) in KQ || (replace (i + 1)%Z with 257%Z in KQ by lia; rewrite (K_L25_exit F L d s) in KQ).
      revive_all MUL WML AOK. kq_fold. enter_cutF (U11A_T _ _ _ JK_) DP. split; [exact EOB | split; [exact ORIG | exact CFP]].
  Qed.
  Lemma U11A_L25_all : A0F_cut_L25 A Q F 1.
  Proof.
    assert (G : forall k : nat, (k <= 255)%nat -> A0F_cut_L25 A Q F (256 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply U11A_L25; [lia| intros; exfalso; lia].
      - apply U11A_L25; [lia| intros _]. replace (256 - Z.of_nat (Datatypes.S k) + 1)%Z with (256 - Z.of_nat k)%Z by lia. apply IH. lia. }
    exact (G 255%nat ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma U11A_L24 : forall i, (0 <= i <= 256)%Z -> ((i < 256)%Z -> A0F_cut_L24 A Q F (i + 1)) -> A0F_cut_L24 A Q F i.
  Proof.
    intros i Hi NXT. unfold A0F_cut_L24. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    prep DM MU DP. cps_destruct DI as (EOB & ORIG & _ & CFP). cps_pose EOB as (NBR & NB9 & SYMB & HIST & HDR).
    pose proof (eobF_psum_range L d i EOB ltac:(lia)) as PS1. pose proof (CFP i ltac:(lia)) as CFi.
    unfold r_of in DR. dr_open. hide_all_but_atF [S + 1096; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro.
    arun_to 0xa69fc%Z.
    pose proof (zw32_read a0segs m (S + 1096) (d_cftab d) 257 i _ CF ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    astep. clear RD. rewrite ?CFi.
    arun; if_cases K1; [ zify_cond_z K1; exfalso; lia | ].
    arun; if_cases K1'; [ zify_cond_z K1'; exfalso; lia | ].
    rewrite (K_L24_pass F L d s i) in KQ by first [lia | rewrite CFi; lia].
    arun; if_cases K2; zify_cond_z K2.
    - pose proof (NXT ltac:(lia)) as NX. unfold A0F_cut_L24 in NX. revive_all MUL WML AOK.
      kq_fold. enter_cutF (NX L _ s JK_) DP. split; [exact EOB | split; [exact ORIG | split; [lia | exact CFP]]].
    - (* [comment removed for export] *)
      arun_to 0xa6a54%Z.
      replace (i + 1)%Z with 257%Z in KQ by lia. rewrite (K_L24_exit F L d s) in KQ.
      revive_all MUL WML AOK. kq_fold.
      enter_cutF (U11A_L25_all _ _ _ JK_) DP. split; [exact EOB | split; [exact ORIG | split; [lia | exact CFP]]].
  Qed.
  Lemma U11A_L24_all : A0F_cut_L24 A Q F 0.
  Proof.
    assert (G : forall k : nat, (k <= 256)%nat -> A0F_cut_L24 A Q F (256 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply U11A_L24; [lia| intros; exfalso; lia].
      - apply U11A_L24; [lia| intros _]. replace (256 - Z.of_nat (Datatypes.S k) + 1)%Z with (256 - Z.of_nat k)%Z by lia. apply IH. lia. }
    exact (G 256%nat ltac:(lia)).
  Qed.
End R.
End ACeilS1.
