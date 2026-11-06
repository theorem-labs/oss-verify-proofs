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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decRet3 A0F_decCutsM A0F_decCutsE A0F_dec_U11A.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_dec_U11A.
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
  Hypothesis HRETP3 : A0F_RETP3 A Q.
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
  Let L24all := U11A_L24_all A AOK ASH Q F HFAST HSMALL.

  (* [comment removed for export] *)
  Lemma U11B_L23 : forall k, (0 <= k <= 255)%Z -> ((k < 255)%Z -> A0F_cut_L23 A Q F (k + 1)) -> A0F_cut_L23 A Q F k.
  Proof.
    intros k Hk NXT. unfold A0F_cut_L23. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    prep DM MU DP. cps_destruct DI as (EOB & ORIG & _ & CS). cps_pose EOB as (NBR & NB9 & SYMB & HIST & HDR).
    pose proof (eobF_psum_range L d k EOB ltac:(lia)) as PS0. pose proof (eobF_psum_range L d (k + 1) EOB ltac:(lia)) as PS1.
    pose proof (eobF_unz_range L d k EOB ltac:(lia)) as UZk.
    pose proof (cf_summed_val _ _ (k + 1) ltac:(lia) CS) as VAL. replace (k + 1 - 1)%Z with k in VAL by lia.
    pose proof (proj2 CS (k + 1)%Z ltac:(lia)) as CFk1. replace (k + 1 - 1)%Z with k in CFk1 by lia.
    pose proof (proj1 CS k ltac:(lia)) as CFk.
    rewrite psum_succ in PS1 by lia.
    unfold r_of in DR. dr_open. hide_all_but_atF [S + 1096; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 1096, S + 2124); (a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro.
    arun_to 0xa69a8%Z.
    pose proof (zw32_read a0segs m (S + 1096) (d_cftab d) 257 (k + 1) _ CF ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    astep. clear RD. rewrite ?CFk1.
    arun_to 0xa69b8%Z.
    zw32_sw CF (k + 1)%Z (zget (d_cftab d) (k + 1) + zget (d_cftab d) k)%Z
      ltac:(rewrite CFk1, CFk; rewrite unsigned_lit by lia; first [reflexivity | f_equal; lia]).
    rewrite (K_L23_step F L d s (k + 1)) in KQ by lia. replace (k + 1 - 1)%Z with k in KQ by lia.
    arun; if_cases K2; zify_cond_z K2.
    - pose proof (NXT ltac:(lia)) as NX. unfold A0F_cut_L23 in NX. revive_all MUL WML AOK.
      kq_fold. enter_cutF (NX L _ s JK_) DP.
      split; [apply eobF_set_cftab; exact EOB | split; [cbn; exact ORIG | split; [lia |]]].
      dmodel_cbn. apply (cf_summed_step' _ _ (k + 1)); [lia | exact CS | f_equal; f_equal; lia].
    - (* [comment removed for export] *)
      arun_to 0xa69ec%Z.
      replace (k + 1 + 1)%Z with 257%Z in KQ by lia. rewrite (K_L23_exit F L) in KQ.
      revive_all MUL WML AOK. kq_fold.
      enter_cutF (L24all _ _ _ JK_) DP.
      split; [apply eobF_set_cftab; exact EOB | split; [cbn; exact ORIG | split; [lia |]]].
      unfold cfps. dmodel_cbn. apply cf_summed_exit. replace 257%Z with (k + 1 + 1)%Z by lia. apply (cf_summed_step' _ _ (k + 1)); [lia | exact CS | f_equal; f_equal; lia].
  Qed.
  Lemma U11B_L23_all : A0F_cut_L23 A Q F 0.
  Proof.
    assert (G : forall k : nat, (k <= 255)%nat -> A0F_cut_L23 A Q F (255 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply U11B_L23; [lia| intros; exfalso; lia].
      - apply U11B_L23; [lia| intros _]. replace (255 - Z.of_nat (Datatypes.S k) + 1)%Z with (255 - Z.of_nat k)%Z by lia. apply IH. lia. }
    exact (G 255%nat ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma U11B_L22 : forall k, (0 <= k <= 255)%Z -> ((k < 255)%Z -> A0F_cut_L22 A Q F (k + 1)) -> A0F_cut_L22 A Q F k.
  Proof.
    intros k Hk NXT. unfold A0F_cut_L22. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    prep DM MU DP. cps_destruct DI as (EOB & ORIG & _ & CC). cps_pose EOB as (NBR & NB9 & SYMB & HIST & HDR).
    pose proof (eobF_unz_range L d k EOB ltac:(lia)) as UZk. pose proof (proj1 CC) as CF0.
    unfold r_of in DR. dr_open.
    hide_all_but_atF [S + 68; S + 1096; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 1096, S + 2124)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro.
    arun_to 0xa693c%Z.
    pose proof (zw32_read a0segs m (S + 68) (d_unzftab d) 256 k _ DRunz ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    astep. clear RD.
    arun_to 0xa6944%Z.
    zw32_sw CF (k + 1)%Z (zget (d_unzftab d) (k + 1 - 1))%Z
      ltac:(replace (k + 1 - 1)%Z with k by lia; rewrite unsigned_lit by lia; reflexivity).
    rewrite (K_L22_step F L d s (k + 1)) in KQ by lia.
    arun; if_cases K2; zify_cond_z K2.
    - pose proof (NXT ltac:(lia)) as NX. unfold A0F_cut_L22 in NX. revive_all MUL WML AOK.
      kq_fold. enter_cutF (NX L _ s JK_) DP.
      split; [apply eobF_set_cftab; exact EOB | split; [cbn; exact ORIG | split; [lia |]]].
      dmodel_cbn. apply (cf_copied_step' _ _ (k + 1)); [lia | exact CC | reflexivity].
    - (* [comment removed for export] *)
      arun_to 0xa6988%Z.
      lazymatch goal with CFn : u32arr _ ?mm (S + 1096)%Z (zw32 ?a _) |- _ =>
        pose proof (zw32_read a0segs mm (S + 1096) a 257 0 _ CFn ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
      rewrite zget_zset_other in RD by lia. rewrite CF0 in RD.
      astep. clear RD.
      arun_to 0xa6998%Z.
      replace (k + 1 + 1)%Z with 257%Z in KQ by lia. rewrite (K_L22_exit F L) in KQ.
      revive_all MUL WML AOK. kq_fold.
      change (Z_to_bv 64 0) with (Z_to_bv 64 (psum (zget (d_unzftab d)) 0)) at 1.
      enter_cutF (U11B_L23_all _ _ _ JK_) DP.
      split; [apply eobF_set_cftab; exact EOB | split; [cbn; exact ORIG | split; [lia |]]].
      dmodel_cbn. apply cf_summed_1. replace 257%Z with (k + 1 + 1)%Z by lia. apply (cf_copied_step' _ _ (k + 1)); [lia | exact CC | reflexivity].
  Qed.
  Lemma U11B_L22_all : A0F_cut_L22 A Q F 0.
  Proof.
    assert (G : forall k : nat, (k <= 255)%nat -> A0F_cut_L22 A Q F (255 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply U11B_L22; [lia| intros; exfalso; lia].
      - apply U11B_L22; [lia| intros _]. replace (255 - Z.of_nat (Datatypes.S k) + 1)%Z with (255 - Z.of_nat k)%Z by lia. apply IH. lia. }
    exact (G 255%nat ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma U11B_L21 : forall i, (0 <= i <= 255)%Z -> ((i < 255)%Z -> A0F_cut_L21 A Q F (i + 1)) -> A0F_cut_L21 A Q F i.
  Proof.
    intros i Hi NXT. unfold A0F_cut_L21. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    prep DM MU DP. cps_destruct DI as (EOB & ORIG & _). cps_pose EOB as (NBR & NB9 & SYMB & HIST & HDR).
    pose proof (eobF_unz_range L d i EOB ltac:(lia)) as UZi.
    unfold r_of in DR. dr_open.
    hide_all_but_atF [S + 68; S + 1096; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 1096, S + 2124); (a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro.
    arun_to 0xa68ac%Z.
    pose proof (zw32_read a0segs m (S + 68) (d_unzftab d) 256 i _ DRunz ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    astep. clear RD.
    arun; if_cases K1; [ zify_cond_z K1; exfalso; lia | ].
    arun; if_cases K1'; [ zify_cond_z K1'; exfalso; lia | ].
    rewrite (K_L21_pass F L d s i) in KQ by lia.
    arun; if_cases K2; zify_cond_z K2.
    - pose proof (NXT ltac:(lia)) as NX. unfold A0F_cut_L21 in NX. revive_all MUL WML AOK.
      kq_fold. enter_cutF (NX L _ s JK_) DP.
      split; [exact EOB | split; [exact ORIG | lia]].
    - (* [comment removed for export] *)
      arun_to 0xa690c%Z.
      zw32_sw CF 0%Z 0%Z ltac:(reflexivity).
      arun_to 0xa691c%Z. sh_norm.
      replace (i + 1)%Z with 256%Z in KQ by lia. rewrite (K_L21_exit F L d s) in KQ.
      revive_all MUL WML AOK. kq_fold.
      enter_cutF (U11B_L22_all _ _ _ JK_) DP.
      split; [apply eobF_set_cftab; exact EOB | split; [cbn; exact ORIG | split; [lia |]]].
      dmodel_cbn. apply cf_copied_1.
  Qed.
  Lemma U11B_L21_all : A0F_cut_L21 A Q F 0.
  Proof.
    assert (G : forall k : nat, (k <= 255)%nat -> A0F_cut_L21 A Q F (255 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply U11B_L21; [lia| intros; exfalso; lia].
      - apply U11B_L21; [lia| intros _]. replace (255 - Z.of_nat (Datatypes.S k) + 1)%Z with (255 - Z.of_nat k)%Z by lia. apply IH. lia. }
    exact (G 255%nat ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U11_HEOB : A0F_cut_HEOB A Q F.
  Proof.
    unfold A0F_cut_HEOB. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    prep DM MU DP. destruct DI as [ML EOBsym]. pose proof (eobF_of_ML L d ML) as EOB. cps_pose EOB as (NBR & NB9 & SYMB & HIST & HDR).
    pose proof (alpha_ok_state L d (proj1 ML)) as NST.
    cps_pose HDR as (_ & _ & OPR).
    unfold r_of in DR. dr_open. hide_all_but_atF [S; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro. unfold K_HEOB in KQ. rewrite (K_HEOB_eq F L d s) in KQ.
    (* [comment removed for export] *)
    arun; if_cases K1; [ zify_cond_z K1; exfalso; lia | ]. zify_cond_z K1.
    arun; if_cases K2; zify_cond_z K2.
    - (* [comment removed for export] *)
      rewrite if_trueP in KQ by blia.
      arun_to 0xa7450%Z. revive_all MUL WML AOK.
      kq_fold. enter_cutF (HRETP3 _ _ _ _ JK_) DP; [ ret_nb | apply dpost14_ne; dmodel_cbn; exact NST ].
    - rewrite if_falseP in KQ by blia.
      (* [comment removed for export] *)
      arun_to 0xa689c%Z. sh_norm.
      revive_all MUL WML AOK. kq_fold.
      enter_cutF (U11B_L21_all _ _ _ JK_) DP. split; [exact EOB | split; [lia | lia]].
  Qed.
End R.

(* [comment removed for export] *)
Lemma A0F_dec_U11 : forall A, act_ok AIHI0 A -> act_sh DI_A0 A -> forall Q, A0F_RETP3 A Q -> forall F,
  A0F_cut_HFAST A Q F -> A0F_cut_HSMALL A Q F -> A0F_cut_HEOB A Q F.
Proof. intros A AOK ASH Q HP3 F HF HS. exact (A0F_U11_HEOB A AOK ASH Q HP3 F HF HS). Qed.
End ACeilS1.
