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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasMtf BzDU5 BzDUM BzDU10 DecAuxL DecTacF3 DecAux10F DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAuxL OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux10F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet DecTacSA A0F_decCutsM A0F_decCutsL A0F_dec_U10J.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsL OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_dec_U10J.
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
  Hypothesis HC : A0F_cut_HMTFC A Q F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation TT := (b_tt (a_cx A)).
  Notation L16 := (b_ll16 (a_cx A)).

  Ltac prep DM MU DP :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold_W14 MU; open_ash ASH AOK;
    lazymatch goal with H : sanchor (b_s _) (a_shs _) |- _ => pose proof (proj2 H : saddr (b_s (a_cx A)) (a_shs A)) as ANS0 end;
    open_dmemF DM; a0img.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac u10_facts MR DP :=
    let AL := fresh "AL" in let GR := fresh "GR" in let TB := fresh "TB" in let BL := fresh "BL" in let CU := fresh "CU" in
    let NST := fresh "NST" in let NBL := fresh "NBL" in let NBM := fresh "NBM" in let BN := fresh "BN" in
    let RP := fresh "RP" in let S0UR := fresh "S0UR" in
    lazymatch type of MR with ml_nomtfF ?L ?d =>
      cps_pose MR as (AL & GR & TB & BL & CU);
      pose proof (alpha_ok_state L d AL) as NST;
      assert (NBL : (0 <= sv_nblock L <= 900000)%Z) by (unfold alpha_ok in AL; tauto);
      assert (NBM : sv_nblockMAX L = (100000 * d_bs100k d)%Z) by (unfold grp_okF in GR; tauto);
      pose proof (dpureF_n _ _ _ _ _ _ DP) as BN; rewrite BN in NBM;
      pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP; unfold drep in RP;
      pose proof (fun i => proj1 (proj2 (proj2 (proj2 RP))) i) as S0UR; cbn beta in S0UR; clear RP
    end.
  (* [comment removed for export] *)
  Ltac fprep DM MU DP MR :=
    u10_facts MR DP; prep DM MU DP; lazymatch goal with D : drest_at _ _ _ _ |- _ => unfold r_of in D end; dr_open.
  (* [comment removed for export] *)
  Ltac mtfa_rdA MA i :=
    let RD := fresh "RD" in let BR := fresh "BR" in
    lazymatch goal with AR : u8arr _ ?mm (b_s (a_cx A) + 3724)%Z (zb8 ?a _) |- _ =>
      pose proof (MA i ltac:(lia)) as BR;
      pose proof (zb8_read1 a0segs mm _ a 4096 i _ AR ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD;
      repeat rewrite zget_zset_other in RD by lia;
      astep; clear RD; rewrite zxb_lit8 by lia end.
  Ltac mtfa_wrA i :=
    lazymatch goal with AR : u8arr _ ?mm (b_s (a_cx A) + 3724)%Z (zb8 ?a _) |- _ => zb8_sb AR i end.
  (* [comment removed for export] *)
  Ltac mtfb_rdA ROW i :=
    let RD := fresh "RD" in let E := fresh "ROWv" in
    lazymatch goal with AR : u32arr _ ?mm (b_s (a_cx A) + 7820)%Z (zw32 ?a _) |- _ =>
      pose proof (ROW i ltac:(lia)) as E;
      pose proof (zw32_read a0segs mm _ a 16 i _ AR ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD;
      astep; clear RD end.
  (* [comment removed for export] *)
  Ltac u10_side MR MA ROW :=
    lazymatch goal with
    | |- ml_nomtfF _ _ => repeat first [apply ml_nomtfF_set_mtfa | apply ml_nomtfF_set_mtfbase]; exact MR
    | |- mtfa_ok _ => rewrite ?d_mtfa_set_mtfa, ?d_mtfa_set_mtfbase; repeat (apply mtfa_ok_set; [ | first [ lia | apply MA; lia ] ]); exact MA
    | |- mbrow _ _ => try (repeat apply mbrow_set_mtfa; exact ROW)
    | |- _ => first [ assumption | lia | idtac ]
    end.

  Let LJ := A0F_U10_LJ A AOK ASH Q F HC.

  (* [comment removed for export] *)
  Lemma A0F_U10_LFZ : forall mb pp uc, A0F_cut_LFZ A Q F mb pp uc.
  Proof.
    intros mb pp uc. unfold A0F_cut_LFZ. intros until w720. intros DM FRL FRH AF ST MU WM MI DP MR MA MTI ROW NB UCR PP FU.
    fprep DM MU DP MR. pose proof (mtf_inv_bounds mb MTI 0 ltac:(lia)) as PPR.
    hide_all_but_atF [S + 3724; S + 7820; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 3724, S + 7820)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro. rewrite K_LFB_exit in KQ.
    arun_to 0xa6498%Z.
    mtfa_wrA pp. (* [comment removed for export] *)
    arun_to 0xa64a8%Z.
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ pp uc DP ltac:(lia)) as DP'.
    revive_all MUL WML AOK.
    pose proof (LJ uc mb) as NX. unfold A0F_cut_LJ in NX.
    kq_fold. enter_cutF (NX L _ s JK_) DP'; u10_side MR MA ROW.
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U10_LFB : forall mb pp uc k, ((2 <= k)%Z -> A0F_cut_LFB A Q F mb pp uc (k - 1)) -> A0F_cut_LFB A Q F mb pp uc k.
  Proof.
    intros mb pp uc k NXT. unfold A0F_cut_LFB. intros until w720. intros DM FRL FRH AF ST MU WM MI DP MR MA MTI ROW NB UCR PP K FU.
    fprep DM MU DP MR. pose proof (mtf_inv_bounds mb MTI 0 ltac:(lia)) as PPR.
    hide_all_but_atF [S + 3724; S + 7820; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 3724, S + 7820)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro. rewrite (K_LFB_step F L d s pp k uc) in KQ by lia.
    arun_to 0xa6448%Z.
    mtfa_rdA MA (pp + k - 1)%Z. (* [comment removed for export] *)
    arun_to 0xa6454%Z.
    mtfa_wrA (pp + k)%Z. (* [comment removed for export] *)
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (pp + k) (zget (d_mtfa d) (pp + k - 1)) DP ltac:(lia)) as DP'.
    arun; if_cases K2; zify_cond_z K2.
    - revive_all MUL WML AOK.
      pose proof (NXT ltac:(lia)) as NX. unfold A0F_cut_LFB in NX.
      kq_fold. enter_cutF (NX L _ s JK_) DP'; u10_side MR MA ROW.
    - astep. revive_all MUL WML AOK.
      pose proof (A0F_U10_LFZ mb pp uc) as NX. unfold A0F_cut_LFZ in NX.
      replace (k - 1)%Z with 0%Z in KQ by lia.
      kq_fold. enter_cutF (NX L _ s JK_) DP'; u10_side MR MA ROW.
  Qed.
  Lemma A0F_U10_LFB_all : forall mb pp uc k, (1 <= k <= 3)%Z -> A0F_cut_LFB A Q F mb pp uc k.
  Proof.
    intros mb pp uc k Hk.
    assert (G : forall n : nat, (n <= 2)%nat -> A0F_cut_LFB A Q F mb pp uc (1 + Z.of_nat n)%Z).
    { induction n as [|n IH]; intros Hn.
      - apply A0F_U10_LFB. intros; exfalso; lia.
      - apply A0F_U10_LFB. intros _. replace (1 + Z.of_nat (Datatypes.S n) - 1)%Z with (1 + Z.of_nat n)%Z by lia. apply IH. lia. }
    replace k with (1 + Z.of_nat (Z.to_nat (k - 1)))%Z by lia. apply G. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U10_LFA : forall mb pp uc mm, ((9 <= mm)%Z -> A0F_cut_LFA A Q F mb pp uc (mm - 4)) -> A0F_cut_LFA A Q F mb pp uc mm.
  Proof.
    intros mb pp uc mm NXT. unfold A0F_cut_LFA. intros until w720. intros DM FRL FRH AF ST MU WM MI DP MR MA MTI ROW NB UCR NSR PP MM FU.
    fprep DM MU DP MR. pose proof (mtf_inv_bounds mb MTI 0 ltac:(lia)) as PPR.
    hide_all_but_atF [S + 3724; S + 7820; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 3724, S + 7820)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro. rewrite (K_LFA_step F L d s pp (mm - 1) uc) in KQ by lia.
    replace (pp + (mm - 1))%Z with (pp + mm - 1)%Z in KQ by lia. replace (pp + mm - 1 - 1)%Z with (pp + mm - 2)%Z in KQ by lia.
    replace (pp + mm - 1 - 2)%Z with (pp + mm - 3)%Z in KQ by lia. replace (pp + mm - 1 - 3)%Z with (pp + mm - 4)%Z in KQ by lia.
    replace (pp + mm - 1 - 4)%Z with (pp + mm - 5)%Z in KQ by lia. replace (mm - 1 - 4)%Z with (mm - 5)%Z in KQ by lia.
    arun_to 0xa6028%Z. mtfa_rdA MA (pp + mm - 2)%Z.
    arun_to 0xa6030%Z. mtfa_wrA (pp + mm - 1)%Z.
    arun_to 0xa604c%Z. mtfa_rdA MA (pp + mm - 3)%Z.
    arun_to 0xa6050%Z. mtfa_wrA (pp + mm - 2)%Z.
    arun_to 0xa606c%Z. mtfa_rdA MA (pp + mm - 4)%Z.
    arun_to 0xa6078%Z. mtfa_wrA (pp + mm - 3)%Z.
    arun_to 0xa608c%Z. mtfa_rdA MA (pp + mm - 5)%Z.
    arun_to 0xa6098%Z. mtfa_wrA (pp + mm - 4)%Z.
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (pp + mm - 1) (zget (d_mtfa d) (pp + mm - 2)) DP ltac:(apply MA; lia)) as DP1.
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (pp + mm - 2) (zget (d_mtfa d) (pp + mm - 3)) DP1 ltac:(apply MA; lia)) as DP2.
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (pp + mm - 3) (zget (d_mtfa d) (pp + mm - 4)) DP2 ltac:(apply MA; lia)) as DP3.
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (pp + mm - 4) (zget (d_mtfa d) (pp + mm - 5)) DP3 ltac:(apply MA; lia)) as DP4.
    clear DP1 DP2 DP3.
    (* [comment removed for export] *)
    arun; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      rewrite (K_LFA_exit F L) in KQ by lia.
      arun; if_cases K0; zify_cond_z K0.
      + revive_all MUL WML AOK.
        pose proof (A0F_U10_LFZ mb pp uc) as NX. unfold A0F_cut_LFZ in NX.
        replace (mm - 5)%Z with 0%Z in KQ by lia.
        kq_fold. enter_cutF (NX L _ s JK_) DP4; u10_side MR MA ROW.
      + arun_to 0xa6410%Z. revive_all MUL WML AOK.
        pose proof (A0F_U10_LFB_all mb pp uc (mm - 5)%Z ltac:(lia)) as NX. unfold A0F_cut_LFB in NX.
        kq_fold. enter_cutF (NX L _ s JK_) DP4; u10_side MR MA ROW.
    - (* [comment removed for export] *)
      astep. revive_all MUL WML AOK.
      pose proof (NXT ltac:(lia)) as NX. unfold A0F_cut_LFA in NX.
      replace (mm - 5)%Z with (mm - 4 - 1)%Z in KQ by lia.
      kq_fold. enter_cutF (NX L _ s JK_) DP4; u10_side MR MA ROW.
  Qed.
  Lemma A0F_U10_LFA_all : forall mb pp uc mm, (5 <= mm <= 16)%Z -> A0F_cut_LFA A Q F mb pp uc mm.
  Proof.
    intros mb pp uc mm Hm.
    assert (G : forall n : nat, (n <= 2)%nat -> forall mm', (5 <= mm' <= 8 + 4 * Z.of_nat n)%Z -> (mm' <= 16)%Z -> A0F_cut_LFA A Q F mb pp uc mm').
    { induction n as [|n IH]; intros Hn mm' H1 H2.
      - apply A0F_U10_LFA. intros; exfalso; lia.
      - apply A0F_U10_LFA. intros H9. apply IH; lia. }
    apply (G 2%nat); lia.
  Qed.
End R.
End ACeilS1.
