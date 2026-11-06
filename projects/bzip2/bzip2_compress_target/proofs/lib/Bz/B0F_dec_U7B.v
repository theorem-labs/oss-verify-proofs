(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU6 BzDU7 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet B0F_decCuts7.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts7.
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

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac.DecAuxB.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zw32_store_done ARR i v :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm ?ga (le4 ?x)) _) =>
      lazymatch type of ARR with u32arr _ _ ?A (zw32 ?a ?n) =>
        let H := fresh "ARR" in
        pose proof (zw32_write segs mm A a n i x v ARR ltac:(lia)
                      ltac:(first [ reflexivity | rewrite unsigned_lit by lia; reflexivity | rewrite unsigned_lit_wrap, <- Znumtheory.Zmod_div_mod by lia; reflexivity ])) as H;
        let ga' := lazymatch ga with wa _ => ga | Z_to_bv 64 ?X => constr:(wa X) | _ => ga end in
        replace (wa (A + 4 * i)%Z) with ga' in H by (cbv delta [wa]; first [reflexivity | f_equal; lia | apply f_equal; lia]);
        clear ARR; store_done; rename H into ARR
      end
  end.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma B0F_U7_C1 : forall t mn mx, B0F_call_HBC A Q F t mn mx -> B0F_cut_L7C A Q F t mn mx.
  Proof.
    intros t mn mx HCALL. unfold B0F_cut_L7C. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof DI as DI'. cps_destruct DI' as (COM & Ht & _). destruct COM as [SEL _]. cps_destruct SEL as (_ & NG & _).
    (* [comment removed for export] *)
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN.
    assert (Ht6 : (0 <= t < 6)%Z) by lia.
    brun_to 0xa8eac%Z. rewrite ?(land64_small t) by lia.
    eapply evt_eq; [ | eapply (HCALL L d s J) ]; [ st_eq | eassumption .. ].
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_U7_C2 : forall t mn mx, B0F_cut_L7D A Q F t -> B0F_cut_HBCR A Q F t mn mx.
  Proof.
    intros t mn mx HL7D. unfold B0F_cut_HBCR. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof DI as DI'. cps_destruct DI' as (COM & Ht & Hmm & SCAN & TU).
    pose proof COM as COM'. destruct COM' as [SEL LALL]. pose proof SEL as SEL'. cps_destruct SEL' as ((AL & NBL) & NG & NSC & SOK).
    assert (Ha : (1 <= sv_alphaSize L <= 258)%Z) by (unfold alpha_ok in AL; lia).
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    kq_intro. rewrite K_L7C_D in KQ. (* [comment removed for export] *)
    pose proof (mt_rows_bridge d t (sv_alphaSize L) mn mx Ha ltac:(lia) Hmm SCAN) as BRG. cbv zeta in BRG.
    pose proof (mt_rows_fields t (sv_alphaSize L) d mn mx) as FL. cbv zeta in FL.
    (* [comment removed for export] *)
    assert (ED : mt_rows t (sv_alphaSize L) d mn mx =
                 (let '(li, ba, pe) := hbCreateDecodeTables (d_limit d) (d_base d) (d_perm d) (d_len d) (258 * t) mn mx (sv_alphaSize L) in
                  d_set_perm (d_set_base (d_set_limit d li) ba) pe)) by reflexivity.
    destruct (hbCreateDecodeTables (d_limit d) (d_base d) (d_perm d) (d_len d) (258 * t) mn mx (sv_alphaSize L)) as [[li ba] pe] eqn:HBD.
    rewrite ED in DM, KQ, BRG, FL. clear ED.
    cps_destruct FL as (El & Eb & Ep & Elen & Eml & Esel & Eniu & Ebs & Est & Era & Esb & Eop & Ebl).
    open_dmemF DM. b0img.
    unfold r_of in DR. dr_open. hide_all_but_atF [S + 64012; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(S + 64012, S + 64036)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    brun_to 0xb1344%Z.
    lazymatch goal with H : u32arr _ ?mm (S + 64012)%Z ?ws |- _ =>
      pose proof (u32arr_store_ok b0segs mm (S + 64012) ws t _ H ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO;
      wstepl; zw32_store_done H t mn end.
    try clear SO.
    brun_to 0xb134c%Z.
    destruct (hb_create (zrow (d_limit d) (258 * t)) (zrow (d_base d) (258 * t)) (zrow (d_perm d) (258 * t))
                        (zrow (d_len d) (258 * t)) mn mx (sv_alphaSize L)) as [[lim bas] per] eqn:HCz.
    destruct BRG as [BROW BFRM]. dmodel_cbn_in BROW. dmodel_cbn_in BFRM.
    revive_all MUL WML AOK.
    kq_fold. enter_cutF (HL7D _ _ _ JK_) DP.
    (* [comment removed for export] *)
    split; [| lia]. unfold dinv_L7T, u7com. dmodel_cbn.
    split; [split; [exact SEL| exact LALL]|]. split; [lia|].
    intros t' Ht'. destruct (Z.eq_dec t' t) as [->|NE].
    - exists mn. apply (tab_okF_of_rows _ _ _ mn mx); [| dmodel_cbn; rewrite zget_zset, Z.eqb_refl; reflexivity].
      exists (zrow (d_len d) (258 * t)), (zrow (d_limit d) (258 * t)), (zrow (d_base d) (258 * t)), (zrow (d_perm d) (258 * t)).
      split; [exact Hmm|]. split; [intros j Hj; unfold zrow; apply SCAN; exact Hj|]. rewrite HCz. dmodel_cbn.
      split; [| split]; intros i Hi; cps_destruct (BROW i Hi) as (Q1 & Q2 & Q3); [exact Q1 | exact Q2 | exact Q3].
    - destruct (TU t' ltac:(lia)) as [mn' G]. exists mn'.
      assert (RNG : forall i, (0 <= i < 258)%Z -> (258 * t' + i < 258 * t \/ 258 * t + 258 <= 258 * t' + i)%Z) by (intros; lia).
      apply (tab_okF_frame_pt d); [exact G | | | | dmodel_cbn; rewrite zget_zset; destruct (Z.eqb_spec t' t); [lia| reflexivity]];
        dmodel_cbn; intros i Hi; cps_destruct (BFRM (258 * t' + i)%Z (RNG i Hi)) as (Q1 & Q2 & Q3); [exact Q1 | exact Q2 | exact Q3].
  Qed.
End R.
End ACeilS1.
