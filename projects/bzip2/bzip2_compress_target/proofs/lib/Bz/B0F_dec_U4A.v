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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2 BzDU4 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet B0F_decCutsA B0F_decCuts4 B0F_gb_C B0F_decAux.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_gb_C OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decAux.
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

(* [comment removed for export] *)

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRETOK : B0F_RET_OK A Q.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  (* [comment removed for export] *)
  Lemma B0F_U4_LZ_body : forall F' k, (0 <= k <= 255)%Z -> B0F_cut_HMAP2 A Q F' ->
    ((k < 255)%Z -> B0F_cut_LZ A Q F' (k + 1)) -> B0F_cut_LZ A Q F' k.
  Proof.
    intros F' k Hk HMAP2 NXT. unfold B0F_cut_LZ. intros until w752. (intros DM FRL FRH AF ST MU WM MI DP; cps_intros (NB & HDR & I16 & NS2); intros FU).
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    open_dmemF DM. b0img. unfold r_of in DR. dr_open. repeat match goal with H : u8arr _ _ _ _ |- _ => progress dmodel_cbn_in H end. kq_intro.
    hide_all_but_atF [S + 3196; a_P A; a_P A + 344]%Z.
    pose proof (munch_refl [(S + 3196, S + 3452)]%Z m) as MUL. pose proof (wmono_refl b0segs m) as WML.
    brun_to 0xafab4%Z.
    lazymatch goal with H : u8arr _ _ (S + 3196)%Z _ |- _ =>
      zb8_sb H k; rewrite (zb8_clear256_snoc iu k) in H by lia end.
    brun; if_cases Kl; zify_cond_z Kl.
    - pose proof (NXT ltac:(lia)) as NX. unfold B0F_cut_LZ in NX.
      revive_all MUL WML AOK.
      replace (S + 3196 + k + 1)%Z with (S + 3196 + (k + 1))%Z by lia.
      kq_fold. enter_cutF (NX _ _ _ JK_ iu) DP. split; [exact NB| split; [exact HDR| split; [exact I16| exact NS2]]].
    - (* [comment removed for export] *)
      brun_to 0xb0080%Z. revive_all MUL WML AOK.
      match goal with H : u8arr _ _ (S + 3196)%Z _ |- _ => replace (Z.to_nat (k + 1)) with 256%nat in H by lia end.
      kq_fold. enter_cutF (HMAP2 _ _ _ JK_ 0%Z) DP.
      unfold dinv_L4O. dmodel_cbn. split; [exact NB|]. split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]. split; [lia|].
      split; [apply in16_ok_frame_inUse; exact I16 |]. split; [apply inUse_ok_clear| exact NS2].
  Qed.

  Lemma B0F_U4_LZ : forall F', B0F_cut_HMAP2 A Q F' -> B0F_cut_LZ A Q F' 0.
  Proof.
    intros F' HMAP2.
    assert (G : forall j : nat, (j <= 255)%nat -> B0F_cut_LZ A Q F' (255 - Z.of_nat j)%Z).
    { induction j as [|j IH]; intros Hj.
      - apply B0F_U4_LZ_body; [lia | exact HMAP2 | intros; exfalso; lia].
      - apply B0F_U4_LZ_body; [lia | exact HMAP2 | intros _].
        replace (255 - Z.of_nat (Datatypes.S j) + 1)%Z with (255 - Z.of_nat j)%Z by lia. apply IH. lia. }
    exact (G 255%nat ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_dec_U4A :
    (forall F', (F' < F)%nat -> B0F_cut_HMAP A Q F') -> (forall F', (F' < F)%nat -> B0F_cut_LZ A Q F' 0) ->
    B0F_cut_HMAP A Q F.
  Proof.
    intros HMAP HLZ. unfold B0F_cut_HMAP. intros until w752. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN. pose proof rnums_words_length as RNL. lin_natZ RNL.
    unfold_W14 MU. open_ash ASH AOK. pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    unfold dinv_HMAP, nb_ok, op_ok in DI. cps_destruct DI as (NB & HDR & Hi & I16).
    open_dmemF DM. b0img.
    gbF_call (B0F_gb_af500 A AOK ASH Q HRETOK _ _ _ _ JK_) MU WM AOK DP FU.
    gbF_nextA [S; S + 3452; a_P A; a_P A + 344]%Z [(S, S + 68); (S + 3452, S + 3468); (a_P A + 344, a_P A + 760)]%Z.
    dr_open. hide_all_but_atF [S; S + 3452; a_P A; a_P A + 344]%Z.
    arun_lwbuf. arun_gbv 1%Z ub.
    rewrite edge_28 in KQ. kq_norm.
    (* [comment removed for export] *)
    Ltac fin_iter HMAP HLZ HDR I16 MUL WML DP AOK :=
      let K16 := fresh "K16" in
      brun; if_cases K16; zify_cond_z K16;
      [ (* [comment removed for export] *)
        match goal with KQ : kq _ _ |- _ => rewrite (@if_falseP _ (_ <? 16)%Z) in KQ by blia end;
        brun_to 0xafa9c%Z;
        revive_all MUL WML AOK;
        replace (Z_to_bv 64 (b_s (a_cx A) + 3196)) with (Z_to_bv 64 (b_s (a_cx A) + 3196 + 0)) by (f_equal; lia);
        enter_nextK HLZ DP;
        unfold nb_ok, in16_ok; dmodel_cbn; split; [lia|]; split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|];
        split; [| cbv; discriminate];
        intros k Hk; rewrite zget_zset; lazymatch goal with |- context [sv_i ?L] => destruct (Z.eqb_spec k (sv_i L)); [unset_Z; lia| apply I16; lia] end
      | match goal with KQ : kq _ _ |- _ => rewrite (@if_trueP _ (_ <? 16)%Z) in KQ by blia end;
        revive_all MUL WML AOK; enter_nextF HMAP DP;
        unfold dinv_HMAP, nb_ok, op_ok; dmodel_cbn; split; [lia|]; split; [apply (hdr_ok_frame _ _ HDR); dmodel_cbn; reflexivity|]; split; [lia|];
        intros k Hk; rewrite zget_zset; lazymatch goal with |- context [sv_i ?L] => destruct (Z.eqb_spec k (sv_i L)); [unset_Z; lia| apply I16; lia] end ].
    (* [comment removed for export] *)
    brun; if_cases Kbit; zify_cond_z Kbit.
    - (* [comment removed for export] *)
      rewrite (@if_falseP _ (ub =? 1)%Z) in KQ by blia.
      brun_to 0xafa78%Z.
      lazymatch goal with H : u8arr _ _ (S + 3452)%Z _ |- _ => zb8_sb H (sv_i L) end.
      fin_iter HMAP HLZ HDR I16 MUL WML DP AOK.
    - (* [comment removed for export] *)
      rewrite (@if_trueP _ (ub =? 1)%Z) in KQ by blia.
      brun_to 0xaf878%Z.
      lazymatch goal with H : u8arr _ _ (S + 3452)%Z _ |- _ => zb8_sb H (sv_i L) end.
      fin_iter HMAP HLZ HDR I16 MUL WML DP AOK.
  Qed.
End R.
End ACeilS1.
