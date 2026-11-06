(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf BzContracts BzWalkArith DecCut S0_bzd_out S0_bzd_loop1 BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDFrame DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out S0F_bzd_outS S0F_bzd_loop1.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac2 AsanKit AsanCut AsanCutB0 AsanKitB0 DecCutB DecCutFB B0F_decV B0F_bzdV B0F_bzd_uV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0F_bzd_skV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0F_bzd_fnr3 B0F_bzd_snr5 B0F_bzd_fr4 B0F_bzd_sk3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
(* [comment removed for export] *)
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLiaS.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac tlia ::= RelLiaS.tlia_bzd_r.
Local Ltac BzSepTac.tlia1 ::= RelLiaS.tlia1_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Lemma B0_fastnr_spec : FASTNR_aspec.
Proof.
  unfold FASTNR_aspec, FAST_aspec. intros c SHS w0 OK OKF ALT ANS SH KJ KE. intros until rest. intros DSm DE FSL ROm MU WM RD0.
  eapply (B0F_bzd_fnr3.B0F_fastnr c SHS w0 OK OKF ALT ANS SH KJ KE); eassumption.
Qed.

Lemma B0_smallnr_spec : SMALLNR_aspec.
Proof.
  unfold SMALLNR_aspec, SMALL_aspec. intros c SHS w0 lo OK OKS OKB ANS SH KJ KE. intros until rest. intros DSm DE FSL ROm MU WM RD0.
  eapply (B0F_bzd_snr5.B0F_smallnr c SHS w0 lo OK OKS OKB ANS SH KJ KE RD0); eassumption.
Qed.

Lemma B0_fastr_spec : FASTR_aspec.
Proof.
  unfold FASTR_aspec, FAST_aspec. intros c SHS w0 OK OKF ALT ANS SH KJ KE. intros until rest. intros DSm DE FSL ROm MU WM RD1.
  eapply (B0F_bzd_fr4.B0F_fastr c SHS w0 _ _ _ _ _ _ _ OK OKF ALT ANS SH KJ KE RD1); eassumption.
Qed.

(* [comment removed for export] *)
Lemma B0_bzd_L1 : forall (z : bzdctx) (SHS : Z) (w0 : word) (QF : Z * dst * dstrm -> machine_state -> Prop),
  bzdctx_okA z SHS -> SMALLR_aspec ->
  ((1 <= b_n (z_cx z))%Z -> b_small (z_cx z) = 0%Z -> b_tt (z_cx z) <> 0%Z) ->
  ((1 <= b_n (z_cx z))%Z -> b_small (z_cx z) = 1%Z -> b_ll16 (z_cx z) <> 0%Z /\ b_ll4 (z_cx z) <> 0%Z) ->
  bzd_sh z (WLA z) (z_m0 z) ->
  forall f : nat, B0_KRet z QF (WLA z) -> (forall f' : nat, f = Datatypes.S f' -> B0_KCall z SHS w0 QF (WLA z) f') -> FLKA1 z SHS w0 QF f.
Proof.
  intros z SHS w0 QF ZOK VSR NN0 NN1 SHL.
  exact (B0F_bzd_sk3.bzd_fLA1 z SHS w0 QF ZOK B0_fastnr_spec B0_fastr_spec B0_smallnr_spec VSR NN0 NN1 SHL).
Qed.
Lemma B0_bzd_L2 : forall (z : bzdctx) (SHS : Z) (w0 : word) (QF : Z * dst * dstrm -> machine_state -> Prop),
  bzdctx_okA z SHS -> SMALLR_aspec ->
  ((1 <= b_n (z_cx z))%Z -> b_small (z_cx z) = 0%Z -> b_tt (z_cx z) <> 0%Z) ->
  ((1 <= b_n (z_cx z))%Z -> b_small (z_cx z) = 1%Z -> b_ll16 (z_cx z) <> 0%Z /\ b_ll4 (z_cx z) <> 0%Z) ->
  bzd_sh z (WLA z) (z_m0 z) ->
  forall f : nat, B0_KRet z QF (WLA z) -> (forall f' : nat, f = Datatypes.S f' -> B0_KCall z SHS w0 QF (WLA z) f') -> FLKA2 z SHS w0 QF f.
Proof.
  intros z SHS w0 QF ZOK VSR NN0 NN1 SHL.
  exact (B0F_bzd_sk3.bzd_fLA2 z SHS w0 QF ZOK B0_fastnr_spec B0_fastr_spec B0_smallnr_spec VSR NN0 NN1 SHL).
Qed.
End ACeilS1.
