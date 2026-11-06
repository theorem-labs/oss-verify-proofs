(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Image SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlDecode YajlParser YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsParse YajlFactsLoop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_acct_needs AY_parse_kit AY_parse_pol AY_parse_head AY_parse_lex AY_parse_lexc AY_parse_epi AY_parse_tails AY_parse_tails2
     AY_parse_sep AY_parse_sep2 AY_parse_agv AY_parse_agv2 AY_parse_mgv AY_parse_mgv2 AY_parse_map AY_parse_map2 AY_parse_mapk AY_parse_kitD AY_parse_kitD2 AY_parse_mape AY_parse_map3
     AY_parse_gv AY_parse_gv2 AY_parse_kitV AY_parse_gv3 AY_parse_val AY_parse_val2 AY_parse_val3 AY_parse_val4 AY_parse_val5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Open Scope yprog_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis YHM : yacct_hand_mono_stmt Y.
Hypothesis RELY : AHK_y_fake_release_stmt Y.
Hypothesis AFLSEP : AHK_y_aflsep_stmt Y.
Hypothesis FLAGY : AHK_y_flag_cell_stmt Y.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.
Variable phr : Z -> Z -> Z -> Z -> Z.
Hypothesis YSPLIT : yphi_hand_split_stmt Y phr.
Hypothesis WREA : aywrap_realloc_stmt Y.
Variable URA : list Z.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells asegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis URA_push : In PUSH_RET URA.
Hypothesis URA_lex : forall pc, lex_site pc -> In (pc + 48) URA.
Hypothesis URA_dec : forall pc, dec_site pc -> In pc URA.
Hypothesis YRP : ayreset_parser_stmt.
Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis YCN : aycb_null_stmt.
Hypothesis YCB : aycb_boolean_stmt.
Hypothesis YCNUM : aycb_number_stmt.
Hypothesis YCS : aycb_string_stmt.
Hypothesis YCSM : aycb_start_map_stmt.
Hypothesis YCSA : aycb_start_array_stmt.
Hypothesis YCEA : aycb_end_array_stmt.
Hypothesis YCEM : aycb_end_map_stmt.
Hypothesis YCMK : aycb_map_key_stmt.
Hypothesis YBC : aybuf_clear_stmt.
Hypothesis YBE : aybuf_err_stmt.
Hypothesis YBD : aybuf_data_stmt.
Hypothesis YBL : aybuf_len_stmt.
Hypothesis YBS : aybs_set_stmt.
Hypothesis YSD : aystring_decode_stmt Y.
Hypothesis YSHAPE : yphi_shape_stmt Y.
Hypothesis YLX : aylex_lex_stmt Y.

(* [comment removed for export] *)
Lemma pass_all : forall (E : apE Y), penvA E -> ppass_stmt E.
Proof. aceil.
  intros E PA. unfold ppass_stmt. intros until t6. intros HI EXIT AGAIN.
  pose proof HI as (_ & OK & _ & _). pose proof OK as (_ & LP & U0 & _).
  destruct (h_stack h) as [|st rest] eqn:HST.
  { exfalso. unfold h_used in U0. rewrite HST in U0. revert U0 CEILB. clear. intros U0 CEILB. cbv in U0. discriminate. }
  destruct st.
  - eapply pass_val; try eassumption; reflexivity.
  - eapply pass_done; try eassumption; reflexivity.
  - eapply pass_done; try eassumption; reflexivity.
  - eapply pass_done; try eassumption; reflexivity.
  - eapply pass_map; try eassumption; reflexivity.
  - eapply pass_sep; try eassumption; reflexivity.
  - eapply pass_val; try eassumption; reflexivity.
  - eapply pass_mgv; try eassumption; reflexivity.
  - eapply pass_map; try eassumption; reflexivity.
  - eapply pass_val; try eassumption; reflexivity.
  - eapply pass_agv; try eassumption; reflexivity.
  - eapply pass_val; try eassumption; reflexivity.
Qed.

Lemma pexit_cont_mono : forall (E : apE Y) (R1 R2 : ystatus * yhandle * yctx -> Prop),
  (forall r, R1 r -> R2 r) -> pexit_cont E R2 -> pexit_cont E R1.
Proof. aceil. intros E R1 R2 HR EX. unfold pexit_cont in *. intros. eapply EX; eauto. Qed.

(* [comment removed for export] *)
Lemma ploop : forall (E : apE Y) fuel, penvA E -> ploop_at E fuel.
Proof. aceil.
  intros E fuel PA. revert fuel. induction fuel as [|fuel IH]; unfold ploop_at; intros until t6; intros HI FUEL EXIT.
  { exfalso. pose proof HI as (_ & (_ & LP & _) & _). pose proof (loop_pre_passes_left_pos _ _ _ LP). clear -CEILB H FUEL. cbn in FUEL. lia. }
  pose proof HI as (_ & OK & _ & _). pose proof OK as (_ & LP & U0 & _).
  eapply (pass_all E PA); [exact HI| |].
  - eapply pexit_cont_mono; [| exact EXIT]. intros [[st h'] cx'] YL. apply yparse_loop_leaf_done. exact YL.
  - intros until t6'. intros YLS HI'.
    destruct (yparse_step_again_facts (p_txt E) (pLEN E) h cx h' cx' eq_refl ltac:(openPA PA; clear -CEILB pa_len0; lia) LP YLS) as (LP' & U1 & PL').
    unfold ploop_at in IH. eapply IH; [exact HI'| clear -CEILB PL' FUEL; lia|].
    eapply pexit_cont_mono; [| exact EXIT]. intros r YL. eapply yparse_loop_leaf_again; [exact YLS| exact YL].
Qed.
End W.
End RC__1.
