(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BY_rz BY_hand BY_acct_needs BY_parse_kit BY_parse_pol BY_parse_head BY_parse_lex BY_parse_lexc BY_parse_epi BY_parse_tails BY_parse_tails2 BY_parse_sep BY_parse_agv.
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
Definition MGV_SW : Z := 0x87fd4.      (* [comment removed for export] *)
Definition MGV_PT : Z := 0x890a4.      (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_mgv : forall txt len h cx rest lx tok off ob n r,
  h_stack h = ST_map_got_val :: rest ->
  yleaf (ylex_lex (h_lexer h) txt len (h_bytesConsumed h)) (lx, tok, off, ob, n) ->
  yleaf (let h := h_set_lex_off h lx off in
         match tok with
         | TK_right_bracket => cx1 <- cb_end_map jf_callbacks cx ;; h1 <- ybs_pop h ;; YRet (SR_again h1 cx1)
         | TK_comma => h1 <- ybs_set h ST_map_need_key ;; YRet (SR_again h1 cx)
         | TK_eof => YRet (SR_done YS_insufficient_data h cx)
         | TK_error => h1 <- ybs_set h ST_lexical_error ;; YRet (SR_again h1 cx)
         | _ => h1 <- ybs_set h ST_parse_error ;;
                let h2 := h_set_perr h1 PE_map_expect in
                let off' := if n <=? off then off - n else 0 in
                YRet (SR_again (h_set_off h2 off') cx)
         end) r ->
  yleaf (yparse_step jf_callbacks txt len h cx) r.
Proof. aceil.
  intros until r. intros HST YL YR. unfold yparse_step. rewrite (ybs_current_eq h _ _ HST). cbn [ybind].
  eapply yleaf_bind; [exact YL|]. cbn beta iota. exact YR.
Qed.

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
Lemma YH_shape : yphi_hand_shape_stmt Y.
Proof. aceil.
  intros h1 h2 L E1 E2 E3 E4 E5 _. destruct YSPLIT as (EQ & _). rewrite (EQ h1 L), (EQ h2 L), E1, E2, E3, E4, E5. reflexivity.
Qed.

Section MGV.
Variables (E : apE Y) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : y_APS Y) (LK : list ablock)
          (h0 : yhandle) (cx0 : yctx) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (cr : Z) (rest : list ystate).
Variables (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5v t3 t4 t5 t6 : word).
Hypothesis PA : penvA E.
Hypothesis OK : pok E h0 cx0.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw cr.
Hypothesis HCR : y_phi_hand Y h (pLEN E) <= cr.
Hypothesis FRM : frm0 fc.
Hypothesis HST : h_stack h = ST_map_got_val :: rest.
Hypothesis SZM' : h_stack_size h mod 8 = 0.
Hypothesis LKL : (length LK <= 1)%nat.
Hypothesis AG : pagain Y E h0 cx0 LK.
Hypothesis EX : pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')).

Let at_switch (tok : ytok) : Prop :=
  realizes_cfg acfg bsegs (mkCfg (pstate E MGV_SW F fc m rav t0 t1 t2 (wz (tok_code tok)) a1 a2 a3 a4 a5 a6 a7 (wz 0) (wz (p_ff E)) s5v t3 t4 t5 t6) mo) (p_K E).   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mgv_eof :
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done YS_insufficient_data h cx) ->
  at_switch TK_eof.
Proof. aceil.
  intros YL. unfold at_switch.
  popen OK PM.
  pose proof (yparse_step_done_facts (p_txt E) (pLEN E) h0 cx0 _ h cx eq_refl ltac:(openPA PA; clear -CEILB pa_len0; lia) LP YL) as W1.
  destruct (weak_inv_exit_facts _ _ W1) as (WL & WD & SZ).
  openPA PA. clear pa_ffCX0 pa_ffH0 pa_CXH0 pa_Tsep0 pa_OT0 pa_j0.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  clear TXT LXR DBR FF OCX GAP PRES UA CRED HS HR HC. yhide SV.
  unfold pstate, MGV_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  zstepA. zstepA. if_true.                                 (* [comment removed for export] *)
  zstepA. zstepA. if_true.                                 (* [comment removed for export] *)
  zstepA. zstepA. if_true.                                 (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  change (Z_to_bv 64 2) with (wz (status_code YS_insufficient_data)).
  pose proof (fun rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5v t3 t4 t5 t6 =>
                pass_exit Y KIPY FRAMEY BLKY BSHY LAYY RRT RELY AFLSEP FLAGY E F fc m mo1 s LK h mh cx obw olw cr
                          rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5v t3 t4 t5 t6 YS_insufficient_data
                          (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')) h0 cx0)
    as PX. unfold pstate, AY_PEXIT, wz in PX.
  eapply PX; [exact PA| exact OK| exact PM1| exact (proj1 (pcr_full YHM E h cr PA HCR))| exact FRM| exact YL| exact LKL| exact WL| exact WD| exact SZ| exact EX].
Qed.

(* [comment removed for export] *)
Lemma mgv_comma :
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_stack h (ST_map_need_key :: rest)) cx) ->
  LK = [] ->
  at_switch TK_comma.
Proof. aceil.
  intros YL LK0. unfold at_switch.
  (* [comment removed for export] *)
  popen OK PM; yhide TB; yhide OTB; yhide LP; yhide FFR0.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US.
  assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (pb_HSB _ _ _ PB) as SEPHS; pose proof (pb_SB _ _ _ PB) as RSB. pose proof (pb_SBA PB) as RSBA.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_CXH0 pa_Tsep0 pa_OT0 pa_j0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_stack mh h SB1)) ltac:(cbn; lia))) as OSH_S; cbn [ab_addr ab_size] in OSH_S.
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H, OSH_S.
  destruct OSH_H as (_ & _ & SHH); destruct OSH_S as (_ & _ & SHS); rewrite EH in SHH.
  remember (blk_shadow 104) as shb eqn:SHHeq in SHH; remember (blk_shadow (h_stack_size h)) as shs eqn:SHSeq in SHS.
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold wz in HC; rewrite EH in HC.
  clear TXT LXR DBR FF OCX GAP PRES UA CRED HS HR; yhide SV. unfold wz in FR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, MGV_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol in pp_stk0, pp_H0, pp_Hs0, pp_SBs0, pp_SB0. clear pp_img0 pp_imgsh0 pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_CX0 pp_CXs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0.
  zstepA. zstepA. if_true.                                 (* [comment removed for export] *)
  zstepA. zstepA. if_false.                                (* [comment removed for export] *)
  shH SHH SHHeq MU WM 60 4.                                (* [comment removed for export] *)
  zstepA. if_true.                                         (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia).   (* [comment removed for export] *)
  bs_inline2 SHH SHHeq SHS SHSeq MU WM BC2 BC3 USED Z0 US h.
  zstepA. if_true.                                         (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + (h_used h - 1)) by (clear; lia).
  change (Z_to_bv 64 8) with (wz (state_code ST_map_need_key)).
  pose proof (J_setb Y KIPY FRAMEY BLKY BSHY LAYY RRT UFRAME E F fc m mo1 s LK h0 cx0 h mh cx obw olw cr ST_map_got_val rest ST_map_need_key) as JS.
  unfold pstate, J_SETB, wz in JS.
  eapply JS; [exact PA| exact OK| exact PM1| exact FRM| exact HST| exact SZM'| exact YL| | left; exact LK0| exact AG].
  apply (pcr_full YHM E _ _ PA). rewrite (YH_shape (h_set_stack h (ST_map_need_key :: rest)) h (pLEN E));
    [exact HCR| reflexivity| reflexivity| reflexivity| unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity| reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma mgv_error :
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_stack h (ST_lexical_error :: rest)) cx) ->
  at_switch TK_error.
Proof. aceil.
  intros YL. unfold at_switch.
  (* [comment removed for export] *)
  popen OK PM; yhide TB; yhide OTB; yhide LP; yhide FFR0.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US.
  assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (pb_HSB _ _ _ PB) as SEPHS; pose proof (pb_SB _ _ _ PB) as RSB. pose proof (pb_SBA PB) as RSBA.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_CXH0 pa_Tsep0 pa_OT0 pa_j0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_stack mh h SB1)) ltac:(cbn; lia))) as OSH_S; cbn [ab_addr ab_size] in OSH_S.
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H, OSH_S.
  destruct OSH_H as (_ & _ & SHH); destruct OSH_S as (_ & _ & SHS); rewrite EH in SHH.
  remember (blk_shadow 104) as shb eqn:SHHeq in SHH; remember (blk_shadow (h_stack_size h)) as shs eqn:SHSeq in SHS.
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold wz in HC; rewrite EH in HC.
  clear TXT LXR DBR FF OCX GAP PRES UA CRED HS HR; yhide SV. unfold wz in FR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, MGV_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol in pp_stk0, pp_H0, pp_Hs0, pp_SBs0, pp_SB0. clear pp_img0 pp_imgsh0 pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_CX0 pp_CXs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0.
  zstepA. zstepA. if_false.                                (* [comment removed for export] *)
  zstepA. zstepA. if_true.                                 (* [comment removed for export] *)
  shH SHH SHHeq MU WM 60 4.                                (* [comment removed for export] *)
  zstepA. if_false.                                        (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia).   (* [comment removed for export] *)
  bs_inline2 SHH SHHeq SHS SHSeq MU WM BC2 BC3 USED Z0 US h.
  zstepA. if_true.                                         (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + (h_used h - 1)) by (clear; lia).
  pose proof (J_lexerr Y KIPY FRAMEY BLKY BSHY LAYY RRT UFRAME E F fc m mo1 s LK h0 cx0 h mh cx obw olw cr ST_map_got_val rest) as JL.
  unfold pstate, J_LEXERR, wz in JL.
  eapply JL; [exact PA| exact OK| exact PM1| exact FRM| exact HST| exact SZM'| exact YL| | exact LKL| exact AG].
  apply (pcr_full YHM E _ _ PA). rewrite (YH_shape (h_set_stack h (ST_lexical_error :: rest)) h (pLEN E));
    [exact HCR| reflexivity| reflexivity| reflexivity| unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity| reflexivity| reflexivity].
Qed.
End MGV.
End W.
End RC__1.
