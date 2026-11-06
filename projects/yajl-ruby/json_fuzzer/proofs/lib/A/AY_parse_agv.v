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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_acct_needs AY_parse_kit AY_parse_pol AY_parse_head AY_parse_lex AY_parse_lexc AY_parse_epi AY_parse_tails AY_parse_tails2 AY_parse_sep.
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
Definition AGV_SW : Z := 0x87850.      (* [comment removed for export] *)
Definition AGV_PT : Z := 0x886d8.      (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_agv : forall txt len h cx rest lx tok off ob n r,
  h_stack h = ST_array_got_val :: rest ->
  yleaf (ylex_lex (h_lexer h) txt len (h_bytesConsumed h)) (lx, tok, off, ob, n) ->
  yleaf (let h := h_set_lex_off h lx off in
         match tok with
         | TK_right_brace => cx1 <- cb_end_array jf_callbacks cx ;; h1 <- ybs_pop h ;; YRet (SR_again h1 cx1)
         | TK_comma => h1 <- ybs_set h ST_array_need_val ;; YRet (SR_again h1 cx)
         | TK_eof => YRet (SR_done YS_insufficient_data h cx)
         | TK_error => h1 <- ybs_set h ST_lexical_error ;; YRet (SR_again h1 cx)
         | _ => yparse_error h cx PE_array_expect
         end) r ->
  yleaf (yparse_step jf_callbacks txt len h cx) r.
Proof. aceil.
  intros until r. intros HST YL YR. unfold yparse_step. rewrite (ybs_current_eq h _ _ HST). cbn [ybind].
  eapply yleaf_bind; [exact YL|]. cbn beta iota. exact YR.
Qed.

(* [comment removed for export] *)
End RC__1.
(* [comment removed for export] *)
Ltac if_litc := let c := goal_cond in let v := eval vm_compute in c in
  lazymatch v with true => change c with true | false => change c with false end; cbv iota.
Ltac iflit2 := first [if_litc | if_true1 | if_false1 | if_true | if_false].   (* [comment removed for export] *)
Ltac bs_inline2 SHH SHHeq SHS SHSeq MU WM BC2 BC3 USED Z0 US hh :=
  zstepA; (let K := fresh "K" in if_cases K; zify_cond K; bkill K BC2 BC3 US USED Z0);     (* [comment removed for export] *)
  zstepA;                                                                  (* [comment removed for export] *)
  shH SHH SHHeq MU WM 56 4;                                                (* [comment removed for export] *)
  zstepA; iflit2;                                                          (* [comment removed for export] *)
  zstepA;                                                                  (* [comment removed for export] *)
  zstepA; rewrite ?ysx32_small by (clear -BC2; lia);                       (* [comment removed for export] *)
  zstepA; (let K := fresh "K" in if_cases K; zify_cond K; bkill K BC2 BC3 US USED Z0);     (* [comment removed for export] *)
  shH SHH SHHeq MU WM 48 8;                                                (* [comment removed for export] *)
  zstepA; iflit2;                                                          (* [comment removed for export] *)
  zstepA;                                                                  (* [comment removed for export] *)
  zstepA; zstepA; stepA; rewrite zext32_shl_shr by (clear -USED Z0 US BC2; lia);   (* [comment removed for export] *)
  zstepA;                                                                  (* [comment removed for export] *)
  shS SHS SHSeq MU WM (h_used hh + -1) (h_stack_size hh).                  (* [comment removed for export] *)

Section RC__2.
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
Lemma YH_shape : yphi_hand_shape_stmt Y.
Proof. aceil.
  intros h1 h2 L E1 E2 E3 E4 E5 _. destruct YSPLIT as (EQ & _). rewrite (EQ h1 L), (EQ h2 L), E1, E2, E3, E4, E5. reflexivity.
Qed.

Section AGV.
Variables (E : apE Y) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : y_APS Y) (LK : list ablock)
          (h0 : yhandle) (cx0 : yctx) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (cr : Z) (rest : list ystate).
Variables (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5v t3 t4 t5 t6 : word).
Hypothesis PA : penvA E.
Hypothesis OK : pok E h0 cx0.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw cr.
Hypothesis HCR : y_phi_hand Y h (pLEN E) <= cr.
Hypothesis FRM : frm0 fc.
Hypothesis HST : h_stack h = ST_array_got_val :: rest.
Hypothesis SZM' : h_stack_size h mod 8 = 0.
Hypothesis LKL : (length LK <= 1)%nat.
Hypothesis AG : pagain Y E h0 cx0 LK.
Hypothesis EX : pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')).

Let at_switch (tok : ytok) : Prop :=
  realizes_cfg acfg asegs (mkCfg (pstate E AGV_SW F fc m rav t0 t1 t2 (wz (tok_code tok)) a1 a2 a3 a4 a5 a6 a7 (wz 0) (wz (pH E + 64)) s5v t3 t4 t5 t6) mo) (p_K E).

(* [comment removed for export] *)
Lemma agv_eof :
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done YS_insufficient_data h cx) ->
  at_switch TK_eof.
Proof. aceil.
  intros YL. unfold at_switch.
  popen OK PM.
  pose proof (yparse_step_done_facts (p_txt E) (pLEN E) h0 cx0 _ h cx eq_refl ltac:(openPA PA; clear -CEILB pa_len0; lia) LP YL) as W1.
  destruct (weak_inv_exit_facts _ _ W1) as (WL & WD & SZ).
  openPA PA. clear pa_ffCX0 pa_ffH0 pa_CXH0 pa_Tsep0 pa_OT0 pa_j0.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  clear TXT LXR DBR FF OCX GAP PRES UA CRED HS HR HC. yhide SV.
  unfold pstate, AGV_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  zstepA. zstepA. if_true.                                 (* [comment removed for export] *)
  zstepA. zstepA. if_true.                                 (* [comment removed for export] *)
  zstepA. zstepA. if_true.                                 (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  change (Z_to_bv 64 2) with (wz (status_code YS_insufficient_data)).
  pose proof (fun rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 =>
                pass_exit Y KIPY FRAMEY BLKY BSHY LAYY RRT RELY AFLSEP FLAGY E F fc m mo1 s LK h mh cx obw olw cr
                          rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 YS_insufficient_data
                          (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')) h0 cx0)
    as PX. unfold pstate, AY_PEXIT, wz in PX.
  eapply PX; [exact PA| exact OK| exact PM1| exact (proj1 (pcr_full YHM E h cr PA HCR))| exact FRM| exact YL| exact LKL| exact WL| exact WD| exact SZ| exact EX].
Qed.

(* [comment removed for export] *)
Lemma agv_comma :
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_stack h (ST_array_need_val :: rest)) cx) ->
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
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC).
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  pose proof (munch_refl [(mh_stack mh + (h_used h - 1), mh_stack mh + (h_used h - 1) + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold pstate, AGV_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol in pp_stk0, pp_H0, pp_Hs0, pp_SBs0, pp_SB0. clear pp_img0 pp_imgsh0 pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_CX0 pp_CXs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0.
  zstepA. zstepA. if_true.                                 (* [comment removed for export] *)
  zstepA. zstepA. if_false.                                (* [comment removed for export] *)
  shH SHH SHHeq MU WM 60 4.                                (* [comment removed for export] *)
  zstepA. if_true.                                         (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia).   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  bs_inline2 SHH SHHeq SHS SHSeq MU WM BC2 BC3 USED Z0 US h.
  zstepA. if_true.                                         (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at asegs mx (mh_stack mh) _ (h_used h + -1) ARR ltac:(rewrite length_app; clear -CEILB L1 L2 US USED Z0; lia)) as SOK end.
  stepA.                                                   (* [comment removed for export] *)
  lazymatch type of ARR with u8arr _ ?mx _ _ =>
    pose proof (u8arr_write asegs mx (mh_stack mh) _ (h_used h + -1) (Z_to_bv 8 11) ARR ltac:(rewrite length_app; clear -CEILB L1 L2 US USED Z0; lia)) as ARR' end.
  rewrite le1_wz by (clear; lia). clear ARR. try clear SHS. try clear SHH. store_done.
  zstepA.                                                  (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  yshow TB. yshow OTB. yshow LP. yshow FFR0. yshow SV.
  assert (PM2 : pmem E m2 mo1 s LK (h_set_stack h (ST_array_need_val :: rest)) mh cx obw olw cr).
  { eapply (pmem_setb Y FRAMEY BLKY BSHY LAYY UFRAME E m m2 mo1 s LK h0 cx0 h mh cx obw olw cr ST_array_got_val rest ST_array_need_val junk);
      [exact PA| exact OK| exact PM1| exact HST| exact SZ| exact MU| exact WM| assumption| | clear -CEILB L2; lia].
    replace (h_used h - 1) with (h_used h + -1) by (clear; lia). cbn [state_code]. exact ARR'. }
  pose proof (J_back Y KIPY BLKY BSHY LAYY RRT E F fc m2 mo1 s LK h0 cx0 (h_set_stack h (ST_array_need_val :: rest)) mh cx obw olw cr) as JB.
  unfold pstate, J_BACK, wz in JB.
  eapply JB; [exact PA| exact OK| exact PM2| | exact FRM| exact YL| cbn [h_stack_size h_set_stack]; exact SZM'| left; exact LK0| exact AG].
  apply (pcr_full YHM E _ _ PA). rewrite (YH_shape (h_set_stack h (ST_array_need_val :: rest)) h (pLEN E));
    [exact HCR| reflexivity| reflexivity| reflexivity| unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity| reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma agv_error :
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
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold pstate, AGV_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol in pp_stk0, pp_H0, pp_Hs0, pp_SBs0, pp_SB0. clear pp_img0 pp_imgsh0 pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_CX0 pp_CXs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0.
  zstepA. zstepA. if_false.                                (* [comment removed for export] *)
  zstepA. zstepA. if_true.                                 (* [comment removed for export] *)
  shH SHH SHHeq MU WM 60 4.                                (* [comment removed for export] *)
  zstepA. if_false.                                        (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia).   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  bs_inline2 SHH SHHeq SHS SHSeq MU WM BC2 BC3 USED Z0 US h.
  zstepA. if_false.                                        (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + (h_used h - 1)) by (clear; lia).
  pose proof (J_lexerr Y KIPY FRAMEY BLKY BSHY LAYY RRT UFRAME E F fc m mo1 s LK h0 cx0 h mh cx obw olw cr ST_array_got_val rest) as JL.
  unfold pstate, J_LEXERR, wz in JL.
  eapply JL; [exact PA| exact OK| exact PM1| exact FRM| exact HST| exact SZM'| exact YL| | exact LKL| exact AG].
  apply (pcr_full YHM E _ _ PA). rewrite (YH_shape (h_set_stack h (ST_lexical_error :: rest)) h (pLEN E));
    [exact HCR| reflexivity| reflexivity| reflexivity| unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity| reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma agv_ptail : forall mo' (a0v a1v t2v : word),
  pmem E m mo' s LK h mh cx obw olw cr ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_array_expect) cx) ->
  realizes_cfg acfg asegs (mkCfg (pstate E AGV_PT F fc m rav t0 t1 t2v a0v a1v a2 a3 a4 a5 a6 a7 (wz 0) (wz (pH E + 64)) s5v t3 t4 t5 t6) mo') (p_K E).
Proof. aceil.
  intros mo' a0v a1v t2v PM' YL. clear PM. rename PM' into PM. rename mo into mo_orig. rename mo' into mo.
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
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC).
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  pose proof (munch_refl [(mh_stack mh + (h_used h - 1), mh_stack mh + (h_used h - 1) + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold pstate, AGV_PT, wz.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_SBs0, pp_SB0, pp_img0. clear pp_imgsh0 pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_CX0 pp_CXs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0.
  shH SHH SHHeq MU WM 60 4.                                (* [comment removed for export] *)
  zstepA. if_false.                                        (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia).   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  bs_inline2 SHH SHHeq SHS SHSeq MU WM BC2 BC3 USED Z0 US h.
  zstepA. if_false.                                        (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  assert (SHB : 2148238848 <= 2147450880 + mh_addr (p_mh E) / 8 /\ 2147450880 + mh_addr (p_mh E) / 8 + 13 <= 17594333495296) by (clear -CEILB pa_H0; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  pose proof SHH as SHH0. yhide SHH0.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at asegs mx (mh_stack mh) _ (h_used h + -1) ARR ltac:(rewrite length_app; clear -CEILB L1 L2 US USED Z0; lia)) as SOK end.
  stepA.                                                   (* [comment removed for export] *)
  lazymatch type of ARR with u8arr _ ?mx _ _ =>
    pose proof (u8arr_write asegs mx (mh_stack mh) _ (h_used h + -1) (Z_to_bv 8 2) ARR ltac:(rewrite length_app; clear -CEILB L1 L2 US USED Z0; lia)) as ARR' end.
  rewrite le1_wz by (clear; lia). clear ARR. try clear SHS. try clear SHH. store_done.
  zstepA.                                                  (* [comment removed for export] *)
  yshow SHH0.
  shH SHH0 SHHeq MU WM 24 8.                               (* [comment removed for export] *)
  zstepA. if_true.                                         (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  yshow TB. yshow OTB. yshow LP. yshow FFR0. yshow SV.
  assert (PM2 : pmem E m2 mo1 s LK (h_set_stack h (ST_parse_error :: rest)) mh cx obw olw cr).
  { eapply (pmem_setb Y FRAMEY BLKY BSHY LAYY UFRAME E m m2 mo1 s LK h0 cx0 h mh cx obw olw cr ST_array_got_val rest ST_parse_error junk);
      [exact PA| exact OK| exact PM1| exact HST| exact SZ| exact MU| exact WM| assumption| | clear -CEILB L2; lia].
    replace (h_used h - 1) with (h_used h + -1) by (clear; lia). cbn [state_code]. exact ARR'. }
  change (Z_to_bv 64 138848) with (wz (ay_perr PE_array_expect)).
  pose proof (J_perr Y KIPY FRAMEY BLKY BSHY LAYY RRT UFRAME E F fc m2 mo1 s LK h0 cx0 (h_set_stack h (ST_parse_error :: rest)) mh cx obw olw cr PE_array_expect) as JP.
  unfold pstate, J_PERR, wz in JP.
  eapply JP; [exact PA| exact OK| exact PM2| exact FRM| cbn [h_stack_size h_set_stack]; exact SZM'
             | unfold h_used; cbn [h_stack h_set_stack]; unfold zlength; cbn [length]; clear; lia| exact YL| | | exact AG].
  - apply (pcr_full YHM E _ _ PA). rewrite (YH_shape (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_array_expect) h (pLEN E));
      [exact HCR| reflexivity| reflexivity| reflexivity| unfold h_used; cbn [h_stack h_set_stack h_set_perr]; rewrite HST; reflexivity| reflexivity| reflexivity].
  - destruct LK as [|b0 LK']; [left; reflexivity| right]. split; [cbn [length] in LKL |- *; clear -CEILB LKL; lia|].
    exists ST_parse_error, rest. split; reflexivity.
Qed.
End AGV.
End W.
End RC__2.
