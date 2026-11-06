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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_acct_needs AY_parse_kit AY_parse_pol AY_parse_head AY_parse_lex AY_parse_lexc AY_parse_epi AY_parse_tails AY_parse_tails2 AY_parse_sep AY_parse_agv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
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
Lemma YH_shape : yphi_hand_shape_stmt Y.
Proof. aceil.
  intros h1 h2 L E1 E2 E3 E4 E5 _. destruct YSPLIT as (EQ & _). rewrite (EQ h1 L), (EQ h2 L), E1, E2, E3, E4, E5. reflexivity.
Qed.

Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis YCEA : aycb_end_array_stmt.

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
Lemma agv_rbrace :
  0 < cx_arrayLevel cx ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_stack h rest) (mkCtx (cx_arrayLevel cx - 1) (cx_objectLevel cx))) ->
  LK = [] ->
  at_switch TK_right_brace.
Proof. aceil.
  intros AL YL LK0. unfold at_switch.
  (* [comment removed for export] *)
  popen OK PM; yhide TB; yhide OTB; yhide LP; yhide FFR0.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US.
  assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (pb_HSB _ _ _ PB) as SEPHS; pose proof (pb_SB _ _ _ PB) as RSB. pose proof (pb_SBA PB) as RSBA.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_Tsep0 pa_OT0 pa_j0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_stack mh h SB1)) ltac:(cbn; lia))) as OSH_S; cbn [ab_addr ab_size] in OSH_S.
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H, OSH_S.
  destruct OSH_H as (_ & _ & SHH); destruct OSH_S as (_ & _ & SHS); rewrite EH in SHH.
  remember (blk_shadow 104) as shb eqn:SHHeq in SHH; remember (blk_shadow (h_stack_size h)) as shs eqn:SHSeq in SHS.
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold wz in HC; rewrite EH in HC.
  clear TXT LXR DBR FF GAP PRES UA CRED HS HR; yhide SV. unfold wz in FR.
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC). yhide SC. pose proof (pb_SBCX _ _ _ PB) as SEPSC.
  (* [comment removed for export] *)
  pose proof YS as (CBS & _ & _ & STA). unfold callbacks_cells in CBS.
  cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ayc] in CBS.
  unfold AY_CALLBACKS, AY_CB_NULL, AY_CB_BOOLEAN, AY_CB_NUMBER, AY_CB_STRING, AY_CB_START_MAP, AY_CB_MAP_KEY, AY_CB_END_MAP, AY_CB_START_ARRAY, AY_CB_END_ARRAY, wz in CBS.
  destruct (GLOBY _ _ _ _ _ AHK) as (GCB & _). unfold oshadow, A_SB, AY_CALLBACKS in GCB. destruct GCB as (_ & _ & GSH).
  unfold AY_CALLBACKS in HC.
  assert (SHB : 2148238848 <= 2147450880 + mh_addr (p_mh E) / 8 /\ 2147450880 + mh_addr (p_mh E) / 8 + 13 <= 17594333495296) by (clear -CEILB pa_H0; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  pose proof SHH as SHH0. yhide SHH0.
  pose proof (munch_refl [(p_lo E, bv_unsigned (Z_to_bv 64 (p_SQ E))); (pCX E, pCX E + 4); (mh_addr (p_mh E) + 60, mh_addr (p_mh E) + 64)] m) as MU.
  assert (USQ : bv_unsigned (Z_to_bv 64 (p_SQ E)) = p_SQ E) by (apply unsigned_lit; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_sp0; lia). pose proof (wmono_refl asegs m) as WM.
  unfold pstate, AGV_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_imgsh0, pp_CX0, pp_CXs0. clear pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_SB0 pp_SBs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0.
  zstepA. zstepA. if_false.                                (* [comment removed for export] *)
  zstepA. zstepA. if_false.                                (* [comment removed for export] *)
  zstepA. zstepA. if_false.                                (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  shH0 SHH SHHeq MU WM 8.                                  (* [comment removed for export] *)
  zstepA. if_true.                                         (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. if_false.                                        (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (SHR : ov_read_bytes asegs mx (Z_to_bv 64 2147537398) 1 = Some [Z_to_bv 8 0]);
    [ change 2147537398 with (2147450880 + (692064 + 80) / 8);
      apply (block_shadow_read0_u asegs mx 2147450880 692064 88 (692064 + 80) 8); [reflexivity| lia| exact GSH| lia| lia| reflexivity| reflexivity] |] end.
  zstepA. clear SHR.                                       (* [comment removed for export] *)
  zstepA. if_true.                                         (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. if_false.                                        (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  shH SHH SHHeq MU WM 8 8.                                 (* [comment removed for export] *)
  zstepA. if_true.                                         (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  rewrite ECX.
  zstepA.                                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ ?P _ _ => pose proof (YCEA P (pCX E) (p_lo E) cx) as CB end. unfold aycb_end_array_rpost in CB.
  call_spA CB.
  - exact STA.
  - exact CXR.
  - exact AL.
  - exact OCX.
  - exact MI.
  - rewrite USQ. exact STK.
  - clear -CEILB pa_ceil0; aceil; lia.
  - rewrite USQ. clear -CEILB pa_SQ0 pa_lo0; lia.
  - rewrite USQ. clear -CEILB pa_SQ0 pa_sp0; lia.
  - first [exact (pa_CXA8 PA) | rewrite ECX; exact (pa_CXA8 PA) | rewrite <- ECX; exact (pa_CXA8 PA)].   (* [comment removed for export] *)
  - clear -CEILB pa_CX0. aceil. lia.
  - reflexivity.
  - rewrite USQ. intros a k Ha Hk. apply pp_stk0; [exact Ha|]. clear -CEILB Hk pa_SQ0; lia.
  - intros a k Ha Hk. apply pp_img0; [exact Ha| exact Hk].
  - split; intros a k Ha Hk; [apply pp_CX0; [exact Ha| exact Hk]| apply pp_CXs0; revert Ha Hk; clear -CEILB pa_CX0; unfold oshw_lo, oshw_hi, A_SB, amem; intros; Z.div_mod_to_equations; lia].
  - (* [comment removed for export] *)
    lazymatch goal with H : stk asegs ?mx _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2 end.
    lazymatch goal with H : mem_inv asegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI2 end.
    lazymatch goal with H : RYajlRep.ctx_rep _ _ _ (mkCtx _ _) |- _ => rename H into CXR2 end.
    lazymatch goal with H : _ = Z_to_bv 64 1 |- _ => rewrite H | H : _ = wz 1 |- _ => rewrite H end. unfold wz.
    zstepA.                                                (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    yshow SHH0.
    yshow pa_CXP0.   (* [comment removed for export] *)
    shH SHH0 SHHeq MU WM 60 4.                             (* [comment removed for export] *)
    zstepA. if_true.                                       (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
    pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    yshow TB. yshow OTB. yshow LP. yshow FFR0. yshow SV. yshow SC. rewrite USQ in MU, ST2.
    assert (PM2 : pmem E m2 mo1 s LK h mh (mkCtx (cx_arrayLevel cx - 1) (cx_objectLevel cx)) obw olw cr).
    { eapply (pmem_updA BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s LK h mh cx obw olw cr);
        [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| exact MI2| | reflexivity| reflexivity| reflexivity| reflexivity| exact I| |
        | exact CXR2
        | exists k0, k224; assumption
        | eapply (rw_cells_transport asegs); [exact SV| exact MU| exact WM| unfold psaved; cbn; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_H0 pa_CX0; lia]
        | exact ST2 ].
      - constructor; [| constructor; [| constructor; [| constructor]]]; unfold ownA; cbn [fst snd].
        + right; right; right. clear -CEILB pa_SQ0. lia.
        + right; right; left. clear. lia.
        + left. rewrite EH. clear. lia.
      - split; [| cbn [h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB;
                 split; [exact BC1| split; [exact BC2| split; [exact BC3| intros; split; intros; congruence]]]].
        exists pew, pad. split; [| exact PW].
        unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app]. unfold wz. rewrite EH.
        lazymatch goal with H0 : rw_cells asegs m2 (mh_addr (p_mh E)) _ |- _ => exact H0 end.
      - eapply (rw_cells_transport asegs) in SC; [| exact MU| exact WM| cbn; clear -CEILB SEPHS RSB SEPSC US USED Z0 EH pa_ceil0; lia].
        unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC. }
    pose proof (J_pop Y KIPY FRAMEY BLKY BSHY LAYY RRT UFRAME E F fc m2 mo1 s LK h0 cx0 h mh (mkCtx (cx_arrayLevel cx - 1) (cx_objectLevel cx)) obw olw cr ST_array_got_val rest) as JP.
    unfold pstate, J_POP, wz in JP.
    eapply JP; [exact PA| exact OK| exact PM2| | exact FRM| exact HST| exact SZM'| left; exact LK0| exact YL| exact AG].
    apply (pcr_full YHM E _ _ PA).
    destruct YSPLIT as (EQ & _ & _ & POP & _). rewrite (EQ (h_set_stack h rest) (pLEN E)). rewrite (EQ h (pLEN E)) in HCR.
    cbn [h_set_stack h_lexer h_decbuf h_bytesConsumed h_stack_size].
    replace (h_used (h_set_stack h rest)) with (h_used h - 1) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; unfold zlength; cbn [length]; clear; lia).
    pose proof (POP (h_bytesConsumed h) (h_used h) (h_stack_size h) (pLEN E) ltac:(clear -CEILB USED Z0; lia)) as PL. clear -CEILB HCR PL. lia.
Qed.

(* [comment removed for export] *)
Lemma agv_default : forall tok,
  tok_code tok <> 2 -> tok_code tok <> 3 -> tok_code tok <> 4 -> tok_code tok <> 8 ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_array_expect) cx) ->
  at_switch tok.
Proof. aceil.
  intros tok N2 N3 N4 N8 YL. unfold at_switch.
  pose proof PM as (AY & _). apply AYST_split in AY. destruct AY as [AHK _].
  pose proof (tok_code_range tok) as TR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold pstate, AGV_SW, wz. arz_seg KIPY AHK.
  Local Ltac tk K TR N2 N3 N4 N8 := first [ exfalso; clear -K TR N2 N3 N4 N8; revert K; unfold wz; rewrite ?unsigned_lit by lia; rewrite ?signed_lit_small by lia; lia | idtac ].
  zstepA. zstepA. if_cases K1; zify_cond K1; tk K1 TR N2 N3 N4 N8.      (* [comment removed for export] *)
  - (* [comment removed for export] *)
    zstepA. zstepA. if_cases K2; zify_cond K2; tk K2 TR N2 N3 N4 N8.    (* [comment removed for export] *)
    zstepA. zstepA. if_cases K3; zify_cond K3; tk K3 TR N2 N3 N4 N8.    (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    pose proof PM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ R1] & _).
    pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    pose proof (agv_ptail Y KIPY FRAMEY BLKY BSHY LAYY RRT YHM UFRAME phr YSPLIT E F fc m s LK h0 cx0 h mh cx obw olw cr rest rav t0 t1 a2 a3 a4 a5 a6 a7 s5v t3 t4 t5 t6
                  PA OK HCR FRM HST SZM' LKL AG mo1) as PT. unfold pstate, AGV_PT, wz in PT.
    eapply PT; [exact PM1| exact YL].
  - (* [comment removed for export] *)
    zstepA. zstepA. if_cases K2; zify_cond K2; tk K2 TR N2 N3 N4 N8.    (* [comment removed for export] *)
    zstepA. zstepA. if_cases K3; zify_cond K3; tk K3 TR N2 N3 N4 N8.    (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    pose proof PM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ R1] & _).
    pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    pose proof (agv_ptail Y KIPY FRAMEY BLKY BSHY LAYY RRT YHM UFRAME phr YSPLIT E F fc m s LK h0 cx0 h mh cx obw olw cr rest rav t0 t1 a2 a3 a4 a5 a6 a7 s5v t3 t4 t5 t6
                  PA OK HCR FRM HST SZM' LKL AG mo1) as PT. unfold pstate, AGV_PT, wz in PT.
    eapply PT; [exact PM1| exact YL].
Qed.
End AGV.

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis YLX : aylex_lex_stmt Y.
Variable URA : list Z.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells asegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis URA_lex : forall pc, lex_site pc -> In (pc + 48) URA.

Lemma pass_agv : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h mh cx
    (rav t0 t1 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 : word) rest,
  penvA E -> phead_inv E fc m mo s LK h mh cx -> h_stack h = ST_array_got_val :: rest ->
  pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h cx) (SR_done st h' cx')) ->
  (forall (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : y_APS Y) (LK' : list ablock) (h' : yhandle) (mh' : mhand) (cx' : yctx)
          (rav' t0' t1' a1' a2' a3' a4' a5' a6' a7' s4v' s5v' t3' t4' t5' t6' : word),
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h cx) (SR_again h' cx') ->
     phead_inv E fc' m' mo' s' (LK' ++ LK) h' mh' cx' ->
     realizes_cfg acfg asegs (mkCfg (phead E F' fc' m' (h_used h') rav' t0' t1' a1' a2' a3' a4' a5' a6' a7' s4v' s5v' t3' t4' t5' t6') mo') (p_K E)) ->
  realizes_cfg acfg asegs (mkCfg (phead E F fc m (h_used h) rav t0 t1 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until rest. intros PA HI HST EXIT AGAIN.
  pose proof HI as ((obw & olw & cr & PM & HCR0) & OK & FRM & PLK).
  pose proof (plk_ok_lex LK h _ _ PLK HST eq_refl) as LK0.
  pose proof OK as (_ & _ & _ & (_ & SZM) & _).
  eapply (pass_lex Y KIPY BLKY BSHY LAYY PERMY RRT YLX URA USTEP URA_lex UFRAME NONNEG phr YSPLIT E F fc m mo s LK h mh cx
            rav t0 t1 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 ST_array_got_val rest); [exact PA| exact HI| exact HST| reflexivity|].
  intros until cr'. intros YL LPOST HINV FRM' LKT PM1 PPOT. cbn [state_targetA Z.add Pos.add].
  pose proof (hinv_weak _ _ _ HINV) as (_ & US & _).
  assert (HCR : y_phi_hand Y (h_set_lex_off h lx' off') (pLEN E) <= cr').
  { unfold ppot in PPOT. destruct YSPLIT as (EQ & _ & LX & _). rewrite (EQ (h_set_lex_off h lx' off') (pLEN E)).
    unfold h_used in PPOT |- *. unfold h_set_lex_off in PPOT |- *. cbn [h_lexer h_decbuf h_bytesConsumed h_stack_size h_stack] in PPOT |- *.
    destruct LPOST as (OFF & _). pose proof (LX (h_bytesConsumed h) off' (zlength (h_stack h)) (h_stack_size h) (pLEN E) ltac:(clear -CEILB OFF; lia)) as L1.
    clear -CEILB PPOT L1. lia. }
  assert (HST1 : h_stack (h_set_lex_off h lx' off') = ST_array_got_val :: rest) by exact HST.
  assert (SZM1 : h_stack_size (h_set_lex_off h lx' off') mod 8 = 0) by exact SZM.
  assert (LKL : (length (LK' ++ LK) <= 1)%nat).
  { rewrite LK0, app_nil_r. destruct LK' as [|b0 LK'']; [cbn; clear; lia|]. destruct (LKT ltac:(discriminate)) as [_ L1]. rewrite L1. clear; lia. }
  assert (AG : pagain Y E h cx (LK' ++ LK)) by (unfold pagain; intros; eapply AGAIN; eassumption).
  pose proof (step_agv (p_txt E) (pLEN E) h cx rest lx' tok off' ob n) as SL.
  pose proof HINV as (_ & _ & _ & _ & (FROK & _ & _ & _ & EOL & EAL) & _).
  assert (AL : 0 < cx_arrayLevel cx) by (rewrite EAL, HST; cbn; pose proof (count_array_nonneg rest); lia).
  destruct tok.
  all: first [ eapply agv_rbrace | eapply agv_comma | eapply agv_error | eapply agv_eof | eapply agv_default ].
  all: lazymatch goal with
       | |- penvA _ => exact PA
       | |- pok _ _ _ => exact OK
       | |- pmem _ _ _ _ _ _ _ _ _ _ _ => exact PM1
       | |- y_phi_hand _ _ _ <= _ => exact HCR
       | |- frm0 _ => exact FRM'
       | |- h_stack _ = _ => exact HST1
       | |- _ mod 8 = 0 => exact SZM1
       | |- (length _ <= 1)%nat => exact LKL
       | |- pagain _ _ _ _ _ => exact AG
       | |- pexit_cont _ _ => exact EXIT
       | |- 0 < cx_arrayLevel _ => exact AL
       | |- AHK_y_globals_shadow_stmt _ => exact GLOBY
       | |- aycb_end_array_stmt => exact YCEA
       | |- tok_code _ <> _ => cbn; clear; lia
       | |- _ ++ _ = [] => rewrite LK0, app_nil_r; destruct LK' as [|b0 LK'']; [reflexivity| destruct (LKT ltac:(discriminate)) as [[X|X] _]; discriminate X]
       | |- yphi_hand_split_stmt _ _ => exact YSPLIT
       | |- _ => try first [assumption | eassumption]
       end.
  all: apply (SL _ HST YL); cbn beta iota.
  all: try (rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_used h_stack h_set_lex_off]; exact US); cbn [ybind]; apply yl_ret).
  all: try apply yl_ret.
  all: try (unfold yparse_error; rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_used h_stack h_set_lex_off]; exact US); cbn [ybind]; apply yl_ret).
  (* [comment removed for export] *)
  cbn [cb_end_array jf_callbacks]. unfold yassert. destruct (Z.ltb_spec 0 (cx_arrayLevel cx)); [| exfalso; clear -CEILB AL H; lia]. cbn [ybind].
  rewrite (ybs_pop_eq _ _ _ HST1). cbn [ybind]. apply yl_ret.
Qed.

End W.
End RC__1.
