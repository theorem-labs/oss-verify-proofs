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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_acct_needs AY_parse_kit AY_parse_pol AY_parse_head AY_parse_lex AY_parse_lexc AY_parse_epi AY_parse_tails AY_parse_tails2 AY_parse_sep AY_parse_agv AY_parse_map AY_parse_kitD AY_parse_kitD2 AY_parse_gv AY_parse_gv2 AY_parse_kitV AY_parse_gv3 AY_parse_val AY_parse_val2 AY_parse_val3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 small_ctx2 () := if Ltac2.Int.le (Ltac2.List.length (Ltac2.Control.hyps ())) 60 then () else Ltac2.Control.backtrack_tactic_failure "big context".
Definition allow_big_lia : Prop := True.
Ltac small_ctx := first [ match goal with H : allow_big_lia |- _ => idtac end | ltac2:(small_ctx2 ()) ].
Local Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | LiaTuning.zify_lia_keep1
        | small_ctx; Zify.zify; xlia zchecker ].
Local Ltac qlia_sep ::= first [ solve [LiaTuning.zify_prune; Zify.zify; xlia zchecker]
                       | solve [unfold yhide in *; LiaTuning.zify_lia_keep1]
                       | solve [unfold yhide in *; keep_sep; Z.div_mod_to_equations; lia]
                       | unfold yhide in *; Z.div_mod_to_equations; Zify.zify; xlia zchecker ].
Local Open Scope yprog_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma val_state_target : forall st, val_state st = true -> state_targetA st = 0x8759c.
Proof. aceil. intros [] H; cbn in H; try discriminate; reflexivity. Qed.
Lemma val_state_lex : forall st, val_state st = true -> lex_state st = true.
Proof. aceil. intros [] H; cbn in H; try discriminate; reflexivity. Qed.

Lemma step_val : forall txt len h cx st rest lx tok off ob n r,
  h_stack h = st :: rest -> val_state st = true ->
  yleaf (ylex_lex (h_lexer h) txt len (h_bytesConsumed h)) (lx, tok, off, ob, n) ->
  yleaf (let h := h_set_lex_off h lx off in
         let bytes := out_bytes txt lx ob n in
         match tok with
         | TK_eof => YRet (SR_done YS_insufficient_data h cx)
         | TK_error => h1 <- ybs_set h ST_lexical_error ;; YRet (SR_again h1 cx)
         | TK_string => cx1 <- cb_string jf_callbacks cx bytes n ;; ygot_value h cx1 None
         | TK_string_esc =>
             h1 <- ydecode_tok h bytes n ;;
             if ybuf_err (h_decbuf h1) then ybuf_chk_fail h1 cx
             else
               _d <- ybuf_data_chk (h_decbuf h1) ;;
               m <- ybuf_len_chk (h_decbuf h1) ;;
               cx1 <- cb_string jf_callbacks cx (yb_bytes (h_decbuf h1)) m ;;
               ygot_value h1 cx1 None
         | TK_bool => cx1 <- cb_boolean jf_callbacks cx (if znth bytes 0 =? c_t then 1 else 0) ;; ygot_value h cx1 None
         | TK_null => cx1 <- cb_null jf_callbacks cx ;; ygot_value h cx1 None
         | TK_left_bracket => cx1 <- cb_start_map jf_callbacks cx ;; ygot_value h cx1 (Some ST_map_start)
         | TK_left_brace => cx1 <- cb_start_array jf_callbacks cx ;; ygot_value h cx1 (Some ST_array_start)
         | TK_integer | TK_double => cx1 <- cb_number jf_callbacks cx bytes n ;; ygot_value h cx1 None
         | TK_right_brace =>
             cur1 <- ybs_current h ;;
             if state_eqb cur1 ST_array_start then
               cx1 <- cb_end_array jf_callbacks cx ;;
               h1 <- ybs_pop h ;;
               YRet (SR_again h1 cx1)
             else yparse_error h cx PE_unallowed_token
         | TK_colon | TK_comma | TK_right_bracket => yparse_error h cx PE_unallowed_token
         | TK_comment => yparse_error h cx PE_invalid_token_internal
         end) r ->
  yleaf (yparse_step jf_callbacks txt len h cx) r.
Proof. aceil.
  intros until r. intros HST VS YL YR. unfold yparse_step. rewrite (ybs_current_eq h _ _ HST). cbn [ybind].
  destruct st; try discriminate; (eapply yleaf_bind; [exact YL|]; cbn beta iota; exact YR).
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
Hypothesis YBC : aybuf_clear_stmt.
Hypothesis YBE : aybuf_err_stmt.
Hypothesis YBD : aybuf_data_stmt.
Hypothesis YBL : aybuf_len_stmt.
Hypothesis YSD : aystring_decode_stmt Y.
Hypothesis YSHAPE : yphi_shape_stmt Y.
Hypothesis YLX : aylex_lex_stmt Y.
Let YH_shape : yphi_hand_shape_stmt Y := YH_shape Y phr YSPLIT.

Section VAL.
Variables (E : apE Y) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : y_APS Y) (LK : list ablock)
          (h0 : yhandle) (cx0 : yctx) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (cr : Z) (st : ystate) (rest : list ystate).
Variables (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5v t3 t4 t5 t6 : word).
Hypothesis PA : penvA E.
Hypothesis OK : pok E h0 cx0.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw cr.
Hypothesis HCR : y_phi_hand Y h (pLEN E) <= cr.
Hypothesis FRM : frm0 fc.
Hypothesis HST : h_stack h = st :: rest.
Hypothesis VS : val_state st = true.
Hypothesis SZM' : h_stack_size h mod 8 = 0.
Hypothesis LKL : (length LK <= 1)%nat.
Hypothesis AG : pagain Y E h0 cx0 LK.
Hypothesis EX : pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')).

Let at_switch (tok : ytok) : Prop :=
  realizes_cfg acfg asegs (mkCfg (pstate E VAL_SW F fc m rav t0 t1 t2 (wz (tok_code tok)) a1 a2 a3 a4 a5 a6 a7 (wz 0) (wz (pH E + 64)) s5v t3 t4 t5 t6) mo) (p_K E).

(* [comment removed for export] *)
Lemma val_rbrace :
  (st = ST_array_start -> 0 < cx_arrayLevel cx /\
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_stack h rest) (mkCtx (cx_arrayLevel cx - 1) (cx_objectLevel cx)))) ->
  (st <> ST_array_start ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_unallowed_token) cx)) ->
  LK = [] ->
  at_switch TK_right_brace.
Proof. aceil.
  intros YST YNK LK0. unfold at_switch.
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
  destruct BSR' as (SBNZ & junk & SC).
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2).
  rewrite HST in ARR.
  pose proof (u8arr_read asegs m (mh_stack mh) _ (zlength rest) (Z_to_bv 8 (state_code st)) _ ARR ltac:(apply stack_top_byte) ltac:(clear -CEILB Z0; lia) eq_refl) as RK.
  yhide SC. clear ARR. pose proof (pb_SBCX _ _ _ PB) as SEPSC.
  (* [comment removed for export] *)
  pose proof YS as (CBS & _ & _ & STA). unfold callbacks_cells in CBS.
  cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ayc] in CBS.
  unfold AY_CALLBACKS, AY_CB_NULL, AY_CB_BOOLEAN, AY_CB_NUMBER, AY_CB_STRING, AY_CB_START_MAP, AY_CB_MAP_KEY, AY_CB_END_MAP, AY_CB_START_ARRAY, AY_CB_END_ARRAY, wz in CBS.
  destruct (GLOBY _ _ _ _ _ AHK) as (GCB & _). unfold oshadow, A_SB, AY_CALLBACKS in GCB. destruct GCB as (_ & _ & GSH).
  unfold AY_CALLBACKS in HC.
  assert (SHB : 2148238848 <= 2147450880 + mh_addr (p_mh E) / 8 /\ 2147450880 + mh_addr (p_mh E) / 8 + 13 <= 17594333495296) by (clear -CEILB pa_H0; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  pose proof SHH as SHH0. yhide SHH0.
  pose proof (munch_refl [(p_lo E, bv_unsigned (Z_to_bv 64 (p_SQ E))); (pCX E, pCX E + 4); (mh_addr (p_mh E) + 60, mh_addr (p_mh E) + 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (USQ : bv_unsigned (Z_to_bv 64 (p_SQ E)) = p_SQ E) by (apply unsigned_lit; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_sp0; lia).
  pose proof (state_code_range st) as CR.
  unfold pstate, VAL_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_imgsh0, pp_CX0, pp_CXs0, pp_SB0, pp_SBs0. clear pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0.
  val_jt MI TK_right_brace.
  shH SHH SHHeq MU WM 60 4.                                (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia).   (* [comment removed for export] *)
  zstepA. if_cases KU; zify_cond KU; bkill KU BC2 BC3 US USED Z0.   (* [comment removed for export] *)
  shH SHH SHHeq MU WM 48 8.                                (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. zstepA. zstepA. rewrite land_M32_small by (clear -CEILB USED Z0 US BC2; lia).   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  shS SHS SHSeq MU WM (h_used h + -1) (h_stack_size h).   (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + zlength rest) by (clear -CEILB USED; lia).
  change (wa (mh_stack mh + zlength rest)) with (Z_to_bv 64 (mh_stack mh + zlength rest)) in RK.
  zstepA. clear RK. cbv beta. rewrite (u8_val (state_code st)) by (clear -CEILB CR; lia).   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  destruct st; try discriminate VS; cbn [state_code state_eqb Z.eqb] in YST, YNK |- *.
  all: zstepA; iflit2.                                     (* [comment removed for export] *)
  (* [comment removed for export] *)
  1,2,4: apply evtA_done; intros mo1 Hag1 HLI1 Hh1; destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01];
         pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1;
         lazymatch goal with |- realizes_cfg _ _ (mkCfg (pstate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _) _ => idtac | _ => idtac end;
         pose proof (val_untail Y KIPY FRAMEY BLKY BSHY LAYY RRT YHM UFRAME phr YSPLIT E F fc m s LK h0 cx0 h mh cx obw olw cr _ rest rav t0 t1 a3 a4 a5 a6 a7 s5v t3 t4 t5 t6
                       PA OK HCR FRM HST SZM' LKL AG mo1) as VT;
         unfold pstate, VAL_UN, wz in VT; eapply VT; [exact PM1| exact (YNK ltac:(discriminate))].
  (* [comment removed for export] *)
  destruct (YST eq_refl) as [AL YL].
  zstepA.                                                  (* [comment removed for export] *)
  shH0 SHH SHHeq MU WM 8.                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (SHR : ov_read_bytes asegs mx (Z_to_bv 64 2147537398) 1 = Some [Z_to_bv 8 0]);
    [ change 2147537398 with (2147450880 + (692064 + 80) / 8);
      apply (block_shadow_read0_u asegs mx 2147450880 692064 88 (692064 + 80) 8); [reflexivity| lia| exact GSH| lia| lia| reflexivity| reflexivity] |] end.
  zstepA. clear SHR.                                       (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  shH SHH SHHeq MU WM 8 8.                                 (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  rewrite ECX.
  zstepA.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ ?P _ _ => pose proof (YCEA P (pCX E) (p_lo E) cx) as CB end. unfold aycb_end_array_rpost in CB.
  try clear GSH. try clear SHS. try clear SHH. call_spA CB.
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
    zstepA. iflit2.                                        (* [comment removed for export] *)
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
    pose proof (J_pop Y KIPY FRAMEY BLKY BSHY LAYY RRT UFRAME E F fc m2 mo1 s LK h0 cx0 h mh (mkCtx (cx_arrayLevel cx - 1) (cx_objectLevel cx)) obw olw cr ST_array_start rest) as JP.
    unfold pstate, J_POP, wz in JP.
    eapply JP; [exact PA| exact OK| exact PM2| | exact FRM| exact HST| exact SZM'| left; exact LK0| exact YL| exact AG].
    apply (pcr_full YHM E _ _ PA).
    pose proof YSPLIT as (EQ & _ & _ & POP & _). rewrite (EQ (h_set_stack h rest) (pLEN E)). rewrite (EQ h (pLEN E)) in HCR.
    cbn [h_set_stack h_lexer h_decbuf h_bytesConsumed h_stack_size].
    replace (h_used (h_set_stack h rest)) with (h_used h - 1) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; unfold zlength; cbn [length]; clear; lia).
    pose proof (POP (h_bytesConsumed h) (h_used h) (h_stack_size h) (pLEN E) ltac:(clear -CEILB USED Z0; lia)) as PL. clear -CEILB HCR PL. lia.
Qed.

(* [comment removed for export] *)
Lemma val_string_esc : forall (i n : Z),
  LK = [] -> obw = wz (p_T E + i) -> olw = wz n ->
  buf_inv (h_decbuf h) -> yb_state (h_decbuf h) = BS_ok ->
  0 <= i -> 0 <= n -> i + n < pLEN E -> sbody_ix (p_txt E) i (i + n) -> lex_inv (h_lexer h) -> h_stack_size h <= pLEN E + 1 + YAJL_BS_INC ->
  (forall db', yleaf (ystring_decode (buf_cleared (h_decbuf h)) (zslice (p_txt E) i n) n) db' -> yb_state db' = BS_ok ->
     gv_push Y E h0 cx0 (gv_handle (h_set_decbuf h db') st rest) cx (cr - y_phi_buf Y (h_decbuf h) + y_phi_buf Y db') (wz 1) (wz 0) None) ->
  (forall db', yleaf (ystring_decode (buf_cleared (h_decbuf h)) (zslice (p_txt E) i n) n) db' -> yb_state db' <> BS_ok ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0)
           (SR_done YS_alloc_failed (h_set_perr (h_set_stack (h_set_decbuf h db') (ST_parse_error :: rest)) PE_alloc_failed) cx)) ->
  (forall LKx, pagain Y E h0 cx0 LKx) ->
  at_switch TK_string_esc.
Proof. aceil.
  intros i n LK0 EOB EOL DBI DBOK I0 N0 INL SBX LXI SZB YOK YFAIL AGX. unfold at_switch. subst LK obw olw.
  pose proof PM as (AY & _ & _ & _ & _ & (k0 & k224 & FR) & _ & _ & _ & _ & _ & MI & _ & _ & _ & [_ R1] & _). apply AYST_split in AY. destruct AY as [AHK _].
  unfold pframe, wz in FR. openPA PA.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold pstate, VAL_SW, wz. cbn [tok_code]. arz_seg KIPY AHK.
  pose proof (aypol_stack Y _ _ _ _ LINK (p_lo E) (pSP E) ltac:(clear -CEILB pa_ceil0; aceil; lia) ltac:(clear -CEILB pa_sp0; lia)) as PSTK.
  pose proof (aypol_img Y _ _ _ _ LINK) as PIMG. unfold pol, AY_IMG_LO, AY_IMG_HI in PSTK, PIMG. pose proof (ppol_mark E mh) as PPM.
  val_jt MI TK_string_esc.
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  pose proof (pmem_remodel E m mo mo1 s [] h mh cx (wz (p_T E + i)) (wz n) cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  pose proof (vesc_main Y KIPY FRAMEY BLKY BSHY LAYY PERMY RRT NONNEG YHM RELY AFLSEP FLAGY UFRAME phr YSPLIT WREA URA USTEP URA_push URA_dec YRP GLOBY YCS YBC YBE YBD YBL YSD YSHAPE
                E h0 cx0 st rest PA OK EX F fc m mo1 s h mh cx cr i n (yb_data (h_decbuf h))) as ME. unfold pstate, VAL_ESC, wz in ME.
  eapply ME; [exact PM1| exact HCR| exact FRM| exact HST| exact SZM'| exact DBI| exact DBOK| reflexivity| exact I0| exact N0| exact INL| exact SBX| exact VS| exact LXI| exact SZB
             | exact YOK| exact YFAIL| exact AGX].
Qed.
End VAL.
End W.
End RC__1.
