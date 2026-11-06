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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BY_rz BY_hand BY_acct_needs BY_parse_kit BY_parse_pol BY_parse_head BY_parse_lex BY_parse_lexc BY_parse_epi BY_parse_tails BY_parse_tails2 BY_parse_sep BY_parse_agv BY_parse_map.
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
Definition MAP_SW : Z := 0x87ed8.      (* [comment removed for export] *)
Definition MAP_DT : Z := 0x88338.      (* [comment removed for export] *)
Definition MAP_RB : Z := 0x8823c.      (* [comment removed for export] *)
Definition MAP_ERR : Z := 0x87f04.     (* [comment removed for export] *)

Definition map_state (s : ystate) : bool :=
  match s with ST_map_start | ST_map_need_key => true | _ => false end.
Lemma map_state_target : forall st, map_state st = true -> state_targetA st = 0x87ea8.
Proof. aceil. intros []; cbn; congruence. Qed.
Lemma map_state_lex : forall st, map_state st = true -> lex_state st = true.
Proof. aceil. intros []; cbn; congruence. Qed.

(* [comment removed for export] *)
Lemma step_map : forall txt len h cx st rest lx tok off ob n r,
  h_stack h = st :: rest -> map_state st = true ->
  yleaf (ylex_lex (h_lexer h) txt len (h_bytesConsumed h)) (lx, tok, off, ob, n) ->
  yleaf (let h := h_set_lex_off h lx off in
         let bytes := out_bytes txt lx ob n in
         let on_key := fun (h : yhandle) (kbytes : list Z) (kn : Z) =>
                         cx1 <- cb_map_key jf_callbacks cx kbytes kn ;;
                         h1 <- ybs_set h ST_map_sep ;;
                         YRet (SR_again h1 cx1) in
         match tok with
         | TK_eof => YRet (SR_done YS_insufficient_data h cx)
         | TK_error => h1 <- ybs_set h ST_lexical_error ;; YRet (SR_again h1 cx)
         | TK_string_esc =>
             h1 <- ydecode_tok h bytes n ;;
             if ybuf_err (h_decbuf h1) then ybuf_chk_fail h1 cx
             else
               _d <- ybuf_data_chk (h_decbuf h1) ;;
               m <- ybuf_len_chk (h_decbuf h1) ;;
               on_key h1 (yb_bytes (h_decbuf h1)) m
         | TK_string => on_key h bytes n
         | TK_right_bracket =>
             cur1 <- ybs_current h ;;
             if state_eqb cur1 ST_map_start then
               cx1 <- cb_end_map jf_callbacks cx ;;
               h1 <- ybs_pop h ;;
               YRet (SR_again h1 cx1)
             else yparse_error h cx PE_invalid_object_key
         | _ => yparse_error h cx PE_invalid_object_key
         end) r ->
  yleaf (yparse_step jf_callbacks txt len h cx) r.
Proof. aceil.
  intros until r. intros HST MST YL YR. unfold yparse_step. rewrite (ybs_current_eq h _ _ HST). cbn [ybind].
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
Lemma YH_shape : yphi_hand_shape_stmt Y.
Proof. aceil.
  intros h1 h2 L E1 E2 E3 E4 E5 _. destruct YSPLIT as (EQ & _). rewrite (EQ h1 L), (EQ h2 L), E1, E2, E3, E4, E5. reflexivity.
Qed.

Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis YCEM : aycb_end_map_stmt.

Hypothesis YCMK : aycb_map_key_stmt.

Definition MAP_KT : Z := 0x884d8.

(* [comment removed for export] *)
Lemma map_ktail : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h0 cx0 h mh cx obw olw cr st rest
    (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> y_phi_hand Y h (pLEN E) <= cr -> frm0 fc ->
  h_stack h = st :: rest -> h_stack_size h mod 8 = 0 -> LK = [] -> 0 < cx_objectLevel cx ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_stack h (ST_map_sep :: rest)) cx) ->
  pagain Y E h0 cx0 LK ->
  realizes_cfg acfg bsegs (mkCfg (pstate E MAP_KT F fc m rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz (p_ff E)) s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM HCR FRM HST SZM' LK0 OL YL AG.
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
  clear TXT LXR DBR GAP PRES UA CRED HS HR; yhide SV. unfold wz in FR.
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC). yhide SC. pose proof (pb_SBCX _ _ _ PB) as SEPSC.
  pose proof FF as (FFA & FOB & FJ2 & FOL & FJ3 & FSH). clear FFA FJ2 FJ3 FSH.
  (* [comment removed for export] *)
  pose proof YS as (CBS & _ & _ & STA). unfold callbacks_cells in CBS.
  cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ayc] in CBS.
  unfold AY_CALLBACKS, AY_CB_NULL, AY_CB_BOOLEAN, AY_CB_NUMBER, AY_CB_STRING, AY_CB_START_MAP, AY_CB_MAP_KEY, AY_CB_END_MAP, AY_CB_START_ARRAY, AY_CB_END_ARRAY, wz in CBS.
  destruct (GLOBY _ _ _ _ _ AHK) as (GCB & _). unfold oshadow, A_SB, AY_CALLBACKS in GCB. destruct GCB as (_ & _ & GSH).
  unfold AY_CALLBACKS in HC.
  assert (SHB : 2148238848 <= 2147450880 + mh_addr (p_mh E) / 8 /\ 2147450880 + mh_addr (p_mh E) / 8 + 13 <= 17594333495296) by (clear -CEILB pa_H0; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  pose proof SHH as SHH0. yhide SHH0. pose proof SHS as SHS0. yhide SHS0.
  pose proof (munch_refl [(p_lo E, bv_unsigned (Z_to_bv 64 (p_SQ E)))] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (USQ : bv_unsigned (Z_to_bv 64 (p_SQ E)) = p_SQ E) by (apply unsigned_lit; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_sp0; lia).
  unfold pstate, MAP_KT, wz.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_imgsh0, pp_CX0, pp_CXs0, pp_SB0, pp_SBs0, pp_ff0. clear pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_ffs0 pp_T0 pp_Ts0.
  zstepA.                                                  (* [comment removed for export] *)
  shH0 SHH SHHeq MU WM 8.                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA. ugd_bs.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (SHR : ov_read_bytes bsegs mx (Z_to_bv 64 2147537775) 1 = Some [Z_to_bv 8 0]);
    [ change 2147537775 with (2147450880 + (695104 + 56) / 8);
      apply (block_shadow_read0_u bsegs mx 2147450880 695104 88 (695104 + 56) 8); [reflexivity| lia| exact GSH| lia| lia| cbn; lia| reflexivity] |] end.
  assert (POLSH : acc_ok (m_vm_lazy mo) (y_aS Y s) (Z_to_bv 64 2147537775, 1%nat)) by (yshow pp_imgsh0; apply (pp_imgsh0 2147537775 1%nat); clear; cbn; lia).  (* [comment removed for export] *)
  zstepA. clear SHR POLSH.                                       (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  shH SHH SHHeq MU WM 8 8.                                 (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  rewrite ECX.
  zstepA.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ ?P _ _ => pose proof (YCMK P (pCX E) (p_lo E) cx) as CB end. unfold aycb_map_key_rpost in CB.
  clear GSH SHS SHH. yhide STK.  (* [comment removed for export] *)
  call_spA CB.
  - (* [comment removed for export] *) hnf. clear -CEILB pa_CX0 ECX. rewrite ?ECX. split; [lia| Z.div_mod_to_equations; lia].
  - exact STA.
  - exact CXR.
  - exact OL.
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
    lazymatch goal with H : stk bsegs ?mx _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2 end.
    lazymatch goal with H : mem_inv bsegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI2 end.
    lazymatch goal with H : RYajlRep.ctx_rep _ ?mx _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into CXR2 end.
    lazymatch goal with H : _ = Z_to_bv 64 1 |- _ => rewrite H | H : _ = wz 1 |- _ => rewrite H end. unfold wz.
    zstepA. iflit2.                                        (* [comment removed for export] *)
    yshow SHH0. yshow SHS0.
    yshow pa_CXP0.   (* [comment removed for export] *)
    shH SHH0 SHHeq MU WM 60 4.                             (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia). (* [comment removed for export] *)
    bs_inline2 SHH0 SHHeq SHS0 SHSeq MU WM BC2 BC3 USED Z0 US h.
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. zstepA.                                        (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
    pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    yshow TB. yshow OTB. yshow LP. yshow FFR0. yshow SV. yshow SC. rewrite USQ in MU, ST2.
    assert (PM2 : pmem E m2 mo1 s LK h mh cx obw olw cr).
    { eapply (pmem_updA BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s LK h mh cx obw olw cr);
        [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| exact MI2| | reflexivity| reflexivity| reflexivity| reflexivity| exact I| |
        | exact CXR2
        | exists k0, k224; assumption
        | eapply (rw_cells_transport bsegs); [exact SV| exact MU| exact WM| unfold psaved; cbn; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0; lia]
        | exact ST2 ].
      - constructor; [| constructor]. unfold ownA; cbn [fst snd]. right; right; right. clear -CEILB pa_SQ0. lia.
      - split; [| cbn [h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB;
                 split; [exact BC1| split; [exact BC2| split; [exact BC3| intros; split; intros; congruence]]]].
        exists pew, pad. split; [| exact PW].
        unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app]. unfold wz. rewrite EH.
        lazymatch goal with H0 : rw_cells bsegs m2 (mh_addr (p_mh E)) _ |- _ => exact H0 end.
      - eapply (rw_cells_transport bsegs) in SC; [| exact MU| exact WM| cbn; clear -CEILB RSB pa_ceil0 US USED Z0; lia].
        unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC. }
    replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + (h_used h - 1)) by (clear; lia).
    change (Z_to_bv 64 5) with (wz (state_code ST_map_sep)).
    pose proof (J_setb Y KIPY FRAMEY BLKY BSHY LAYY RRT UFRAME E F fc m2 mo1 s LK h0 cx0 h mh cx obw olw cr st rest ST_map_sep) as JS.
    unfold pstate, J_SETB, wz in JS.
    eapply JS; [exact PA| exact OK| exact PM2| exact FRM| exact HST| exact SZM'| exact YL| | left; exact LK0| exact AG].
    apply (pcr_full YHM E _ _ PA). rewrite (YH_shape (h_set_stack h (ST_map_sep :: rest)) h (pLEN E));
      [exact HCR| reflexivity| reflexivity| reflexivity| unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity| reflexivity| reflexivity].
Qed.

Section MAP.
Variables (E : apE Y) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : y_APS Y) (LK : list ablock)
          (h0 : yhandle) (cx0 : yctx) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (cr : Z) (st : ystate) (rest : list ystate).
Variables (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5v t3 t4 t5 t6 : word).
Hypothesis PA : penvA E.
Hypothesis OK : pok E h0 cx0.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw cr.
Hypothesis HCR : y_phi_hand Y h (pLEN E) <= cr.
Hypothesis FRM : frm0 fc.
Hypothesis HST : h_stack h = st :: rest.
Hypothesis MST : map_state st = true.
Hypothesis SZM' : h_stack_size h mod 8 = 0.
Hypothesis LKL : (length LK <= 1)%nat.
Hypothesis AG : pagain Y E h0 cx0 LK.
Hypothesis EX : pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')).

Let at_switch (tok : ytok) : Prop :=
  realizes_cfg acfg bsegs (mkCfg (pstate E MAP_SW F fc m rav t0 t1 t2 (wz (tok_code tok)) a1 a2 a3 a4 a5 a6 a7 (wz 0) (wz (p_ff E)) s5v t3 t4 t5 t6) mo) (p_K E).   (* [comment removed for export] *)


(* [comment removed for export] *)
Lemma map_string :
  0 < cx_objectLevel cx ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_stack h (ST_map_sep :: rest)) cx) ->
  LK = [] ->
  at_switch TK_string.
Proof. aceil.
  intros OL YL LK0. unfold at_switch.
  pose proof PM as (AY & _ & _ & _ & _ & (k0 & k224 & FR) & _ & _ & _ & _ & _ & MI & _ & _ & _ & [_ R1] & _). apply AYST_split in AY. destruct AY as [AHK _].
  unfold pframe, wz in FR. openPA PA.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, MAP_SW, wz. cbn [tok_code]. arz_seg KIPY AHK.
  pose proof (aypol_stack Y _ _ _ _ LINK (p_lo E) (pSP E) ltac:(clear -CEILB pa_ceil0; aceil; lia) ltac:(clear -CEILB pa_sp0; lia)) as PSTK.
  pose proof (aypol_img Y _ _ _ _ LINK) as PIMG. unfold pol, AY_IMG_LO, AY_IMG_HI in PSTK, PIMG. pose proof (ppol_mark E mh) as PPM.
  map_jt MI TK_string.
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  pose proof (map_ktail E F fc m mo1 s LK h0 cx0 h mh cx obw olw cr st rest) as KT. unfold pstate, MAP_KT, wz in KT.
  eapply KT; [exact PA| exact OK| exact PM1| exact HCR| exact FRM| exact HST| exact SZM'| exact LK0| exact OL| exact YL| exact AG].
Qed.
End MAP.
End W.
End RC__1.
