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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlDecode YajlParser YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsParse YajlFactsLoop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BY_rz BY_hand BY_acct_needs BY_parse_kit BY_parse_pol BY_parse_head BY_parse_lex BY_parse_lexc BY_parse_epi BY_parse_tails BY_parse_tails2 BY_parse_sep BY_parse_agv BY_parse_map BY_parse_map2 BY_parse_mapk BY_parse_kitD BY_parse_kitD2 BY_parse_mape.
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
Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
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
Variable URA : list Z.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells bsegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis URA_lex : forall pc, lex_site pc -> In (pc + 48) URA.
Hypothesis URA_dec : forall pc, dec_site pc -> In pc URA.

Let YH_shape : yphi_hand_shape_stmt Y := YH_shape Y phr YSPLIT.

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
Hypothesis EX : pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')).

Let at_switch (tok : ytok) : Prop :=
  realizes_cfg acfg bsegs (mkCfg (pstate E MAP_SW F fc m rav t0 t1 t2 (wz (tok_code tok)) a1 a2 a3 a4 a5 a6 a7 (wz 0) (wz (p_ff E)) s5v t3 t4 t5 t6) mo) (p_K E).   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma map_string_esc : forall (i n : Z),
  LK = [] -> obw = wz (p_T E + i) -> olw = wz n ->
  buf_inv (h_decbuf h) -> yb_state (h_decbuf h) = BS_ok ->
  0 <= i -> 0 <= n -> i + n < pLEN E -> sbody_ix (p_txt E) i (i + n) -> 0 < cx_objectLevel cx ->
  (forall db', yleaf (ystring_decode (buf_cleared (h_decbuf h)) (zslice (p_txt E) i n) n) db' -> yb_state db' = BS_ok ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_stack (h_set_decbuf h db') (ST_map_sep :: rest)) cx)) ->
  (forall db', yleaf (ystring_decode (buf_cleared (h_decbuf h)) (zslice (p_txt E) i n) n) db' -> yb_state db' <> BS_ok ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0)
           (SR_done YS_alloc_failed (h_set_perr (h_set_stack (h_set_decbuf h db') (ST_parse_error :: rest)) PE_alloc_failed) cx)) ->
  (forall LKx, pagain Y E h0 cx0 LKx) ->
  at_switch TK_string_esc.
Proof. aceil.
  intros i n LK0 EOB EOL DBI DBOK I0 N0 INL SBX OL YOK YFAIL AGX. unfold at_switch. subst LK obw olw.
  pose proof PM as (AY & _ & _ & _ & _ & (k0 & k224 & FR) & _ & _ & _ & _ & _ & MI & _ & _ & _ & [_ R1] & _). apply AYST_split in AY. destruct AY as [AHK _].
  unfold pframe, wz in FR. openPA PA.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, MAP_SW, wz. cbn [tok_code]. arz_seg KIPY AHK.
  pose proof (aypol_stack Y _ _ _ _ LINK (p_lo E) (pSP E) ltac:(clear -CEILB pa_ceil0; aceil; lia) ltac:(clear -CEILB pa_sp0; lia)) as PSTK.
  pose proof (aypol_img Y _ _ _ _ LINK) as PIMG. unfold pol, AY_IMG_LO, AY_IMG_HI in PSTK, PIMG. pose proof (ppol_mark E mh) as PPM.
  map_jt MI TK_string_esc.
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  pose proof (pmem_remodel E m mo mo1 s [] h mh cx (wz (p_T E + i)) (wz n) cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  pose proof (mape_main Y KIPY FRAMEY BLKY BSHY LAYY PERMY RRT NONNEG YHM RELY AFLSEP FLAGY UFRAME phr YSPLIT GLOBY YCMK YBC YBE YBD YBL YBS YSD YSHAPE URA USTEP URA_dec
                E h0 cx0 st rest PA OK EX F fc m mo1 s h mh cx cr i n (yb_data (h_decbuf h))) as ME. unfold pstate, MAP_ESC, wz in ME.
  eapply ME; [exact PM1| exact HCR| exact FRM| exact HST| exact SZM'| exact DBI| exact DBOK| reflexivity| exact I0| exact N0| exact INL| exact SBX| exact OL| exact YOK| exact YFAIL| exact AGX].
Qed.
End MAP.

(* [comment removed for export] *)
Lemma pass_map : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h mh cx
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word) st rest,
  penvA E -> phead_inv E fc m mo s LK h mh cx -> h_stack h = st :: rest -> map_state st = true ->
  pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h cx) (SR_done st h' cx')) ->
  (forall (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : y_APS Y) (LK' : list ablock) (h' : yhandle) (mh' : mhand) (cx' : yctx)
          (rav' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2v' s5v' t3' t4' t5' t6' : word),
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h cx) (SR_again h' cx') ->
     phead_inv E fc' m' mo' s' (LK' ++ LK) h' mh' cx' ->
     realizes_cfg acfg bsegs (mkCfg (phead E F' fc' m' (h_used h') rav' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2v' s5v' t3' t4' t5' t6') mo') (p_K E)) ->
  realizes_cfg acfg bsegs (mkCfg (phead E F fc m (h_used h) rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until rest. intros PA HI HST MST EXIT AGAIN.
  pose proof HI as ((obw & olw & cr & PM & HCR0) & OK & FRM & PLK).
  pose proof (plk_ok_lex LK h _ _ PLK HST (map_state_lex _ MST)) as LK0.
  pose proof OK as (_ & _ & _ & (_ & SZM) & _).
  eapply (pass_lex Y KIPY BLKY BSHY LAYY PERMY RRT YLX URA USTEP URA_lex UFRAME NONNEG phr YSPLIT E F fc m mo s LK h mh cx
            rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 st rest); [exact PA| exact HI| exact HST| apply map_state_lex; exact MST|].
  intros until cr'. intros YL LPOST HINV FRM' LKT PM1 PPOT. rewrite (map_state_target _ MST). cbn [Z.add Pos.add].
  pose proof (hinv_weak _ _ _ HINV) as (_ & US & _).
  assert (HCR : y_phi_hand Y (h_set_lex_off h lx' off') (pLEN E) <= cr').
  { unfold ppot in PPOT. pose proof YSPLIT as (EQ & _ & LX & _). rewrite (EQ (h_set_lex_off h lx' off') (pLEN E)).
    unfold h_used in PPOT |- *. unfold h_set_lex_off in PPOT |- *. cbn [h_lexer h_decbuf h_bytesConsumed h_stack_size h_stack] in PPOT |- *.
    destruct LPOST as (OFF & _). pose proof (LX (h_bytesConsumed h) off' (zlength (h_stack h)) (h_stack_size h) (pLEN E) ltac:(clear -CEILB OFF; lia)) as L1.
    clear -CEILB PPOT L1. lia. }
  assert (HST1 : h_stack (h_set_lex_off h lx' off') = st :: rest) by exact HST.
  assert (SZM1 : h_stack_size (h_set_lex_off h lx' off') mod 8 = 0) by exact SZM.
  assert (LKL : (length (LK' ++ LK) <= 1)%nat).
  { rewrite LK0, app_nil_r. destruct LK' as [|b0 LK'']; [cbn; clear; lia|]. destruct (LKT ltac:(discriminate)) as [_ L1]. rewrite L1. clear; lia. }
  assert (AG : pagain Y E h cx (LK' ++ LK)) by (unfold pagain; intros; eapply AGAIN; eassumption).
  assert (AGX : forall LKx, pagain Y E h cx LKx).
  { intros LKx. unfold pagain. intros. eapply (AGAIN _ _ _ _ _ LKx); [eassumption|]. rewrite LK0, app_nil_r. eassumption. }
  pose proof (step_map (p_txt E) (pLEN E) h cx st rest lx' tok off' ob n) as SL.
  pose proof HINV as (_ & OFFB & DBI & DBOK & (FROK & _ & _ & _ & EOL & EAL) & _).
  assert (OL : 0 < cx_objectLevel cx) by (rewrite EOL, HST; pose proof (count_map_nonneg rest); destruct st; cbn in MST |- *; try discriminate; lia).
  assert (DBI1 : buf_inv (h_decbuf (h_set_lex_off h lx' off'))) by exact DBI.
  assert (DBOK1 : yb_state (h_decbuf (h_set_lex_off h lx' off')) = BS_ok) by exact DBOK.
  (* [comment removed for export] *)
  assert (GENS : (tok = TK_string \/ tok = TK_string_esc) ->
            exists i0, ob = OB_text i0 /\ 0 <= i0 /\ 0 <= n /\ i0 + n < pLEN E /\ sbody_ix (p_txt E) i0 (i0 + n)).
  { intros HT. destruct HT as [-> | ->]; cbn -[zslice znth] in LPOST;
      destruct LPOST as (OF1 & _ & _ & _ & _ & i1 & EOB & Hi & Hn & Hin & _ & _ & _ & Hoff & SB); exists i1; (split; [exact EOB|]);
      (split; [clear -CEILB Hi OFFB; lia| split; [exact Hn| split; [clear -CEILB Hoff OF1; lia| exact SB]]]). }
  destruct tok.
  all: first [ eapply map_eof | eapply map_error | eapply map_rbracket | eapply map_string
             | destruct (GENS (or_intror eq_refl)) as (i0 & EOB0 & I0 & N0 & INL & SBX); eapply map_string_esc with (i := i0) (n := n)
             | eapply map_default ].
  all: lazymatch goal with
       | |- penvA _ => exact PA
       | |- pok _ _ _ => exact OK
       | |- pmem _ _ _ _ _ _ _ _ _ _ _ => exact PM1
       | |- y_phi_hand _ _ _ <= _ => exact HCR
       | |- frm0 _ => exact FRM'
       | |- h_stack _ = _ => exact HST1
       | |- map_state _ = true => exact MST
       | |- _ mod 8 = 0 => exact SZM1
       | |- (length _ <= 1)%nat => exact LKL
       | |- pagain _ _ _ _ _ => exact AG
       | |- forall LKx, pagain _ _ _ _ LKx => exact AGX
       | |- pexit_cont _ _ => exact EXIT
       | |- 0 < cx_objectLevel _ => exact OL
       | |- buf_inv _ => exact DBI1
       | |- yb_state _ = BS_ok => exact DBOK1
       | |- wz _ = wz _ => rewrite ?EOB0; cbn [outref_addr]; reflexivity
       | |- 0 <= _ => assumption
       | |- _ + _ < _ => exact INL
       | |- sbody_ix _ _ _ => exact SBX
       | |- tok_code _ <> _ => cbn; clear; lia
       | |- _ ++ _ = [] => rewrite LK0, app_nil_r; destruct LK' as [|b0 LK'']; [reflexivity| destruct (LKT ltac:(discriminate)) as [[X|X] _]; discriminate X]
       | |- yphi_hand_split_stmt _ _ => exact YSPLIT
       | |- _ => try first [assumption | eassumption]
       end.
  all: try (intros db' YLD HDOK).
  all: apply (SL _ HST MST YL); cbv beta iota zeta; cbn [h_bytesConsumed h_set_lex_off h_decbuf out_bytes h_stack].
  all: try (unfold yparse_error; rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_used h_stack h_set_lex_off]; exact US); cbn [ybind]; apply yl_ret).
  all: try (rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_used h_stack h_set_lex_off]; exact US); cbn [ybind]; apply yl_ret).
  all: try apply yl_ret.
  (* [comment removed for export] *)
  1:{ rewrite (ybs_current_eq _ _ _ HST1). cbn [ybind]. destruct st; try discriminate MST; cbn [state_eqb state_code Z.eqb Pos.eqb].
      - cbn [cb_end_map jf_callbacks]. unfold yassert. destruct (Z.ltb_spec 0 (cx_objectLevel cx)); [| exfalso; clear -CEILB OL H; lia]. cbn [ybind].
        rewrite (ybs_pop_eq _ _ _ HST1). cbn [ybind]. apply yl_ret.
      - unfold yparse_error. rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_used h_stack h_set_lex_off]; exact US). cbn [ybind]. apply yl_ret. }
  (* [comment removed for export] *)
  1:{ cbn [cb_map_key jf_callbacks]. unfold yassert. destruct (Z.ltb_spec 0 (cx_objectLevel cx)); [| exfalso; clear -CEILB OL H; lia]. cbn [ybind].
      rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_used h_stack h_set_lex_off]; exact US). cbn [ybind]. apply yl_ret. }
  (* [comment removed for export] *)
  all: rewrite EOB0; cbn [out_bytes]; unfold ydecode_tok; cbn [h_decbuf h_set_lex_off];
       (eapply yleaf_bind; [eapply yleaf_bind; [apply ybuf_clear_leaf; exact DBOK|]; cbv beta; eapply yleaf_bind; [exact YLD|]; apply yl_ret|]);
       cbv beta; cbn [h_decbuf h_set_decbuf]; unfold ybuf_err, buf_state_ok, ybuf_data_chk, ybuf_len_chk.
  1:{ rewrite HDOK. cbn [negb ybind cb_map_key jf_callbacks]. unfold yassert. destruct (Z.ltb_spec 0 (cx_objectLevel cx)); [| exfalso; clear -CEILB OL H; lia]. cbn [ybind].
      rewrite (ybs_set_eq _ st rest) by (first [exact HST| cbn [h_stack_size h_set_decbuf h_set_lex_off]; unfold h_used; cbn [h_stack h_set_decbuf h_set_lex_off]; unfold h_used in US; exact US]).
      cbn [ybind]. apply yl_ret. }
  1:{ destruct (yb_state db'); [congruence| |]; cbn [negb ybind]; unfold ybuf_chk_fail;
      (rewrite (ybs_set_eq _ st rest) by (first [exact HST| cbn [h_stack_size h_set_decbuf h_set_lex_off]; unfold h_used; cbn [h_stack h_set_decbuf h_set_lex_off]; unfold h_used in US; exact US]));
      cbn [ybind]; apply yl_ret. }
Qed.
End W.
End RC__1.
