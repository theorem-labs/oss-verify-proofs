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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_acct_needs AY_parse_kit AY_parse_pol AY_parse_head AY_parse_lex AY_parse_lexc AY_parse_epi AY_parse_tails AY_parse_tails2 AY_parse_sep AY_parse_agv AY_parse_map AY_parse_kitD AY_parse_kitD2 AY_parse_gv AY_parse_gv2 AY_parse_kitV AY_parse_gv3 AY_parse_val AY_parse_val2.
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
Definition J_FAIL2 : Z := 0x892e8.     (* [comment removed for export] *)
Definition VAL_ESC : Z := 0x8818c.     (* [comment removed for export] *)
Definition VAL_EBK : Z := 0x88210.     (* [comment removed for export] *)
Definition VAL_RB : Z := 0x882d8.      (* [comment removed for export] *)

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
Hypothesis URA_dec : forall pc, dec_site pc -> In pc URA.
Hypothesis YRP : ayreset_parser_stmt.
Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis YCS : aycb_string_stmt.
Hypothesis YCEA : aycb_end_array_stmt.
Hypothesis YBC : aybuf_clear_stmt.
Hypothesis YBE : aybuf_err_stmt.
Hypothesis YBD : aybuf_data_stmt.
Hypothesis YBL : aybuf_len_stmt.
Hypothesis YSD : aystring_decode_stmt Y.
Hypothesis YSHAPE : yphi_shape_stmt Y.
Let YH_shape : yphi_hand_shape_stmt Y := YH_shape Y phr YSPLIT.

(* [comment removed for export] *)
Lemma J_fail2 : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h0 cx0 h mh cx obw olw cr st rest
    (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> y_phi_hand Y h (pLEN E) <= cr -> frm0 fc ->
  h_stack h = st :: rest -> h_stack_size h mod 8 = 0 -> (length LK <= 1)%nat ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0)
        (SR_done YS_alloc_failed (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_alloc_failed) cx) ->
  pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')) ->
  realizes_cfg acfg asegs (mkCfg (pstate E J_FAIL2 F fc m rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz (pH E + 64)) s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM HCR FRM HST SZM' LKL YL EX.
  popen OK PM; yhide TB; yhide OTB; yhide FFR0.
  pose proof (yparse_step_done_facts (p_txt E) (pLEN E) h0 cx0 _ _ cx eq_refl ltac:(openPA PA; clear -CEILB pa_len0; lia) LP YL) as W1.
  destruct (weak_inv_exit_facts _ _ W1) as (WL & WD & SZ). cbn [h_set_perr h_set_stack h_lexer h_decbuf h_stack_size] in WL, WD, SZ.
  yhide LP.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US.
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (pb_HSB _ _ _ PB) as SEPHS; pose proof (pb_SB _ _ _ PB) as RSB. pose proof (pb_SBA PB) as RSBA.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_Tsep0 pa_OT0 pa_j0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  assert (OHH : oshw_hi 0 (2^47) <= mh_addr mh) by (revert pa_H0 EH; clear; unfold oshw_hi, A_SB; cbn; intros; lia).
  pose proof (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_stack mh h SB1)) ltac:(cbn; lia)) as [OSH_S OHS]; cbn [ab_addr ab_size] in OSH_S, OHS.
  pose proof YS as (_ & _ & _ & STA).
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC).
  pose proof (pb_SBCX _ _ _ PB) as SEPSC.
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold wz in HC; rewrite EH in HC.
  clear TXT LXR DBR FF OCX GAP PRES UA CRED HR; yhide SV. unfold wz in FR.
  pose proof (munch_refl [(mh_stack mh + (h_used h - 1), mh_stack mh + (h_used h - 1) + 1); (mh_addr (p_mh E) + 24, mh_addr (p_mh E) + 32)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (USQ : bv_unsigned (Z_to_bv 64 (p_SQ E)) = p_SQ E) by (apply unsigned_lit; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_sp0; lia).
  unfold pstate, J_FAIL2, wz.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_SB0, pp_SBs0. clear pp_imgsh0 pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_CX0 pp_CXs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  assert (LEN : length (zbytes (stack_bytes (h_stack h)) ++ junk) = Z.to_nat (h_stack_size h)) by (rewrite length_app; clear -CEILB L1 L2 US USED Z0; lia).
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H, OSH_S. destruct OSH_H as (_ & _ & SHH); destruct OSH_S as (_ & _ & SHS); rewrite EH in SHH.
  remember (blk_shadow 104) as shb eqn:SHHeq in SHH; remember (blk_shadow (h_stack_size h)) as shs eqn:SHSeq in SHS.
  pose proof SHH as SHH0; yhide SHH0.
  shH SHH SHHeq MU WM 60 4.                                (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia).   (* [comment removed for export] *)
  bs_inline2 SHH SHHeq SHS SHSeq MU WM BC2 BC3 USED Z0 US h.
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at asegs mx (mh_stack mh) _ (h_used h + -1) ARR ltac:(rewrite LEN; clear -CEILB US USED Z0; lia)) as SOK end.
  stepA.                                                   (* [comment removed for export] *)
  lazymatch type of ARR with u8arr _ ?mx _ _ =>
    pose proof (u8arr_write asegs mx (mh_stack mh) _ (h_used h + -1) (Z_to_bv 8 2) ARR ltac:(rewrite LEN; clear -CEILB US USED Z0; lia)) as ARR' end.
  rewrite le1_wz by (clear; lia). clear ARR. try clear SHS. try clear SHH. store_done.
  yshow SHH0. rename SHH0 into SHH2.
    zstepA.                                                (* [comment removed for export] *)
    shH SHH2 SHHeq MU WM 24 8.                             (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. zstepA.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA. zstepA.                                        (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
    lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    lazymatch goal with H : stk asegs m2 (p_lo E) (p_SQ E) |- _ => rename H into ST2 end.
    pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.

    yshow TB. yshow OTB. yshow FFR0. yshow LP. yshow SV.
    set (h' := h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_alloc_failed) in *.
    assert (HU' : h_used h' = h_used h) by (unfold h_used, h'; cbn [h_stack h_set_stack h_set_perr]; rewrite HST; reflexivity).
    assert (PM2 : pmem E m2 mo1 s LK h' mh cx obw olw cr).
    { eapply (pmem_updA BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s LK h mh cx obw olw cr);
        [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| exact MI2| | reflexivity| reflexivity| reflexivity| reflexivity| exact I| |
        | eapply ctx_rep_agree; [eapply munch_agree; [exact MU| exact WM]| exact CXR| intros a Ha; cbn; clear -CEILB Ha pa_CX0 pa_ceil0 pa_CXH0 SEPSC US USED Z0 EH pa_SQ0 pa_lo0; lia]
        | exists k0, k224; assumption
        | eapply (rw_cells_transport asegs); [exact SV| exact MU| exact WM| unfold psaved; cbn; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 RSB US USED Z0 pa_H0; lia]
        | exact ST2 ].
      - constructor; [| constructor; [| constructor]]; unfold ownA; cbn [fst snd];
          [right; left; clear -CEILB US USED Z0; lia| left; rewrite EH; clear; lia].
      - split; [| rewrite HU'; replace (h_bytesConsumed h') with (h_bytesConsumed h) by reflexivity; replace (h_stack_size h') with (h_stack_size h) by reflexivity;
                 replace (h_stack_blk h') with (h_stack_blk h) by reflexivity; rewrite HSB;
                 split; [exact BC1| split; [exact BC2| split; [exact BC3| split; intros; congruence]]]].
        exists (Z_to_bv 64 (ay_perr PE_alloc_failed)), pad. split; [| replace (h_parseError h') with (Some PE_alloc_failed) by reflexivity; cbn [perr_word]; reflexivity].
        unfold hand_cells, hand_head_cells, alloc_cells. rewrite HU'.
        replace (h_bytesConsumed h') with (h_bytesConsumed h) by reflexivity. replace (h_stack_size h') with (h_stack_size h) by reflexivity.
        cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w yc_perr ayc app ay_perr]. unfold wz. rewrite EH.
        lazymatch goal with H0 : rw_cells asegs m2 (mh_addr (p_mh E)) _ |- _ => exact H0 end.
      - unfold RYajlRep.bs_rep. replace (h_stack_blk h') with (h_stack_blk h) by reflexivity. rewrite HSB. split; [exact SBNZ|]. exists junk.
        rewrite HU'. replace (h_stack h') with (ST_parse_error :: rest) by reflexivity. replace (h_stack_size h') with (h_stack_size h) by reflexivity.
        apply CB2_of_u8arr; [| rewrite zbytes_length, stack_bytes_length; cbn [length]; rewrite USED; unfold zlength; clear; lia| exact L2].
        lazymatch goal with H0 : u8arr asegs m2 (mh_stack mh) _ |- _ => revert H0 end.
        rewrite HST, !stack_bytes_cons, !zbytes_app. cbn [zbytes map state_code]. rewrite <- !app_assoc. cbn [app].
        rewrite (upd_app_len _ _ _ _ _) by (rewrite zbytes_length, stack_bytes_length; unfold zlength in USED; clear -CEILB USED; lia).
        intros H0. exact H0. }
    change (Z_to_bv 64 4) with (wz (status_code YS_alloc_failed)).
    pose proof (fun rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 =>
                  pass_exit Y KIPY FRAMEY BLKY BSHY LAYY RRT RELY AFLSEP FLAGY E F fc m2 mo1 s LK h' mh cx obw olw cr
                            rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 YS_alloc_failed
                            (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')) h0 cx0)
      as PX. unfold pstate, AY_PEXIT, wz in PX.
    eapply PX; [exact PA| exact OK| exact PM2| | exact FRM| exact YL| exact LKL| exact WL| exact WD| exact SZ| exact EX].
    rewrite (YH_shape h' h 0); [| reflexivity| reflexivity| reflexivity| exact HU'| reflexivity| reflexivity].
    exact (proj1 (pcr_full YHM E h cr PA HCR)).
Qed.
Section VESC.
Variables (E : apE Y) (h0 : yhandle) (cx0 : yctx) (st : ystate) (rest : list ystate).
Hypothesis PA : penvA E.
Hypothesis OK : pok E h0 cx0.
Hypothesis EX : pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')).

(* [comment removed for export] *)
Lemma vesc_tail : forall (F : bvmap 5 word) (fc : bv 32) m mo s LK h mh cx obw olw cr (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  pmem E m mo s LK h mh cx obw olw cr -> y_phi_hand Y h (pLEN E) <= cr -> frm0 fc ->
  h_stack h = st :: rest -> h_stack_size h mod 8 = 0 -> (length LK <= 1)%nat -> buf_inv (h_decbuf h) ->
  val_state st = true -> lex_inv (h_lexer h) -> h_stack_size h <= pLEN E + 1 + YAJL_BS_INC ->
  (yb_state (h_decbuf h) = BS_ok -> LK = [] /\ gv_push Y E h0 cx0 (gv_handle h st rest) cx cr (wz 1) (wz 0) None) ->
  (yb_state (h_decbuf h) <> BS_ok ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done YS_alloc_failed (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_alloc_failed) cx)) ->
  pagain Y E h0 cx0 LK ->
  realizes_cfg acfg asegs (mkCfg (pstate E VAL_EBK F fc m (wz VAL_EBK) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (pH E + 40)) (wz (pH E + 64)) (wz ((pH E + 40) / 8 + 2147450880)) t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PM HCR FRM HST SZM' LKL DBI VS LXI SZB YOK YFAIL AG.
  popen OK PM; yhide TB; yhide OTB; yhide FFR0; yhide LP.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US. assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (pb_HSB _ _ _ PB) as SEPHS; pose proof (pb_SB _ _ _ PB) as RSB; pose proof (pb_SBA PB) as RSBA; pose proof (pb_DB _ _ _ PB) as RDB; pose proof (pb_HDB _ _ _ PB) as SEPHDB.
  pose proof (pb_DBff _ _ _ PB) as SEPDBff.
  openPA PA; clear pa_ffCX0 pa_Tsep0 pa_OT0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  assert (OHH : oshw_hi 0 (2^47) <= mh_addr mh) by (revert pa_H0 EH; clear; unfold oshw_hi, A_SB; cbn; intros; lia).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_decbuf mh h)) ltac:(cbn; unfold SIZEOF_BUF; lia))) as OSH_DB; cbn [ab_addr ab_size] in OSH_DB.
  assert (ODBH : oshw_hi 0 (2^47) <= mb_addr (mh_decbuf mh)) by (revert RDB; clear; unfold oshw_hi, A_SB; cbn; intros; lia).
  pose proof YS as (CBS & _ & _ & STA). unfold callbacks_cells in CBS.
  cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ayc] in CBS.
  unfold AY_CALLBACKS, AY_CB_NULL, AY_CB_BOOLEAN, AY_CB_NUMBER, AY_CB_STRING, AY_CB_START_MAP, AY_CB_MAP_KEY, AY_CB_END_MAP, AY_CB_START_ARRAY, AY_CB_END_ARRAY, wz in CBS.
  destruct (GLOBY _ _ _ _ _ AHK) as (GCB & _). unfold oshadow, A_SB, AY_CALLBACKS in GCB. destruct GCB as (_ & _ & GSH). yhide GSH.
  pose proof OSH_H as OSH_H'. unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H'. destruct OSH_H' as (_ & _ & SHH); rewrite EH in SHH.
  remember (blk_shadow 104) as shb eqn:SHHeq in SHH. pose proof SHH as SHH0. yhide SHH0.
  pose proof DBR as ((DBC & DBZ & DBL & DBU) & DBD & DBF).
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC). yhide SC.
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold AY_CALLBACKS, wz in HC; rewrite EH in HC.
  pose proof FF as (FFA & FOB & FJ2 & FOL & FJ3 & FSH). clear FFA FJ2 FJ3 FSH.
  clear TXT LXR GAP PRES UA CRED HR; yhide SV. unfold wz in FR.
  pose proof (munch_refl [(p_lo E, bv_unsigned (Z_to_bv 64 (p_SQ E))); (p_SQ E + 16, p_SQ E + 24)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (USQ : bv_unsigned (Z_to_bv 64 (p_SQ E)) = p_SQ E) by (apply unsigned_lit; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_sp0; lia).
  unfold pstate, VAL_EBK, wz.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_imgsh0, pp_DB0, pp_DBs0, pp_ff0. clear pp_L0 pp_Ls0 pp_SB0 pp_SBs0 pp_CX0 pp_CXs0 pp_ffs0 pp_T0 pp_Ts0.
  ret_pc_lit.
  shH SHH SHHeq MU WM 40 8.                                (* [comment removed for export] *)
  zstepA. if_true.                                         (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    destruct (proj1 (ycells_app asegs mx (mb_addr (mh_decbuf mh)) [C4 (wz (buf_state_code (yb_state (h_decbuf h))))]
                 [C4 (wz (yb_len (h_decbuf h))); C4 (wz (yb_used (h_decbuf h))); C4 (wz 0); C8 (wz (mb_data (mh_decbuf mh))); C8 (wz (mh_addr mh + 72))]) DBC) as [DBC1 DBCr] end.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in DBCr. clear DBC.
  lazymatch goal with |- evtA _ ?P _ _ => pose proof (YBE P (mb_addr (mh_decbuf mh)) (buf_state_code (yb_state (h_decbuf h))) (p_lo E) (mb_addr (mh_decbuf mh)) 32) as CB end.
  unfold aybuf_err_rpost in CB.
  try clear SHH. call_spA CB; rewrite ?USQ.
  - exact STA.
  - exact DBC1.
  - clear; destruct (yb_state (h_decbuf h)); cbn; lia.
  - clear -CEILB RDB; lia.
  - clear -CEILB RDB; Z.div_mod_to_equations; lia.
  - exact OSH_DB.
  - clear; lia.
  - clear; lia.
  - clear -CEILB RDB; lia.
  - clear -CEILB RDB pa_ceil0; lia.
  - unfold oshw_hi, A_SB, amem; clear -CEILB RDB pa_ceil0; cbn; lia.
  - left; unfold oshw_hi, A_SB, amem; clear -CEILB RDB; cbn; lia.
  - exact MI.
  - exact STK.
  - clear -CEILB pa_ceil0; aceil; lia.
  - clear -CEILB pa_SQ0 pa_lo0; lia.
  - clear -CEILB pa_SQ0 pa_sp0; lia.
  - reflexivity.
  - intros a k Ha Hk. apply pp_stk0; [exact Ha|]. clear -CEILB Hk pa_SQ0; lia.
  - intros a k Ha Hk. apply pp_img0; [exact Ha| exact Hk].
  - intros a k Ha Hk. apply pp_DB0; [exact Ha|]. clear -CEILB Hk; lia.
  - unfold oshw_lo, oshw_hi, A_SB, amem. intros a k Ha Hk. apply pp_DBs0; [exact Ha| exact Hk].
  - (* [comment removed for export] *)
    lazymatch goal with H : stk asegs ?mx (p_lo E) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2; rewrite ?USQ in ST2 end.
    lazymatch goal with H : ?x = wz (buf_state_code _) |- _ => subst x end.
    lazymatch goal with H : rw_cells asegs ?mx (mb_addr (mh_decbuf mh)) [C4 _] |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (proj2 (ycells_app asegs mx (mb_addr (mh_decbuf mh)) [C4 (wz (buf_state_code (yb_state (h_decbuf h))))]
                    [C4 (wz (yb_len (h_decbuf h))); C4 (wz (yb_used (h_decbuf h))); C4 (wz 0); C8 (wz (mb_data (mh_decbuf mh))); C8 (wz (mh_addr mh + 72))])
                    (conj H ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; exact DBCr))) as DBC; clear H DBCr; cbn [app] in DBC end.
    lazymatch goal with H : ay_statics ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into STA2 end.
    lazymatch goal with H : mem_inv asegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI2 end.
    lazymatch goal with H : oshadow ?mx (mb_addr (mh_decbuf mh)) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into OSH_DB2 end.
    clear STA.
    unfold wz. zstepA. if_cases K5; zify_cond K5.           (* [comment removed for export] *)
    + (* [comment removed for export] *)
      assert (HOK : yb_state (h_decbuf h) = BS_ok).
      { revert K5. destruct (yb_state (h_decbuf h)); intros K5; [reflexivity| exfalso | exfalso]; revert K5 CEILB; clear; cbn [buf_state_code]; intros K5 CEILB; vm_compute in K5; lia. }
      clear YFAIL. destruct (YOK HOK) as (LK0 & GP).
      zstepA.                                                (* [comment removed for export] *)
      yshow SHH0. shH0 SHH0 SHHeq MU WM 8. yhide SHH0.       (* [comment removed for export] *)
      zstepA. iflit2.                                        (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA. zstepA.                                        (* [comment removed for export] *)
      yshow GSH.
      lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (u8arr_transport asegs _ _ mx _ _ GSH MU WM ltac:(rewrite (blk_shadow_length 88) by (clear; lia); cbn [disjoint_from fst snd]; clear -CEILB pa_ceil0 USQ pa_SQ0 pa_lo0; lia)) as GSH2;
        assert (SHR : ov_read_bytes asegs mx (Z_to_bv 64 2147537393) 1 = Some [Z_to_bv 8 0]);
        [ change 2147537393 with (2147450880 + (692064 + 40) / 8);
          apply (block_shadow_read0_u asegs mx 2147450880 692064 88 (692064 + 40) 8); [reflexivity| lia| exact GSH2| lia| lia| cbn; lia| reflexivity] |] end.
      clear GSH GSH2.
      zstepA. clear SHR.                                     (* [comment removed for export] *)
      zstepA. iflit2.                                        (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      yshow SHH0. shH SHH0 SHHeq MU WM 8 8.                  (* [comment removed for export] *)
      zstepA. iflit2.                                        (* [comment removed for export] *)
      shH SHH0 SHHeq MU WM 40 8. yhide SHH0.                 (* [comment removed for export] *)
      zstepA. iflit2.                                        (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      lazymatch goal with |- evtA _ ?P _ _ => pose proof (YBD P (mb_addr (mh_decbuf mh)) (mb_data (mh_decbuf mh)) (mh_addr mh + 72) (p_lo E) (h_decbuf h)) as CB2 end.
      unfold aybuf_data_rpost in CB2.
      call_spA CB2; rewrite ?USQ.
      * statics_via YS MU WM. constructor; [cbn [fst snd]; clear -CEILB pa_ceil0 USQ; lia| constructor; [cbn [fst snd]; clear -CEILB pa_ceil0 pa_SQ0 pa_lo0; lia| constructor]].
      * split; [exact DBC| split; [exact DBZ| split; [exact DBL| exact DBU]]].
      * exact HOK.
      * clear -CEILB RDB; lia.
      * eapply oshadow_agree; [eapply munch_agree; [exact MU| exact WM]| exact OSH_DB|].
        intros a Ha; cbn; unfold oshw_lo, oshw_hi, A_SB, amem, SIZEOF_BUF in Ha; clear -CEILB Ha RDB pa_ceil0 USQ pa_SQ0 pa_lo0; lia.
      * exact ODBH.
      * unfold SIZEOF_BUF; aceil; clear -CEILB RDB; lia.
      * exact MI2.
      * exact ST2.
      * clear -CEILB pa_ceil0; aceil; lia.
      * clear -CEILB pa_SQ0 pa_lo0; lia.
      * clear -CEILB pa_SQ0 pa_sp0; lia.
      * reflexivity.
      * intros a k Ha Hk. apply pp_stk0; [exact Ha|]. clear -CEILB Hk pa_SQ0; lia.
      * intros a k Ha Hk. apply pp_img0; [exact Ha| exact Hk].
      * unfold opol, oshw_lo, oshw_hi, A_SB, amem, SIZEOF_BUF. split; intros a k Ha Hk; [apply pp_DB0| apply pp_DBs0]; first [exact Ha| exact Hk].
      * (* [comment removed for export] *)
        try clear STA2; try clear OSH_DB2.
        lazymatch goal with H : stk asegs ?mx (p_lo E) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST3; rewrite ?USQ in ST3 end.
        lazymatch goal with H : ?x = wz (mb_data _) |- _ => subst x end.
        lazymatch goal with H : abuf_struct ?mx _ _ _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => destruct H as (DBC3 & _); unfold buf_cells in DBC3 end.
        lazymatch goal with H : ay_statics ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into STA3 end.
        lazymatch goal with H : mem_inv asegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI3 end.
        lazymatch goal with H : oshadow ?mx (mb_addr (mh_decbuf mh)) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into OSH_DB3 end.
        unfold wz.
        yshow pa_ffP0. yshow SHH0. shH SHH0 SHHeq MU WM 40 8. yhide SHH0. yhide pa_ffP0.  (* [comment removed for export] *)
        zstepA. iflit2.                                      (* [comment removed for export] *)
        zstepA.                                              (* [comment removed for export] *)
        zstepA.                                              (* [comment removed for export] *)
        zstepA.                                              (* [comment removed for export] *)
        lazymatch goal with |- evtA _ ?P _ _ => pose proof (YBL P (mb_addr (mh_decbuf mh)) (mb_data (mh_decbuf mh)) (mh_addr mh + 72) (p_lo E) (h_decbuf h)) as CB3 end.
        unfold aybuf_len_rpost in CB3.
        call_spA CB3; rewrite ?USQ.
        -- exact STA3.
        -- split; [unfold buf_cells; exact DBC3| split; [exact DBZ| split; [exact DBL| exact DBU]]].
        -- exact HOK.
        -- clear -CEILB RDB; lia.
        -- eapply oshadow_agree; [eapply munch_agree; [exact MU| exact WM]| exact OSH_DB|].
           intros a Ha; cbn; unfold oshw_lo, oshw_hi, A_SB, amem, SIZEOF_BUF in Ha; clear -CEILB Ha RDB pa_ceil0 USQ pa_SQ0 pa_lo0; lia.
        -- exact ODBH.
        -- unfold SIZEOF_BUF; aceil; clear -CEILB RDB; lia.
        -- exact MI3.
        -- exact ST3.
        -- clear -CEILB pa_ceil0; aceil; lia.
        -- clear -CEILB pa_SQ0 pa_lo0; lia.
        -- clear -CEILB pa_SQ0 pa_sp0; lia.
        -- reflexivity.
        -- intros a k Ha Hk. apply pp_stk0; [exact Ha|]. clear -CEILB Hk pa_SQ0; lia.
        -- intros a k Ha Hk. apply pp_img0; [exact Ha| exact Hk].
        -- unfold opol, oshw_lo, oshw_hi, A_SB, amem, SIZEOF_BUF. split; intros a k Ha Hk; [apply pp_DB0| apply pp_DBs0]; first [exact Ha| exact Hk].
        -- (* [comment removed for export] *)
           try clear STA3; try clear OSH_DB3.
           lazymatch goal with H : stk asegs ?mx (p_lo E) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST4; rewrite ?USQ in ST4 end.
           lazymatch goal with H : ?x = wz (yb_used _) |- _ => subst x end.
           lazymatch goal with H : abuf_struct ?mx _ _ _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => clear H end.
           lazymatch goal with H : mem_inv asegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI4 end.
           unfold wz.
           zstepA. zstepA. zstepA.                           (* [comment removed for export] *)
           zstepA.                                           (* [comment removed for export] *)
           lazymatch goal with |- evtA _ ?P _ _ => pose proof (YCS P) as CB4 end. unfold aycb_string_rpost in CB4.
           call_spA CB4; [exact MI4|].
           lazymatch goal with H : _ = wz 1 |- _ => rewrite H end. lazymatch goal with H : @eq mem ?x ?y |- _ => first [subst x| subst y] | _ => idtac end. unfold wz.
           zstepA. iflit2.                                   (* [comment removed for export] *)
           zstepA.                                           (* [comment removed for export] *)
           zstepA.                                           (* [comment removed for export] *)
           zstepA.                                           (* [comment removed for export] *)
           zstepA.                                           (* [comment removed for export] *)
           zstepA.                                           (* [comment removed for export] *)
           zstepA.                                           (* [comment removed for export] *)
           zstepA.                                           (* [comment removed for export] *)
           apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
           lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
           lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI5 end.
           lazymatch goal with H : stk asegs m2 (p_lo E) (p_SQ E) |- _ => rename H into ST5 end.
           lazymatch goal with H : rw_cells asegs m2 (p_SQ E) _ |- _ => rename H into FR5 end.
           pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
           rewrite USQ in MU.
           yshow TB. yshow OTB. yshow FFR0. yshow LP. yshow SV. yshow SC.
           assert (FR6 : rw_cells asegs m2 (p_SQ E) (pframe E (firstn 16 k0 ++ le8 (Z_to_bv 64 (p_ff E / 8 + 2147450880))) k224)).
           { unfold pframe, wz. eapply rw_cells_reshape; [exact FR5| | |].
             - pose proof (proj1 (proj1 FR5)) as WF. cbn [cells_wf cell_wf] in WF |- *. rewrite length_app, length_le8. clear -CEILB WF. intuition lia.
             - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
             - cbn [cells_size csize Nat.add]. reflexivity. }
           assert (PM2 : pmem E m2 mo1 s LK h mh cx obw olw cr).
           { eapply (pmem_updA BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s LK h mh cx obw olw cr);
               [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| exact MI5| | reflexivity| reflexivity| reflexivity| reflexivity| exact I| |
               | eapply ctx_rep_agree; [eapply munch_agree; [exact MU| exact WM]| exact CXR| intros a Ha; cbn; clear -CEILB Ha pa_CX0 pa_ceil0 pa_SQ0 pa_lo0; lia]
               | exists (firstn 16 k0 ++ le8 (Z_to_bv 64 (p_ff E / 8 + 2147450880))), k224; exact FR6
               | eapply (rw_cells_transport asegs); [exact SV| exact MU| exact WM| unfold psaved; cbn; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0; lia]
               | exact ST5 ].
             - apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold ownA; cbn [fst snd]; [right; right; right; clear -CEILB pa_SQ0; lia| right; right; right; clear -CEILB pa_SQ0 pa_lo0; lia].
             - split; [| cbn [h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB; split; [exact BC1| split; [exact BC2| split; [exact BC3| split; intros; congruence]]]].
               exists pew, pad. split; [| exact PW].
               unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app]. unfold AY_CALLBACKS, wz. rewrite EH.
               lazymatch goal with H0 : rw_cells asegs m2 (mh_addr (p_mh E)) _ |- _ => exact H0 end.
             - eapply (rw_cells_transport asegs) in SC; [| exact MU| exact WM| cbn; clear -CEILB RSB pa_ceil0 pa_SQ0 pa_lo0 US BC3; lia].
               unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC. }
           pose proof (J_gotval Y KIPY FRAMEY BLKY BSHY LAYY PERMY RRT NONNEG YHM UFRAME WREA URA USTEP URA_push YRP
                         E F fc m2 mo1 s h0 cx0 h mh cx obw olw cr st rest None) as JG. unfold pstate, J_GV, wz in JG. cbn [gv_push] in GP. subst LK.
           eapply JG; [exact PA| exact OK| exact PM2| exact FRM| exact HST| exact VS| exact SZM'| exact LXI| exact SZB| exact GP| exact AG| exact EX].
    + (* [comment removed for export] *)
      assert (HNOK : yb_state (h_decbuf h) <> BS_ok).
      { intros HOK. revert K5. rewrite HOK. cbn [buf_state_code]. clear. intros K5. vm_compute in K5. first [lia | congruence | exact (K5 eq_refl)]. }
      clear YOK. specialize (YFAIL HNOK).
      zstepA.                                                (* [comment removed for export] *)
      apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
      lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
      pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
      rewrite USQ in MU.
      yshow TB. yshow OTB. yshow FFR0. yshow LP. yshow SV.
      yshow SC.
      assert (PM2 : pmem E m2 mo1 s LK h mh cx obw olw cr).
      { eapply (pmem_updA BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s LK h mh cx obw olw cr);
          [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| exact MI2| | reflexivity| reflexivity| reflexivity| reflexivity| exact I| |
          | eapply ctx_rep_agree; [eapply munch_agree; [exact MU| exact WM]| exact CXR| intros a Ha; cbn; clear -CEILB Ha pa_CX0 pa_ceil0 pa_SQ0 pa_lo0; lia]
          | exists k0, k224; assumption
          | eapply (rw_cells_transport asegs); [exact SV| exact MU| exact WM| unfold psaved; cbn; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0; lia]
          | exact ST2 ].
        - apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold ownA; cbn [fst snd]; [right; right; right; clear -CEILB pa_SQ0; lia| right; right; right; clear -CEILB pa_SQ0 pa_lo0; lia].
        - split; [| cbn [h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB; split; [exact BC1| split; [exact BC2| split; [exact BC3| split; intros; congruence]]]].
          exists pew, pad. split; [| exact PW].
          unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app]. unfold AY_CALLBACKS, wz. rewrite EH.
          lazymatch goal with H0 : rw_cells asegs m2 (mh_addr (p_mh E)) _ |- _ => exact H0 end.
        - eapply (rw_cells_transport asegs) in SC; [| exact MU| exact WM| cbn; clear -CEILB RSB pa_ceil0 pa_SQ0 pa_lo0 US BC3; lia].
          unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC. }
      pose proof (J_fail2 E F fc m2 mo1 s LK h0 cx0 h mh cx obw olw cr st rest) as JF. unfold pstate, J_FAIL2, wz in JF.
      eapply JF; [exact PA| exact OK| exact PM2| exact HCR| exact FRM| exact HST| exact SZM'| exact LKL| exact YFAIL| exact EX].
Qed.
(* [comment removed for export] *)
Lemma vesc_main : forall (F : bvmap 5 word) (fc : bv 32) m mo s h mh cx cr (i n : Z) (od : option yptr) (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word),
  pmem E m mo s [] h mh cx (wz (p_T E + i)) (wz n) cr -> y_phi_hand Y h (pLEN E) <= cr -> frm0 fc ->
  h_stack h = st :: rest -> h_stack_size h mod 8 = 0 -> buf_inv (h_decbuf h) -> yb_state (h_decbuf h) = BS_ok -> yb_data (h_decbuf h) = od ->
  0 <= i -> 0 <= n -> i + n < pLEN E -> sbody_ix (p_txt E) i (i + n) -> val_state st = true -> lex_inv (h_lexer h) -> h_stack_size h <= pLEN E + 1 + YAJL_BS_INC ->
  (forall db', yleaf (ystring_decode (buf_cleared (h_decbuf h)) (zslice (p_txt E) i n) n) db' -> yb_state db' = BS_ok ->
     gv_push Y E h0 cx0 (gv_handle (h_set_decbuf h db') st rest) cx (cr - y_phi_buf Y (h_decbuf h) + y_phi_buf Y db') (wz 1) (wz 0) None) ->
  (forall db', yleaf (ystring_decode (buf_cleared (h_decbuf h)) (zslice (p_txt E) i n) n) db' -> yb_state db' <> BS_ok ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0)
           (SR_done YS_alloc_failed (h_set_perr (h_set_stack (h_set_decbuf h db') (ST_parse_error :: rest)) PE_alloc_failed) cx)) ->
  (forall LKx, pagain Y E h0 cx0 LKx) ->
  realizes_cfg acfg asegs (mkCfg (pstate E VAL_ESC F fc m rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz (pH E + 64)) s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PM HCR FRM HST SZM' DBI DBOK HDB I0 N0 INL SBX VS LXI SZB YOK YFAIL AGX.
  popen OK PM; yhide TB; yhide OTB; yhide FFR0; yhide LP.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US. assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  pose proof (mk_pblk BLKY LAYY BSHY E s [] h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (pb_HSB _ _ _ PB) as SEPHS; pose proof (pb_SB _ _ _ PB) as RSB; pose proof (pb_SBA PB) as RSBA; pose proof (pb_DB _ _ _ PB) as RDB; pose proof (pb_HDB _ _ _ PB) as SEPHDB.
  pose proof (pb_DBff _ _ _ PB) as SEPDBff. pose proof (pb_DD _ _ _ PB) as RDD0. pose proof (pb_HDD _ _ _ PB) as SEPHDD0. pose proof (pb_DDff _ _ _ PB) as SEPDDff0.
  pose proof (mk_pdec BLKY E s [] h mh h0 cx0 m mo PA OK AHK SAME SB1) as PD. pose proof (pd_DBDD _ _ _ _ _ PD) as SEPDBDD0. clear PD.
  openPA PA; clear pa_ffCX0 pa_Tsep0 pa_OT0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ [] ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  assert (OHH : oshw_hi 0 (2^47) <= mh_addr mh) by (revert pa_H0 EH; clear; unfold oshw_hi, A_SB; cbn; intros; lia).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_decbuf mh h)) ltac:(cbn; unfold SIZEOF_BUF; lia))) as OSH_DB; cbn [ab_addr ab_size] in OSH_DB.
  assert (ODBH : oshw_hi 0 (2^47) <= mb_addr (mh_decbuf mh)) by (revert RDB; clear; unfold oshw_hi, A_SB; cbn; intros; lia).
  pose proof DBR as ((DBC & DBZ & DBL & DBU) & DBD & DBF).
  assert (OSH_DD : yb_data (h_decbuf h) <> None -> oshadow m (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h)) /\ amem (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h))).
  { intros HD. destruct (yb_data (h_decbuf h)) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity].
    unfold RYajlRep.buf_data in DBD. rewrite Hd in DBD. destruct DBD as (UL & _).
    pose proof (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_decdata mh h ltac:(rewrite Hd; discriminate))) ltac:(cbn; clear -CEILB UL; lia)) as X. cbn [ab_addr ab_size] in X. exact X. }
  pose proof YS as (CBS & _ & _ & STA). unfold callbacks_cells in CBS.
  cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ayc] in CBS.
  unfold AY_CALLBACKS, AY_CB_NULL, AY_CB_BOOLEAN, AY_CB_NUMBER, AY_CB_STRING, AY_CB_START_MAP, AY_CB_MAP_KEY, AY_CB_END_MAP, AY_CB_START_ARRAY, AY_CB_END_ARRAY, wz in CBS.
  destruct (GLOBY _ _ _ _ _ AHK) as (GCB & _). unfold oshadow, A_SB, AY_CALLBACKS in GCB. destruct GCB as (_ & _ & GSH).
  pose proof OSH_H as OSH_H'. unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H'. destruct OSH_H' as (_ & _ & SHH); rewrite EH in SHH.
  remember (blk_shadow 104) as shb eqn:SHHeq in SHH. pose proof SHH as SHH0. yhide SHH0.
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold AY_CALLBACKS, wz in HC; rewrite EH in HC.
  pose proof FF as (FFA & FOB & FJ2 & FOL & FJ3 & FSH). clear FFA FJ2 FJ3 FSH. unfold wz in FOB, FOL.
  clear TXT LXR GAP PRES UA CRED HR; yhide SV. unfold wz in FR.
  assert (USQ : bv_unsigned (Z_to_bv 64 (p_SQ E)) = p_SQ E) by (apply unsigned_lit; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_sp0; lia).
  pose proof (ypost_yleaf _ _ _ (ybuf_clear_post _ DBI DBOK) (ybuf_clear_leaf _ DBOK)) as [DBI' _].
  assert (PHIC : y_phi_buf Y (buf_cleared (h_decbuf h)) = y_phi_buf Y (h_decbuf h)).
  { clear -CEILB YSHAPE DBOK. unfold buf_cleared. destruct (h_decbuf h) as [st0 len0 u0 d0 bs0]. cbn in DBOK |- *. subst st0. apply YSHAPE. }
  assert (HCR' : y_phi_hand Y (h_set_decbuf h (buf_cleared (h_decbuf h))) (pLEN E) <= cr).
  { pose proof (proj1 YSPLIT) as EQ. rewrite (EQ _ (pLEN E)). rewrite (EQ h (pLEN E)) in HCR. cbn [h_set_decbuf h_lexer h_decbuf h_bytesConsumed h_stack_size].
    unfold h_used in HCR |- *. cbn [h_stack h_set_decbuf]. rewrite PHIC. clear -CEILB HCR. lia. }
  unfold pstate, VAL_ESC, wz.
  (* [comment removed for export] *)
  clear OHH pa_CXH0 pa_ffH0 pa_CX0 BC4 DBF PW.
  yhide SEPHS; yhide RSB; yhide SEPDBDD0; yhide BC1; yhide BC2; yhide DBL; yhide DBU; yhide USED; yhide Z0; yhide US; yhide HCR; yhide HCR'; yhide PHIC.
  yhide I0; yhide N0; yhide INL; yhide SBX; yhide DBZ; yhide DBD; yhide ODBH.
  destruct od as [dd|].
  - (* [comment removed for export] *)
    specialize (RDD0 dd HDB). specialize (SEPHDD0 dd HDB). specialize (SEPDDff0 dd HDB).
    destruct (OSH_DD ltac:(rewrite HDB; discriminate)) as [OSH_DDc ODDH]. clear OSH_DD.
    assert (DDLO : 6303744 <= mb_data (mh_decbuf mh) /\ (mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= 2147446784 \/ 17594333495296 <= mb_data (mh_decbuf mh))) by (clear -CEILB ODDH; unfold oshw_hi, A_SB, amem in ODDH; lia).
    assert (DDX : 0 < yb_len (h_decbuf h)).
    { yshow DBU. pose proof DBI as (_ & _ & _ & _ & DBX & _). specialize (DBX ltac:(rewrite HDB; discriminate)). clear -CEILB DBX DBU. lia. }
    assert (DDHI : mb_data (mh_decbuf mh) + 1 <= alloc_ceiling) by (clear -CEILB RDD0 DDX; lia).
    pose proof (munch_refl [(p_lo E, bv_unsigned (Z_to_bv 64 (p_SQ E))); (mb_addr (mh_decbuf mh) + 8, mb_addr (mh_decbuf mh) + 12); (mb_data (mh_decbuf mh), mb_data (mh_decbuf mh) + 1)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    arz_seg KIPY AHK.
    pose proof (mk_ppol BLKY LAYY BSHY E s [] h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
    unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_imgsh0, pp_DB0, pp_DBs0, pp_ff0. clear pp_L0 pp_Ls0 pp_SB0 pp_SBs0 pp_CX0 pp_CXs0 pp_ffs0 pp_T0 pp_Ts0.
    destruct (aypol_opol_block Y _ _ _ _ LINK (mkABlock (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h))) (IN _ (yb_in_decdata mh h ltac:(rewrite HDB; discriminate)))
                ltac:(cbn; clear -CEILB ODDH; unfold oshw_hi, A_SB, amem in ODDH; lia) ltac:(cbn; unfold oshw_lo, oshw_hi, A_SB, amem in *; clear -CEILB ODDH; lia)
                ltac:(cbn; unfold oshw_hi, A_SB, amem in *; clear -CEILB ODDH RDD0; Z.div_mod_to_equations; lia) ltac:(cbn; clear -CEILB RDD0; aceil; lia)) as [PDD PDDs].
    cbn [ab_addr ab_size] in PDD, PDDs. yhide PDDs. yhide pp_DBs0. yhide pp_imgsh0. yhide ODDH. clear LINK.
    zstepA.                                                (* [comment removed for export] *)
    shH0 SHH SHHeq MU WM 8.                                (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA. zstepA.                                        (* [comment removed for export] *)
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (SHR : ov_read_bytes asegs mx (Z_to_bv 64 2147537393) 1 = Some [Z_to_bv 8 0]);
      [ change 2147537393 with (2147450880 + (692064 + 40) / 8);
        apply (block_shadow_read0_u asegs mx 2147450880 692064 88 (692064 + 40) 8); [reflexivity| lia| exact GSH| lia| lia| cbn; lia| reflexivity] |] end.
    zstepA. clear SHR GSH.                                 (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. clear CBS.                                     (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA. shadow_addr. zstepA.                           (* [comment removed for export] *)
    shH SHH SHHeq MU WM 40 8. clear SHH.                   (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    lazymatch goal with |- evtA _ ?P _ _ => pose proof (YBC P (mb_addr (mh_decbuf mh)) (mb_data (mh_decbuf mh)) (mh_addr mh + 72) (p_lo E) (h_decbuf h)) as CLR end.
    unfold aybuf_clear_rpost in CLR. rewrite HDB in CLR. cbn [app] in CLR.
    pose proof (I : allow_big_lia) as ALLOW. yhide DBC. call_spA CLR; rewrite ?USQ. all: try clear ALLOW.
    + exact STA.
    + yshow DBZ; yshow DBL; yshow DBU. split; [exact DBC| split; [exact DBZ| split; [exact DBL| exact DBU]]].
    + yshow DBD. exact DBD.
    + exact DBOK.
    + exact DBI.
    + clear -CEILB RDB; lia.
    + exact OSH_DB.
    + yshow ODBH. exact ODBH.
    + unfold SIZEOF_BUF; aceil; clear -CEILB RDB; lia.
    + intros _. yshow ODDH. yshow SEPDBDD0. split; [exact OSH_DDc|]. split; [exact ODDH|]. split; [aceil; clear -CEILB RDD0; lia|].
      unfold SIZEOF_BUF. exact (SEPDBDD0 dd HDB).
    + exact MI.
    + exact STK.
    + clear -CEILB pa_ceil0; aceil; lia.
    + clear -CEILB pa_SQ0 pa_lo0; lia.
    + clear -CEILB pa_SQ0 pa_sp0; lia.
    + reflexivity.
    + intros a k Ha Hk. apply pp_stk0; [exact Ha|]. clear -CEILB Hk pa_SQ0; lia.
    + intros a k Ha Hk. apply pp_img0; [exact Ha| exact Hk].
    + yshow pp_DBs0. unfold opol, oshw_lo, oshw_hi, A_SB, amem, SIZEOF_BUF. split; intros a k Ha Hk; [apply pp_DB0| apply pp_DBs0]; first [exact Ha| exact Hk].
    + intros _. yshow PDDs. unfold opol, oshw_lo, oshw_hi, A_SB, amem. split; [exact PDD| exact PDDs].
    + (* [comment removed for export] *)
      lazymatch goal with H : stk asegs ?mx (p_lo E) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2; rewrite ?USQ in ST2 end.
      lazymatch goal with H : abuf_struct ?mx _ _ _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into BS2 end.
      lazymatch goal with H : abuf_data ?mx _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into BD2 end.
      lazymatch goal with H : mem_inv asegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI2 end.
      lazymatch goal with H : ay_statics ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => clear H end.
      yshow pa_ffP0. yshow SHH0. shH SHH0 SHHeq MU WM 40 8. yhide SHH0. yhide pa_ffP0.    (* [comment removed for export] *)
      zstepA. iflit2.                                        (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA. yshow N0; yshow INL; yshow I0. rewrite ?ysx32_small by (clear -CEILB N0 INL I0 pa_len0; lia).   (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
      lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
      pose proof (pmem_remodel E m mo mo1 s [] h mh cx (wz (p_T E + i)) (wz n) cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
      rewrite USQ in MU.
      yshow TB. yshow OTB. yshow FFR0. yshow LP. yshow SV. yshow USED. yshow Z0. yshow US. yshow HCR'. yshow SBX. yshow DBU.
      assert (PM2 : pmem E m2 mo1 s [] (h_set_decbuf h (buf_cleared (h_decbuf h))) mh cx (wz (p_T E + i)) (wz n) cr).
      { eapply (pmem_updD BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s [] h mh cx _ _ cr _ h0 cx0);
          [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| exact MI2| | reflexivity| reflexivity| | exact ST2].
        - pose proof DBI as (_ & _ & _ & _ & DBX & _). specialize (DBX ltac:(rewrite HDB; discriminate)).
          constructor; [| constructor; [| constructor; [| constructor]]]; unfold ownD; cbn [fst snd];
            [left; clear; lia| right; left; clear; lia| right; right; split; [rewrite HDB; discriminate| clear -CEILB DBX DBU; lia]].
        - split; [exact BS2| split; [exact BD2| unfold buf_cleared; cbn [yb_bytes]; constructor]]. }
      clear PM1 PM.
      eapply (dec_call Y BLKY BSHY LAYY PERMY RRT YSD URA USTEP URA_dec UFRAME NONNEG phr YSPLIT E VAL_EBK m2 mo1 s [] h0 cx0
                (h_set_decbuf h (buf_cleared (h_decbuf h))) mh cx (wz (p_T E + i)) (wz n) cr F fc i n);
        [exact PA| exact OK| exact PM2| exact HCR'| exact FRM| right; reflexivity| reflexivity| exact DBI'| reflexivity| reflexivity| exact SZ
        | exact I0| exact N0| exact INL| exact SBX| ].
      cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m3 mo3 s3 db' mbd' LK' YLD MBS FRM2 LKT PM3 HCR3.
      eapply vesc_tail; [exact PM3| exact HCR3| exact FRM2| exact HST| exact SZM'| | | exact VS| exact LXI| exact SZB| | | exact (AGX (LK' ++ []))].
      * rewrite app_nil_r. destruct LK' as [|b0 L0]; [cbn; clear; lia| destruct (LKT ltac:(discriminate)) as [_ L1]; rewrite L1; clear; lia].
      * exact (proj1 (ypost_yleaf _ _ _ (ystring_decode_post _ _ _ (sbody_ix_slice _ _ _ I0 SBX) N0 DBI' ltac:(cbn [yb_used buf_cleared]; clear -CEILB N0 I0 INL pa_len0; lia)) YLD)).
      * intros HOK. split; [| yshow PHIC; cbn [h_decbuf h_set_decbuf]; rewrite PHIC; exact (YOK db' YLD HOK)].
        destruct LK' as [|b0 L0]; [reflexivity| exfalso; destruct (LKT ltac:(discriminate)) as [NS _]; exact (NS HOK)].
      * intros HN. exact (YFAIL db' YLD HN).
  - (* [comment removed for export] *)
    clear RDD0 SEPHDD0 SEPDDff0 OSH_DD.
    pose proof (munch_refl [(p_lo E, bv_unsigned (Z_to_bv 64 (p_SQ E))); (mb_addr (mh_decbuf mh) + 8, mb_addr (mh_decbuf mh) + 12)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    arz_seg KIPY AHK.
    pose proof (mk_ppol BLKY LAYY BSHY E s [] h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
    unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_imgsh0, pp_DB0, pp_DBs0, pp_ff0. clear pp_L0 pp_Ls0 pp_SB0 pp_SBs0 pp_CX0 pp_CXs0 pp_ffs0 pp_T0 pp_Ts0.
    yhide pp_DBs0. yhide pp_imgsh0. clear LINK.
    zstepA.                                                (* [comment removed for export] *)
    shH0 SHH SHHeq MU WM 8.                                (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA. zstepA.                                        (* [comment removed for export] *)
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (SHR : ov_read_bytes asegs mx (Z_to_bv 64 2147537393) 1 = Some [Z_to_bv 8 0]);
      [ change 2147537393 with (2147450880 + (692064 + 40) / 8);
        apply (block_shadow_read0_u asegs mx 2147450880 692064 88 (692064 + 40) 8); [reflexivity| lia| exact GSH| lia| lia| cbn; lia| reflexivity] |] end.
    zstepA. clear SHR GSH.                                 (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. clear CBS.                                     (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA. shadow_addr. zstepA.                           (* [comment removed for export] *)
    shH SHH SHHeq MU WM 40 8. clear SHH.                   (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    lazymatch goal with |- evtA _ ?P _ _ => pose proof (YBC P (mb_addr (mh_decbuf mh)) (mb_data (mh_decbuf mh)) (mh_addr mh + 72) (p_lo E) (h_decbuf h)) as CLR end.
    unfold aybuf_clear_rpost in CLR. rewrite HDB in CLR. cbn [app] in CLR.
    pose proof (I : allow_big_lia) as ALLOW. yhide DBC. call_spA CLR; rewrite ?USQ. all: try clear ALLOW.
    + exact STA.
    + yshow DBZ; yshow DBL; yshow DBU. split; [exact DBC| split; [exact DBZ| split; [exact DBL| exact DBU]]].
    + yshow DBD. exact DBD.
    + exact DBOK.
    + exact DBI.
    + clear -CEILB RDB; lia.
    + exact OSH_DB.
    + yshow ODBH. exact ODBH.
    + unfold SIZEOF_BUF; aceil; clear -CEILB RDB; lia.
    + intros X. exfalso. apply X. reflexivity.
    + exact MI.
    + exact STK.
    + clear -CEILB pa_ceil0; aceil; lia.
    + clear -CEILB pa_SQ0 pa_lo0; lia.
    + clear -CEILB pa_SQ0 pa_sp0; lia.
    + reflexivity.
    + intros a k Ha Hk. apply pp_stk0; [exact Ha|]. clear -CEILB Hk pa_SQ0; lia.
    + intros a k Ha Hk. apply pp_img0; [exact Ha| exact Hk].
    + yshow pp_DBs0. unfold opol, oshw_lo, oshw_hi, A_SB, amem, SIZEOF_BUF. split; intros a k Ha Hk; [apply pp_DB0| apply pp_DBs0]; first [exact Ha| exact Hk].
    + intros X. exfalso. apply X. reflexivity.
    + (* [comment removed for export] *)
      lazymatch goal with H : stk asegs ?mx (p_lo E) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2; rewrite ?USQ in ST2 end.
      lazymatch goal with H : abuf_struct ?mx _ _ _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into BS2 end.
      lazymatch goal with H : abuf_data ?mx _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into BD2 end.
      lazymatch goal with H : mem_inv asegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI2 end.
      lazymatch goal with H : ay_statics ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => clear H end.
      yshow pa_ffP0. yshow SHH0. shH SHH0 SHHeq MU WM 40 8. yhide SHH0. yhide pa_ffP0.    (* [comment removed for export] *)
      zstepA. iflit2.                                        (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      zstepA. yshow N0; yshow INL; yshow I0. rewrite ?ysx32_small by (clear -CEILB N0 INL I0 pa_len0; lia).   (* [comment removed for export] *)
      zstepA.                                                (* [comment removed for export] *)
      apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
      lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
      pose proof (pmem_remodel E m mo mo1 s [] h mh cx (wz (p_T E + i)) (wz n) cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
      rewrite USQ in MU.
      yshow TB. yshow OTB. yshow FFR0. yshow LP. yshow SV. yshow USED. yshow Z0. yshow US. yshow HCR'. yshow SBX. yshow DBU.
      assert (PM2 : pmem E m2 mo1 s [] (h_set_decbuf h (buf_cleared (h_decbuf h))) mh cx (wz (p_T E + i)) (wz n) cr).
      { eapply (pmem_updD BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s [] h mh cx _ _ cr _ h0 cx0);
          [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| exact MI2| | reflexivity| reflexivity| | exact ST2].
        - constructor; [| constructor; [| constructor]]; unfold ownD; cbn [fst snd]; [left; clear; lia| right; left; clear; lia].
        - split; [exact BS2| split; [exact BD2| unfold buf_cleared; cbn [yb_bytes]; constructor]]. }
      clear PM1 PM.
      eapply (dec_call Y BLKY BSHY LAYY PERMY RRT YSD URA USTEP URA_dec UFRAME NONNEG phr YSPLIT E VAL_EBK m2 mo1 s [] h0 cx0
                (h_set_decbuf h (buf_cleared (h_decbuf h))) mh cx (wz (p_T E + i)) (wz n) cr F fc i n);
        [exact PA| exact OK| exact PM2| exact HCR'| exact FRM| right; reflexivity| reflexivity| exact DBI'| reflexivity| reflexivity| exact SZ
        | exact I0| exact N0| exact INL| exact SBX| ].
      cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m3 mo3 s3 db' mbd' LK' YLD MBS FRM2 LKT PM3 HCR3.
      eapply vesc_tail; [exact PM3| exact HCR3| exact FRM2| exact HST| exact SZM'| | | exact VS| exact LXI| exact SZB| | | exact (AGX (LK' ++ []))].
      * rewrite app_nil_r. destruct LK' as [|b0 L0]; [cbn; clear; lia| destruct (LKT ltac:(discriminate)) as [_ L1]; rewrite L1; clear; lia].
      * exact (proj1 (ypost_yleaf _ _ _ (ystring_decode_post _ _ _ (sbody_ix_slice _ _ _ I0 SBX) N0 DBI' ltac:(cbn [yb_used buf_cleared]; clear -CEILB N0 I0 INL pa_len0; lia)) YLD)).
      * intros HOK. split; [| yshow PHIC; cbn [h_decbuf h_set_decbuf]; rewrite PHIC; exact (YOK db' YLD HOK)].
        destruct LK' as [|b0 L0]; [reflexivity| exfalso; destruct (LKT ltac:(discriminate)) as [NS _]; exact (NS HOK)].
      * intros HN. exact (YFAIL db' YLD HN).
Qed.
End VESC.
End W.
End RC__1.
