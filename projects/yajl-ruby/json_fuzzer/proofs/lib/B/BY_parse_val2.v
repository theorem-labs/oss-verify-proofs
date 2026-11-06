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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BY_rz BY_hand BY_acct_needs BY_parse_kit BY_parse_pol BY_parse_head BY_parse_lex BY_parse_lexc BY_parse_epi BY_parse_tails BY_parse_tails2 BY_parse_sep BY_parse_agv BY_parse_map BY_parse_kitD BY_parse_gv BY_parse_gv2 BY_parse_kitV BY_parse_gv3 BY_parse_val.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Open Scope yprog_scope.


(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia1 := LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Local Ltac solve_cond_base1 :=
  first [ reflexivity
        | apply Z.ltb_lt; lia1 | apply Z.ltb_ge; lia1
        | apply Z.leb_le; lia1 | apply Z.leb_gt; lia1
        | apply Z.eqb_eq; lia1 | apply Z.eqb_neq; lia1 ].
Local Ltac solve_cond_rec1 :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); solve_cond_rec1
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); solve_cond_rec1
  | _ => solve_cond_base1
  end.
Local Ltac solve_cond1 := unfold_cond; fold_lit_ux; solve_cond_rec1.
Local Ltac if_true1 := let c := goal_cond in replace c with true; [cbv iota| symmetry; solve_cond1].
Local Ltac if_false1 := let c := goal_cond in replace c with false; [cbv iota| symmetry; solve_cond1].
(* [comment removed for export] *)
Local Ltac if_litc1 := let c := goal_cond in let v := eval vm_compute in c in
  lazymatch v with true => change c with true | false => change c with false end; cbv iota.
(* [comment removed for export] *)
Local Ltac iflit2 := first [if_litc1 | if_true1 | if_false1 | if_true | if_false].
(* [comment removed for export] *)
Lemma zext32_shl_shr : forall x, 0 <= x < 4294967296 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 32))) 32) = Z_to_bv 64 x.
Proof.
  intros x Hx. f_equal. rewrite unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Local Ltac shH SHH SHHeq MU WM k w ::=
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of SHH with u8arr _ ?m0 (2147450880 + ?H / 8) ?shb =>
      let R := fresh "SHR" in
      assert (R : ov_read_bytes bsegs mx (Z_to_bv 64 ((H + k) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]);
      [ replace ((H + k) / 8 + 2147450880) with (2147450880 + (H + k) / 8) by qlia0;
        apply (block_shadow_read0_u bsegs mx 2147450880 H 104 (H + k) w);
        [ qliaH | qlia0 | rewrite <- SHHeq; first [exact SHH | eapply (u8arr_transport bsegs); [exact SHH| exact MU| exact WM| rewrite SHHeq, (blk_shadow_length 104) by qlia0; cbn [disjoint_from fst snd]; qlia_sep]]
        | qlia0 | qlia0 | qlia0 | qliaH ]
      | zstepA; clear R; rewrite ?zxb_small, ?sxb_small by qlia0 ]
    end end.
Local Ltac shH0 SHH SHHeq MU WM w ::=
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of SHH with u8arr _ ?m0 (2147450880 + ?H / 8) ?shb =>
      let R := fresh "SHR" in
      assert (R : ov_read_bytes bsegs mx (Z_to_bv 64 (H / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]);
      [ replace (H / 8 + 2147450880) with (2147450880 + H / 8) by qlia0;
        apply (block_shadow_read0_u bsegs mx 2147450880 H 104 H w);
        [ qliaH | qlia0 | rewrite <- SHHeq; first [exact SHH | eapply (u8arr_transport bsegs); [exact SHH| exact MU| exact WM| rewrite SHHeq, (blk_shadow_length 104) by qlia0; cbn [disjoint_from fst snd]; qlia_sep]]
        | qlia0 | qlia0 | qlia0 | qliaH ]
      | zstepA; clear R; rewrite ?zxb_small, ?sxb_small by qlia0 ]
    end end.
Local Ltac qliaB := first [solve [keep_bsg; Z.div_mod_to_equations; lia] | Z.div_mod_to_equations; lia].
Local Ltac shS SHS SHSeq MU WM i size ::=
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of SHS with u8arr _ ?m0 (2147450880 + ?B / 8) ?shb =>
      let R := fresh "SHR" in
      assert (R : ov_read_bytes bsegs mx (Z_to_bv 64 ((B + i) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]);
      [ replace ((B + i) / 8 + 2147450880) with (2147450880 + (B + i) / 8) by qlia0;
        apply (block_shadow_read0_u bsegs mx 2147450880 B size (B + i) 1);
        [ qliaS | qliaB | rewrite <- SHSeq; first [exact SHS | eapply (u8arr_transport bsegs); [exact SHS| exact MU| exact WM| rewrite SHSeq, (blk_shadow_length size) by qliaB; cbn [disjoint_from fst snd]; qlia_sep]]
        | qliaB | qlia0 | qliaB | first [solve [clear; Z.div_mod_to_equations; lia] | qliaB] ]
      | zstepA; try shadow_addr; zstepA; zstepA; clear R; rewrite ?zxb_small, ?sxb_small by qlia0 ]
    end end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma vtext_byte_range : forall txt i, Forall (fun c => 0 <= c < 256) txt -> 0 <= znth txt i < 256.
Proof. aceil.
  intros txt i HF. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length txt)).
  - apply (proj1 (Forall_forall _ _) HF). apply nth_In. assumption.
  - rewrite nth_overflow by lia. lia.
Qed.
Lemma vznth_nth_error : forall (l : list Z) i, 0 <= i < zlength l -> nth_error l (Z.to_nat i) = Some (znth l i).
Proof. aceil.
  intros l i Hi. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (nth_error l (Z.to_nat i)) as [c|] eqn:E.
  - rewrite (nth_error_nth _ _ _ E). reflexivity.
  - apply nth_error_None in E. unfold zlength in Hi. lia.
Qed.
Lemma vtext_read : forall m T txt i,
  text_at bsegs m T txt -> 0 <= i < zlength txt ->
  ov_read_bytes bsegs m (wa (T + i)) 1 = Some [Z_to_bv 8 (znth txt i)].
Proof. aceil.
  intros m T txt i (TB & TF & T0 & TL) Hi.
  eapply (u8ro_read bsegs m T (zbytes txt) i); [exact TB| | lia| reflexivity].
  unfold zbytes. rewrite nth_error_map, (vznth_nth_error _ _ Hi). reflexivity.
Qed.

Definition J_GV14 : Z := 0x895c4.      (* [comment removed for export] *)

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
    rw_cells bsegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis URA_push : In PUSH_RET URA.
Hypothesis YRP : ayreset_parser_stmt.
Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis YCN : aycb_null_stmt.
Hypothesis YCB : aycb_boolean_stmt.
Hypothesis YCNUM : aycb_number_stmt.
Hypothesis YCS : aycb_string_stmt.
Hypothesis YCSM : aycb_start_map_stmt.
Hypothesis YCSA : aycb_start_array_stmt.
Let YH_shape : yphi_hand_shape_stmt Y := YH_shape Y phr YSPLIT.

(* [comment removed for export] *)
Lemma J_gv14 : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s h0 cx0 h mh cx obw olw cr st rest push
    (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s [] h mh cx obw olw cr -> frm0 fc ->
  h_stack h = st :: rest -> val_state st = true -> h_stack_size h mod 8 = 0 -> lex_inv (h_lexer h) -> h_stack_size h <= pLEN E + 1 + YAJL_BS_INC ->
  gv_push Y E h0 cx0 (gv_handle h st rest) cx cr (wz 1) (wz 0) push -> pagain Y E h0 cx0 [] ->
  pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')) ->
  realizes_cfg acfg bsegs (mkCfg (pstate E J_GV14 F fc m rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz (p_ff E)) s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM FRM HST VS SZM' LXI SZB GP AG EX.
  pose proof PM as (AY & _ & _ & _ & _ & (k0 & k224 & FR) & _ & _ & _ & _ & _ & MI & _ & _ & _ & [_ R1] & _). apply AYST_split in AY. destruct AY as [AHK _].
  unfold pframe, wz in FR. openPA PA.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, J_GV14, wz. arz_seg KIPY AHK.
  pose proof (aypol_stack Y _ _ _ _ LINK (p_lo E) (pSP E) ltac:(clear -CEILB pa_ceil0; aceil; lia) ltac:(clear -CEILB pa_sp0; lia)) as PSTK.
  unfold pol in PSTK. pose proof (ppol_mark E mh) as PPM. clear LINK.
  zstepA. zstepA.                                          (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  pose proof (pmem_remodel E m mo mo1 s [] h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  pose proof (J_gotval Y KIPY FRAMEY BLKY BSHY LAYY PERMY RRT NONNEG YHM UFRAME WREA URA USTEP URA_push YRP
                E F fc m mo1 s h0 cx0 h mh cx obw olw cr st rest push) as JG. unfold pstate, J_GV, wz in JG.
  eapply JG; [exact PA| exact OK| exact PM1| exact FRM| exact HST| exact VS| exact SZM'| exact LXI| exact SZB| exact GP| exact AG| exact EX].
Qed.

Section VAL.
Variables (E : apE Y) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : y_APS Y)
          (h0 : yhandle) (cx0 : yctx) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (cr : Z) (st : ystate) (rest : list ystate).
Variables (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5v t3 t4 t5 t6 : word).
Hypothesis PA : penvA E.
Hypothesis OK : pok E h0 cx0.
Hypothesis PM : pmem E m mo s [] h mh cx obw olw cr.
Hypothesis FRM : frm0 fc.
Hypothesis HST : h_stack h = st :: rest.
Hypothesis VS : val_state st = true.
Hypothesis SZM' : h_stack_size h mod 8 = 0.
Hypothesis LXI : lex_inv (h_lexer h).
Hypothesis SZB : h_stack_size h <= pLEN E + 1 + YAJL_BS_INC.
Hypothesis AG : pagain Y E h0 cx0 [].
Hypothesis EX : pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')).

Let at_switch (tok : ytok) : Prop :=
  realizes_cfg acfg bsegs (mkCfg (pstate E VAL_SW F fc m rav t0 t1 t2 (wz (tok_code tok)) a1 a2 a3 a4 a5 a6 a7 (wz 0) (wz (p_ff E)) s5v t3 t4 t5 t6) mo) (p_K E).   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma val_null :
  gv_push Y E h0 cx0 (gv_handle h st rest) cx cr (wz 1) (wz 0) None ->
  at_switch TK_null.
Proof. aceil.
  intros GP. unfold at_switch.
  popen OK PM; yhide TB; yhide OTB; yhide LP; yhide FFR0.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_Tsep0 pa_OT0 pa_j0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US. assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ [] ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H. destruct OSH_H as (_ & _ & SHH); rewrite EH in SHH. remember (blk_shadow 104) as shb eqn:SHHeq in SHH.
  pose proof YS as (CBS & _ & _ & STA). unfold callbacks_cells in CBS.
  cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ayc] in CBS.
  unfold AY_CALLBACKS, AY_CB_NULL, AY_CB_BOOLEAN, AY_CB_NUMBER, AY_CB_STRING, AY_CB_START_MAP, AY_CB_MAP_KEY, AY_CB_END_MAP, AY_CB_START_ARRAY, AY_CB_END_ARRAY, wz in CBS.
  destruct (GLOBY _ _ _ _ _ AHK) as (GCB & _). unfold oshadow, A_SB, AY_CALLBACKS in GCB. destruct GCB as (_ & _ & GSH).
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold AY_CALLBACKS, wz in HC; rewrite EH in HC.
  clear TXT LXR DBR FF OCX GAP PRES UA CRED HS HR; yhide SV. unfold wz in FR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, VAL_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s [] h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_imgsh0, pp_CX0, pp_CXs0. clear pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_SB0 pp_SBs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0 LINK.
  val_jt MI TK_null.
  zstepA.                                                  (* [comment removed for export] *)
  shH0 SHH SHHeq MU WM 8.                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA. ugd_bs.                                        (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (SHR : ov_read_bytes bsegs mx (Z_to_bv 64 2147537768) 1 = Some [Z_to_bv 8 0]);
    [ change 2147537768 with (2147450880 + (695104 + 0) / 8);
      apply (block_shadow_read0_u bsegs mx 2147450880 695104 88 (695104 + 0) 8); [reflexivity| lia| exact GSH| lia| lia| cbn; lia| reflexivity] |] end.
  zstepA. clear SHR.                                       (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  shH SHH SHHeq MU WM 8 8.                                 (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ ?P _ _ => pose proof (YCN P) as CB end. unfold aycb_null_rpost in CB.
  call_spA CB.
  - exact I.   (* [comment removed for export] *)
  - exact MI.
  - lazymatch goal with H : _ = wz 1 |- _ => rewrite H end. lazymatch goal with H : @eq mem ?x m |- _ => subst x | H : @eq mem m ?x |- _ => subst x | _ => idtac end. unfold wz.
    zstepA. iflit2.                                        (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    pose proof (pmem_remodel E m mo mo1 s [] h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    pose proof (J_gv14 E F fc m mo1 s h0 cx0 h mh cx obw olw cr st rest None) as JG. unfold pstate, J_GV14, wz in JG. cbn [gv_push] in GP.
    eapply JG; [exact PA| exact OK| exact PM1| exact FRM| exact HST| exact VS| exact SZM'| exact LXI| exact SZB| exact GP| exact AG| exact EX].
Qed.

(* [comment removed for export] *)
Lemma val_string :
  gv_push Y E h0 cx0 (gv_handle h st rest) cx cr (wz 1) (wz 0) None ->
  at_switch TK_string.
Proof. aceil.
  intros GP. unfold at_switch.
  popen OK PM; yhide TB; yhide OTB; yhide LP; yhide FFR0.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_Tsep0 pa_OT0 pa_j0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US. assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ [] ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H. destruct OSH_H as (_ & _ & SHH); rewrite EH in SHH. remember (blk_shadow 104) as shb eqn:SHHeq in SHH.
  pose proof YS as (CBS & _ & _ & STA). unfold callbacks_cells in CBS.
  cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ayc] in CBS.
  unfold AY_CALLBACKS, AY_CB_NULL, AY_CB_BOOLEAN, AY_CB_NUMBER, AY_CB_STRING, AY_CB_START_MAP, AY_CB_MAP_KEY, AY_CB_END_MAP, AY_CB_START_ARRAY, AY_CB_END_ARRAY, wz in CBS.
  destruct (GLOBY _ _ _ _ _ AHK) as (GCB & _). unfold oshadow, A_SB, AY_CALLBACKS in GCB. destruct GCB as (_ & _ & GSH).
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold AY_CALLBACKS, wz in HC; rewrite EH in HC.
  pose proof FF as (FFA & FOB & FJ2 & FOL & FJ3 & FSH). clear FFA FJ2 FJ3 FSH. unfold wz in FOB, FOL.
  clear TXT LXR DBR FF OCX GAP PRES UA CRED HS HR; yhide SV. unfold wz in FR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, VAL_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s [] h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_imgsh0, pp_CX0, pp_CXs0, pp_ff0. clear pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_SB0 pp_SBs0 pp_ffs0 pp_T0 pp_Ts0 LINK.
  val_jt MI TK_string.
  zstepA.                                                  (* [comment removed for export] *)
  shH0 SHH SHHeq MU WM 8.                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA. ugd_bs.                                        (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (SHR : ov_read_bytes bsegs mx (Z_to_bv 64 2147537773) 1 = Some [Z_to_bv 8 0]);
    [ change 2147537773 with (2147450880 + (695104 + 40) / 8);
      apply (block_shadow_read0_u bsegs mx 2147450880 695104 88 (695104 + 40) 8); [reflexivity| lia| exact GSH| lia| lia| cbn; lia| reflexivity] |] end.
  zstepA. clear SHR.                                       (* [comment removed for export] *)
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
  zstepA.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ ?P _ _ => pose proof (YCS P) as CB end. unfold aycb_string_rpost in CB.
  call_spA CB.
  - exact I.   (* [comment removed for export] *)
  - exact MI.
  - lazymatch goal with H : _ = wz 1 |- _ => rewrite H end. lazymatch goal with H : @eq mem ?x m |- _ => subst x | H : @eq mem m ?x |- _ => subst x | _ => idtac end. unfold wz.
    zstepA. iflit2.                                        (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    pose proof (pmem_remodel E m mo mo1 s [] h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    pose proof (J_gv14 E F fc m mo1 s h0 cx0 h mh cx obw olw cr st rest None) as JG. unfold pstate, J_GV14, wz in JG. cbn [gv_push] in GP.
    eapply JG; [exact PA| exact OK| exact PM1| exact FRM| exact HST| exact VS| exact SZM'| exact LXI| exact SZB| exact GP| exact AG| exact EX].
Qed.

(* [comment removed for export] *)
Lemma val_number : forall tok (n : Z),
  (tok = TK_integer \/ tok = TK_double) -> olw = wz n -> 0 < n < 2^31 ->
  gv_push Y E h0 cx0 (gv_handle h st rest) cx cr (wz 1) (wz 0) None ->
  at_switch tok.
Proof. aceil.
  intros tok n TOK EOL NB GP. unfold at_switch. subst olw.
  popen OK PM; yhide TB; yhide OTB; yhide LP; yhide FFR0.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_Tsep0 pa_OT0 pa_j0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US. assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ [] ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H. destruct OSH_H as (_ & _ & SHH); rewrite EH in SHH. remember (blk_shadow 104) as shb eqn:SHHeq in SHH.
  pose proof YS as (CBS & _ & _ & STA). unfold callbacks_cells in CBS.
  cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ayc] in CBS.
  unfold AY_CALLBACKS, AY_CB_NULL, AY_CB_BOOLEAN, AY_CB_NUMBER, AY_CB_STRING, AY_CB_START_MAP, AY_CB_MAP_KEY, AY_CB_END_MAP, AY_CB_START_ARRAY, AY_CB_END_ARRAY, wz in CBS.
  destruct (GLOBY _ _ _ _ _ AHK) as (GCB & _). unfold oshadow, A_SB, AY_CALLBACKS in GCB. destruct GCB as (_ & _ & GSH).
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold AY_CALLBACKS, wz in HC; rewrite EH in HC.
  pose proof FF as (FFA & FOB & FJ2 & FOL & FJ3 & FSH). clear FFA FJ2 FJ3 FSH. unfold wz in FOB, FOL.
  clear TXT LXR DBR FF OCX GAP PRES UA CRED HS HR; yhide SV. unfold wz in FR.
  pose proof (munch_refl [(p_lo E, bv_unsigned (Z_to_bv 64 (p_SQ E)))] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, VAL_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s [] h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_imgsh0, pp_CX0, pp_CXs0, pp_ff0. clear pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_SB0 pp_SBs0 pp_ffs0 pp_T0 pp_Ts0 LINK.
  destruct TOK as [-> | ->]; cbn [tok_code]; [val_jt MI TK_integer | val_jt MI TK_double].   (* [comment removed for export] *)
  all: zstepA;                                             (* [comment removed for export] *)
       shH0 SHH SHHeq MU WM 8;                             (* [comment removed for export] *)
       zstepA; iflit2;                                     (* [comment removed for export] *)
       zstepA;                                             (* [comment removed for export] *)
       zstepA;                                             (* [comment removed for export] *)
       zstepA;                                             (* [comment removed for export] *)
       zstepA; iflit2;                                     (* [comment removed for export] *)
       zstepA; ugd_bs;                                     (* [comment removed for export] *)
       zstepA;                                             (* [comment removed for export] *)
       zstepA; zstepA;                                     (* [comment removed for export] *)
       lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
         assert (SHR : ov_read_bytes bsegs mx (Z_to_bv 64 2147537772) 1 = Some [Z_to_bv 8 0]);
         [ change 2147537772 with (2147450880 + (695104 + 32) / 8);
           apply (block_shadow_read0_u bsegs mx 2147450880 695104 88 (695104 + 32) 8); [reflexivity| lia| exact GSH| lia| lia| cbn; lia| reflexivity] |] end;
       zstepA; clear SHR;                                  (* [comment removed for export] *)
       zstepA; iflit2;                                     (* [comment removed for export] *)
       zstepA;                                             (* [comment removed for export] *)
       zstepA; iflit2.                                     (* [comment removed for export] *)
  all: zstepA;                                             (* [comment removed for export] *)
       shH SHH SHHeq MU WM 8 8;                            (* [comment removed for export] *)
       zstepA; iflit2;                                     (* [comment removed for export] *)
       zstepA;                                             (* [comment removed for export] *)
       zstepA;                                             (* [comment removed for export] *)
       zstepA; zstepA;                                     (* [comment removed for export] *)
       zstepA; zstepA; rewrite ?ysx32_small by (clear -CEILB NB; lia);   (* [comment removed for export] *)
       zstepA.                                             (* [comment removed for export] *)
  all: assert (USQ : bv_unsigned (Z_to_bv 64 (p_SQ E)) = p_SQ E) by (apply unsigned_lit; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_sp0; lia).
  all: lazymatch goal with |- evtA _ ?P _ _ => pose proof (YCNUM P n (p_lo E)) as CB end; unfold aycb_number_rpost in CB.
  all: clear GSH SHH; yhide STK.  (* [comment removed for export] *)
  all: call_spA CB; rewrite ?USQ.
  all: lazymatch goal with
       | |- BYajlAlign.BA_aycb_number _ _ _ _ => exact I
       | |- ay_statics _ => exact STA
       | |- mem_inv _ _ => exact MI
       | |- _ = wz _ => reflexivity
       | |- 0 < _ < _ => clear -CEILB NB; lia
       | |- stk _ _ _ _ => exact STK
       | |- alloc_ceiling <= _ => clear -CEILB pa_ceil0; aceil; lia
       | |- p_lo E <= _ => clear -CEILB pa_SQ0 pa_lo0; lia
       | |- p_SQ E <= _ => clear -CEILB pa_SQ0 pa_sp0; lia
       | |- pol _ _ _ => intros a k Ha Hk; apply pp_stk0; [exact Ha|]; clear -CEILB Hk pa_SQ0; lia
       | |- _ => idtac
       end.
  all: lazymatch goal with H : _ = wz 1 |- _ => rewrite H end; unfold wz.
  all: lazymatch goal with H : stk bsegs ?mx (p_lo E) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2; rewrite ?USQ in ST2 end.
  all: lazymatch goal with H : mem_inv bsegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI2 end.
  all: zstepA; iflit2.                                     (* [comment removed for export] *)
  all: apply evtA_done; intros mo1 Hag1 HLI1 Hh1; destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  all: lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
  all: pose proof (pmem_remodel E m mo mo1 s [] h mh cx obw (Z_to_bv 64 n) cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1; rewrite USQ in MU.
  all: yshow TB; yshow OTB; yshow LP; yshow FFR0; yshow SV.
  all: assert (PM2 : pmem E m2 mo1 s [] h mh cx obw (Z_to_bv 64 n) cr)
    by (eapply (pmem_updO BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s [] h mh cx obw (Z_to_bv 64 n) cr _ _ h0 cx0);
          [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| exact MI2
          | constructor; [unfold ownO; cbn [fst snd]; left; clear; lia| constructor]
          | exact FOB| exact FOL| exact ST2]).
  all: pose proof (J_gv14 E F fc m2 mo1 s h0 cx0 h mh cx obw (Z_to_bv 64 n) cr st rest None) as JG; unfold pstate, J_GV14, wz in JG; cbn [gv_push] in GP.
  all: eapply JG; [exact PA| exact OK| exact PM2| exact FRM| exact HST| exact VS| exact SZM'| exact LXI| exact SZB| exact GP| exact AG| exact EX].
Qed.
(* [comment removed for export] *)
Lemma val_start_map :
  cx_objectLevel cx + 1 < 2^31 ->
  gv_push Y E h0 cx0 (gv_handle h st rest) (mkCtx (cx_arrayLevel cx) (cx_objectLevel cx + 1)) cr (wz 0) (wz 4) (Some ST_map_start) ->
  at_switch TK_left_bracket.
Proof. aceil.
  intros LVO GP. unfold at_switch.
  popen OK PM; yhide TB; yhide OTB; yhide LP; yhide FFR0.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_Tsep0 pa_OT0 pa_j0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US. assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ [] ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H. destruct OSH_H as (_ & _ & SHH); rewrite EH in SHH. remember (blk_shadow 104) as shb eqn:SHHeq in SHH.
  pose proof YS as (CBS & _ & _ & STA). unfold callbacks_cells in CBS.
  cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ayc] in CBS.
  unfold AY_CALLBACKS, AY_CB_NULL, AY_CB_BOOLEAN, AY_CB_NUMBER, AY_CB_STRING, AY_CB_START_MAP, AY_CB_MAP_KEY, AY_CB_END_MAP, AY_CB_START_ARRAY, AY_CB_END_ARRAY, wz in CBS.
  destruct (GLOBY _ _ _ _ _ AHK) as (GCB & _). unfold oshadow, A_SB, AY_CALLBACKS in GCB. destruct GCB as (_ & _ & GSH).
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold AY_CALLBACKS, wz in HC; rewrite EH in HC.
  pose proof FF as (FFA & FOB & FJ2 & FOL & FJ3 & FSH). clear FFA FJ2 FJ3 FSH. unfold wz in FOB, FOL.
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC). yhide SC. pose proof (pb_SBCX _ _ _ (mk_pblk BLKY LAYY BSHY E s [] h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ)) as SEPSC. pose proof (pb_SB _ _ _ (mk_pblk BLKY LAYY BSHY E s [] h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ)) as RSB.
  clear TXT LXR DBR FF GAP PRES UA CRED HS HR; yhide SV. unfold wz in FR.
  pose proof (munch_refl [(p_lo E, bv_unsigned (Z_to_bv 64 (p_SQ E))); (pCX E + 4, pCX E + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (USQ : bv_unsigned (Z_to_bv 64 (p_SQ E)) = p_SQ E) by (apply unsigned_lit; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_sp0; lia).
  unfold pstate, VAL_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s [] h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_imgsh0, pp_CX0, pp_CXs0, pp_ff0. clear pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_SB0 pp_SBs0 pp_ffs0 pp_T0 pp_Ts0 LINK.
  val_jt MI TK_left_bracket.
  zstepA.                                                  (* [comment removed for export] *)
  shH0 SHH SHHeq MU WM 8.                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA. ugd_bs.                                        (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (SHR : ov_read_bytes bsegs mx (Z_to_bv 64 2147537774) 1 = Some [Z_to_bv 8 0]);
    [ change 2147537774 with (2147450880 + (695104 + 48) / 8);
      apply (block_shadow_read0_u bsegs mx 2147450880 695104 88 (695104 + 48) 8); [reflexivity| lia| exact GSH| lia| lia| cbn; lia| reflexivity] |] end.
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
  lazymatch goal with |- evtA _ ?P _ _ => pose proof (YCSM P (pCX E) (p_lo E) cx) as CB end. unfold aycb_start_map_rpost in CB.
  clear FOB GSH SHH. yhide STK.  (* [comment removed for export] *)
  call_spA CB; rewrite ?USQ.
  - (* [comment removed for export] *) hnf. clear -CEILB pa_CX0 ECX. rewrite ?ECX. split; [lia| Z.div_mod_to_equations; lia].
  - exact STA.
  - exact CXR.
  - exact LVO.
  - exact OCX.
  - exact MI.
  - exact STK.
  - clear -CEILB pa_ceil0; aceil; lia.
  - clear -CEILB pa_SQ0 pa_lo0; lia.
  - clear -CEILB pa_SQ0 pa_sp0; lia.
  - first [exact (pa_CXA8 PA) | rewrite ECX; exact (pa_CXA8 PA) | rewrite <- ECX; exact (pa_CXA8 PA)].   (* [comment removed for export] *)
  - clear -CEILB pa_CX0. aceil. lia.
  - reflexivity.
  - intros a k Ha Hk. apply pp_stk0; [exact Ha|]. clear -CEILB Hk pa_SQ0; lia.
  - intros a k Ha Hk. apply pp_img0; [exact Ha| exact Hk].
  - split; intros a k Ha Hk; [apply pp_CX0; [exact Ha| exact Hk]| apply pp_CXs0; revert Ha Hk; clear -CEILB pa_CX0; unfold oshw_lo, oshw_hi, A_SB, amem; intros; Z.div_mod_to_equations; lia].
  - (* [comment removed for export] *)
    lazymatch goal with H : stk bsegs ?mx _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2; rewrite ?USQ in ST2 end.
    lazymatch goal with H : mem_inv bsegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI2 end.
    lazymatch goal with H : RYajlRep.ctx_rep _ _ _ (mkCtx _ _) |- _ => rename H into CXR2 end.
    lazymatch goal with H : _ = Z_to_bv 64 1 |- _ => rewrite H | H : _ = wz 1 |- _ => rewrite H end. unfold wz.
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. zstepA.                                        (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
    pose proof (pmem_remodel E m mo mo1 s [] h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    yshow TB. yshow OTB. yshow LP. yshow FFR0. yshow SV. yshow SC. rewrite USQ in MU.
    assert (PM2 : pmem E m2 mo1 s [] h mh (mkCtx (cx_arrayLevel cx) (cx_objectLevel cx + 1)) obw olw cr).
    { eapply (pmem_updA BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s [] h mh cx obw olw cr);
        [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| exact MI2| | reflexivity| reflexivity| reflexivity| reflexivity| exact I| |
        | exact CXR2
        | exists k0, k224; assumption
        | eapply (rw_cells_transport bsegs); [exact SV| exact MU| exact WM| unfold psaved; cbn; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_H0 pa_CX0; lia]
        | exact ST2 ].
      - constructor; [| constructor; [| constructor]]; unfold ownA; cbn [fst snd]; [right; right; right; clear -CEILB pa_SQ0; lia| right; right; left; clear; lia].
      - split; [| cbn [h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB;
                 split; [exact BC1| split; [exact BC2| split; [exact BC3| split; intros; congruence]]]].
        exists pew, pad. split; [| exact PW].
        unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app]. unfold AY_CALLBACKS, wz. rewrite EH.
        lazymatch goal with H0 : rw_cells bsegs m2 (mh_addr (p_mh E)) _ |- _ => exact H0 end.
      - eapply (rw_cells_transport bsegs) in SC; [| exact MU| exact WM| cbn; clear -CEILB SEPSC RSB pa_ceil0 pa_SQ0 pa_lo0 BC3; lia].
        unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC. }
    pose proof (J_gotval Y KIPY FRAMEY BLKY BSHY LAYY PERMY RRT NONNEG YHM UFRAME WREA URA USTEP URA_push YRP
                  E F fc m2 mo1 s h0 cx0 h mh (mkCtx (cx_arrayLevel cx) (cx_objectLevel cx + 1)) obw olw cr st rest (Some ST_map_start)) as JG.
    unfold pstate, J_GV, wz in JG. cbn [state_code] in GP.
    eapply JG; [exact PA| exact OK| exact PM2| exact FRM| exact HST| exact VS| exact SZM'| exact LXI| exact SZB| exact GP| exact AG| exact EX].
Qed.

(* [comment removed for export] *)
Lemma val_start_array :
  cx_arrayLevel cx + 1 < 2^31 ->
  gv_push Y E h0 cx0 (gv_handle h st rest) (mkCtx (cx_arrayLevel cx + 1) (cx_objectLevel cx)) cr (wz 0) (wz 9) (Some ST_array_start) ->
  at_switch TK_left_brace.
Proof. aceil.
  intros LVA GP. unfold at_switch.
  popen OK PM; yhide TB; yhide OTB; yhide LP; yhide FFR0.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_Tsep0 pa_OT0 pa_j0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US. assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ [] ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H. destruct OSH_H as (_ & _ & SHH); rewrite EH in SHH. remember (blk_shadow 104) as shb eqn:SHHeq in SHH.
  pose proof YS as (CBS & _ & _ & STA). unfold callbacks_cells in CBS.
  cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ayc] in CBS.
  unfold AY_CALLBACKS, AY_CB_NULL, AY_CB_BOOLEAN, AY_CB_NUMBER, AY_CB_STRING, AY_CB_START_MAP, AY_CB_MAP_KEY, AY_CB_END_MAP, AY_CB_START_ARRAY, AY_CB_END_ARRAY, wz in CBS.
  destruct (GLOBY _ _ _ _ _ AHK) as (GCB & _). unfold oshadow, A_SB, AY_CALLBACKS in GCB. destruct GCB as (_ & _ & GSH).
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold AY_CALLBACKS, wz in HC; rewrite EH in HC.
  pose proof FF as (FFA & FOB & FJ2 & FOL & FJ3 & FSH). clear FFA FJ2 FJ3 FSH. unfold wz in FOB, FOL.
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC). yhide SC. pose proof (pb_SBCX _ _ _ (mk_pblk BLKY LAYY BSHY E s [] h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ)) as SEPSC. pose proof (pb_SB _ _ _ (mk_pblk BLKY LAYY BSHY E s [] h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ)) as RSB.
  clear TXT LXR DBR FF GAP PRES UA CRED HS HR; yhide SV. unfold wz in FR.
  pose proof (munch_refl [(p_lo E, bv_unsigned (Z_to_bv 64 (p_SQ E))); (pCX E, pCX E + 4)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (USQ : bv_unsigned (Z_to_bv 64 (p_SQ E)) = p_SQ E) by (apply unsigned_lit; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_sp0; lia).
  unfold pstate, VAL_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s [] h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_imgsh0, pp_CX0, pp_CXs0, pp_ff0. clear pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_SB0 pp_SBs0 pp_ffs0 pp_T0 pp_Ts0 LINK.
  val_jt MI TK_left_brace.
  zstepA.                                                  (* [comment removed for export] *)
  shH0 SHH SHHeq MU WM 8.                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA. ugd_bs.                                        (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (SHR : ov_read_bytes bsegs mx (Z_to_bv 64 2147537777) 1 = Some [Z_to_bv 8 0]);
    [ change 2147537777 with (2147450880 + (695104 + 72) / 8);
      apply (block_shadow_read0_u bsegs mx 2147450880 695104 88 (695104 + 72) 8); [reflexivity| lia| exact GSH| lia| lia| cbn; lia| reflexivity] |] end.
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
  lazymatch goal with |- evtA _ ?P _ _ => pose proof (YCSA P (pCX E) (p_lo E) cx) as CB end. unfold aycb_start_array_rpost in CB.
  clear FOL FOB GSH SHH. yhide STK.  (* [comment removed for export] *)
  call_spA CB; rewrite ?USQ.
  - (* [comment removed for export] *) hnf. clear -CEILB pa_CX0 ECX. rewrite ?ECX. split; [lia| Z.div_mod_to_equations; lia].
  - exact STA.
  - exact CXR.
  - exact LVA.
  - exact OCX.
  - exact MI.
  - exact STK.
  - clear -CEILB pa_ceil0; aceil; lia.
  - clear -CEILB pa_SQ0 pa_lo0; lia.
  - clear -CEILB pa_SQ0 pa_sp0; lia.
  - first [exact (pa_CXA8 PA) | rewrite ECX; exact (pa_CXA8 PA) | rewrite <- ECX; exact (pa_CXA8 PA)].   (* [comment removed for export] *)
  - clear -CEILB pa_CX0. aceil. lia.
  - reflexivity.
  - intros a k Ha Hk. apply pp_stk0; [exact Ha|]. clear -CEILB Hk pa_SQ0; lia.
  - intros a k Ha Hk. apply pp_img0; [exact Ha| exact Hk].
  - split; intros a k Ha Hk; [apply pp_CX0; [exact Ha| exact Hk]| apply pp_CXs0; revert Ha Hk; clear -CEILB pa_CX0; unfold oshw_lo, oshw_hi, A_SB, amem; intros; Z.div_mod_to_equations; lia].
  - (* [comment removed for export] *)
    lazymatch goal with H : stk bsegs ?mx _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2; rewrite ?USQ in ST2 end.
    lazymatch goal with H : mem_inv bsegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI2 end.
    lazymatch goal with H : RYajlRep.ctx_rep _ _ _ (mkCtx _ _) |- _ => rename H into CXR2 end.
    lazymatch goal with H : _ = Z_to_bv 64 1 |- _ => rewrite H | H : _ = wz 1 |- _ => rewrite H end. unfold wz.
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. zstepA.                                        (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
    pose proof (pmem_remodel E m mo mo1 s [] h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    yshow TB. yshow OTB. yshow LP. yshow FFR0. yshow SV. yshow SC. rewrite USQ in MU.
    assert (PM2 : pmem E m2 mo1 s [] h mh (mkCtx (cx_arrayLevel cx + 1) (cx_objectLevel cx)) obw olw cr).
    { eapply (pmem_updA BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s [] h mh cx obw olw cr);
        [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| exact MI2| | reflexivity| reflexivity| reflexivity| reflexivity| exact I| |
        | exact CXR2
        | exists k0, k224; assumption
        | eapply (rw_cells_transport bsegs); [exact SV| exact MU| exact WM| unfold psaved; cbn; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_H0 pa_CX0; lia]
        | exact ST2 ].
      - constructor; [| constructor; [| constructor]]; unfold ownA; cbn [fst snd]; [right; right; right; clear -CEILB pa_SQ0; lia| right; right; left; clear; lia].
      - split; [| cbn [h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB;
                 split; [exact BC1| split; [exact BC2| split; [exact BC3| split; intros; congruence]]]].
        exists pew, pad. split; [| exact PW].
        unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app]. unfold AY_CALLBACKS, wz. rewrite EH.
        lazymatch goal with H0 : rw_cells bsegs m2 (mh_addr (p_mh E)) _ |- _ => exact H0 end.
      - eapply (rw_cells_transport bsegs) in SC; [| exact MU| exact WM| cbn; clear -CEILB SEPSC RSB pa_ceil0 pa_SQ0 pa_lo0 BC3; lia].
        unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC. }
    pose proof (J_gotval Y KIPY FRAMEY BLKY BSHY LAYY PERMY RRT NONNEG YHM UFRAME WREA URA USTEP URA_push YRP
                  E F fc m2 mo1 s h0 cx0 h mh (mkCtx (cx_arrayLevel cx + 1) (cx_objectLevel cx)) obw olw cr st rest (Some ST_array_start)) as JG.
    unfold pstate, J_GV, wz in JG. cbn [state_code] in GP.
    eapply JG; [exact PA| exact OK| exact PM2| exact FRM| exact HST| exact VS| exact SZM'| exact LXI| exact SZB| exact GP| exact AG| exact EX].
Qed.

(* [comment removed for export] *)
Lemma val_bool : forall (i : Z),
  obw = wz (p_T E + i) -> 0 <= i < pLEN E ->
  gv_push Y E h0 cx0 (gv_handle h st rest) cx cr (wz 1) (wz 0) None ->
  at_switch TK_bool.
Proof. aceil.
  intros i EOB IR GP. unfold at_switch. subst obw.
  popen OK PM; yhide TB; yhide OTB; yhide LP; yhide FFR0.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_Tsep0 pa_j0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US. assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ [] ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H. destruct OSH_H as (_ & _ & SHH); rewrite EH in SHH. remember (blk_shadow 104) as shb eqn:SHHeq in SHH.
  pose proof YS as (CBS & _ & _ & STA). unfold callbacks_cells in CBS.
  cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ayc] in CBS.
  unfold AY_CALLBACKS, AY_CB_NULL, AY_CB_BOOLEAN, AY_CB_NUMBER, AY_CB_STRING, AY_CB_START_MAP, AY_CB_MAP_KEY, AY_CB_END_MAP, AY_CB_START_ARRAY, AY_CB_END_ARRAY, wz in CBS.
  destruct (GLOBY _ _ _ _ _ AHK) as (GCB & _). unfold oshadow, A_SB, AY_CALLBACKS in GCB. destruct GCB as (_ & _ & GSH).
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold AY_CALLBACKS, wz in HC; rewrite EH in HC.
  pose proof FF as (FFA & FOB & FJ2 & FOL & FJ3 & FSH). clear FFA FJ2 FJ3 FSH. unfold wz in FOB, FOL.
  clear LXR DBR FF OCX GAP PRES UA CRED HS HR; yhide SV. unfold wz in FR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, VAL_SW, wz. cbn [tok_code].
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s [] h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0, pp_imgsh0, pp_CX0, pp_CXs0, pp_ff0. clear pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_SB0 pp_SBs0 pp_ffs0 LINK.
  pose proof (pp_T0 ltac:(clear -CEILB IR; lia)) as PT. pose proof (pp_Ts0 ltac:(clear -CEILB IR; lia)) as PTS0. clear pp_T0 pp_Ts0. unfold pol in PT, PTS0.
  (* [comment removed for export] *)
  yshow OTB. destruct OTB as [ZL0| (bt & HBT & Q1 & Q2)]; [exfalso; clear -CEILB ZL0 IR; lia|]. destruct (pa_OT0 ltac:(clear -CEILB IR; lia)) as (O8 & O1 & O2 & O3 & O4).
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & _ & _). pose proof (RNG bt ltac:(apply in_or_app; right; apply in_or_app; right; exact HBT)) as RT.
  unfold ablock_range, ACONSTS in RT. cbn [c_img_hi] in RT. aceil.
  destruct (BSHY _ _ _ _ _ bt AHK ltac:(apply in_or_app; right; apply in_or_app; right; exact HBT) ltac:(clear -CEILB Q1 Q2 O1 O2 IR; lia)) as [OSB OBH].
  unfold oshadow in OSB. destruct OSB as (BA8 & Bn & SHT). remember (blk_shadow (ab_size bt)) as sht eqn:SHTeq in SHT. unfold A_SB in SHT.
  assert (PTS : acc_ok (m_vm_lazy mo) (y_aS Y s) (Z_to_bv 64 ((p_T E + i) / 8 + 2147450880), 1%nat)).
  { apply PTS0; [clear -CEILB O1 IR; Z.div_mod_to_equations; lia| clear -CEILB O2 O8 IR; Z.div_mod_to_equations; lia]. }
  pose proof TXT as (TXB & TXF & TX0 & TX62).
  val_jt MI TK_bool.
  zstepA.                                                  (* [comment removed for export] *)
  shH0 SHH SHHeq MU WM 8.                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA. ugd_bs.                                        (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (SHR : ov_read_bytes bsegs mx (Z_to_bv 64 2147537769) 1 = Some [Z_to_bv 8 0]);
    [ change 2147537769 with (2147450880 + (695104 + 8) / 8);
      apply (block_shadow_read0_u bsegs mx 2147450880 695104 88 (695104 + 8) 8); [reflexivity| lia| exact GSH| lia| lia| cbn; lia| reflexivity] |] end.
  assert (POLSH : acc_ok (m_vm_lazy mo) (y_aS Y s) (Z_to_bv 64 2147537769, 1%nat)) by (yshow pp_imgsh0; apply (pp_imgsh0 2147537769 1%nat); clear; cbn; lia).  (* [comment removed for export] *)
  zstepA. clear SHR POLSH.                                       (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  zstepA. if_cases Gn; zify_cond Gn; [clear Gn| exfalso; revert Gn; clear -CEILB O1 Q1 IR TX0; unfold wz; rewrite ?unsigned_lit by lia; intros Gn; lia].   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  shH SHH SHHeq MU WM 8 8.                                 (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  destruct (block_shadow_read_u bsegs m 2147450880 (ab_addr bt) (ab_size bt) (p_T E + i) 1 BA8 Bn ltac:(rewrite <- SHTeq; exact SHT)
              ltac:(clear -CEILB Q1 O1 IR; lia) ltac:(clear; lia) ltac:(clear -CEILB Q2 O2 IR; lia) ltac:(clear; Z.div_mod_to_equations; lia)) as (kk & SHR & HK).
  replace (2147450880 + (p_T E + i) / 8) with ((p_T E + i) / 8 + 2147450880) in SHR by (clear; lia).
  zstepA. shadow_addr. zstepA.                             (* [comment removed for export] *)
  zstepA. clear SHR.                                       (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  pose proof (vtext_read m (p_T E) (p_txt E) i TXT IR) as RDT. pose proof (vtext_byte_range (p_txt E) i TXF) as RBT.
  change (wa (p_T E + i)) with (Z_to_bv 64 (p_T E + i)) in RDT.
  destruct HK as [-> | HK].
  1: rewrite ?zxb_small, ?sxb_small by (clear; lia); zstepA; iflit2.          (* [comment removed for export] *)
  2: rewrite ?zxb_small, ?sxb_small by (clear -CEILB HK; lia); zstepA; if_cases Kc; zify_cond Kc; [exfalso; clear -CEILB Kc HK; lia| clear Kc];   (* [comment removed for export] *)
     zstepA;                                               (* [comment removed for export] *)
     zstepA;                                               (* [comment removed for export] *)
     change 7 with (Z.ones 3); rewrite ?Z.land_ones by (clear -CEILB O1 Q1 IR TX0; lia); change (2^3) with 8;
     zstepA; if_cases Kb; zify_cond Kb; [exfalso; revert Kb; clear -CEILB HK; rewrite ?sxb_small, ?zxb_small, ?signed_lit_small by lia; intros Kb; lia| clear Kb];   (* [comment removed for export] *)
     zstepA.                                               (* [comment removed for export] *)
  all: zstepA; clear RDT; cbv beta; rewrite (u8_val (znth (p_txt E) i)) by exact RBT.   (* [comment removed for export] *)
  all: zstepA; zstepA; zstepA;                             (* [comment removed for export] *)
       zstepA.                                             (* [comment removed for export] *)
  all: lazymatch goal with |- evtA _ ?P _ _ => pose proof (YCB P) as CB end; unfold aycb_boolean_rpost in CB.
  all: call_spA CB; [exact I| exact MI|].   (* [comment removed for export] *)
  all: lazymatch goal with H : _ = wz 1 |- _ => rewrite H end; lazymatch goal with H : @eq mem ?x m |- _ => subst x | H : @eq mem m ?x |- _ => subst x | _ => idtac end; unfold wz.
  all: zstepA; iflit2.                                     (* [comment removed for export] *)
  all: apply evtA_done; intros mo1 Hag1 HLI1 Hh1; destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  all: pose proof (pmem_remodel E m mo mo1 s [] h mh cx (Z_to_bv 64 (p_T E + i)) olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  all: pose proof (J_gv14 E F fc m mo1 s h0 cx0 h mh cx (Z_to_bv 64 (p_T E + i)) olw cr st rest None) as JG; unfold pstate, J_GV14, wz in JG; cbn [gv_push] in GP.
  all: eapply JG; [exact PA| exact OK| exact PM1| exact FRM| exact HST| exact VS| exact SZM'| exact LXI| exact SZB| exact GP| exact AG| exact EX].
Qed.

End VAL.
End W.
End RC__1.
