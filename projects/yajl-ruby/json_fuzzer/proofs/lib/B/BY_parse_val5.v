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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BY_rz BY_hand BY_acct_needs BY_parse_kit BY_parse_pol BY_parse_head BY_parse_lex BY_parse_lexc BY_parse_epi BY_parse_tails BY_parse_tails2 BY_parse_sep BY_parse_agv BY_parse_map BY_parse_kitD BY_parse_kitD2 BY_parse_gv BY_parse_gv2 BY_parse_kitV BY_parse_gv3 BY_parse_val BY_parse_val2 BY_parse_val3 BY_parse_val4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma ygot_value_leaf : forall h cx st rest push r,
  h_stack h = st :: rest -> val_state st = true -> h_used h <= h_stack_size h -> yb_state (lx_buf (h_lexer h)) = BS_ok ->
  yleaf (match push with
         | None => YRet (SR_again (gv_handle h st rest) cx)
         | Some stp => r0 <- ybs_push (gv_handle h st rest) stp ;;
                       (let '(ok, h2) := r0 in if ok then YRet (SR_again h2 cx) else YRet (SR_done YS_alloc_failed h2 cx))
         end) r ->
  yleaf (ygot_value h cx push) r.
Proof. aceil.
  intros h cx st rest push r HST VS US BOK YR. unfold ygot_value. rewrite (ybs_current_eq _ _ _ HST). cbn [ybind].
  destruct st; try discriminate VS; cbn [gv_handle] in YR.
  - eapply yleaf_bind; [eapply yleaf_bind; [apply ylex_realloc_leaf; exact BOK| apply yl_ret]|]. cbv beta. exact YR.
  - rewrite (ybs_set_eq _ _ _ _ HST US). cbn [ybind]. exact YR.
  - rewrite (ybs_set_eq _ _ _ _ HST US). cbn [ybind]. exact YR.
  - rewrite (ybs_set_eq _ _ _ _ HST US). cbn [ybind]. exact YR.
Qed.

Lemma lex_reset_buf : forall lx, lex_inv lx -> lx_buf (lex_reset lx) = lx_buf lx.
Proof. aceil. intros lx (_ & _ & _ & _ & _ & _ & E). cbn. rewrite E. reflexivity. Qed.

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

(* [comment removed for export] *)
Lemma gv_handle_phi : forall h1 st rest L,
  h_stack h1 = st :: rest -> val_state st = true -> lex_inv (h_lexer h1) ->
  y_phi_hand Y (gv_handle h1 st rest) L = y_phi_hand Y h1 L.
Proof. aceil.
  intros h1 st rest L HST VS LXI. pose proof YSPLIT as (EQ & _). rewrite !EQ.
  destruct st; try discriminate VS; cbn [gv_handle h_set_lexer h_set_stack h_lexer h_decbuf h_bytesConsumed h_stack_size];
    rewrite ?(lex_reset_buf _ LXI); unfold h_used; cbn [h_stack h_set_stack h_set_lexer]; rewrite ?HST; reflexivity.
Qed.

(* [comment removed for export] *)
Local Ltac side :=
  lazymatch goal with
  | |- pagain _ _ _ _ _ => match goal with A : forall LKx, pagain _ _ _ _ LKx |- _ => apply A end
  | |- (forall LKx, pagain _ _ _ _ LKx) => assumption
  | |- wz _ = wz _ => cbn [outref_addr]; reflexivity
  | |- tok_code _ = _ \/ _ => cbn [tok_code]; lia
  | |- _ = _ \/ _ = _ => first [left; reflexivity| right; reflexivity]
  | |- @eq (list _) _ [] => reflexivity
  | |- y_phi_hand _ _ _ <= _ => assumption
  | |- _ => first [assumption| eassumption| idtac]
  end.

(* [comment removed for export] *)
Lemma pass_val : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h mh cx
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word) st rest,
  penvA E -> phead_inv E fc m mo s LK h mh cx -> h_stack h = st :: rest -> val_state st = true ->
  pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h cx) (SR_done st h' cx')) ->
  (forall (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : y_APS Y) (LK' : list ablock) (h' : yhandle) (mh' : mhand) (cx' : yctx)
          (rav' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2v' s5v' t3' t4' t5' t6' : word),
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h cx) (SR_again h' cx') ->
     phead_inv E fc' m' mo' s' (LK' ++ LK) h' mh' cx' ->
     realizes_cfg acfg bsegs (mkCfg (phead E F' fc' m' (h_used h') rav' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2v' s5v' t3' t4' t5' t6') mo') (p_K E)) ->
  realizes_cfg acfg bsegs (mkCfg (phead E F fc m (h_used h) rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until rest. intros PA HI HST VS EXIT AGAIN.
  pose proof HI as ((obw & olw & cr & PM & HCR0) & OK & FRM & PLK).
  pose proof (plk_ok_lex LK h _ _ PLK HST (val_state_lex _ VS)) as LK0.
  pose proof OK as (_ & _ & _ & (_ & SZM) & _).
  eapply (pass_lex Y KIPY BLKY BSHY LAYY PERMY RRT YLX URA USTEP URA_lex UFRAME NONNEG phr YSPLIT E F fc m mo s LK h mh cx
            rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 st rest); [exact PA| exact HI| exact HST| apply val_state_lex; exact VS|].
  intros until cr'. intros YL LPOST HINV FRM' LKT PM1 PPOT. rewrite (val_state_target _ VS). cbn [Z.add Pos.add].
  openPA PA.
  pose proof (hinv_weak _ _ _ HINV) as (_ & US & _).
  pose proof HINV as (LXI0 & OFFB & DBI & DBOK & (FROK & USZ & BLK & SZK & EOL & EAL) & DEPTH & SZB).
  pose proof YSPLIT as (EQ & PNN & LX & POP & PUSH & PUSHR & L6).
  assert (HCR : y_phi_hand Y (h_set_lex_off h lx' off') (pLEN E) <= cr').
  { unfold ppot in PPOT. rewrite (EQ (h_set_lex_off h lx' off') (pLEN E)).
    unfold h_used in PPOT |- *. unfold h_set_lex_off in PPOT |- *. cbn [h_lexer h_decbuf h_bytesConsumed h_stack_size h_stack] in PPOT |- *.
    destruct LPOST as (OFF & _). pose proof (LX (h_bytesConsumed h) off' (zlength (h_stack h)) (h_stack_size h) (pLEN E) ltac:(clear -CEILB OFF; lia)) as L1.
    clear -CEILB PPOT L1. lia. }
  assert (HST1 : h_stack (h_set_lex_off h lx' off') = st :: rest) by exact HST.
  assert (SZM1 : h_stack_size (h_set_lex_off h lx' off') mod 8 = 0) by exact SZM.
  assert (SZB1 : h_stack_size (h_set_lex_off h lx' off') <= pLEN E + 1 + YAJL_BS_INC) by exact SZB.
  assert (US1 : h_used (h_set_lex_off h lx' off') <= h_stack_size (h_set_lex_off h lx' off')) by exact US.
  subst LK.
  assert (LKL : (length (LK' ++ []) <= 1)%nat).
  { rewrite app_nil_r. destruct LK' as [|b0 LK'']; [cbn; clear; lia|]. destruct (LKT ltac:(discriminate)) as [_ L1]. rewrite L1. clear; lia. }
  assert (AGX : forall LKx, pagain Y E h cx LKx).
  { intros LKx. unfold pagain. intros. eapply (AGAIN _ _ _ _ _ LKx); [eassumption|]. rewrite app_nil_r. eassumption. }
  assert (LVA : cx_arrayLevel cx + 1 < 2^31).
  { rewrite EAL. pose proof (count_array_le (h_stack h)). unfold h_used in DEPTH. clear -CEILB H DEPTH OFFB pa_len0. lia. }
  assert (LVO : cx_objectLevel cx + 1 < 2^31).
  { rewrite EOL. pose proof (count_map_le (h_stack h)). unfold h_used in DEPTH. clear -CEILB H DEPTH OFFB pa_len0. lia. }
  pose proof (step_val (p_txt E) (pLEN E) h cx st rest lx' tok off' ob n) as SL.
  (* [comment removed for export] *)
  assert (VT : tok <> TK_eof -> tok <> TK_error -> tok <> TK_comment ->
            LK' = [] /\ lex_inv lx' /\ h_bytesConsumed h < off' /\ off' <= pLEN E /\
            exists i0, ob = OB_text i0 /\ h_bytesConsumed h <= i0 /\ 0 <= n /\ i0 + n <= off').
  { intros N1 N2 N3. split.
    - destruct LK' as [|b0 LK'']; [reflexivity|]. destruct (LKT ltac:(discriminate)) as [[X|X] _]; congruence.
    - destruct LPOST as (OFF & _ & _ & REST). destruct tok; try congruence; destruct REST as (LI & OO & i0 & EOB & Hi & Hn & Hin & _);
        (split; [exact LI| split; [exact OO| split; [clear -CEILB OFF; lia| exists i0; repeat split; assumption]]]). }
  assert (SZ0 : 0 <= h_stack_size h) by (unfold h_used in US; pose proof (zlength_nonneg (h_stack h)); clear -CEILB US H; lia).
  (* [comment removed for export] *)
  assert (GPUSH : forall stp cx1, tok <> TK_eof -> tok <> TK_error -> tok <> TK_comment ->
            (forall r, yleaf (r0 <- ybs_push (gv_handle (h_set_lex_off h lx' off') st rest) stp ;;
                              (let '(ok, h2) := r0 in if ok then YRet (SR_again h2 cx1) else YRet (SR_done YS_alloc_failed h2 cx1))) r ->
                       yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h cx) r) ->
            gv_push Y E h cx (gv_handle (h_set_lex_off h lx' off') st rest) cx1 cr' (wz 0) (wz (state_code stp)) (Some stp)).
  { intros stp cx1 N1 N2 N3 YG. destruct (VT N1 N2 N3) as (_ & LI & CLT & OLE & _).
    assert (GH : forall L, y_phi_hand Y (gv_handle (h_set_lex_off h lx' off') st rest) L = y_phi_hand Y (h_set_lex_off h lx' off') L)
      by (intros L; apply (gv_handle_phi _ _ _ L HST1 VS LI)).
    assert (GU : h_used (gv_handle (h_set_lex_off h lx' off') st rest) = h_used h)
      by (destruct st; try discriminate VS; unfold h_used; cbn [gv_handle h_stack h_set_lexer h_set_stack h_set_lex_off]; rewrite ?HST; reflexivity).
    assert (GS : h_stack_size (gv_handle (h_set_lex_off h lx' off') st rest) = h_stack_size h)
      by (destruct st; try discriminate VS; reflexivity).
    assert (GC : h_bytesConsumed (gv_handle (h_set_lex_off h lx' off') st rest) = off')
      by (destruct st; try discriminate VS; reflexivity).
    assert (GLX : y_phi_buf Y (lx_buf (h_lexer (gv_handle (h_set_lex_off h lx' off') st rest))) = y_phi_buf Y (lx_buf lx'))
      by (destruct st; try discriminate VS; cbn [gv_handle h_lexer h_set_lexer h_set_stack h_set_lex_off]; rewrite ?(lex_reset_buf _ LI); reflexivity).
    assert (GDB : h_decbuf (gv_handle (h_set_lex_off h lx' off') st rest) = h_decbuf h)
      by (destruct st; try discriminate VS; reflexivity).
    unfold ppot in PPOT. cbn [h_lexer h_decbuf h_set_lex_off] in PPOT.
    split; [reflexivity| split; [reflexivity| split; [| split]]].
    - intros ULT. apply (pcr_full YHM E _ _ PA). rewrite EQ. cbn [h_set_stack h_lexer h_decbuf h_bytesConsumed h_stack_size].
      rewrite GLX, GDB, GS, GC. rewrite GU, GS in ULT.
      replace (h_used (h_set_stack (gv_handle (h_set_lex_off h lx' off') st rest) (stp :: h_stack (gv_handle (h_set_lex_off h lx' off') st rest))))
        with (h_used h + 1) by (rewrite <- GU; unfold h_used; cbn [h_stack h_set_stack]; unfold zlength; cbn [length]; clear; lia).
      pose proof (PUSH (h_bytesConsumed h) off' (h_used h) (h_stack_size h) (pLEN E) ltac:(clear -CEILB OFFB; lia) ltac:(clear -CEILB CLT OLE; lia) SZ0 ULT) as P1.
      clear -CEILB PPOT P1. lia.
    - intros UEQ. rewrite GU, GS in UEQ.
      destruct (PUSHR (h_bytesConsumed h) off' (h_used h) (h_stack_size h) (pLEN E) ltac:(clear -CEILB OFFB; lia) ltac:(clear -CEILB CLT OLE; lia) SZ0 UEQ) as [PL PR].
      split.
      + rewrite EQ. cbn [h_set_stack3 h_lexer h_decbuf h_bytesConsumed h_stack_size]. rewrite GLX, GDB, GS, GC.
        replace (h_used (h_set_stack3 (gv_handle (h_set_lex_off h lx' off') st rest) (h_stack (gv_handle (h_set_lex_off h lx' off') st rest)) (h_stack_size h + YAJL_BS_INC) None))
          with (h_used h) by (rewrite <- GU; unfold h_used; cbn [h_stack h_set_stack3]; reflexivity).
        clear -CEILB PPOT PL. lia.
      + intros p. rewrite EQ. cbn [h_set_stack3 h_lexer h_decbuf h_bytesConsumed h_stack_size].
        rewrite GLX, GDB, GS, GC.
        replace (h_used (h_set_stack3 (gv_handle (h_set_lex_off h lx' off') st rest) (stp :: h_stack (gv_handle (h_set_lex_off h lx' off') st rest)) (h_stack_size h + YAJL_BS_INC) (Some p)))
          with (h_used h + 1) by (rewrite <- GU; unfold h_used; cbn [h_stack h_set_stack3]; unfold zlength; cbn [length]; clear; lia).
        clear -CEILB PPOT PR. lia.
    - exact YG. }
  (* [comment removed for export] *)
  assert (GNONE : forall cx1, tok <> TK_eof -> tok <> TK_error -> tok <> TK_comment ->
            yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h cx) (SR_again (gv_handle (h_set_lex_off h lx' off') st rest) cx1) ->
            gv_push Y E h cx (gv_handle (h_set_lex_off h lx' off') st rest) cx1 cr' (wz 1) (wz 0) None).
  { intros cx1 N1 N2 N3 YG. destruct (VT N1 N2 N3) as (_ & LI & _).
    split; [unfold wz; rewrite unsigned_lit by (clear; lia); clear; lia| split; [| exact YG]].
    apply (pcr_full YHM E _ _ PA). rewrite (gv_handle_phi _ _ _ _ HST1 VS LI). exact HCR. }
  assert (BOK1 : tok <> TK_eof -> tok <> TK_error -> tok <> TK_comment -> yb_state (lx_buf (h_lexer (h_set_lex_off h lx' off'))) = BS_ok).
  { intros N1 N2 N3. destruct (VT N1 N2 N3) as (_ & LI & _). destruct LI as (_ & _ & _ & _ & _ & _ & E0). cbn [h_lexer h_set_lex_off]. rewrite E0. reflexivity. }
  destruct tok.
  - (* [comment removed for export] *)
    destruct (VT ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as (-> & LI & CLT & OLE & i0 & EOB & Hi & Hn & Hin). subst ob. cbn [app] in PM1.
    cbn -[zslice znth] in LPOST. destruct LPOST as (_ & _ & _ & _ & _ & i1 & EI & _ & _ & _ & N45). injection EI as <-.
    eapply val_bool. all: side. 1:{ clear -CEILB Hi Hin OLE N45 OFFB; lia. }
    apply GNONE; [discriminate| discriminate| discriminate|].
    apply (SL _ HST VS YL). cbv beta iota zeta. cbn [ybind cb_boolean jf_callbacks].
    eapply ygot_value_leaf; [exact HST1| exact VS| exact US1| apply BOK1; discriminate| cbv beta iota; apply yl_ret].
  - (* [comment removed for export] *)
    eapply val_unallowed. all: side.
    apply (SL _ HST VS YL). cbv beta iota zeta. unfold yparse_error. rewrite (ybs_set_eq _ _ _ _ HST1 US1). cbn [ybind]. apply yl_ret.
  - (* [comment removed for export] *)
    eapply val_unallowed. all: side.
    apply (SL _ HST VS YL). cbv beta iota zeta. unfold yparse_error. rewrite (ybs_set_eq _ _ _ _ HST1 US1). cbn [ybind]. apply yl_ret.
  - (* [comment removed for export] *)
    eapply val_eof. all: side.
    apply (SL _ HST VS YL). cbv beta iota zeta. apply yl_ret.
  - (* [comment removed for export] *)
    eapply val_error. all: side.
    apply (SL _ HST VS YL). cbv beta iota zeta. rewrite (ybs_set_eq _ _ _ _ HST1 US1). cbn [ybind]. apply yl_ret.
  - (* [comment removed for export] *)
    destruct (VT ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as (-> & LI & _). cbn [app] in PM1.
    eapply val_start_array. all: side.
    apply (GPUSH ST_array_start); [discriminate| discriminate| discriminate|]. intros r YR.
    apply (SL _ HST VS YL). cbv beta iota zeta. cbn [ybind cb_start_array jf_callbacks].
    eapply ygot_value_leaf; [exact HST1| exact VS| exact US1| apply BOK1; discriminate| cbv beta iota; exact YR].
  - (* [comment removed for export] *)
    destruct (VT ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as (-> & LI & _). cbn [app] in PM1.
    eapply val_start_map. all: side.
    apply (GPUSH ST_map_start); [discriminate| discriminate| discriminate|]. intros r YR.
    apply (SL _ HST VS YL). cbv beta iota zeta. cbn [ybind cb_start_map jf_callbacks].
    eapply ygot_value_leaf; [exact HST1| exact VS| exact US1| apply BOK1; discriminate| cbv beta iota; exact YR].
  - (* [comment removed for export] *)
    destruct (VT ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as (-> & LI & _). cbn [app] in PM1.
    eapply val_null. all: side.
    apply GNONE; [discriminate| discriminate| discriminate|].
    apply (SL _ HST VS YL). cbv beta iota zeta. cbn [ybind cb_null jf_callbacks].
    eapply ygot_value_leaf; [exact HST1| exact VS| exact US1| apply BOK1; discriminate| cbv beta iota; apply yl_ret].
  - (* [comment removed for export] *)
    destruct (VT ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as (-> & LI & _). cbn [app] in PM1.
    eapply val_rbrace. all: side.
    + intros E9. split.
      * rewrite EAL, HST, E9. cbn. pose proof (count_array_nonneg rest). lia.
      * apply (SL _ HST VS YL). cbv beta iota zeta. rewrite (ybs_current_eq _ _ _ HST1). cbn [ybind]. rewrite E9.
        cbn [state_eqb state_code Z.eqb cb_end_array jf_callbacks]. unfold yassert.
        destruct (Z.ltb_spec 0 (cx_arrayLevel cx)); [| exfalso; rewrite EAL, HST, E9 in *; cbn in *; pose proof (count_array_nonneg rest); lia]. cbn [ybind].
        rewrite (ybs_pop_eq _ _ _ HST1). cbn [ybind]. apply yl_ret.
    + intros NE. apply (SL _ HST VS YL). cbv beta iota zeta. rewrite (ybs_current_eq _ _ _ HST1). cbn [ybind].
      replace (state_eqb st ST_array_start) with false by (clear -CEILB NE VS; destruct st; cbn in *; first [reflexivity| congruence| discriminate]).
      unfold yparse_error. rewrite (ybs_set_eq _ _ _ _ HST1 US1). cbn [ybind]. apply yl_ret.
  - (* [comment removed for export] *)
    eapply val_unallowed. all: side.
    apply (SL _ HST VS YL). cbv beta iota zeta. unfold yparse_error. rewrite (ybs_set_eq _ _ _ _ HST1 US1). cbn [ybind]. apply yl_ret.
  - (* [comment removed for export] *)
    destruct (VT ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as (-> & LI & CLT & OLE & i0 & EOB & Hi & Hn & Hin). cbn [app] in PM1.
    cbn -[zslice znth] in LPOST. destruct LPOST as (_ & _ & _ & _ & _ & i1 & EI & _ & _ & Hin1 & NP & _). rewrite EOB in EI. injection EI as <-.
    eapply val_number with (n := n). all: side. 1:{ clear -CEILB NP Hn Hin1 OLE pa_len0 Hi OFFB; lia. }
    apply GNONE; [discriminate| discriminate| discriminate|].
    apply (SL _ HST VS YL). cbv beta iota zeta. cbn [ybind cb_number jf_callbacks]. unfold yassert.
    replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; exact NP). cbn [ybind].
    eapply ygot_value_leaf; [exact HST1| exact VS| exact US1| apply BOK1; discriminate| cbv beta iota; apply yl_ret].
  - (* [comment removed for export] *)
    destruct (VT ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as (-> & LI & CLT & OLE & i0 & EOB & Hi & Hn & Hin). cbn [app] in PM1.
    cbn -[zslice znth] in LPOST. destruct LPOST as (_ & _ & _ & _ & _ & i1 & EI & _ & _ & Hin1 & NP & _). rewrite EOB in EI. injection EI as <-.
    eapply val_number with (n := n). all: side. 1:{ clear -CEILB NP Hn Hin1 OLE pa_len0 Hi OFFB; lia. }
    apply GNONE; [discriminate| discriminate| discriminate|].
    apply (SL _ HST VS YL). cbv beta iota zeta. cbn [ybind cb_number jf_callbacks]. unfold yassert.
    replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; exact NP). cbn [ybind].
    eapply ygot_value_leaf; [exact HST1| exact VS| exact US1| apply BOK1; discriminate| cbv beta iota; apply yl_ret].
  - (* [comment removed for export] *)
    destruct (VT ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as (-> & LI & _). cbn [app] in PM1.
    eapply val_string. all: side.
    apply GNONE; [discriminate| discriminate| discriminate|].
    apply (SL _ HST VS YL). cbv beta iota zeta. cbn [ybind cb_string jf_callbacks].
    eapply ygot_value_leaf; [exact HST1| exact VS| exact US1| apply BOK1; discriminate| cbv beta iota; apply yl_ret].
  - (* [comment removed for export] *)
    destruct (VT ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)) as (-> & LI & CLT & OLE & i0 & EOB & Hi & Hn & Hin). cbn [app] in PM1.
    cbn -[zslice znth] in LPOST. destruct LPOST as (_ & _ & _ & _ & _ & i1 & EI & _ & _ & _ & _ & _ & _ & Hoff & SB). rewrite EOB in EI. injection EI as <-.
    subst ob.
    eapply val_string_esc with (i := i0) (n := n). all: side.
    1:{ clear -CEILB Hi OFFB; lia. }
    1:{ clear -CEILB Hoff OLE; lia. }
    + intros db' YLD HDOK.
      assert (HSTd : h_stack (h_set_decbuf (h_set_lex_off h lx' off') db') = st :: rest) by exact HST.
      assert (LId : lex_inv (h_lexer (h_set_decbuf (h_set_lex_off h lx' off') db'))) by exact LI.
      split; [unfold wz; rewrite unsigned_lit by (clear; lia); clear; lia| split].
      * apply (pcr_full YHM E _ _ PA). rewrite (gv_handle_phi _ _ _ _ HSTd VS LId).
        rewrite (EQ (h_set_decbuf (h_set_lex_off h lx' off') db') (pLEN E)). rewrite (EQ (h_set_lex_off h lx' off') (pLEN E)) in HCR.
        cbn [h_set_decbuf h_lexer h_decbuf h_bytesConsumed h_stack_size h_set_lex_off] in HCR |- *.
        unfold h_used in HCR |- *. cbn [h_stack h_set_decbuf h_set_lex_off] in HCR |- *. clear -CEILB HCR. lia.
      * apply (SL _ HST VS YL). cbv beta iota zeta. cbn [out_bytes]. unfold ydecode_tok. cbn [h_decbuf h_set_lex_off].
        eapply yleaf_bind; [eapply yleaf_bind; [apply ybuf_clear_leaf; exact DBOK|]; cbv beta; eapply yleaf_bind; [exact YLD|]; apply yl_ret|].
        cbv beta. cbn [h_decbuf h_set_decbuf]. unfold ybuf_err, buf_state_ok, ybuf_data_chk, ybuf_len_chk.
        rewrite HDOK. cbn [negb ybind cb_string jf_callbacks].
        eapply ygot_value_leaf; [exact HSTd| exact VS| exact US1| apply BOK1; discriminate| cbv beta iota; apply yl_ret].
    + intros db' YLD HNOK.
      apply (SL _ HST VS YL). cbv beta iota zeta. cbn [out_bytes]. unfold ydecode_tok. cbn [h_decbuf h_set_lex_off].
      eapply yleaf_bind; [eapply yleaf_bind; [apply ybuf_clear_leaf; exact DBOK|]; cbv beta; eapply yleaf_bind; [exact YLD|]; apply yl_ret|].
      cbv beta. cbn [h_decbuf h_set_decbuf]. unfold ybuf_err, buf_state_ok, ybuf_data_chk, ybuf_len_chk.
      destruct (yb_state db'); [congruence| |]; cbn [negb ybind]; unfold ybuf_chk_fail;
        (rewrite (ybs_set_eq _ st rest) by (first [exact HST| exact US1])); cbn [ybind]; apply yl_ret.
  - (* [comment removed for export] *)
    exfalso. exact (proj2 (proj2 (proj2 LPOST))).
Qed.
End W.
End RC__1.
