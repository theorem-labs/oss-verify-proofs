(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr FP NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajlAlign UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_rz UY_kit2 UY_parse_kit UY_parse_kitJ UY_parse_kitD UY_parse_kitV UY_parse_gv UY_parse_val.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlParser YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsParse YajlFactsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope yprog_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Notation buf_rep := (buf_rep usegs).
Notation buf_struct := (buf_struct usegs).
Notation buf_data := (buf_data usegs).
Notation lexer_rep := (lexer_rep usegs).
Notation hand_rep := (hand_rep usegs ryc).
Notation hand_struct := (hand_struct usegs ryc).
Notation bs_rep := (bs_rep usegs).
Notation ctx_rep := (ctx_rep usegs).
Notation text_at := (text_at usegs).
Notation RYST := (RYST HK).
Notation yparse_head_inv := (yparse_head_inv HK).
Notation yparse_exit_cont := (yparse_exit_cont HK).
Notation pmem := (pmem HK).
Notation again_cont := (again_cont HK).
Notation exit_cont := (exit_cont HK).
Notation yhead_invX := (yhead_invX HK).

Hypothesis YLX : ylex_lex_stmt HK.
Hypothesis YWR : ywrap_realloc_stmt HK.
Hypothesis YRP : yreset_parser_stmt.
Hypothesis YCN : ycb_null_stmt.
Hypothesis YCB : ycb_boolean_stmt.
Hypothesis YCNUM : ycb_number_stmt.
Hypothesis YCS : ycb_string_stmt.
Hypothesis YCSM : ycb_start_map_stmt.
Hypothesis YCSA : ycb_start_array_stmt.
Hypothesis YCEA : ycb_end_array_stmt.
Hypothesis VSE : val_esc_stmt HK.
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

Lemma val_state_target : forall st, val_state st = true -> state_target st = 0x15a38.
Proof. intros [] H; cbn in H; try discriminate; reflexivity. Qed.
Lemma val_state_lex : forall st, val_state st = true -> lex_state st = true.
Proof. intros [] H; cbn in H; try discriminate; reflexivity. Qed.

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
Proof.
  intros until r. intros HST VS YL YR. unfold yparse_step. rewrite (ybs_current_eq h _ _ HST). cbn [ybind].
  destruct st; try discriminate; (eapply yleaf_bind; [exact YL|]; cbn beta iota; exact YR).
Qed.

Lemma pass_val : forall E m mo s h mh cx obw olw st rest
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s [] h mh cx obw olw -> h = p_h E -> cx = p_cx E ->
  h_stack h = st :: rest -> val_state st = true ->
  again_cont E -> exit_cont E ->
  realizes_cfg acfg usegs (mkCfg (yparse_head_state rav (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                           (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E) m
                           (pH E) (p_T E) (pLEN E) (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM EH ECX HST VS AG EX.
  eapply pass_lex; [exact HKS| exact HKP| exact HKB| exact YLX| exact OK| exact PM| exact EH| exact ECX| exact HST| apply val_state_lex; exact VS|].
  intros until LK'. intros YL LPOST HINV PM1. rewrite (val_state_target _ VS).
  pose proof (pmem_ranges _ HKB _ _ _ _ _ _ _ _ _ _ OK PM1) as (_ & _ & _ & _ & _ & _ & _ & B3).
  assert (HST1 : h_stack (h_set_lex_off h lx' off') = st :: rest) by exact HST.
  pose proof HINV as (_ & OFFB & DBI & DBOK & (FROK & USZ & BLK & SZK & EOL & EAL) & DEPTH & SZB).
  pose proof OK as (_ & _ & _ & _ & L26 & _).
  assert (LVA : cx_arrayLevel cx + 1 < 2^31).
  { rewrite EAL. pose proof (count_array_le (h_stack h)). unfold h_used in DEPTH. unfold pLEN in *. clear -H DEPTH OFFB L26. lia. }
  assert (LVO : cx_objectLevel cx + 1 < 2^31).
  { rewrite EOL. pose proof (count_map_le (h_stack h)). unfold h_used in DEPTH. unfold pLEN in *. clear -H DEPTH OFFB L26. lia. }
  subst h cx.
  pose proof (step_val (p_txt E) (pLEN E) (p_h E) (p_cx E) st rest lx' tok off' ob n) as SL.
  assert (SZK' : exists k, 0 < k /\ h_stack_size (h_set_lex_off (p_h E) lx' off') = YAJL_BS_INC * k) by exact SZK.
  assert (SZB' : h_stack_size (h_set_lex_off (p_h E) lx' off') <= pLEN E + 1 + YAJL_BS_INC) by exact SZB.
  pose proof PM1 as (RY1 & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _). apply RYST_split in RY1. destruct RY1 as [HK1 _].
  unfold pstate. cbn [Z.add Pos.add]. unfold wz, RY_JT_TOKVAL, RY_JT_STATE.
  rz_seg HKS HK1.
  destruct tok; cbn [tok_code] in *; cbn -[zslice znth] in LPOST.
  all: zstep; if_lit.
  (* [comment removed for export] *)
  1-14: zstep; zstep; zstep; zstep; zstep; zstep.
  all: apply evt_done.
  (* [comment removed for export] *)
  all: try (exfalso; exact (proj2 (proj2 (proj2 LPOST)))).
  all: first
    [ eapply (val_unallowed HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YWR|exact YRP|exact YCN|exact YCB|exact YCNUM|exact YCS|exact YCSM|exact YCSA|exact YCEA|exact OK|exact PM1|exact HST1|exact VS|cbn [h_lexer h_set_lex_off]; exact LXI'|exact SZK'|exact SZB'|exact LVA|exact LVO|exact AG|exact EX|left; reflexivity|right; reflexivity|idtac]
    | change (Z_to_bv 64 2) with (wz (status_code YS_insufficient_data)); eapply (J_exit HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YWR|exact YRP|exact YCN|exact YCB|exact YCNUM|exact YCS|exact YCSM|exact YCSA|exact YCEA|exact OK|exact PM1|exact HST1|exact VS|cbn [h_lexer h_set_lex_off]; exact LXI'|exact SZK'|exact SZB'|exact LVA|exact LVO|exact AG|exact EX|left; reflexivity|right; reflexivity|idtac]
    | eapply (val_error HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YWR|exact YRP|exact YCN|exact YCB|exact YCNUM|exact YCS|exact YCSM|exact YCSA|exact YCEA|exact OK|exact PM1|exact HST1|exact VS|cbn [h_lexer h_set_lex_off]; exact LXI'|exact SZK'|exact SZB'|exact LVA|exact LVO|exact AG|exact EX|left; reflexivity|right; reflexivity|idtac]
    | destruct LPOST as (OF1 & _ & _ & LXI' & _ & i0 & EOB & Hi & Hn & Hin & TAIL); subst ob;
      first [ eapply (val_null HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YWR|exact YRP|exact YCN|exact YCB|exact YCNUM|exact YCS|exact YCSM|exact YCSA|exact YCEA|exact OK|exact PM1|exact HST1|exact VS|cbn [h_lexer h_set_lex_off]; exact LXI'|exact SZK'|exact SZB'|exact LVA|exact LVO|exact AG|exact EX|left; reflexivity|right; reflexivity|idtac]
            | eapply (val_string HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YWR|exact YRP|exact YCN|exact YCB|exact YCNUM|exact YCS|exact YCSM|exact YCSA|exact YCEA|exact OK|exact PM1|exact HST1|exact VS|cbn [h_lexer h_set_lex_off]; exact LXI'|exact SZK'|exact SZB'|exact LVA|exact LVO|exact AG|exact EX|left; reflexivity|right; reflexivity|idtac]
            | eapply (val_bool HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YWR|exact YRP|exact YCN|exact YCB|exact YCNUM|exact YCS|exact YCSM|exact YCSA|exact YCEA|exact OK|exact PM1|exact HST1|exact VS|cbn [h_lexer h_set_lex_off]; exact LXI'|exact SZK'|exact SZB'|exact LVA|exact LVO|exact AG|exact EX|left; reflexivity|right; reflexivity|idtac]
            | eapply (val_start_map HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YWR|exact YRP|exact YCN|exact YCB|exact YCNUM|exact YCS|exact YCSM|exact YCSA|exact YCEA|exact OK|exact PM1|exact HST1|exact VS|cbn [h_lexer h_set_lex_off]; exact LXI'|exact SZK'|exact SZB'|exact LVA|exact LVO|exact AG|exact EX|left; reflexivity|right; reflexivity|idtac]
            | eapply (val_start_array HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YWR|exact YRP|exact YCN|exact YCB|exact YCNUM|exact YCS|exact YCSM|exact YCSA|exact YCEA|exact OK|exact PM1|exact HST1|exact VS|cbn [h_lexer h_set_lex_off]; exact LXI'|exact SZK'|exact SZB'|exact LVA|exact LVO|exact AG|exact EX|left; reflexivity|right; reflexivity|idtac]
            | eapply (val_rbrace HK); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YWR|exact YRP|exact YCN|exact YCB|exact YCNUM|exact YCS|exact YCSM|exact YCSA|exact YCEA|exact OK|exact PM1|exact HST1|exact VS|cbn [h_lexer h_set_lex_off]; exact LXI'|exact SZK'|exact SZB'|exact LVA|exact LVO|exact AG|exact EX|left; reflexivity|right; reflexivity|idtac]
            | eapply (VSE E); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YWR|exact YRP|exact YCN|exact YCB|exact YCNUM|exact YCS|exact YCSM|exact YCSA|exact YCEA|exact OK|exact PM1|exact HST1|exact VS|cbn [h_lexer h_set_lex_off]; exact LXI'|exact SZK'|exact SZB'|exact LVA|exact LVO|exact AG|exact EX|left; reflexivity|right; reflexivity|idtac]
            | eapply (val_number HK) with (pc := 0x15f30); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YWR|exact YRP|exact YCN|exact YCB|exact YCNUM|exact YCS|exact YCSM|exact YCSA|exact YCEA|exact OK|exact PM1|exact HST1|exact VS|cbn [h_lexer h_set_lex_off]; exact LXI'|exact SZK'|exact SZB'|exact LVA|exact LVO|exact AG|exact EX|left; reflexivity|right; reflexivity|idtac]
            | eapply (val_number HK) with (pc := 0x15efc); first [exact HKS|exact HKP|exact HKF|exact HKB|exact YWR|exact YRP|exact YCN|exact YCB|exact YCNUM|exact YCS|exact YCSM|exact YCSA|exact YCEA|exact OK|exact PM1|exact HST1|exact VS|cbn [h_lexer h_set_lex_off]; exact LXI'|exact SZK'|exact SZB'|exact LVA|exact LVO|exact AG|exact EX|left; reflexivity|right; reflexivity|idtac] ]
    | match goal with |- realizes_cfg _ _ (mkCfg (MS _ _ ?pc _ _ _ _) _) _ => idtac "NOARM" pc end ].
  (* [comment removed for export] *)
  all: try (cbn [outref_addr]; reflexivity).
  all: try reflexivity.
  all: try (cbn [h_decbuf h_set_lex_off]; first [exact DBI| exact DBOK]).
  all: try (destruct TAIL as (_ & _ & _ & _ & SB); exact SB).
  all: try (clear -Hi Hn Hin OF1 OFFB L26 TAIL; unfold pLEN in *; lia).
  (* [comment removed for export] *)
  all: try (intros r YR; apply (SL _ HST VS YL); cbv beta iota zeta; cbn [ybind cb_null cb_boolean cb_string cb_start_map cb_start_array cb_number jf_callbacks];
            first [exact YR| unfold yassert; replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; clear -TAIL; lia); cbn [ybind]; exact YR]).
  all: try (apply (SL _ HST VS YL); cbv beta iota zeta; cbn [h_bytesConsumed h_set_lex_off];
            first [ apply yl_ret
                  | rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_set_lex_off]; exact (proj2 B3)); cbn [ybind]; apply yl_ret
                  | unfold yparse_error; rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_set_lex_off]; exact (proj2 B3)); cbn [ybind]; apply yl_ret ]).
  (* [comment removed for export] *)
  1:{ intros E9. split.
      - rewrite EAL, HST, E9. cbn. pose proof (count_array_nonneg rest). lia.
      - apply (SL _ HST VS YL). cbv beta iota zeta. rewrite (ybs_current_eq _ _ _ HST1). cbn [ybind]. rewrite E9. cbn [state_eqb state_code Z.eqb cb_end_array jf_callbacks].
        unfold yassert. destruct (Z.ltb_spec 0 (cx_arrayLevel (p_cx E))); [| exfalso; rewrite EAL, HST, E9 in *; cbn in *; pose proof (count_array_nonneg rest); lia]. cbn [ybind].
        rewrite (ybs_pop_eq _ _ _ HST1). cbn [ybind]. apply yl_ret. }
  1:{ intros NE. apply (SL _ HST VS YL). cbv beta iota zeta. rewrite (ybs_current_eq _ _ _ HST1). cbn [ybind].
      replace (state_eqb st ST_array_start) with false by (clear -NE VS; destruct st; cbn in *; first [reflexivity| congruence| discriminate]).
      unfold yparse_error. rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_set_lex_off]; exact (proj2 B3)). cbn [ybind]. apply yl_ret. }
  (* [comment removed for export] *)
  all: cbn [h_decbuf h_set_lex_off]; intros db' YLD HOK; try intros r YR; apply (SL _ HST VS YL); cbv beta iota zeta; unfold ydecode_tok; cbn [h_decbuf h_set_lex_off];
       (eapply yleaf_bind; [eapply yleaf_bind; [apply ybuf_clear_leaf; exact DBOK|]; cbv beta; eapply yleaf_bind; [exact YLD|]; apply yl_ret|]);
       cbv beta; cbn [h_decbuf h_set_decbuf]; unfold ybuf_err, buf_state_ok, ybuf_data_chk, ybuf_len_chk.
  1:{ rewrite HOK. cbn [negb ybind cb_string jf_callbacks]. exact YR. }
  1:{ destruct (yb_state db'); [congruence| |]; cbn [negb ybind]; unfold ybuf_chk_fail;
      (rewrite (ybs_set_eq _ st rest) by (first [exact HST| unfold h_used; cbn [h_stack h_stack_size h_set_decbuf h_set_lex_off]; unfold h_used in B3; exact (proj2 B3)]));
      cbn [ybind]; apply yl_ret. }
Qed.


End S.
End RC__1.
