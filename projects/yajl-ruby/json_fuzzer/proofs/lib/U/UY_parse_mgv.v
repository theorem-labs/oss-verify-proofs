(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_rz UY_kit2 UY_parse_kit UY_parse_kitJ.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlParser YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
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

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

Hypothesis YLX : ylex_lex_stmt HK.

Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis YCEM : ycb_end_map_stmt.

Section MGV.
Variables (E : penv) (m : mem) (mo : Model) (s : PState) (LK : list block) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (rest : list ystate).
Variables (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v s8v : word).
Hypothesis OK : pok E.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw.
Hypothesis HST : h_stack h = ST_map_got_val :: rest.
Hypothesis AG : again_cont E.
Hypothesis EX : exit_cont E.

Let at_switch (tok : ytok) := realizes_cfg acfg usegs (mkCfg (pstate E 0x15b50 m (wz 0x15b50) t0 t1 t2 (wz (tok_code tok)) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (wz 0) s6v s8v (wz 13)) mo) (p_K E).

(* [comment removed for export] *)
Lemma mgv_rbracket :
  0 < cx_objectLevel cx ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h rest) (mkCtx (cx_arrayLevel cx) (cx_objectLevel cx - 1))) ->
  at_switch TK_right_bracket.
Proof.
  intros OL YL. unfold at_switch. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof YS as (CBS & _ & _). unfold callbacks_cells in CBS. cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ryc] in CBS.
  unfold RY_CALLBACKS, RY_CB_NULL, RY_CB_BOOLEAN, RY_CB_NUMBER, RY_CB_STRING, RY_CB_START_MAP, RY_CB_MAP_KEY, RY_CB_END_MAP, RY_CB_START_ARRAY, RY_CB_END_ARRAY, wz in CBS.
  unfold RY_CALLBACKS in HC.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz. cbn [tok_code].
  pose proof (munch_refl [(mh_ctx (p_mh E) + 4, mh_ctx (p_mh E) + 8)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  rz_seg HKS HK0.
  zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep. if_lit.
  zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep.
  rewrite <- ECX in CXC, MU.
  call (YCEM (mh_ctx mh) cx).
  all: lazymatch goal with
       | |- UA_ycb_end_map _ _ _ => unfold UA_ycb_end_map; unfold pCX in AL4; rewrite ECX; clear -SPC AL4 FRB; split; [lia| exact AL4]
       | |- RYajlRep.ctx_rep _ _ _ _ => split; [exact CXC|exact CXB2] | |- 0 < _ => exact OL | |- mem_inv _ _ => exact MI | |- _ = wz _ => reflexivity | |- _ => idtac end.
  lazymatch goal with H : _ = wz 1 |- _ => rewrite H end. unfold wz.
  zstep. if_lit.
  apply evt_done.
  pose proof (J_pop4c HK HKS HKF HKB E) as JP. unfold pstate, pH, wz in JP. eapply JP; [exact OK| | exact HST| exact YL| exact AG].
  eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| assumption| | reflexivity| reflexivity| reflexivity| reflexivity| |
    | lazymatch goal with H : RYajlRep.ctx_rep _ _ _ _ |- _ => unfold pCX; rewrite <- ECX; exact H end | exists padw; exact FR| exact STK].
  - constructor; [| constructor]. unfold ownA, pCX. cbn [fst snd]. clear -ECX. lia.
  - split; [| cbn [h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB; repeat split; try (clear -B1 B2 B3; lia); intros; congruence].
    exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
    cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app h_bytesConsumed h_stack_size h_parseError]. unfold wz, RY_CALLBACKS. rewrite EHA. exact HC.
  - unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC.
Qed.

(* [comment removed for export] *)
Lemma mgv_comma :
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h (ST_map_need_key :: rest)) cx) ->
  at_switch TK_comma.
Proof.
  intros YL. unfold at_switch. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  clear ERR TXT LXR DBR. unfold pstate, pH, wz. cbn [tok_code].
  rz_seg HKS HK0.
  zstep. zstep. if_lit. zstep. zstep. if_lit.
  inline_addr USED Z0 B2 B3 R2. zstep. step. apply evt_done.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + h_used h - 1) by (clear; lia).
  change (Z_to_bv 64 8) with (wz (state_code ST_map_need_key)).
  pose proof (J_setb HK HKS HKF HKB E) as JS. unfold pstate, pH in JS. eapply JS; [exact OK| exact PM| exact HST| exact YL| exact AG].
Qed.

Lemma mgv_eof :
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_done YS_insufficient_data h cx) ->
  at_switch TK_eof.
Proof.
  intros YL. unfold at_switch. open_env HKB OK PM.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz. cbn [tok_code].
  rz_seg HKS HK0.
  zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep. if_lit.
  zstep. step. apply evt_done.
  change (Z_to_bv 64 2) with (wz (status_code YS_insufficient_data)).
  pose proof (J_exit HK HKS E) as JE. unfold pstate, pH in JE. eapply JE; [exact OK| exact PM| exact YL| exact EX].
Qed.

Lemma mgv_error :
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h (ST_lexical_error :: rest)) cx) ->
  at_switch TK_error.
Proof.
  intros YL. unfold at_switch. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  clear ERR TXT LXR DBR. unfold pstate, pH, wz. cbn [tok_code].
  rz_seg HKS HK0.
  zstep. zstep. if_lit. zstep. zstep. if_lit.
  zstep. rewrite ysx32_small by (clear -USED Z0 B2 B3; lia).
  zstep. if_cases K; zify_cond K. { kill K. }
  zstep. rewrite ysx32_small by (clear -B2; lia).
  zstep. if_cases K'; zify_cond K'. 2:{ kill K'. }
  apply evt_done.
  pose proof (J_lexerr HK HKS HKF HKB E) as JL. unfold pstate, pH, wz in JL. eapply JL; [exact OK| exact PM| exact HST| exact YL| exact AG].
Qed.

(* [comment removed for export] *)
Lemma mgv_tail94 : forall a0v a1v (n : Z),
  olw = wz n -> 0 <= n <= h_bytesConsumed h ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E))
        (SR_again (h_set_off (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_map_expect) (h_bytesConsumed h - n)) cx) ->
  realizes_cfg acfg usegs (mkCfg (pstate E 0x16224 m (wz 0x15b50) t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (wz 0) s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros a0v a1v n EOL NB YL. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  subst olw. clear ERR TXT LXR DBR. unfold pstate, pH, wz. unfold wz in FR.
  pose proof (munch_refl [(mh_stack mh + h_used h - 1, mh_stack mh + h_used h); (mh_addr (p_mh E) + 24, mh_addr (p_mh E) + 36)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  assert (LEN : length (zbytes (stack_bytes (h_stack h)) ++ junk) = Z.to_nat (h_stack_size h)) by (rewrite length_app; clear -L1 L2 B3; lia).
  rz_seg HKS HK0.
  inline_addr USED Z0 B2 B3 R2. zstep.
  ubs_store h ARR ARR' L1 L2 B3 USED Z0.
  zstep. rewrite ysx32_small by (clear -B1; lia).
  zstep. rewrite ysx32_small by (clear -NB B1; lia).
  zstep. zstep. zstep. zstep.
  rewrite (swrap32_small (h_bytesConsumed h - n)) by (clear -NB B1; lia).
  rewrite (land_W64_small (h_bytesConsumed h - n)) by (clear -NB B1; lia).
  replace (h_bytesConsumed h <? h_bytesConsumed h - n) with false by (symmetry; apply Z.ltb_ge; clear -NB; lia).
  cbn [Z.b2z]. change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615.
  rewrite (Z.land_comm 18446744073709551615), (land_W64_small (h_bytesConsumed h - n)) by (clear -NB B1; lia).
  zstep. zstep.
  zstep. lit_store. zstep. step. apply evt_done.
  pose proof (J_back HK HKS E) as JB. unfold pstate, pH in JB. eapply JB; [exact OK| | exact YL| exact AG].
  eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| exact MI| | reflexivity| reflexivity| reflexivity| reflexivity| | | exact (conj CXC CXB2)| exists padw; exact FR| exact STK].
  - constructor; [| constructor; [| constructor]]; unfold ownA; cbn [fst snd]; [clear -B3 USED Z0; lia| clear -EHA; lia].
  - assert (EU : h_used (h_set_off (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_map_expect) (h_bytesConsumed h - n)) = h_used h)
      by (unfold h_used; cbn [h_stack h_set_stack h_set_perr h_set_off]; rewrite HST; reflexivity).
    split; [| cbn [h_set_off h_set_perr h_set_stack h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB, EU; repeat split; try (clear -B1 B2 B3 NB; lia); intros; congruence].
    exists (Z_to_bv 64 (yc_perr ryc PE_map_expect)), pad. split; [| reflexivity].
    unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w yc_perr ryc app h_set_off h_set_perr h_set_stack h_bytesConsumed h_stack_size]. unfold wz, ry_perr.
    rewrite EU, EHA. exact HC.
  - unfold RYajlRep.bs_rep. cbn [h_stack_blk h_set_off h_set_perr h_set_stack h_stack h_stack_size]. rewrite HSB. split; [exact SBNZ|].
    exists junk.
    replace (h_used (h_set_off (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_map_expect) (h_bytesConsumed h - n))) with (h_used h)
      by (unfold h_used; cbn [h_stack h_set_stack h_set_perr h_set_off]; rewrite HST; reflexivity).
    apply CB2_of_u8arr; [| rewrite zbytes_length, stack_bytes_length; cbn [length]; unfold zlength in USED; clear -USED; lia | exact L2].
    revert ARR'. rewrite HST, !stack_bytes_cons, !zbytes_app. cbn [zbytes map state_code]. rewrite <- !app_assoc. cbn [app].
    rewrite (upd_app_len _ _ _ _ _) by (rewrite zbytes_length, stack_bytes_length; unfold zlength in USED; clear -USED; lia).
    intros ARR'. exact ARR'.
Qed.

Lemma mgv_default : forall tok (n : Z),
  tok_code tok <> 2 -> tok_code tok <> 3 -> tok_code tok <> 4 -> tok_code tok <> 9 ->
  olw = wz n -> 0 <= n <= h_bytesConsumed h ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E))
        (SR_again (h_set_off (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_map_expect) (h_bytesConsumed h - n)) cx) ->
  at_switch tok.
Proof.
  intros tok n N2 N3 N4 N9 EOL NB YL. unfold at_switch. open_env HKB OK PM.
  pose proof (tok_code_range tok) as TR.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  rz_seg HKS HK0.
  zstep. zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *) zstep. zstep. if_cases K2; zify_cond K2. 2:{ kill K2. }
    zstep. zstep. if_cases K3; zify_cond K3. { kill K3. }
    apply evt_done. eapply mgv_tail94; [exact EOL| exact NB| exact YL].
  - (* [comment removed for export] *) zstep. zstep. if_cases K2; zify_cond K2. { kill K2. }
    zstep. zstep. if_cases K3; zify_cond K3. 2:{ kill K3. }
    apply evt_done. eapply mgv_tail94; [exact EOL| exact NB| exact YL].
Qed.
End MGV.

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
Proof.
  intros until r. intros HST YL YR. unfold yparse_step. rewrite (ybs_current_eq h _ _ HST). cbn [ybind].
  eapply yleaf_bind; [exact YL|]. cbn beta iota. exact YR.
Qed.

Lemma pass_mgv : forall E m mo s h mh cx obw olw rest
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s [] h mh cx obw olw -> h = p_h E -> cx = p_cx E ->
  h_stack h = ST_map_got_val :: rest ->
  again_cont E -> exit_cont E ->
  realizes_cfg acfg usegs (mkCfg (yparse_head_state rav (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                           (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E) m
                           (pH E) (p_T E) (pLEN E) (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM EH ECX HST AG EX.
  eapply pass_lex; [exact HKS| exact HKP| exact HKB| exact YLX| exact OK| exact PM| exact EH| exact ECX| exact HST| reflexivity|].
  intros until LK'. intros YL LPOST HINV PM1.
  pose proof (pmem_ranges _ HKB _ _ _ _ _ _ _ _ _ _ OK PM1) as (_ & _ & _ & _ & _ & _ & _ & B3).
  assert (HST1 : h_stack (h_set_lex_off h lx' off') = ST_map_got_val :: rest) by exact HST.
  pose proof HINV as (_ & OFFB & _ & _ & (FROK & _ & _ & _ & EOL & EAL) & _).
  assert (OL : 0 < cx_objectLevel cx).
  { rewrite EOL, HST. cbn. pose proof (count_map_nonneg rest). lia. }
  subst h cx.
  pose proof (step_mgv (p_txt E) (pLEN E) (p_h E) (p_cx E) rest lx' tok off' ob n) as SL.
  (* [comment removed for export] *)
  assert (GEN : tok_code tok <> 2 -> tok_code tok <> 3 -> tok_code tok <> 4 -> tok_code tok <> 9 -> 0 <= n <= off').
  { intros N2 N3 N4 N9. destruct tok; cbn in N2, N3, N4, N9; try lia; cbn -[zslice znth] in LPOST;
      destruct LPOST as (_ & _ & _ & LP4); try contradiction;
      destruct LP4 as (_ & _ & i & _ & Hi & Hn & Hin & _); clear -Hi Hn Hin OFFB; lia. }
  destruct tok.
  all: first [ eapply mgv_rbracket; [exact OK| exact PM1| exact HST1| exact AG| exact OL|]
             | eapply mgv_comma; [exact OK| exact PM1| exact HST1| exact AG|]
             | eapply mgv_error; [exact OK| exact PM1| exact HST1| exact AG|]
             | eapply mgv_eof; [exact OK| exact PM1| exact EX|]
             | eapply mgv_default; [exact OK| exact PM1| exact HST1| exact AG| cbn; lia| cbn; lia| cbn; lia| cbn; lia| reflexivity| cbn [h_bytesConsumed h_set_lex_off]; apply GEN; cbn; lia|] ].
  all: apply (SL _ HST YL); cbv beta iota zeta; cbn [h_bytesConsumed h_set_lex_off].
  all: try (rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_set_lex_off]; exact (proj2 B3)); cbn [ybind]; apply yl_ret).
  all: try apply yl_ret.
  all: try (rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_set_lex_off]; exact (proj2 B3)); cbn [ybind];
            replace (n <=? off') with true by (symmetry; apply Z.leb_le; apply GEN; cbn; lia); apply yl_ret).
  (* [comment removed for export] *)
  cbn [cb_end_map jf_callbacks]; unfold yassert; destruct (Z.ltb_spec 0 (cx_objectLevel (p_cx E))); try lia; cbn [ybind];
    rewrite (ybs_pop_eq _ _ _ HST1); cbn [ybind]; apply yl_ret.
Qed.

End S.
End RC__1.
