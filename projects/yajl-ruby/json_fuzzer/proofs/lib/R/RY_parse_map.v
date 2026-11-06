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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2 RY_parse_kit RY_parse_kitJ RY_parse_kitD.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_fastcall.
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
Notation buf_rep := (buf_rep rsegs).
Notation buf_struct := (buf_struct rsegs).
Notation buf_data := (buf_data rsegs).
Notation lexer_rep := (lexer_rep rsegs).
Notation hand_rep := (hand_rep rsegs ryc).
Notation hand_struct := (hand_struct rsegs ryc).
Notation bs_rep := (bs_rep rsegs).
Notation ctx_rep := (ctx_rep rsegs).
Notation text_at := (text_at rsegs).
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
Ltac inline_addr USED Z0 B2 B3 :=
  zstep; rewrite ysx32_small by (clear -USED Z0 B2 B3; lia);
  zstep; (let K := fresh "K" in if_cases K; zify_cond K; [kill K|]);
  zstep; rewrite ysx32_small by (clear -B2; lia);
  zstep; (let K := fresh "K" in if_cases K; zify_cond K; [kill K|]);
  zstep; zstep; zstep; zstep; rewrite (land_M32_small (h_used _ + -1)) by (clear -USED Z0 B3 B2; lia); zstep.

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis YCEM : ycb_end_map_stmt.
Hypothesis YCMK : ycb_map_key_stmt.
Hypothesis YSD : ystring_decode_stmt HK.
Hypothesis YBC : ybuf_clear_stmt.
Hypothesis YBE : ybuf_err_stmt.
Hypothesis YBD : ybuf_data_stmt.
Hypothesis YBL : ybuf_len_stmt.
Hypothesis YBS : ybs_set_stmt.

Lemma buf_state_code_range : forall st, 0 <= buf_state_code st <= 2.
Proof. intros []; cbn; lia. Qed.

Definition map_target (tok : ytok) : Z :=
  match tok with
  | TK_eof => 0x16124 | TK_error => 0x15544 | TK_right_bracket => 0x15664
  | TK_string => 0x1570c | TK_string_esc => 0x156bc
  | _ => 0x1575c
  end.

Definition map_state (st : ystate) : bool :=
  match st with ST_map_start | ST_map_need_key => true | _ => false end.

Section MAP.
Variables (E : penv) (m : mem) (mo : Model) (s : PState) (LK : list block) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (st : ystate) (rest : list ystate).
Variables (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v s8v : word).
Hypothesis OK : pok E.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw.
Hypothesis HST : h_stack h = st :: rest.
Hypothesis MS4 : map_state st = true.
Hypothesis AG : again_cont E.
Hypothesis EX : exit_cont E.

Let at_pc (pc : Z) (rav a0v a1v s5v : word) := realizes_cfg acfg rsegs (mkCfg (pstate E pc m rav t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).

Lemma map_error : forall rav a0v a1v s5v,
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h (ST_lexical_error :: rest)) cx) ->
  at_pc 0x15544 rav a0v a1v s5v.
Proof.
  intros rav a0v a1v s5v YL. unfold at_pc. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  rz_seg HKS HK0.
  zstep. rewrite ysx32_small by (clear -USED Z0 B2 B3; lia).
  zstep. if_cases K; zify_cond K. { kill K. }
  zstep. rewrite ysx32_small by (clear -B2; lia).
  zstep. if_cases K'; zify_cond K'. 2:{ kill K'. }
  apply evt_done.
  pose proof (J_lexerr HK HKS HKF HKB E) as JL. unfold pstate, pH, wz in JL. eapply JL; [exact OK| exact PM| exact HST| exact YL| exact AG].
Qed.

(* [comment removed for export] *)
Lemma map_tail6d8 : forall rav a0v a2v a3v s5v,
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_invalid_object_key) cx) ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x15764 m rav t0 t1 t2 a0v (wz (h_used h)) a2v a3v a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros rav a0v a2v a3v s5v YL. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  rz_seg HKS HK0.
  zstep. rewrite ysx32_small by (clear -B2; lia).
  zstep. if_cases K; zify_cond K. { kill K. }
  zstep. zstep. zstep. zstep. rewrite (land_M32_small (h_used h + -1)) by (clear -USED Z0 B3 B2; lia). zstep.
  zstep. zstep. step. apply evt_done.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + h_used h - 1) by (clear; lia).
  change (Z_to_bv 64 67696) with (wz (yc_perr ryc PE_invalid_object_key)).
  pose proof (J_perr HK HKS HKF HKB E) as JP. unfold pstate, pH in JP. eapply JP; [exact OK| exact PM| exact HST| exact YL| exact AG].
Qed.

Lemma map_default : forall rav a0v a1v s5v,
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_invalid_object_key) cx) ->
  at_pc 0x1575c rav a0v a1v s5v.
Proof.
  intros rav a0v a1v s5v YL. unfold at_pc. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  rz_seg HKS HK0.
  zstep. rewrite ysx32_small by (clear -USED Z0 B2 B3; lia).
  zstep. if_cases K; zify_cond K. { kill K. }
  apply evt_done. apply map_tail6d8. exact YL.
Qed.

(* [comment removed for export] *)
Lemma map_rbracket : forall rav a0v a1v s5v,
  (st = ST_map_start -> 0 < cx_objectLevel cx /\
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h rest) (mkCtx (cx_arrayLevel cx) (cx_objectLevel cx - 1)))) ->
  (st = ST_map_need_key ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_invalid_object_key) cx)) ->
  at_pc 0x15664 rav a0v a1v s5v.
Proof.
  intros rav a0v a1v s5v YST YNK. unfold at_pc. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof YS as (CBS & _ & _). unfold callbacks_cells in CBS. cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ryc] in CBS.
  unfold RY_CALLBACKS, RY_CB_NULL, RY_CB_BOOLEAN, RY_CB_NUMBER, RY_CB_STRING, RY_CB_START_MAP, RY_CB_MAP_KEY, RY_CB_END_MAP, RY_CB_START_ARRAY, RY_CB_END_ARRAY, wz in CBS.
  unfold RY_CALLBACKS in HC.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2).
  pose proof (u8arr_read rsegs m (mh_stack mh) _ (h_used h - 1) (Z_to_bv 8 (state_code st)) _ ARR
                ltac:(rewrite HST; replace (Z.to_nat (h_used h - 1)) with (Z.to_nat (zlength rest)) by (clear -USED; lia); apply stack_top_byte) ltac:(clear -USED Z0; lia) eq_refl) as RK.
  pose proof (munch_refl [(mh_ctx (p_mh E) + 4, mh_ctx (p_mh E) + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  rz_seg HKS HK0.
  zstep. rewrite ysx32_small by (clear -USED Z0 B2 B3; lia).
  zstep. if_cases K; zify_cond K. { kill K. }
  zstep. zstep. rewrite (swrap32_small (h_used h + -1)) by (clear -USED Z0 B2 B3; lia).
  zstep. zstep. rewrite (land_M32_small (h_used h + -1)) by (clear -USED Z0 B3 B2; lia). zstep.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + (h_used h - 1)) by (clear; lia).
  change (wa (mh_stack mh + (h_used h - 1))) with (Z_to_bv 64 (mh_stack mh + (h_used h - 1))) in RK.
  step. clear RK. change (Z_to_bv 8 (state_code st)) with (b8 (state_code st)). rewrite (zxb_b8 (state_code st)) by (clear; destruct st; cbn; lia).
  zstep. zstep. if_cases K4; zify_cond K4; unfold wz in K4; rewrite unsigned_lit in K4 by (clear; pose proof (state_code_range st); lia).
  2:{ (* [comment removed for export] *)
    assert (E4 : st = ST_map_start) by (clear -K4 MS4; destruct st; cbn in K4, MS4; first [reflexivity| discriminate| lia]).
    destruct (YST E4) as [OL YL].
    zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep.
    rewrite <- ECX in CXC, MU.
    call (YCEM (mh_ctx mh) cx).
    all: lazymatch goal with |- RYajlRep.ctx_rep _ _ _ _ => split; [exact CXC|exact CXB2] | |- 0 < _ => exact OL | |- mem_inv _ _ => exact MI | |- _ = wz _ => reflexivity | |- _ => idtac end.
    lazymatch goal with H : _ = wz 1 |- _ => rewrite H end. unfold wz.
    zstep. if_lit.
    apply evt_done.
    pose proof (J_pop1c HK HKS HKF HKB E) as JP. unfold pstate, pH, wz in JP. eapply JP; [exact OK| | exact HST| exact YL| exact AG].
    eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| assumption| | reflexivity| reflexivity| reflexivity| reflexivity| | 
      | lazymatch goal with H : RYajlRep.ctx_rep _ _ _ _ |- _ => unfold pCX; rewrite <- ECX; exact H end | exists padw; exact FR| exact STK].
    + constructor; [| constructor]. unfold ownA, pCX. cbn [fst snd]. clear -ECX. lia.
    + split; [| cbn [h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB; repeat split; try (clear -B1 B2 B3; lia); intros; congruence].
      exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
      cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app h_bytesConsumed h_stack_size h_parseError]. unfold wz, RY_CALLBACKS. rewrite EHA. exact HC.
    + unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC. }
  (* [comment removed for export] *)
  assert (E8 : st = ST_map_need_key) by (clear -K4 MS4; destruct st; cbn in K4, MS4; first [reflexivity| discriminate| lia]).
  apply evt_done. apply map_tail6d8. exact (YNK E8).
Qed.

(* [comment removed for export] *)
Lemma map_key_tail : forall rav a0v a1v s5v,
  0 < cx_objectLevel cx ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h (ST_map_sep :: rest)) cx) ->
  at_pc 0x1570c rav a0v a1v s5v.
Proof.
  intros rav a0v a1v s5v OL YL. unfold at_pc. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof YS as (CBS & _ & _). unfold callbacks_cells in CBS. cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ryc] in CBS.
  unfold RY_CALLBACKS, RY_CB_NULL, RY_CB_BOOLEAN, RY_CB_NUMBER, RY_CB_STRING, RY_CB_START_MAP, RY_CB_MAP_KEY, RY_CB_END_MAP, RY_CB_START_ARRAY, RY_CB_END_ARRAY, wz in CBS.
  unfold RY_CALLBACKS in HC.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz. unfold wz in FR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
  rz_seg HKS HK0.
  zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep. zstep. zstep.
  rewrite <- ECX in CXC.
  call (YCMK (mh_ctx mh) cx).
  all: lazymatch goal with |- RYajlRep.ctx_rep _ _ _ _ => split; [exact CXC|exact CXB2] | |- 0 < _ => exact OL | |- mem_inv _ _ => exact MI | |- _ = wz _ => reflexivity | |- _ => idtac end.
  lazymatch goal with H : _ = wz 1 |- _ => rewrite H end. unfold wz.
  lazymatch goal with H : @eq mem ?x ?y |- _ => first [subst y| subst x] end.
  zstep. if_lit.
  inline_addr USED Z0 B2 B3. zstep. step. apply evt_done.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + h_used h - 1) by (clear; lia).
  change (Z_to_bv 64 5) with (wz (state_code ST_map_sep)).
  rewrite ECX in CXC.
  pose proof (J_setb HK HKS HKF HKB E) as JS. unfold pstate, pH in JS. eapply JS; [exact OK| exact PM| exact HST| exact YL| exact AG].
Qed.

End MAP.

Section MAP2.
Variables (E : penv) (m : mem) (mo : Model) (s : PState) (LK : list block) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (st : ystate) (rest : list ystate).
Variables (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v s8v : word).
Hypothesis OK : pok E.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw.
Hypothesis HST : h_stack h = st :: rest.
Hypothesis MS4 : map_state st = true.
Hypothesis AG : again_cont E.
Hypothesis EX : exit_cont E.

(* [comment removed for export] *)
Lemma map_esc_fail : forall rav a0v a1v s5v bst,
  yb_state (h_decbuf h) = bst -> buf_state_code bst <> 0 -> buf_inv (h_decbuf h) ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E))
        (SR_done YS_alloc_failed (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_alloc_failed) cx) ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x156e4 m rav t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros rav a0v a1v s5v bst HSTT BNZ DBI YL. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof DBR as ((DBC & DBZ & DBL & DBU) & DBD & DBF).
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG _].
  assert (IDB : In (mb_id (mh_decbuf mh), mb_addr (mh_decbuf mh), SIZEOF_BUF) (yblocks mh h ++ LK ++ p_REST E)).
  { unfold yblocks. cbn [app]. right. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. left. reflexivity. }
  pose proof (all_range_In _ _ RNG IDB) as RDB. unfold rblock_range, alloc_ceiling, SIZEOF_BUF in RDB. cbn [blk_addr blk_size fst snd] in RDB. clear RNG IDB.
  clear ERR TXT LXR. unfold pstate, pH, wz. unfold wz in FR.
  pose proof (buf_state_code_range bst) as BSR'.
  unfold buf_cells in DBC. rewrite HSTT in DBC. unfold wz in DBC.
  pose proof (munch_refl [(p_lo E, bv_unsigned (p_sp E)); (mh_stack mh + h_used h - 1, mh_stack mh + h_used h)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  rz_seg HKS HK0.
  zstep. zstep.
  call (YBE (mb_addr (mh_decbuf mh)) (buf_state_code bst)).
  all: lazymatch goal with |- rw_cells _ _ _ (C4 _ :: _) => exact DBC | |- 0 <= _ < _ => clear -BSR'; lia | |- _ <> 0 => clear -RDB; lia | |- mem_inv _ _ => assumption | |- _ = wz _ => reflexivity | |- _ => idtac end.
  lazymatch goal with H : _ = wz (buf_state_code bst) |- _ => rewrite H end. lazymatch goal with H : @eq mem ?x ?y |- _ => first [subst y| subst x] end. unfold wz.
  zstep. if_cases K; zify_cond K. 2:{ exfalso. revert K BNZ BSR'. clear. intros. rewrite ?unsigned_lit in K by lia. lia. }
  zstep. zstep. zstep.
  call (YBS h mh st ST_parse_error rest (p_lo E)).
  all: lazymatch goal with
       | |- RYajlRep.hand_struct _ _ _ _ _ => exact HS
       | |- RYajlRep.bs_rep _ _ _ _ => unfold RYajlRep.bs_rep; rewrite HSB; split; [exact SBNZ| exists junk; exact SC]
       | |- h_stack _ = _ => exact HST
       | |- h_stack_blk _ <> None => rewrite HSB; discriminate
       | |- stk _ _ _ _ => assumption
       | |- _ <= bv_unsigned _ - _ => clear -LO; lia
       | |- _ + SIZEOF_HANDLE <= _ \/ _ => unfold SIZEOF_HANDLE; rewrite EHA; clear -S12; lia
       | |- _ + SIZEOF_HANDLE <= _ => unfold SIZEOF_HANDLE; rewrite EHA; clear -R1 CEIL; lia
       | |- mh_stack _ + _ <= _ => clear -R2 CEIL; lia
       | |- mem_inv _ _ => assumption
       | |- _ = wz _ => rewrite ?EHA; reflexivity
       | |- _ => idtac end.
  zstep. zstep. step. apply evt_done.
  lazymatch goal with H : RYajlRep.hand_struct _ _ _ _ _ |- _ => rename H into HS2 end.
  lazymatch goal with H : RYajlRep.bs_rep _ _ _ _ |- _ => rename H into BS2 end.
  lazymatch goal with H : stk _ _ _ _ |- _ => rename H into STK2 end.
  change (Z_to_bv 64 67531) with (wz (yc_perr ryc PE_alloc_failed)).
  pose proof (J_fail4 HK HKS HKF HKB E) as JF. unfold pstate, pH in JF. eapply JF; [exact OK| | exact YL| exact EX].
  eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| assumption| | reflexivity| reflexivity| reflexivity| reflexivity| | | exact (conj CXC CXB2)| exists padw; exact FR| exact STK2].
  + constructor; [| constructor; [| constructor]]; unfold ownA, pSP; cbn [fst snd]; [clear; lia| clear -B3 USED Z0; lia].
  + destruct HS2 as ((pew2 & pad2 & HC2 & PW2) & HB2). split; [| cbn [h_set_stack h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB;
       replace (h_used (h_set_stack h (ST_parse_error :: rest))) with (h_used h) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity);
       repeat split; try (clear -B1 B2 B3; lia); intros; congruence].
    exists pew2, pad2. split; [| exact PW2]. unfold hand_cells, hand_head_cells in HC2 |- *. cbn [h_set_stack h_bytesConsumed h_stack_size h_parseError].
    replace (h_used (h_set_stack h (ST_parse_error :: rest))) with (h_used h) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity). exact HC2.
  + exact BS2.
Qed.

(* [comment removed for export] *)
Lemma map_esc_tail58 : forall rav a0v a1v s5v,
  0 < cx_objectLevel cx -> buf_inv (h_decbuf h) ->
  (yb_state (h_decbuf h) = BS_ok ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h (ST_map_sep :: rest)) cx)) ->
  (yb_state (h_decbuf h) <> BS_ok ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E))
           (SR_done YS_alloc_failed (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_alloc_failed) cx)) ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x156e4 m rav t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros rav a0v a1v s5v OL DBI YOK YFAIL. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof DBR as ((DBC & DBZ & DBL & DBU) & DBD & DBF).
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG _].
  assert (IDB : In (mb_id (mh_decbuf mh), mb_addr (mh_decbuf mh), SIZEOF_BUF) (yblocks mh h ++ LK ++ p_REST E)).
  { unfold yblocks. cbn [app]. right. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. left. reflexivity. }
  pose proof (all_range_In _ _ RNG IDB) as RDB. unfold rblock_range, alloc_ceiling, SIZEOF_BUF in RDB. cbn [blk_addr blk_size fst snd] in RDB. clear RNG IDB.
  clear ERR TXT LXR. unfold pstate, pH, wz. unfold wz in FR.
  pose proof (rw_cells_bound _ _ _ _ DBC) as DBCB. rewrite buf_cells_size in DBCB.
  destruct (yb_state (h_decbuf h)) eqn:HSTT.
  - (* [comment removed for export] *)
    specialize (YOK eq_refl). clear YFAIL.
    pose proof (munch_refl [(p_lo E, bv_unsigned (p_sp E) + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof DBC as DBC'. unfold buf_cells in DBC'. rewrite HSTT in DBC'. cbn [buf_state_code] in DBC'. unfold wz in DBC'.
    rz_seg HKS HK0.
    zstep. zstep.
    call (YBE (mb_addr (mh_decbuf mh)) 0).
    all: lazymatch goal with |- rw_cells _ _ _ (C4 _ :: _) => exact DBC' | |- 0 <= 0 < _ => clear; lia | |- _ <> 0 => clear -RDB; lia | |- mem_inv _ _ => assumption | |- _ = wz _ => reflexivity | |- _ => idtac end.
    lazymatch goal with H : _ = wz 0 |- _ => rewrite H end. lazymatch goal with H : @eq mem ?x ?y |- _ => first [subst y| subst x] end. unfold wz.
    zstep. if_lit.
    zstep. zstep.
    call (YBD (mb_addr (mh_decbuf mh)) (mb_data (mh_decbuf mh)) (mh_addr (p_mh E) + 72) (p_lo E) (h_decbuf h)).
    all: lazymatch goal with |- RYajlRep.buf_struct _ _ _ _ _ _ => exact (conj DBC (conj DBZ (conj DBL DBU))) | |- yb_state _ = BS_ok => exact HSTT | |- _ <> 0 => clear -RDB; lia
        | |- stk _ _ _ _ => exact STK | |- _ <= bv_unsigned _ - _ => unfold RY_BUF_SMALL_STACK; clear -LO; lia | |- _ + SIZEOF_BUF <= _ => unfold SIZEOF_BUF; clear -RDB CEIL; lia
        | |- mem_inv _ _ => assumption | |- _ = wz _ => reflexivity | |- _ => idtac end.
    lazymatch goal with H : _ = wz (mb_data _) |- _ => rewrite H end. unfold wz.
    lazymatch goal with H : RYajlRep.buf_struct _ _ _ _ _ _ |- _ => destruct H as (BC2 & _); unfold buf_cells in BC2 end.
    zstep. zstep. zstep. zstep.
    call (YBL (mb_addr (mh_decbuf mh)) (mb_data (mh_decbuf mh)) (mh_addr (p_mh E) + 72) (p_lo E) (h_decbuf h)).
    all: lazymatch goal with |- RYajlRep.buf_struct _ _ _ _ _ _ => exact (conj BC2 (conj DBZ (conj DBL DBU))) | |- yb_state _ = BS_ok => exact HSTT | |- _ <> 0 => clear -RDB; lia
        | |- stk _ _ _ _ => assumption | |- _ <= bv_unsigned _ - _ => unfold RY_BUF_SMALL_STACK; clear -LO; lia | |- _ + SIZEOF_BUF <= _ => unfold SIZEOF_BUF; clear -RDB CEIL; lia
        | |- mem_inv _ _ => assumption | |- _ = wz _ => reflexivity | |- _ => idtac end.
    lazymatch goal with H : _ = wz (yb_used _) |- _ => rewrite H end. unfold wz.
    lazymatch goal with H : RYajlRep.buf_struct _ _ _ _ _ _ |- _ => destruct H as (BC3 & _); unfold buf_cells in BC3 end.
    zstep. apply evt_done.
    lazymatch goal with H : stk _ _ _ _ |- _ => rename H into STK3 end.
    pose proof (map_key_tail E) as MK. unfold pstate, pH, wz in MK.
    eapply MK; [exact OK| | exact HST| exact AG| exact OL| exact YOK].
    eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| assumption| | reflexivity| reflexivity| reflexivity| reflexivity| | | exact (conj CXC CXB2)| exists padw; exact FR| exact STK3].
    + constructor; [| constructor]. unfold ownA, pSP. cbn [fst snd]. clear -SPC CXB LO. unfold pSP, pCX in *. lia.
    + split; [| rewrite HSB; repeat split; try (clear -B1 B2 B3; lia); intros; congruence].
      exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
      cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. unfold wz, RY_CALLBACKS. rewrite EHA. exact HC.
    + unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC.
  - eapply map_esc_fail; [exact HSTT| | exact DBI| apply YFAIL; try rewrite HSTT; discriminate]. cbn. clear; lia.
  - eapply map_esc_fail; [exact HSTT| | exact DBI| apply YFAIL; try rewrite HSTT; discriminate]. cbn. clear; lia.
Qed.
End MAP2.

Section MAP3.
Variables (E : penv) (m : mem) (mo : Model) (s : PState) (LK : list block) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (st : ystate) (rest : list ystate).
Variables (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v s8v : word).
Hypothesis OK : pok E.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw.
Hypothesis HST : h_stack h = st :: rest.
Hypothesis MS4 : map_state st = true.
Hypothesis AG : again_cont E.
Hypothesis EX : exit_cont E.

(* [comment removed for export] *)
Lemma map_string_esc : forall rav a0v a1v s5v (i n : Z),
  0 < cx_objectLevel cx ->
  obw = wz (p_T E + i) -> olw = wz n -> 0 <= i -> 0 <= n -> i + n <= pLEN E -> sbody_ix (p_txt E) i (i + n) ->
  buf_inv (h_decbuf h) -> yb_state (h_decbuf h) = BS_ok ->
  (forall db', yleaf (ystring_decode (buf_cleared (h_decbuf h)) (zslice (p_txt E) i n) n) db' -> yb_state db' = BS_ok ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack (h_set_decbuf h db') (ST_map_sep :: rest)) cx)) ->
  (forall db', yleaf (ystring_decode (buf_cleared (h_decbuf h)) (zslice (p_txt E) i n) n) db' -> yb_state db' <> BS_ok ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E))
           (SR_done YS_alloc_failed (h_set_perr (h_set_stack (h_set_decbuf h db') (ST_parse_error :: rest)) PE_alloc_failed) cx)) ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x156bc m rav t0 t1 t2 a0v a1v a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros rav a0v a1v s5v i n OL EOB EOL I0 N0 IN SBX DBI DBOK YOK YFAIL. open_env HKB OK PM.
  pose proof YS as (CBS & _ & _). unfold callbacks_cells in CBS. cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ryc] in CBS.
  unfold RY_CALLBACKS, RY_CB_NULL, RY_CB_BOOLEAN, RY_CB_NUMBER, RY_CB_STRING, RY_CB_START_MAP, RY_CB_MAP_KEY, RY_CB_END_MAP, RY_CB_START_ARRAY, RY_CB_END_ARRAY, wz in CBS.
  unfold RY_CALLBACKS in HC. subst obw olw.
  pose proof DBR as ((DBC & DBZ & DBL & DBU) & DBD & DBF). pose proof (proj1 DBR) as DBS.
  pose proof (decbuf_facts _ HKB _ _ _ _ _ _ _ _ _ _ OK PM) as [RDB RDD]. rewrite EHA in RDB, RDD.
  clear ERR TXT LXR. unfold pstate, pH, wz. unfold wz in FR.
  pose proof (rw_cells_bound _ _ _ _ DBC) as DBCB. rewrite buf_cells_size in DBCB.
  pose proof (ypost_yleaf _ _ _ (ybuf_clear_post _ DBI DBOK) (ybuf_clear_leaf _ DBOK)) as [DBI' _].
  (* [comment removed for export] *)
  pose proof (YBC (mb_addr (mh_decbuf mh)) (mb_data (mh_decbuf mh)) (mh_addr (p_mh E) + 72) (p_lo E) (h_decbuf h)) as CLR'. unfold ybuf_clear_rpost in CLR'.
  pose proof (munch_refl ([(p_lo E, bv_unsigned (p_sp E)); (mb_addr (mh_decbuf mh) + 8, mb_addr (mh_decbuf mh) + 12)] ++ match yb_data (h_decbuf h) with Some _ => [(mb_data (mh_decbuf mh), mb_data (mh_decbuf mh) + 1)] | None => [] end) m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (OWN : Forall (ownD E mh h) ([(p_lo E, bv_unsigned (p_sp E)); (mb_addr (mh_decbuf mh) + 8, mb_addr (mh_decbuf mh) + 12)] ++ match yb_data (h_decbuf h) with Some _ => [(mb_data (mh_decbuf mh), mb_data (mh_decbuf mh) + 1)] | None => [] end)).
  { apply Forall_app. split.
    - constructor; [| constructor; [| constructor]]; unfold ownD, pSP; cbn [fst snd]; [clear; lia| clear; lia].
    - destruct (yb_data (h_decbuf h)) eqn:HD; [| constructor]. constructor; [| constructor]. unfold ownD. cbn [fst snd]. right; right.
      pose proof DBI as (_ & _ & _ & _ & DBX & _). specialize (DBX ltac:(rewrite HD; discriminate)). rewrite HD. split; [discriminate| clear -DBX DBU; lia]. }
  destruct (yb_data (h_decbuf h)) as [dp|] eqn:HDB; cbn [app] in CLR', MU, OWN; [specialize (RDD ltac:(discriminate))| clear RDD].
  all: rz_seg HKS HK0.
  all: zstep; zstep; if_lit; zstep; zstep; if_lit; zstep; zstep.
  all: fcall CLR'.   (* [comment removed for export] *)
  all: lazymatch goal with
       | |- RYajlRep.buf_struct _ _ _ _ _ _ => exact DBS
       | |- RYajlRep.buf_data _ _ _ _ => exact DBD
       | |- yb_state _ = BS_ok => exact DBOK
       | |- buf_inv _ => exact DBI
       | |- _ <> 0 => clear -RDB; lia
       | |- stk _ _ _ _ => exact STK
       | |- _ <= bv_unsigned _ - _ => unfold RY_BUF_SMALL_STACK; clear -LO; lia
       | |- _ + SIZEOF_BUF <= _ => unfold SIZEOF_BUF; clear -RDB CEIL; lia
       | |- _ <> None -> _ => intros HD; unfold SIZEOF_BUF; first [clear -RDD CEIL LO; lia| exfalso; apply HD; reflexivity]
       | |- mem_inv _ _ => assumption
       | |- _ = wz _ => reflexivity
       | |- _ => idtac end.
  all: zstep; zstep; zstep; rewrite ysx32_small by (clear -N0 I0 IN L26; unfold pLEN in *; lia); zstep; apply evt_done.
  all: lazymatch goal with H : RYajlRep.buf_struct _ _ _ _ _ _ |- _ => rename H into BS1 end;
       lazymatch goal with H : RYajlRep.buf_data _ _ _ _ |- _ => rename H into BD1 end;
       lazymatch goal with H : stk _ _ _ _ |- _ => rename H into STK1 end.
  all: pose proof (decode_call HK HKP HKB YSD E) as DC; unfold pH in DC; eapply (DC _ _ _ _ (h_set_decbuf h (buf_cleared (h_decbuf h))) mh); clear DC;
       [exact OK| | cbn [h_decbuf h_set_decbuf]; exact DBI'| reflexivity| exact I0| exact N0| exact IN| exact SBX|].
  1,3: eapply pmem_updD; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| assumption| exact OWN| reflexivity| reflexivity| | exact STK1];
       split; [unfold pH; exact BS1| split; [exact BD1| cbn; constructor]].
  all: cbn [h_decbuf h_set_decbuf]; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2 db' mbd' LK' YLD MBS PM2.
  all: replace (ret_pc (Z_to_bv 64 87780)) with (Z_to_bv 64 87780) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
  all: pose proof (map_esc_tail58 E) as MT; unfold pstate, pH, wz in MT; eapply MT; clear MT;
       [exact OK| exact PM2| exact HST| exact AG| exact EX| exact OL
       | exact (proj1 (ypost_yleaf _ _ _ (ystring_decode_post _ _ _ (sbody_ix_slice _ _ _ I0 SBX) N0 DBI' ltac:(cbn; clear -N0 I0 IN L26; unfold pLEN in *; lia)) YLD))
       | intros HOK; exact (YOK _ YLD HOK)
       | intros HNOK; exact (YFAIL _ YLD HNOK)].
Qed.
End MAP3.

Lemma map_state_target : forall st, map_state st = true -> state_target st = 0x154fc.
Proof. intros [] H; cbn in H; try discriminate; reflexivity. Qed.
Lemma map_state_lex : forall st, map_state st = true -> lex_state st = true.
Proof. intros [] H; cbn in H; try discriminate; reflexivity. Qed.

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
Proof.
  intros until r. intros HST MS YL YR. unfold yparse_step. rewrite (ybs_current_eq h _ _ HST). cbn [ybind].
  destruct st; try discriminate; (eapply yleaf_bind; [exact YL|]; cbn beta iota; exact YR).
Qed.



End S.
End RC__1.
