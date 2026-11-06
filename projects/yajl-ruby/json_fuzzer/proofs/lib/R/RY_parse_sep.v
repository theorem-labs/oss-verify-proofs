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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2 RY_parse_kit RY_parse_kitJ.
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

(* [comment removed for export] *)
Lemma step_sep : forall txt len h cx rest lx tok off ob n r,
  h_stack h = ST_map_sep :: rest ->
  yleaf (ylex_lex (h_lexer h) txt len (h_bytesConsumed h)) (lx, tok, off, ob, n) ->
  yleaf (let h := h_set_lex_off h lx off in
         match tok with
         | TK_colon => h1 <- ybs_set h ST_map_need_val ;; YRet (SR_again h1 cx)
         | TK_eof => YRet (SR_done YS_insufficient_data h cx)
         | TK_error => h1 <- ybs_set h ST_lexical_error ;; YRet (SR_again h1 cx)
         | _ => yparse_error h cx PE_expect_colon
         end) r ->
  yleaf (yparse_step jf_callbacks txt len h cx) r.
Proof.
  intros until r. intros HST YL YR. unfold yparse_step. rewrite (ybs_current_eq h _ _ HST). cbn [ybind].
  eapply yleaf_bind; [exact YL|]. cbn beta iota. exact YR.
Qed.

Section SEP.
(* [comment removed for export] *)
Variables (E : penv) (m : mem) (mo : Model) (s : PState) (LK : list block) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (rest : list ystate).
Variables (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v s8v : word).
Hypothesis OK : pok E.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw.
Hypothesis HST : h_stack h = ST_map_sep :: rest.
Hypothesis AG : again_cont E.
Hypothesis EX : exit_cont E.

Let at_switch (tok : ytok) := realizes_cfg acfg rsegs (mkCfg (pstate E 0x1561c m (wz 0x1561c) t0 t1 t2 (wz (tok_code tok)) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (wz 0) s6v s8v (wz 13)) mo) (p_K E).

Lemma sep_colon :
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h (ST_map_need_val :: rest)) cx) ->
  at_switch TK_colon.
Proof.
  intros YL. unfold at_switch. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  clear ERR TXT LXR DBR. unfold pstate, pH, wz. cbn [tok_code].
  rz_seg HKS HK0.
  zstep. zstep. if_lit.
  inline_addr USED Z0 B2 B3. zstep. step. apply evt_done.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + h_used h - 1) by (clear; lia).
  change (Z_to_bv 64 6) with (wz (state_code ST_map_need_val)).
  pose proof (J_setb HK HKS HKF HKB E) as JS. unfold pstate, pH in JS. eapply JS; [exact OK| exact PM| exact HST| exact YL| exact AG].
Qed.

Lemma sep_error :
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

Lemma sep_eof :
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

Lemma sep_default : forall tok,
  tok_code tok <> 1 -> tok_code tok <> 3 -> tok_code tok <> 4 ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_expect_colon) cx) ->
  at_switch tok.
Proof.
  intros tok N1 N3 N4 YL. unfold at_switch. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (tok_code_range tok) as TR.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  rz_seg HKS HK0.
  zstep. zstep. if_cases K1; zify_cond K1. { kill K1. }
  zstep. zstep. if_cases K2; zify_cond K2. { kill K2. }
  zstep. zstep. if_cases K3; zify_cond K3. { kill K3. }
  inline_addr USED Z0 B2 B3. zstep. zstep. step. apply evt_done.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + h_used h - 1) by (clear; lia).
  change (Z_to_bv 64 67081) with (wz (yc_perr ryc PE_expect_colon)).
  pose proof (J_perr HK HKS HKF HKB E) as JP. unfold pstate, pH in JP. eapply JP; [exact OK| exact PM| exact HST| exact YL| exact AG].
Qed.
End SEP.

(* [comment removed for export] *)
Lemma pass_sep : forall E m mo s h mh cx obw olw rest
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s [] h mh cx obw olw -> h = p_h E -> cx = p_cx E ->
  h_stack h = ST_map_sep :: rest ->
  again_cont E -> exit_cont E ->
  realizes_cfg acfg rsegs (mkCfg (yparse_head_state rav (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                           (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E) m
                           (pH E) (p_T E) (pLEN E) (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM EH ECX HST AG EX.
  eapply pass_lex; [exact HKS| exact HKP| exact HKB| exact YLX| exact OK| exact PM| exact EH| exact ECX| exact HST| reflexivity|].
  intros until LK'. intros YL LPOST HINV PM1. cbn [state_target Z.add Pos.add].
  pose proof (pmem_ranges _ HKB _ _ _ _ _ _ _ _ _ _ OK PM1) as (_ & _ & _ & _ & _ & _ & _ & B3).
  assert (HST1 : h_stack (h_set_lex_off h lx' off') = ST_map_sep :: rest) by exact HST.
  subst h cx.
  pose proof (step_sep (p_txt E) (pLEN E) (p_h E) (p_cx E) rest lx' tok off' ob n) as SL.
  destruct tok.
  all: first [ eapply sep_colon; [exact OK| exact PM1| exact HST1| exact AG|]
             | eapply sep_error; [exact OK| exact PM1| exact HST1| exact AG|]
             | eapply sep_eof; [exact OK| exact PM1| exact EX|]
             | eapply sep_default; [exact OK| exact PM1| exact HST1| exact AG| cbn; lia| cbn; lia| cbn; lia|] ].
  all: apply (SL _ HST YL); cbn beta iota.
  all: try (rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_set_lex_off]; exact (proj2 B3)); cbn [ybind]; apply yl_ret).
  all: try apply yl_ret.
  all: unfold yparse_error; rewrite (ybs_set_eq _ _ _ _ HST1) by (cbn [h_stack_size h_set_lex_off]; exact (proj2 B3)); cbn [ybind]; apply yl_ret.
Qed.

End S.
End RC__1.
