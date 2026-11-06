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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_rz UY_kit2 UY_parse_kit UY_parse_kitJ UY_parse_kitD UY_parse_kitV UY_parse_gv.
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
Definition cx_al (CX : Z) : Prop := 0 < CX /\ CX mod 4 = 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis YWR : ywrap_realloc_stmt HK.
Hypothesis YRP : yreset_parser_stmt.
Hypothesis YCN : ycb_null_stmt.
Hypothesis YCB : ycb_boolean_stmt.
Hypothesis YCNUM : ycb_number_stmt.
Hypothesis YCS : ycb_string_stmt.
Hypothesis YCSM : ycb_start_map_stmt.
Hypothesis YCSA : ycb_start_array_stmt.
Hypothesis YCEA : ycb_end_array_stmt.

Lemma pznth_nth_error : forall l i, 0 <= i < zlength l -> nth_error l (Z.to_nat i) = Some (znth l i).
Proof.
  intros l i Hi. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (nth_error l (Z.to_nat i)) as [c|] eqn:E.
  - rewrite (nth_error_nth _ _ _ E). reflexivity.
  - apply nth_error_None in E. unfold zlength in Hi. lia.
Qed.

Section VAL.
Variables (E : penv) (m : mem) (mo : Model) (s : PState) (LK : list block) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (st : ystate) (rest : list ystate).
Variables (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v s8v : word).
Hypothesis OK : pok E.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw.
Hypothesis HST : h_stack h = st :: rest.
Hypothesis VS : val_state st = true.
Hypothesis LXI : lex_inv (h_lexer h).
Hypothesis SZK : exists k, 0 < k /\ h_stack_size h = YAJL_BS_INC * k.
Hypothesis SZB : h_stack_size h <= pLEN E + 1 + YAJL_BS_INC.
Hypothesis LVA : cx_arrayLevel cx + 1 < 2^31.
Hypothesis LVO : cx_objectLevel cx + 1 < 2^31.
Hypothesis AG : again_cont E.
Hypothesis EX : exit_cont E.

Let at_pc (pc : Z) (rav a0v s5v : word) := realizes_cfg acfg usegs (mkCfg (pstate E pc m rav t0 t1 t2 a0v a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).

Ltac cbs_tac CBS HC :=
  unfold callbacks_cells in CBS; cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ryc] in CBS;
  unfold RY_CALLBACKS, RY_CB_NULL, RY_CB_BOOLEAN, RY_CB_NUMBER, RY_CB_STRING, RY_CB_START_MAP, RY_CB_MAP_KEY, RY_CB_END_MAP, RY_CB_START_ARRAY, RY_CB_END_ARRAY, wz in CBS;
  unfold RY_CALLBACKS in HC.

(* [comment removed for export] *)
Ltac cx_hook CX AL16 AL4 SPC ECX :=
  assert (UACB : cx_al CX) by (unfold cx_al; rewrite ECX; unfold pCX in AL4; clear -SPC AL4; split; [| exact AL4]; pose proof (bv_unsigned_in_range _ (p_sp E)); lia);
  clear AL16 AL4.

(* [comment removed for export] *)
Lemma val_unallowed : forall rav a0v a1v a2v a3v a4v s5v,
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_unallowed_token) cx) ->
  realizes_cfg acfg usegs (mkCfg (pstate E 0x15a70 m rav t0 t1 t2 a0v a1v a2v a3v a4v a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros rav a0v a1v a2v a3v a4v s5v YL. open_env HKB OK PM. clear AL16 AL4.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  pose proof (munch_refl [(mh_stack mh + h_used h - 1, mh_stack mh + h_used h)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  rz_seg HKS HK0.
  inline_addr USED Z0 B2 B3 R2. zstep.
  ubs_store h ARR ARR' L1 L2 B3 USED Z0.
  zstep. zstep. step. apply evt_done.
  change (Z_to_bv 64 66739) with (wz (yc_perr ryc PE_unallowed_token)).
  pose proof (J_perr HK HKS HKF HKB E) as JP. unfold pstate, pH in JP.
  eapply JP; [exact OK| exact PM| exact HST| exact MU| exact WM| exact MI| exact ARR'| exact L2| | exact CXC| exists padw; exact FR| exact STK| exact YL| exact AG].
  exists pew, pad. split; [| exact PW].
  unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. unfold wz. rewrite EHA. exact HC.
Qed.

(* [comment removed for export] *)
Lemma val_error : forall rav a0v s5v,
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h (ST_lexical_error :: rest)) cx) ->
  at_pc 0x1612c rav a0v s5v.
Proof.
  intros rav a0v s5v YL. unfold at_pc. open_env HKB OK PM. clear AL16 AL4.
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
Ltac to_gotval0 OK PM HST VS LXI SZK SZB AG EX YG :=
  lazymatch goal with H : _ = wz 1 |- _ => rewrite H end; lazymatch goal with H : @eq mem ?x ?y |- _ => first [subst y| subst x] end; unfold wz;
  zstep; if_lit; apply evt_done;
  let JG := fresh "JG" in
  pose proof (J_gotval0 HK HKS HKP HKF HKB YWR YRP E) as JG; unfold pstate, pH, wz in JG;
  eapply JG; [exact OK| exact PM| exact HST| exact VS| exact LXI| exact SZK| exact SZB| exact AG| exact YG].

Lemma val_null : forall rav a0v s5v,
  (forall r, yleaf (ygot_value h cx None) r -> yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) r) ->
  at_pc 0x15f64 rav a0v s5v.
Proof.
  intros rav a0v s5v YG. unfold at_pc. open_env HKB OK PM. clear AL16 AL4.
  pose proof YS as (CBS & _ & _). cbs_tac CBS HC.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
  rz_seg HKS HK0.
  zstep. zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep.
  call YCN. all: try assumption. all: try exact I.
  to_gotval0 OK PM HST VS LXI SZK SZB AG EX YG.
Qed.

Lemma val_string : forall rav a0v s5v,
  (forall r, yleaf (ygot_value h cx None) r -> yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) r) ->
  at_pc 0x16140 rav a0v s5v.
Proof.
  intros rav a0v s5v YG. unfold at_pc. open_env HKB OK PM. clear AL16 AL4.
  pose proof YS as (CBS & _ & _). cbs_tac CBS HC.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz. unfold wz in FR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
  rz_seg HKS HK0.
  zstep. zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep. zstep. zstep.
  call YCS. all: try assumption. all: try exact I.
  to_gotval0 OK PM HST VS LXI SZK SZB AG EX YG.
Qed.

Lemma val_number : forall rav a0v s5v (n : Z) (pc : Z),
  (pc = 0x15f30 \/ pc = 0x15efc) ->
  olw = wz n -> 0 < n < 2^31 ->
  (forall r, yleaf (ygot_value h cx None) r -> yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) r) ->
  at_pc pc rav a0v s5v.
Proof.
  intros rav a0v s5v n pc PC EOL NB YG. unfold at_pc. open_env HKB OK PM. clear AL16 AL4.
  pose proof YS as (CBS & _ & _). cbs_tac CBS HC.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz. subst olw. unfold wz in FR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
  rz_seg HKS HK0.
  destruct PC as [-> | ->];
    (zstep; zstep; zstep; if_lit; zstep; zstep; if_lit; zstep; zstep; if_lit; zstep; zstep; zstep; rewrite ysx32_small by (clear -NB; lia); zstep;
     call (YCNUM n); try assumption; try exact I; try reflexivity; try (clear -NB; lia);
     to_gotval0 OK PM HST VS LXI SZK SZB AG EX YG).
Qed.

(* [comment removed for export] *)
Lemma val_bool : forall rav a0v s5v (i : Z),
  obw = wz (p_T E + i) -> 0 <= i < pLEN E ->
  (forall r, yleaf (ygot_value h cx None) r -> yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) r) ->
  at_pc 0x15fbc rav a0v s5v.
Proof.
  intros rav a0v s5v i EOB IB YG. unfold at_pc. open_env HKB OK PM. clear AL16 AL4.
  pose proof YS as (CBS & _ & _). cbs_tac CBS HC.
  pose proof TXT as (TXB & TXF & T0 & T62).
  pose proof (u8ro_read usegs m (p_T E) (zbytes (p_txt E)) i (Z_to_bv 8 (znth (p_txt E) i)) _ TXB
                ltac:(unfold zbytes; rewrite nth_error_map, (pznth_nth_error _ _ ltac:(unfold pLEN in IB; exact IB)); reflexivity) ltac:(clear -IB; lia) eq_refl) as RKT.
  change (wa (p_T E + i)) with (Z_to_bv 64 (p_T E + i)) in RKT.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz. subst obw. unfold wz in FR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
  rz_seg HKS HK0.
  zstep. zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep. if_lit.
  (* [comment removed for export] *)
  zstep. zstep. if_cases KN; zify_cond KN. { clear -KN T0 IB T62. unfold pLEN in *. kill KN. }
  step. clear RKT. zstep. zstep. zstep. zstep.
  call YCB. all: try assumption. all: try exact I.
  to_gotval0 OK PM HST VS LXI SZK SZB AG EX YG.
Qed.

(* [comment removed for export] *)
Lemma val_start_map : forall rav a0v s5v,
  (forall r, yleaf (ygot_value h (mkCtx (cx_arrayLevel cx) (cx_objectLevel cx + 1)) (Some ST_map_start)) r ->
             yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) r) ->
  at_pc 0x15ffc rav a0v s5v.
Proof.
  intros rav a0v s5v YG. unfold at_pc. open_env HKB OK PM. cx_hook (mh_ctx mh) AL16 AL4 SPC ECX.
  pose proof YS as (CBS & _ & _). cbs_tac CBS HC.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  pose proof (munch_refl [(mh_ctx (p_mh E) + 4, mh_ctx (p_mh E) + 8)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  rz_seg HKS HK0.
  zstep. zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep.
  rewrite <- ECX in CXC, MU.
  call (YCSM (mh_ctx mh) cx).
  all: lazymatch goal with |- UA_ycb_start_map _ _ _ => exact UACB | |- RYajlRep.ctx_rep _ _ _ _ => exact (conj CXC CXB2) | |- _ + 1 < _ => exact LVO | |- mem_inv _ _ => assumption | |- _ = wz _ => reflexivity | |- _ => idtac end.
  lazymatch goal with H : _ = wz 1 |- _ => rewrite H end. unfold wz.
  zstep. if_lit. zstep. step. apply evt_done.
  lazymatch goal with H : RYajlRep.ctx_rep _ _ _ _ |- _ => destruct H as [CXC2 CXB3] end.
  pose proof (J_gotval HK HKS HKP HKF HKB YWR YRP E) as JG. unfold pstate, pH, wz in JG.
  change (Z_to_bv 64 4) with (Z_to_bv 64 (state_code ST_map_start)).
  eapply JG with (push := Some ST_map_start); [exact OK| | exact HST| exact VS| exact LXI| exact SZK| exact SZB| exact AG| reflexivity| intros stp X; injection X as <-; reflexivity| exact YG].
  eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| assumption| | reflexivity| reflexivity| reflexivity| reflexivity| | | unfold pCX; rewrite <- ECX; exact (conj CXC2 CXB3)| exists padw; exact FR| exact STK].
  2:{ destruct HS as [_ HB]. split; [| exact HB]. exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
      cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. unfold wz, RY_CALLBACKS. rewrite EHA. exact HC. }
  - constructor; [| constructor]. unfold ownA, pCX. cbn [fst snd]. clear -ECX. lia.
  - unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC.
Qed.

Lemma val_start_array : forall rav a0v s5v,
  (forall r, yleaf (ygot_value h (mkCtx (cx_arrayLevel cx + 1) (cx_objectLevel cx)) (Some ST_array_start)) r ->
             yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) r) ->
  at_pc 0x15f90 rav a0v s5v.
Proof.
  intros rav a0v s5v YG. unfold at_pc. open_env HKB OK PM. cx_hook (mh_ctx mh) AL16 AL4 SPC ECX.
  pose proof YS as (CBS & _ & _). cbs_tac CBS HC.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  pose proof (munch_refl [(mh_ctx (p_mh E), mh_ctx (p_mh E) + 4)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  rz_seg HKS HK0.
  zstep. zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep.
  rewrite <- ECX in CXC, MU.
  call (YCSA (mh_ctx mh) cx).
  all: lazymatch goal with |- UA_ycb_start_array _ _ _ => exact UACB | |- RYajlRep.ctx_rep _ _ _ _ => exact (conj CXC CXB2) | |- _ + 1 < _ => exact LVA | |- mem_inv _ _ => assumption | |- _ = wz _ => reflexivity | |- _ => idtac end.
  lazymatch goal with H : _ = wz 1 |- _ => rewrite H end. unfold wz.
  zstep. if_lit. zstep. step. apply evt_done.
  lazymatch goal with H : RYajlRep.ctx_rep _ _ _ _ |- _ => destruct H as [CXC2 CXB3] end.
  pose proof (J_gotval HK HKS HKP HKF HKB YWR YRP E) as JG. unfold pstate, pH, wz in JG.
  change (Z_to_bv 64 9) with (Z_to_bv 64 (state_code ST_array_start)).
  eapply JG with (push := Some ST_array_start); [exact OK| | exact HST| exact VS| exact LXI| exact SZK| exact SZB| exact AG| reflexivity| intros stp X; injection X as <-; reflexivity| exact YG].
  eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| assumption| | reflexivity| reflexivity| reflexivity| reflexivity| | | unfold pCX; rewrite <- ECX; exact (conj CXC2 CXB3)| exists padw; exact FR| exact STK].
  2:{ destruct HS as [_ HB]. split; [| exact HB]. exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
      cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. unfold wz, RY_CALLBACKS. rewrite EHA. exact HC. }
  - constructor; [| constructor]. unfold ownA, pCX. cbn [fst snd]. clear -ECX. lia.
  - unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC.
Qed.


(* [comment removed for export] *)
Lemma val_rbrace : forall rav a0v s5v,
  (st = ST_array_start -> 0 < cx_arrayLevel cx /\
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h rest) (mkCtx (cx_arrayLevel cx - 1) (cx_objectLevel cx)))) ->
  (st <> ST_array_start ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_unallowed_token) cx)) ->
  at_pc 0x160bc rav a0v s5v.
Proof.
  intros rav a0v s5v YST YNK. unfold at_pc. open_env HKB OK PM. cx_hook (mh_ctx mh) AL16 AL4 SPC ECX.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof YS as (CBS & _ & _). cbs_tac CBS HC.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2).
  pose proof (u8arr_read usegs m (mh_stack mh) _ (h_used h - 1) (Z_to_bv 8 (state_code st)) _ ARR
                ltac:(rewrite HST; replace (Z.to_nat (h_used h - 1)) with (Z.to_nat (zlength rest)) by (clear -USED; lia); apply stack_top_byte) ltac:(clear -USED Z0; lia) eq_refl) as RK.
  pose proof (munch_refl [(mh_ctx (p_mh E), mh_ctx (p_mh E) + 4)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  rz_seg HKS HK0.
  zstep. rewrite ysx32_small by (clear -USED Z0 B2 B3; lia).
  zstep. if_cases K; zify_cond K. { kill K. }
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. rewrite (land_M32_small (h_used h + -1)) by (clear -USED Z0 B3 B2; lia). zstep.
  uguards R2 B3 USED Z0.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + (h_used h - 1)) by (clear; lia).
  change (wa (mh_stack mh + (h_used h - 1))) with (Z_to_bv 64 (mh_stack mh + (h_used h - 1))) in RK.
  step. clear RK. change (Z_to_bv 8 (state_code st)) with (b8 (state_code st)). rewrite (zxb_b8 (state_code st)) by (clear; destruct st; cbn; lia).
  zstep. zstep. if_cases K9; zify_cond K9; unfold wz in K9; rewrite ?unsigned_lit in K9 by (clear; pose proof (state_code_range st); lia).
  - (* [comment removed for export] *)
    assert (NE : st <> ST_array_start) by (intros ->; cbn in K9; clear -K9; lia).
    apply evt_done. apply val_unallowed. exact (YNK NE).
  - (* [comment removed for export] *)
    assert (E9 : st = ST_array_start) by (clear -K9 VS; destruct st; cbn in K9, VS; first [reflexivity| discriminate| lia]).
    destruct (YST E9) as [AL YL].
    zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep. if_lit. zstep. zstep.
    rewrite <- ECX in CXC, MU.
    call (YCEA (mh_ctx mh) cx).
    all: lazymatch goal with |- UA_ycb_end_array _ _ _ => exact UACB | |- RYajlRep.ctx_rep _ _ _ _ => exact (conj CXC CXB2) | |- 0 < _ => exact AL | |- mem_inv _ _ => assumption | |- _ = wz _ => reflexivity | |- _ => idtac end.
    lazymatch goal with H : _ = wz 1 |- _ => rewrite H end. unfold wz.
    zstep. rewrite ysx32_small by (clear -USED Z0 B2 B3; lia).
    zstep. if_lit.
    zstep. step. apply evt_done.
    lazymatch goal with H : RYajlRep.ctx_rep _ _ _ _ |- _ => destruct H as [CXC2 CXB3] end.
    replace (h_used h + -1) with (h_used h - 1) by (clear; lia).
    pose proof (J_pop54 HK HKS HKF HKB E) as JP. unfold pstate, pH, wz in JP. eapply JP; [exact OK| | exact HST| exact YL| exact AG].
    eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| assumption| | reflexivity| reflexivity| reflexivity| reflexivity| | | unfold pCX; rewrite <- ECX; exact (conj CXC2 CXB3)| exists padw; exact FR| exact STK].
  2:{ destruct HS as [_ HB]. split; [| exact HB]. exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
      cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. unfold wz, RY_CALLBACKS. rewrite EHA. exact HC. }
    + constructor; [| constructor]. unfold ownA, pCX. cbn [fst snd]. clear -ECX. lia.
    + unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC.
Qed.
End VAL.

(* [comment removed for export] *)
Definition val_esc_stmt : Prop :=
  forall (E : penv) (m : mem) (mo : Model) (s : PState) (LK : list block) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (st : ystate) (rest : list ystate)
         (rav t0 t1 t2 a0v a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word) (i n : Z),
  pok E -> pmem E m mo s LK h mh cx obw olw -> h_stack h = st :: rest -> val_state st = true ->
  lex_inv (h_lexer h) -> (exists k, 0 < k /\ h_stack_size h = YAJL_BS_INC * k) -> h_stack_size h <= pLEN E + 1 + YAJL_BS_INC ->
  again_cont E -> exit_cont E ->
  obw = wz (p_T E + i) -> olw = wz n -> 0 <= i -> 0 <= n -> i + n <= pLEN E -> sbody_ix (p_txt E) i (i + n) ->
  buf_inv (h_decbuf h) -> yb_state (h_decbuf h) = BS_ok ->
  (forall db', yleaf (ystring_decode (buf_cleared (h_decbuf h)) (zslice (p_txt E) i n) n) db' -> yb_state db' = BS_ok ->
     forall r, yleaf (ygot_value (h_set_decbuf h db') cx None) r ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) r) ->
  (forall db', yleaf (ystring_decode (buf_cleared (h_decbuf h)) (zslice (p_txt E) i n) n) db' -> yb_state db' <> BS_ok ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E))
           (SR_done YS_alloc_failed (h_set_perr (h_set_stack (h_set_decbuf h db') (ST_parse_error :: rest)) PE_alloc_failed) cx)) ->
  realizes_cfg acfg usegs (mkCfg (pstate E 0x1602c m rav t0 t1 t2 a0v a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).

End S.
End RC__1.
