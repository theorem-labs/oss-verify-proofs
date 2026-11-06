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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2 RY_parse_kit RY_parse_kitJ RY_parse_kitD RY_parse_kitV RY_parse_gv RY_parse_val.
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

Ltac cbs_tac CBS HC :=
  unfold callbacks_cells in CBS; cbn [yc_cb_null yc_cb_boolean yc_cb_number yc_cb_string yc_cb_start_map yc_cb_map_key yc_cb_end_map yc_cb_start_array yc_cb_end_array ryc] in CBS;
  unfold RY_CALLBACKS, RY_CB_NULL, RY_CB_BOOLEAN, RY_CB_NUMBER, RY_CB_STRING, RY_CB_START_MAP, RY_CB_MAP_KEY, RY_CB_END_MAP, RY_CB_START_ARRAY, RY_CB_END_ARRAY, wz in CBS;
  unfold RY_CALLBACKS in HC.

Hypothesis YSD : ystring_decode_stmt HK.
Hypothesis YBC : ybuf_clear_stmt.
Hypothesis YBE : ybuf_err_stmt.
Hypothesis YBD : ybuf_data_stmt.
Hypothesis YBL : ybuf_len_stmt.
Hypothesis YCS : ycb_string_stmt.
Hypothesis YWR : ywrap_realloc_stmt HK.
Hypothesis YRP : yreset_parser_stmt.

Lemma buf_state_code_range' : forall st, 0 <= buf_state_code st <= 2.
Proof. intros []; cbn; lia. Qed.

Section ESC2.
Variables (E : penv) (m : mem) (mo : Model) (s : PState) (LK : list block) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (st : ystate) (rest : list ystate).
Variables (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v : word).
Hypothesis OK : pok E.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw.
Hypothesis HST : h_stack h = st :: rest.
Hypothesis VS : val_state st = true.
Hypothesis LXI : lex_inv (h_lexer h).
Hypothesis SZK : exists k, 0 < k /\ h_stack_size h = YAJL_BS_INC * k.
Hypothesis SZB : h_stack_size h <= pLEN E + 1 + YAJL_BS_INC.
Hypothesis AG : again_cont E.
Hypothesis EX : exit_cont E.

(* [comment removed for export] *)
Lemma esc_fail : forall rav a0v a1v a2v s5v bst,
  yb_state (h_decbuf h) = bst -> buf_state_code bst <> 0 -> buf_inv (h_decbuf h) ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E))
        (SR_done YS_alloc_failed (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_alloc_failed) cx) ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x1595c m rav t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v (wz 1) (wz 13)) mo) (p_K E).
Proof.
  intros rav a0v a1v a2v s5v bst HSTT BNZ DBI YL. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof DBR as ((DBC & DBZ & DBL & DBU) & DBD & DBF).
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG _].
  assert (IDB : In (mb_id (mh_decbuf mh), mb_addr (mh_decbuf mh), SIZEOF_BUF) (yblocks mh h ++ LK ++ p_REST E)).
  { unfold yblocks. cbn [app]. right. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. left. reflexivity. }
  pose proof (all_range_In _ _ RNG IDB) as RDB. unfold rblock_range, alloc_ceiling, SIZEOF_BUF in RDB. cbn [blk_addr blk_size fst snd] in RDB. clear RNG IDB.
  clear ERR TXT LXR. unfold pstate, pH, wz. unfold wz in FR.
  pose proof (buf_state_code_range' bst) as BSR'.
  unfold buf_cells in DBC. rewrite HSTT in DBC. unfold wz in DBC.
  pose proof (munch_refl [(mh_stack mh + h_used h - 1, mh_stack mh + h_used h)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  pose proof L1 as L1'. rewrite zbytes_length, stack_bytes_length, HST in L1'. cbn [length] in L1'.
  assert (LEN : length (zbytes (stack_bytes (h_stack h)) ++ junk) = Z.to_nat (h_stack_size h)) by (rewrite length_app; clear -L1 L2 B3; lia).
  rz_seg HKS HK0.
  zstep. zstep.
  call (YBE (mb_addr (mh_decbuf mh)) (buf_state_code bst)).
  all: lazymatch goal with |- rw_cells _ _ _ (C4 _ :: _) => exact DBC | |- 0 <= _ < _ => clear -BSR'; lia | |- _ <> 0 => clear -RDB; lia | |- mem_inv _ _ => assumption | |- _ = wz _ => reflexivity | |- _ => idtac end.
  lazymatch goal with H : _ = wz (buf_state_code bst) |- _ => rewrite H end. lazymatch goal with H : @eq mem ?x ?y |- _ => first [subst y| subst x] end. unfold wz.
  zstep. if_cases K; zify_cond K. 2:{ exfalso. revert K BNZ BSR'. clear. intros. rewrite ?unsigned_lit in K by lia. lia. }
  (* [comment removed for export] *)
  inline_addr USED Z0 B2 B3.
  zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at rsegs mx (mh_stack mh) _ (h_used h - 1) ARR ltac:(rewrite length_app; clear -L1 L2 B3 USED Z0; lia)) as SOK end.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + (h_used h - 1)) by (clear; lia).
  step.
  match type of ARR with Arr.u8arr _ ?mx _ _ =>
    pose proof (u8arr_write rsegs mx (mh_stack mh) _ (h_used h - 1) (Z_to_bv 8 2) ARR ltac:(rewrite length_app; clear -L1 L2 B3 USED Z0; lia)) as ARR' end.
  change (le1 (Z_to_bv 64 2)) with [Z_to_bv 8 2]. clear ARR. store_done.
  zstep. zstep. step. apply evt_done.
  lazymatch goal with H : stk _ _ _ _ |- _ => rename H into STK2 end.
  change (Z_to_bv 64 67531) with (wz (yc_perr ryc PE_alloc_failed)).
  pose proof (J_fail4 HK HKS HKF HKB E) as JF. unfold pstate, pH in JF. eapply JF; [exact OK| | exact YL| exact EX].
  eapply pmem_setb; [exact HKF| exact HKB| exact OK| exact PM| exact HST| exact MU| exact WM| assumption| exact ARR'| | | exact CXC| exists padw; exact FR| exact STK2].
  - rewrite L2. clear -B3 USED Z0 L1'. unfold zlength in *. lia.
  - exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
    cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. unfold wz. rewrite EHA. exact HC.
Qed.

(* [comment removed for export] *)
Lemma esc_tail_d0 : forall rav a0v a1v a2v s5v,
  buf_inv (h_decbuf h) ->
  (yb_state (h_decbuf h) = BS_ok ->
     forall r, yleaf (ygot_value h cx None) r -> yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) r) ->
  (yb_state (h_decbuf h) <> BS_ok ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E))
           (SR_done YS_alloc_failed (h_set_perr (h_set_stack h (ST_parse_error :: rest)) PE_alloc_failed) cx)) ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x1595c m rav t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v (wz 1) (wz 13)) mo) (p_K E).
Proof.
  intros rav a0v a1v a2v s5v DBI YOK YFAIL. open_env HKB OK PM.
  pose proof YS as (CBS & _ & _). cbs_tac CBS HC.
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
    pose proof (munch_refl [(p_lo E, bv_unsigned (p_sp E))] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof DBC as DBC'. unfold buf_cells in DBC'. rewrite HSTT in DBC'. cbn [buf_state_code] in DBC'. unfold wz in DBC'.
    rz_seg HKS HK0.
    zstep. zstep.
    call (YBE (mb_addr (mh_decbuf mh)) 0).
    all: lazymatch goal with |- rw_cells _ _ _ (C4 _ :: _) => exact DBC' | |- 0 <= 0 < _ => clear; lia | |- _ <> 0 => clear -RDB; lia | |- mem_inv _ _ => assumption | |- _ = wz _ => reflexivity | |- _ => idtac end.
    lazymatch goal with H : _ = wz 0 |- _ => rewrite H end. lazymatch goal with H : @eq mem ?x ?y |- _ => first [subst y| subst x] end. unfold wz.
    zstep. if_lit.
    zstep. zstep. zstep. zstep. zstep.
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
    zstep. zstep. zstep. zstep.
    call YCS. all: try assumption.
    lazymatch goal with H : _ = wz 1 |- _ => rewrite H end. lazymatch goal with H : @eq mem ?x ?y |- _ => first [subst y| subst x] end. unfold wz.
    zstep. if_lit. zstep. zstep. step. apply evt_done.
    lazymatch goal with H : stk _ _ _ _ |- _ => rename H into STK3 end.
    pose proof (J_gotval HK HKS HKP HKF HKB YWR YRP E) as JG. unfold pstate, pH, wz in JG.
    eapply JG with (push := None); [exact OK| | exact HST| exact VS| exact LXI| exact SZK| exact SZB| exact AG| reflexivity| intros stp X; discriminate| exact YOK].
    eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| assumption| | reflexivity| reflexivity| reflexivity| reflexivity| | | exact (conj CXC CXB2)| exists padw; exact FR| exact STK3].
    + constructor; [| constructor]. unfold ownA, pSP. cbn [fst snd]. clear -LO. unfold pSP in *. lia.
    + split; [| rewrite HSB; repeat split; try (clear -B1 B2 B3; lia); intros; congruence].
      exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
      cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. unfold wz, RY_CALLBACKS. rewrite EHA. exact HC.
    + unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC.
  - eapply esc_fail; [exact HSTT| | exact DBI| apply YFAIL; try rewrite HSTT; discriminate]. cbn. clear; lia.
  - eapply esc_fail; [exact HSTT| | exact DBI| apply YFAIL; try rewrite HSTT; discriminate]. cbn. clear; lia.
Qed.
End ESC2.

Section ESC3.
Variables (E : penv) (m : mem) (mo : Model) (s : PState) (LK : list block) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (st : ystate) (rest : list ystate).
Variables (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v : word).
Hypothesis OK : pok E.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw.
Hypothesis HST : h_stack h = st :: rest.
Hypothesis VS : val_state st = true.
Hypothesis LXI : lex_inv (h_lexer h).
Hypothesis SZK : exists k, 0 < k /\ h_stack_size h = YAJL_BS_INC * k.
Hypothesis SZB : h_stack_size h <= pLEN E + 1 + YAJL_BS_INC.
Hypothesis AG : again_cont E.
Hypothesis EX : exit_cont E.

(* [comment removed for export] *)
Lemma esc_main : forall rav a0v a1v a2v s5v s8v (i n : Z),
  obw = wz (p_T E + i) -> olw = wz n -> 0 <= i -> 0 <= n -> i + n <= pLEN E -> sbody_ix (p_txt E) i (i + n) ->
  buf_inv (h_decbuf h) -> yb_state (h_decbuf h) = BS_ok ->
  (forall db', yleaf (ystring_decode (buf_cleared (h_decbuf h)) (zslice (p_txt E) i n) n) db' -> yb_state db' = BS_ok ->
     forall r, yleaf (ygot_value (h_set_decbuf h db') cx None) r ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) r) ->
  (forall db', yleaf (ystring_decode (buf_cleared (h_decbuf h)) (zslice (p_txt E) i n) n) db' -> yb_state db' <> BS_ok ->
     yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E))
           (SR_done YS_alloc_failed (h_set_perr (h_set_stack (h_set_decbuf h db') (ST_parse_error :: rest)) PE_alloc_failed) cx)) ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x15930 m rav t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros rav a0v a1v a2v s5v s8v i n EOB EOL I0 N0 IN SBX DBI DBOK YOK YFAIL. open_env HKB OK PM.
  pose proof YS as (CBS & _ & _). cbs_tac CBS HC. subst obw olw.
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
  all: zstep; zstep; zstep; if_lit; zstep; zstep; if_lit; zstep; zstep.
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
  all: replace (ret_pc (Z_to_bv 64 88412)) with (Z_to_bv 64 88412) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
  all: pose proof (esc_tail_d0 E) as MT; unfold pstate, pH, wz in MT; eapply MT; clear MT;
       [exact OK| exact PM2| exact HST| exact VS| exact LXI| exact SZK| exact SZB| exact AG| exact EX
       | exact (proj1 (ypost_yleaf _ _ _ (ystring_decode_post _ _ _ (sbody_ix_slice _ _ _ I0 SBX) N0 DBI' ltac:(cbn; clear -N0 I0 IN L26; unfold pLEN in *; lia)) YLD))
       | intros HOK; exact (YOK _ YLD HOK)
       | intros HNOK; exact (YFAIL _ YLD HNOK)].
Qed.
End ESC3.

Theorem val_esc_proof : val_esc_stmt HK.
Proof.
  unfold val_esc_stmt. intros until n. intros OK PM HST VS LXI SZK SZB AG EX EOB EOL I0 N0 IN SBX DBI DBOK YOK YFAIL.
  eapply esc_main; eassumption.
Qed.

End S.
End RC__1.
