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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2 RY_parse_kit RY_parse_kitJ RY_parse_kitD RY_parse_kitV.
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
Hypothesis YWR : ywrap_realloc_stmt HK.
Hypothesis YRP : yreset_parser_stmt.

Definition val_state (st : ystate) : bool :=
  match st with ST_start | ST_map_need_val | ST_array_need_val | ST_array_start => true | _ => false end.


(* [comment removed for export] *)
Lemma push_store : forall E m mo s LK h mh cx obw olw stp
    (rav t0 t1 t2 a2v a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s8v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw -> h_used h < h_stack_size h ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h (stp :: h_stack h)) cx) ->
  again_cont E ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x15d64 m rav t0 t1 t2 (wz (mh_stack mh)) (wz (h_used h)) a2v a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v (wz (state_code stp)) s8v (wz 13)) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM UL YL AG. open_env HKB OK PM.
  pose proof (state_code_range stp) as CR.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  pose proof (munch_refl [(mh_addr (p_mh E) + 60, mh_addr (p_mh E) + 64); (mh_stack mh + h_used h, mh_stack mh + h_used h + 1)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  assert (LEN : length (zbytes (stack_bytes (h_stack h)) ++ junk) = Z.to_nat (h_stack_size h)) by (rewrite length_app; clear -L1 L2 B3; lia).
  rz_seg HKS HK0.
  zstep. zstep. zstep. zstep. rewrite (land_M32_small (h_used h)) by (clear -B3 B2; lia). zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at rsegs mx (mh_stack mh) _ (h_used h) ARR ltac:(rewrite LEN; clear -B3 UL; lia)) as SOK end.
  step.
  match type of ARR with Arr.u8arr _ ?mx _ _ =>
    pose proof (u8arr_write rsegs mx (mh_stack mh) _ (h_used h) (Z_to_bv 8 (state_code stp)) ARR ltac:(rewrite LEN; clear -B3 UL; lia)) as ARR' end.
  rewrite le1_wz by (clear -CR; lia). clear ARR. store_done.
  apply evt_done.
  pose proof (J_back HK HKS E) as JB. unfold pstate, pH in JB.
  replace (h_used h + 1) with (h_used (h_set_stack h (stp :: h_stack h))) by (unfold h_used; cbn [h_stack h_set_stack]; unfold zlength; cbn [length]; clear; lia).
  eapply JB; [exact OK| | exact YL| exact AG].
  rewrite <- EHA in MU.
  eapply pmem_push; [exact HKF| exact HKB| exact OK| exact PM| exact UL| exact MU| exact WM| exact MI| | exact ARR'| exact L2| exact CXC| exists padw; exact FR| exact STK].
  exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
  cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app h_set_stack h_bytesConsumed h_stack_size h_parseError]. unfold wz. rewrite EHA.
  replace (h_used (h_set_stack h (stp :: h_stack h))) with (h_used h + 1) by (unfold h_used; cbn [h_stack h_set_stack]; unfold zlength; cbn [length]; clear; lia). exact HC.
Qed.

Section PUSH.
Variables (E : penv) (m : mem) (mo : Model) (s : PState) (LK : list block) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (stp : ystate).
Variables (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s8v : word).
Hypothesis OK : pok E.
Hypothesis PM : pmem E m mo s LK h mh cx obw olw.
Hypothesis SZK : exists k, 0 < k /\ h_stack_size h = YAJL_BS_INC * k.
Hypothesis SZB : h_stack_size h <= pLEN E + 1 + YAJL_BS_INC.
Hypothesis AG : again_cont E.
Hypothesis EX : exit_cont E.
(* [comment removed for export] *)
Hypothesis YP : forall ok h2, yleaf (ybs_push h stp) (ok, h2) ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (if ok then SR_again h2 cx else SR_done YS_alloc_failed h2 cx).

(* [comment removed for export] *)
Lemma push_norealloc : forall rav a0v a2v,
  h_used h < h_stack_size h ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x15d60 m rav t0 t1 t2 a0v (wz (h_used h)) a2v a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v (wz (state_code stp)) s8v (wz 13)) mo) (p_K E).
Proof.
  intros rav a0v a2v UL. open_env HKB OK PM.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  rz_seg HKS HK0. zstep. apply evt_done.
  pose proof (push_store E) as PS. unfold pstate, pH, wz in PS.
  eapply PS; [exact OK| exact PM| exact UL| | exact AG].
  apply (YP true). unfold ybs_push. replace (h_stack_size h - h_used h =? 0) with false by (symmetry; apply Z.eqb_neq; clear -UL; lia). apply yl_ret.
Qed.

(* [comment removed for export] *)
Lemma push_realloc : forall rav a0v a1v,
  h_used h = h_stack_size h ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x15d34 m rav t0 t1 t2 a0v a1v (wz (h_stack_size h)) a3 a4 a5 a6 a7 t3 t4 t5 t6 (wz 4) (wz (state_code stp)) s8v (wz 13)) mo) (p_K E).
Proof.
  intros rav a0v a1v FULL. open_env HKB OK PM.
  pose proof (state_code_range stp) as CR.
  destruct SZK as (k & K1 & SZ). unfold YAJL_BS_INC in SZ, SZB.
  unfold pstate, pH, wz. destruct ERR as [errv ERR]. rewrite (ry_errno_lit _ TP) in ERR. unfold RERRNO in ERR.
  unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, RY_CALLBACKS in HC.
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  (* [comment removed for export] *)
  rewrite (yblocks_mid mh h LK (p_REST E) SB1) in HK0, RNG, SEP.
  set (REST0 := (mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: mid_blocks mh h ++ LK ++ p_REST E).
  assert (PERM : Permutation.Permutation ((mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: mid_blocks mh h ++ (mh_sid mh, mh_stack mh, h_stack_size h) :: LK ++ p_REST E)
                                          ((mh_sid mh, mh_stack mh, h_stack_size h) :: REST0)).
  { unfold REST0. symmetry. apply (Permutation.Permutation_middle ((mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: mid_blocks mh h) (LK ++ p_REST E)). }
  pose proof (HKP _ _ _ _ _ HK0 PERM) as HK1. clear HK0.
  pose proof (munch_refl [(mh_addr (p_mh E) + 56, mh_addr (p_mh E) + 60)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2).
  rz_seg HKS HK1.
  zstep. zstep. zstep. zstep. zstep. rewrite (swrap32_small (h_stack_size h + 128)) by (clear -B2 SZB L26; unfold pLEN in *; lia).
  zstep. zstep.
  apply evt_done.
  (* [comment removed for export] *)
  assert (IHD : In (mh_id mh, mh_addr mh, SIZEOF_HANDLE) ((mh_sid mh, mh_stack mh, h_stack_size h) :: REST0)) by (right; left; reflexivity).
  destruct (yown_writes HK HKF _ _ _ _ _ _ (p_B E) HK1 AX MU WM) as [HK2 AX2].
  { constructor; [| constructor]. right; right. eexists. split; [exact IHD|]. cbn. unfold SIZEOF_HANDLE. clear -EHA. rewrite EHA. lia. }
  { constructor; [| constructor]. cbn. unfold RAUXV_CELL. clear -R1 CXB SPC CEIL LO. unfold pSP, pCX in *. lia. }
  pose proof (ystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; clear -R1; lia| constructor])) as YS2.
  pose proof (HK_nodup HK HKB _ _ _ _ HK2) as ND2.
  assert (LOLD : Z.of_nat (length (zbytes (stack_bytes (h_stack h)) ++ junk)) = h_stack_size h) by (rewrite length_app; clear -L1 L2 B3; lia).
  lazymatch goal with H : stk _ ?mx _ _ |- _ => rename H into STK1; rename mx into m1 end.
  lazymatch goal with H : mem_inv _ m1 |- _ => rename H into MI1 end.
  pose proof YWR as YWR'. unfold ywrap_realloc_stmt in YWR'.
  eapply YWR' with (LB := (mh_sid mh, mh_stack mh, h_stack_size h) :: REST0) (p := mh_sid mh) (A := mh_stack mh) (sz := h_stack_size h) (n := h_stack_size h + 128) (lo := p_lo E) (B := p_B E) (old := zbytes (stack_bytes (h_stack h)) ++ junk) (errv := errv);
    [exact K0| exact HK2| left; reflexivity| exact (proj1 ARR)| exact LOLD| exact AX2| clear -SPC CXB; unfold pSP, pCX in *; lia| exact STK1
    | unfold alloc_ceiling; clear -CEIL; lia| unfold RY_WRAP_STACK; clear -LO; unfold pSP in *; lia
    | rewrite (ry_errno_lit _ TP); exact ERR| exact MI1| exact TP| reflexivity| reflexivity| unfold NUSERc; clear -B2 SZB L26; unfold pLEN in *; lia
    | unfold REST0, mid_blocks; clear -PYR LK0; yroom_solve|].
  clear YWR'.
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2 errv2 p' A' MI2 STK2 ERR2 AX3 EA0 BR' HK3 HP3 NEWC'.
  replace (ret_pc (Z_to_bv 64 89424)) with (Z_to_bv 64 89424) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
  rewrite (ry_errno_lit _ TP) in ERR2. unfold RERRNO in ERR2.
  (* [comment removed for export] *)
  cbn [all_sep] in SEP. destruct SEP as [SEPH SEPT].
  assert (OUTHg : forall lo hi y a, mh_addr (p_mh E) <= lo -> hi <= mh_addr (p_mh E) + 104 ->
                 In y (mid_blocks mh h) \/ In y (LK ++ p_REST E) -> blk_addr y <= a < blk_addr y + blk_size y -> outside [(lo, hi)] a).
  { intros lo hi y a Hlo Hhi Hy Ha. pose proof (sep_from_In _ _ _ SEPH ltac:(apply in_or_app; destruct Hy as [Hy|Hy]; [left; exact Hy| right; right; exact Hy])) as X.
    unfold bsep, SIZEOF_HANDLE in X. cbn [blk_addr blk_size fst snd] in X. rewrite EHA in X. cbn. clear -X Ha Hlo Hhi. lia. }
  pose proof (fun y a => OUTHg (mh_addr (p_mh E) + 48) (mh_addr (p_mh E) + 56) y a ltac:(clear; lia) ltac:(clear; lia)) as OUTH. cbv beta in OUTH.
  assert (TXT1 : text_at m1 (p_T E) (p_txt E)).
  { eapply text_at_agree; [apply (munch_agree _ _ _ MU WM)| exact TXT|]. intros a Ha. destruct TB as [(bt & HIN & HB)|Z0]; [| unfold pLEN in Z0; clear -Ha Z0; lia].
    apply (OUTHg _ _ bt a); [clear; lia| clear; lia| right; apply in_or_app; right; exact HIN| unfold pLEN in HB; clear -Ha HB; lia]. }
  clear TXT. rename TXT1 into TXT.
  assert (LXR1 : lexer_rep m1 (mh_lexer mh) (h_lexer h) (mh_lexbuf mh) (mh_addr (p_mh E) + 72)).
  { eapply lexer_rep_agree; [apply (munch_agree _ _ _ MU WM)| exact LXR| | |];
      [intros a Ha| intros a Ha| intros HD a Ha]; (eapply (OUTHg (mh_addr (p_mh E) + 56) (mh_addr (p_mh E) + 60) _ a ltac:(clear; lia) ltac:(clear; lia)); [left|]);
      [left; reflexivity| cbn; exact Ha| right; left; reflexivity| cbn; exact Ha
      | unfold mid_blocks, lexer_blocks, buf_blocks; right; destruct (yb_data (lx_buf (h_lexer h))); [| congruence]; right; left; reflexivity| cbn; exact Ha]. }
  assert (DBR1 : buf_rep m1 (mh_decbuf mh) (h_decbuf h) (mh_addr (p_mh E) + 72)).
  { eapply buf_rep_agree; [apply (munch_agree _ _ _ MU WM)| exact DBR| |];
      [intros a Ha| intros HD a Ha]; (eapply (OUTHg (mh_addr (p_mh E) + 56) (mh_addr (p_mh E) + 60) _ a ltac:(clear; lia) ltac:(clear; lia)));
      [left; unfold mid_blocks; apply in_or_app; right; left; reflexivity| cbn; exact Ha
      | left; unfold mid_blocks, buf_blocks; apply in_or_app; right; destruct (yb_data (h_decbuf h)); [| congruence]; right; left; reflexivity| cbn; exact Ha]. }
  clear LXR DBR. rename LXR1 into LXR. rename DBR1 into DBR.
  assert (PRES1 : ry_pres (p_REST E) (bv_unsigned (p_sp E) + 144) [(mh_ctx (p_mh E), mh_ctx (p_mh E) + 8)] (p_m0 E) m1).
  { eapply ry_pres_trans; [exact PRES|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc _. cbn. split; [| exact I]. destruct Hc as [Hc|[[Hc _]|(b & Hb & Hr)]]; [unfold pSP in Hc; clear -Hc R1 CEIL LO; lia| clear -Hc R1; lia|].
    pose proof (sep_from_In _ _ _ SEPH ltac:(apply in_or_app; right; right; apply in_or_app; right; exact Hb)) as X.
    unfold bsep, SIZEOF_HANDLE in X. cbn [blk_addr blk_size fst snd] in X. clear -X Hr EHA. rewrite <- EHA. lia. }
  assert (IMID : forall y, In y (mid_blocks mh h) -> In y REST0) by (intros y Hy; unfold REST0; right; apply in_or_app; left; exact Hy).
  assert (IRR : forall y, In y (p_REST E) -> In y REST0) by (intros y Hy; unfold REST0; right; apply in_or_app; right; apply in_or_app; right; exact Hy).
  (* [comment removed for export] *)
    destruct NEWC' as (junk2 & NEWC). subst a0'. unfold wz.
    rewrite (lb_remove_head _ _ ND2) in HK3, HP3.
    unfold rblock_range, alloc_ceiling in BR'.
    assert (JN : junk = []) by (destruct junk; [reflexivity| cbn [length] in L2; clear -L2 FULL; lia]). subst junk.
    rewrite app_nil_r in NEWC. rewrite Z.min_r in NEWC by (clear -B2; lia).
    rewrite firstn_all2 in NEWC by (rewrite zbytes_length, stack_bytes_length; unfold h_used, zlength in FULL; clear -FULL; lia).
    replace (h_stack_size h + 128 - h_stack_size h) with 128 in NEWC by (clear; lia).
    pose proof (rw_cells_bound _ _ _ _ NEWC) as NEWB. cbn [cells_size csize Nat.add] in NEWB.
    destruct (HK_blocks HK HKB _ _ _ _ HK3) as [RNG3 SEP3]. cbn [all_sep] in SEP3. destruct SEP3 as [SEPN _].
    pose proof (sep_from_In _ _ _ SEPN ltac:(left; reflexivity)) as NH. unfold bsep, SIZEOF_HANDLE in NH. cbn [blk_addr blk_size fst snd] in NH. rewrite EHA in NH.
    (* [comment removed for export] *)
    pose proof (ypres_block _ _ _ _ _ _ HP3 HC ltac:(rewrite <- EHA; eexists; split; [left; reflexivity| cbn; unfold SIZEOF_HANDLE; clear; lia])) as HC2. clear HC.
    pose proof (ypres_frame _ _ _ _ _ _ HP3 CXC ltac:(clear -SPC; unfold pSP, pCX in *; lia)) as CXC2. clear CXC.
    pose proof (ypres_frame _ _ _ _ _ _ HP3 FR ltac:(clear; lia)) as FR2. clear FR.
    pose proof (ypres_text _ _ _ _ _ _ HP3 TXT ltac:(destruct TB as [(bt & HIN & HB)|Z0]; [left; exists bt; split; [apply IRR; exact HIN| exact HB]| right; exact Z0])) as TXT2. clear TXT.
    pose proof (lexer_rep_pres_sub _ _ _ _ _ _ _ _ (mh_lid mh) LXR HP3 ltac:(intros y Hy; apply IMID; unfold mid_blocks; apply in_or_app; left; exact Hy)) as LXR2. clear LXR.
    pose proof (buf_rep_pres_sub _ _ _ _ _ _ _ DBR HP3 ltac:(intros y Hy; apply IMID; unfold mid_blocks; apply in_or_app; right; exact Hy)) as DBR2. clear DBR.
    pose proof (ystatics_pres _ _ _ _ YS2 HP3) as YS3.
    assert (PRES2 : ry_pres (p_REST E) (bv_unsigned (p_sp E) + 144) [(mh_ctx (p_mh E), mh_ctx (p_mh E) + 8)] (p_m0 E) m2).
    { eapply ry_pres_trans; [exact PRES1|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP3| clear; lia| exact IRR]. }
    clear PRES1 HK1 HK2 AX AX2 MU WM YS YS2 STK1 MI1 ERR.
    (* [comment removed for export] *)
    pose proof (munch_refl [(mh_addr (p_mh E) + 48, mh_addr (p_mh E) + 56)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
    rz_seg HKS HK3.
    zstep. zstep. if_cases K; zify_cond K. { exfalso. revert K BR'. clear. intros. rewrite ?unsigned_lit in K by lia. lia. }
    zstep. rewrite ysx32_small by (clear -B2 B3; lia). step. apply evt_done.
    set (h2 := h_set_stack3 h (h_stack h) (h_stack_size h + 128) (Some 0%nat)).
    set (mh2 := mkMH (mh_id mh) (mh_addr mh) (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (mh_decbuf mh) p' A' (mh_ctx mh)).
    pose proof (push_store E) as PS. unfold pstate, pH, wz in PS.
    replace (Z_to_bv 64 A') with (Z_to_bv 64 (mh_stack mh2)) by reflexivity.
    replace (h_used h) with (h_used h2) by reflexivity.
    eapply PS; [exact OK| | unfold h2; cbn [h_stack_size h_set_stack3]; replace (h_used _) with (h_used h) by reflexivity; clear -FULL; lia| | exact AG].
    2:{ apply (YP true). unfold ybs_push. replace (h_stack_size h - h_used h =? 0) with true by (symmetry; apply Z.eqb_eq; clear -FULL; lia).
        replace (UINT_MAX - YAJL_BS_INC <? h_stack_size h) with false by (symmetry; apply Z.ltb_ge; unfold UINT_MAX, YAJL_BS_INC; clear -B2; lia).
        unfold yrealloc. cbn [ybind]. apply (yl_realloc _ _ _ (Some 0%nat)). unfold YAJL_BS_INC, h2. apply yl_ret. }
    lazymatch goal with H : mem_inv _ ?mx |- _ => rename H into MI4; rename mx into m4 end.
    lazymatch goal with H : stk _ m4 _ _ |- _ => rename H into STK4 end.
    pose proof (munch_agree _ _ _ MU WM) as AG4.
    split.
    { apply RYST_split. split.
      - eapply HKP; [eapply HKF; [exact HK3| exact MU| exact WM|]|].
        + constructor; [| constructor]. right; right. eexists. split; [right; left; reflexivity|]. cbn. unfold SIZEOF_HANDLE. clear -EHA. rewrite <- EHA. lia.
        + rewrite (yblocks_mid mh2 h2 LK (p_REST E)) by (unfold h2; cbn; discriminate).
          unfold REST0, h2, mh2. cbn [mh_id mh_addr mh_sid mh_stack h_stack_size h_set_stack3 mid_blocks mh_lid mh_lexer mh_lexbuf mh_decbuf h_lexer h_decbuf].
          apply (Permutation.Permutation_middle ((mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: mid_blocks mh h) (LK ++ p_REST E) (p', A', h_stack_size h + 128)).
      - eapply ystatics_munch; [exact YS3| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RY_CALLBACKS. clear -R1. lia. }
    split.
    { split; [| split; [| split]].
      - split; [| unfold h2, mh2; cbn [h_set_stack3 h_bytesConsumed h_stack_size h_stack_blk h_parseError mh_stack]; replace (h_used _) with (h_used h) by reflexivity;
               split; [exact B1|]; split; [clear -B2 SZB L26; unfold pLEN in *; lia|]; split; [clear -B3; lia|]; split; [intros X; discriminate| intros X; exfalso; clear -X BR'; lia]].
        exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells, h2, mh2.
        cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app h_set_stack3 h_bytesConsumed h_stack_size h_parseError mh_addr mh_ctx mh_lexer mh_decbuf mh_stack].
        unfold wz, RY_CALLBACKS, RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W. replace (h_used _) with (h_used h) by reflexivity. rewrite EHA. exact HC2.
      - unfold h2, mh2. cbn [mh_lexer mh_lexbuf mh_addr h_lexer h_set_stack3]. rewrite EHA. eapply lexer_rep_agree; [exact AG4| exact LXR2| | |];
          [intros a Ha| intros a Ha| intros HD a Ha]; (eapply OUTH; [left|]);
          [left; reflexivity| cbn; exact Ha| right; left; reflexivity| cbn; exact Ha
          | unfold mid_blocks, lexer_blocks, buf_blocks; right; destruct (yb_data (lx_buf (h_lexer h))); [| congruence]; right; left; reflexivity| cbn; exact Ha].
      - unfold h2, mh2. cbn [mh_decbuf mh_addr h_decbuf h_set_stack3]. rewrite EHA. eapply buf_rep_agree; [exact AG4| exact DBR2| |];
          [intros a Ha| intros HD a Ha]; (eapply OUTH);
          [left; unfold mid_blocks; apply in_or_app; right; left; reflexivity| cbn; exact Ha
          | left; unfold mid_blocks, buf_blocks; apply in_or_app; right; destruct (yb_data (h_decbuf h)); [| congruence]; right; left; reflexivity| cbn; exact Ha].
      - unfold RYajlRep.bs_rep, h2, mh2. cbn [h_stack_blk h_set_stack3 mh_stack h_stack h_stack_size]. split; [clear -BR'; lia|].
        exists junk2. replace (h_used _) with (h_used h) by reflexivity. rewrite <- FULL in NEWC |- *.
        replace (h_used h + 128 - h_used h) with 128 by (clear; lia). exact NEWC. }
    split. { unfold mh_same, mh2. cbn. exact SAME. }
    split. { exact (conj CXC2 CXB2). }
    split.
    { eapply text_at_agree; [exact AG4| exact TXT2|]. intros a Ha. destruct TB as [(bt & HIN & HB)|Z0]; [| unfold pLEN in Z0; clear -Ha Z0; lia].
      apply (OUTH bt a); [right; apply in_or_app; right; exact HIN| unfold pLEN in HB; clear -Ha HB; lia]. }
    split; [exists padw; exact FR2|].
    split.
    { eapply rauxv_ok_frame; [exact AX3| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL.
      pose proof AX3 as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & CB0 & _). unfold alloc_ceiling in CB0. clear -R1 CB0. lia. }
    split; [exact STK4|]. split; [eexists; rewrite (ry_errno_lit _ TP); unfold RERRNO; eassumption|]. split; [exact MI4|].
    split.
    { eapply ry_pres_trans; [exact PRES2|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
      intros a Ha Hc _. cbn. split; [| exact I]. destruct Hc as [Hc|[[Hc _]|(b & Hb & Hr)]]; [unfold pSP in Hc; clear -Hc R1 CEIL LO; lia| clear -Hc R1; lia|].
      pose proof (OUTH b a (or_intror ltac:(apply in_or_app; right; exact Hb)) Hr) as X. cbn in X. exact (proj1 X). }
    split; [unfold h2; cbn; discriminate| exact LK0].
Qed.

(* [comment removed for export] *)
Lemma push_tail : forall rav a0v a1v a2v,
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x15d1c m rav t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v (wz (state_code stp)) s8v (wz 13)) mo) (p_K E).
Proof.
  intros rav a0v a1v a2v. open_env HKB OK PM.
  pose proof SZB as SZB'. unfold YAJL_BS_INC in SZB'.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  rz_seg HKS HK0.
  zstep. rewrite ysx32_small by (clear -B2; lia).
  zstep. rewrite ysx32_small by (clear -B2 B3; lia).
  zstep. if_cases K; zify_cond K.
  - apply evt_done. pose proof push_norealloc as PN. unfold pstate, pH, wz in PN. apply PN. clear -K B3. lia.
  - zstep. zstep. zstep. if_cases K2; zify_cond K2.
    { exfalso. revert K2 B2 SZB' L26. clear. unfold pLEN. intros. rewrite ?unsigned_lit in K2 by lia.
      change 18446744073709551615 with (Z.ones 64) in K2. rewrite ?Z.land_ones in K2 by lia. cbn in K2. lia. }
    apply evt_done. pose proof push_realloc as PR. unfold pstate, pH, wz in PR. rewrite <- K. apply PR. clear -K. lia.
Qed.
End PUSH.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section GV.
Variables (E : penv) (m : mem) (mo : Model) (s : PState) (LK : list block) (h : yhandle) (mh : mhand) (cx : yctx) (obw olw : word) (st : ystate) (rest : list ystate).
Variables (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 s5v : word).
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
Definition gv_handle : yhandle :=
  match st with
  | ST_start => h_set_lexer h (lex_reset (h_lexer h))
  | ST_map_need_val => h_set_stack h (ST_map_got_val :: rest)
  | _ => h_set_stack h (ST_array_got_val :: rest)
  end.


(* [comment removed for export] *)
Lemma gv_set88 : forall rav a2v a3v s6v s8v st' (push : option ystate),
  s8v = wz (match push with None => 1 | Some _ => 0 end) ->
  (forall stp, push = Some stp -> s6v = wz (state_code stp)) ->
  (forall r, yleaf (match push with
                    | None => YRet (SR_again (h_set_stack h (st' :: rest)) cx)
                    | Some stp => ybind (ybs_push (h_set_stack h (st' :: rest)) stp)
                                        (fun r0 => let '(ok, h2) := r0 in if ok then YRet (SR_again h2 cx) else YRet (SR_done YS_alloc_failed h2 cx))
                    end) r ->
             yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) r) ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x15d14 m rav t0 t1 t2 (wz (state_code st')) (wz (mh_stack mh + h_used h - 1)) a2v a3v a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros rav a2v a3v s6v s8v st' push ES8 ES6 YGG. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (state_code_range st') as CR. subst s8v.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  pose proof (munch_refl [(mh_stack mh + h_used h - 1, mh_stack mh + h_used h)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  assert (LEN : length (zbytes (stack_bytes (h_stack h)) ++ junk) = Z.to_nat (h_stack_size h)) by (rewrite length_app; clear -L1 L2 B3; lia).
  rz_seg HKS HK0.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at rsegs mx (mh_stack mh) _ (h_used h - 1) ARR ltac:(rewrite LEN; clear -B3 USED Z0; lia)) as SOK end.
  replace (mh_stack mh + h_used h - 1) with (mh_stack mh + (h_used h - 1)) by (clear; lia).
  step.
  match type of ARR with Arr.u8arr _ ?mx _ _ =>
    pose proof (u8arr_write rsegs mx (mh_stack mh) _ (h_used h - 1) (Z_to_bv 8 (state_code st')) ARR ltac:(rewrite LEN; clear -B3 USED Z0; lia)) as ARR' end.
  rewrite le1_wz by (clear -CR; lia). clear ARR. store_done.
  assert (PM1 : forall m1, mem_inv rsegs m1 -> munch [(mh_stack mh + h_used h - 1, mh_stack mh + h_used h)] m m1 -> wmono rsegs m m1 ->
            u8arr rsegs m1 (mh_stack mh) (upd (zbytes (stack_bytes (h_stack h)) ++ junk) (Z.to_nat (h_used h - 1)) (Z_to_bv 8 (state_code st'))) ->
            rw_cells rsegs m1 (mh_addr (p_mh E)) (hand_cells ryc h mh pew pad) ->
            rw_cells rsegs m1 (mh_ctx (p_mh E)) (ctx_cells cx) ->
            yparse_frame m1 (p_sp E) (p_ra E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (reg_get (p_F E) 8) padw obw olw ->
            stk rsegs m1 (p_lo E) (bv_unsigned (p_sp E)) ->
            pmem E m1 mo s LK (h_set_stack h (st' :: rest)) mh cx obw olw).
  { intros m1 MI1 MU1 WM1 ARR1 HC1 CXC1 FR1 STK1.
    eapply pmem_setb; [exact HKF| exact HKB| exact OK| exact PM| exact HST| exact MU1| exact WM1| exact MI1| exact ARR1| exact L2| | exact CXC1| exists padw; exact FR1| exact STK1].
    exists pew, pad. split; [rewrite EHA; exact HC1| exact PW]. }
  zstep. if_cases KS; zify_cond KS.
  - (* [comment removed for export] *)
    destruct push as [stp|]; [exfalso; apply KS; vm_compute; reflexivity|].
    apply evt_done.
    pose proof (J_back HK HKS E) as JB. unfold pstate, pH in JB. eapply JB; [exact OK| | apply YGG; apply yl_ret| exact AG].
    eapply PM1; [assumption| exact MU| exact WM| exact ARR'| | exact CXC| exact FR| exact STK].
    unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. unfold wz. rewrite EHA. exact HC.
  - (* [comment removed for export] *)
    destruct push as [stp|]; [| exfalso; revert KS; clear; intros KS; vm_compute in KS; lia].
    rewrite (ES6 stp eq_refl). apply evt_done.
    pose proof (push_tail E) as PT. unfold pstate, pH, wz in PT.
    eapply (PT _ mo s LK (h_set_stack h (st' :: rest)) mh cx obw olw stp); clear PT; [exact OK| | exact SZK| exact SZB| exact AG|].
    + eapply PM1; [assumption| exact MU| exact WM| exact ARR'| | exact CXC| exact FR| exact STK].
      unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. unfold wz. rewrite EHA. exact HC.
    + intros ok h2 YPU. apply YGG. eapply yleaf_bind; [exact YPU|]. cbv beta iota. destruct ok; apply yl_ret.
Qed.

Lemma J_gotval : forall rav a0v a1v a2v a3v s6v s8v (push : option ystate),
  s8v = wz (match push with None => 1 | Some _ => 0 end) ->
  (forall stp, push = Some stp -> s6v = wz (state_code stp)) ->
  (forall r, yleaf (ygot_value h cx push) r -> yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) r) ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x15cbc m rav t0 t1 t2 a0v a1v a2v a3v a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros rav a0v a1v a2v a3v s6v s8v push ES8 ES6 YG. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (lexer_facts _ HKB _ _ _ _ _ _ _ _ _ _ OK PM) as (RL & RLB & HL & HLB & LLB & SL & SLB). rewrite EHA in HL, HLB.
  clear ERR TXT DBR. unfold pstate, pH, wz.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2).
  pose proof (u8arr_read rsegs m (mh_stack mh) _ (h_used h - 1) (Z_to_bv 8 (state_code st)) _ ARR
                ltac:(rewrite HST; replace (Z.to_nat (h_used h - 1)) with (Z.to_nat (zlength rest)) by (clear -USED; lia); apply stack_top_byte) ltac:(clear -USED Z0; lia) eq_refl) as RK.
  assert (LEN : length (zbytes (stack_bytes (h_stack h)) ++ junk) = Z.to_nat (h_stack_size h)) by (rewrite length_app; clear -L1 L2 B3; lia).
  (* [comment removed for export] *)
  rz_seg HKS HK0.
  zstep. rewrite ysx32_small by (clear -USED Z0 B2 B3; lia).
  zstep. if_cases KU; zify_cond KU. { kill KU. }
  zstep. zstep. zstep. zstep. rewrite (land_M32_small (h_used h + -1)) by (clear -USED Z0 B3 B2; lia). zstep.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + (h_used h - 1)) by (clear; lia).
  change (wa (mh_stack mh + (h_used h - 1))) with (Z_to_bv 64 (mh_stack mh + (h_used h - 1))) in RK.
  step. clear RK. change (Z_to_bv 8 (state_code st)) with (b8 (state_code st)). rewrite (zxb_b8 (state_code st)) by (clear; destruct st; cbn; lia).
  zstep. zstep. if_cases K6; zify_cond K6; unfold wz in K6; rewrite ?unsigned_lit in K6 by (clear; pose proof (state_code_range st); lia).
  - (* [comment removed for export] *)
    assert (E6 : st = ST_map_need_val) by (clear -K6 VS; destruct st; cbn in *; first [reflexivity| discriminate| lia]).
    zstep. rewrite ysx32_small by (clear -B2; lia).
    zstep. if_cases KB; zify_cond KB. { kill KB. }
    zstep. step. apply evt_done.
    change (Z_to_bv 64 7) with (wz (state_code ST_map_got_val)).
    replace (mh_stack mh + (h_used h - 1)) with (mh_stack mh + h_used h - 1) by (clear; lia).
    pose proof gv_set88 as GS. unfold pstate, pH, wz in GS. eapply GS; clear GS; [exact ES8| exact ES6|].
    intros r YR. apply YG. unfold ygot_value. rewrite (ybs_current_eq _ _ _ HST). cbn [ybind]. rewrite E6.
    rewrite (ybs_set_eq _ _ _ _ HST) by (exact (proj2 B3)). cbn [ybind]. exact YR.
  - zstep. if_cases KZ; zify_cond KZ; unfold wz in KZ; rewrite ?unsigned_lit in KZ by (clear; pose proof (state_code_range st); lia).
    + (* [comment removed for export] *)
      assert (EA : st = ST_array_need_val \/ st = ST_array_start) by (clear -K6 KZ VS; destruct st; cbn in *; first [left; reflexivity| right; reflexivity| discriminate| lia]).
      zstep. rewrite ysx32_small by (clear -B2; lia).
      zstep. if_cases KB; zify_cond KB. { kill KB. }
      zstep. apply evt_done.
      change (Z_to_bv 64 10) with (wz (state_code ST_array_got_val)).
      replace (mh_stack mh + (h_used h - 1)) with (mh_stack mh + h_used h - 1) by (clear; lia).
      pose proof gv_set88 as GS. unfold pstate, pH, wz in GS. eapply GS; clear GS; [exact ES8| exact ES6|].
      intros r YR. apply YG. unfold ygot_value. rewrite (ybs_current_eq _ _ _ HST). cbn [ybind].
      destruct EA as [EA|EA]; rewrite EA; (rewrite (ybs_set_eq _ _ _ _ HST) by (exact (proj2 B3)); cbn [ybind]; exact YR).
    + (* [comment removed for export] *)
      assert (E0 : st = ST_start) by (clear -KZ VS; destruct st; cbn in *; first [reflexivity| discriminate| lia]).
      pose proof LXI as (LI1 & LI2 & LI3 & LI4 & LI5 & LI6 & LZ).
      pose proof (munch_refl [(p_lo E, bv_unsigned (p_sp E)); (mh_addr (p_mh E) + 16, mh_addr (p_mh E) + 24); (mh_lexer mh, mh_lexer mh + 48);
                              (mb_addr (mh_lexbuf mh), mb_addr (mh_lexbuf mh) + 32)] m) as MU.
      pose proof (wmono_refl rsegs m) as WM.
      rewrite <- EHA in LXR.
      (* [comment removed for export] *)
      clear HC. yhide SC. yhide FR. yhide CXC.
      (* [comment removed for export] *)
      assert (SG1 : mh_addr mh + SIZEOF_HANDLE <= mh_lexer mh \/ mh_lexer mh + SIZEOF_LEXER <= mh_addr mh) by (unfold SIZEOF_HANDLE, SIZEOF_LEXER; rewrite EHA; clear -HL; lia).
      assert (SG2 : mh_addr mh + SIZEOF_HANDLE <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + SIZEOF_BUF <= mh_addr mh) by (unfold SIZEOF_HANDLE, SIZEOF_BUF; rewrite EHA; clear -HLB; lia).
      assert (SG3 : mh_lexer mh + SIZEOF_LEXER <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + SIZEOF_BUF <= mh_lexer mh) by (unfold SIZEOF_LEXER, SIZEOF_BUF; clear -LLB; lia).
      assert (SG4 : mh_addr mh + SIZEOF_HANDLE <= p_lo E) by (unfold SIZEOF_HANDLE; rewrite EHA; clear -R1 CEIL; lia).
      assert (SG5 : mh_lexer mh + SIZEOF_LEXER <= p_lo E) by (unfold SIZEOF_LEXER; clear -RL CEIL; lia).
      assert (SG6 : mb_addr (mh_lexbuf mh) + SIZEOF_BUF <= p_lo E) by (unfold SIZEOF_BUF; clear -RLB CEIL; lia).
      assert (SG7 : mh_addr mh <> 0) by (rewrite EHA; clear -R1; lia).
      assert (SG8 : mh_lexer mh <> 0) by (clear -RL; lia).
      assert (SG9 : mb_addr (mh_lexbuf mh) <> 0) by (clear -RLB; lia).
      assert (SG10 : p_lo E <= bv_unsigned (p_sp E) - RY_RESET_STACK) by (unfold RY_RESET_STACK, RY_LEX_REALLOC_STACK, RY_BUF_SMALL_STACK; clear -LO; lia).
      clear ARR R1 R2 S12 RL RLB HL HLB LLB SL SLB K6 KZ KU L1 LEN.
      zstep. zstep.
      call (YRP h mh (p_lo E)).
      all: lazymatch goal with
           | |- RYajlRep.hand_struct _ _ _ _ _ => exact HS
           | |- RYajlRep.lexer_rep _ _ _ _ _ _ => exact LXR
           | |- yb_state _ = BS_ok => rewrite LZ; reflexivity
           | |- buf_inv _ => rewrite LZ; apply buf_inv_zero
           | |- yb_data _ = None => rewrite LZ; reflexivity
           | |- stk _ _ _ _ => exact STK
           | |- mem_inv _ _ => exact MI
           | |- _ = wz _ => rewrite EHA; reflexivity
           | |- _ => first [assumption| idtac] end.
      lazymatch goal with H : RYajlRep.hand_struct _ _ _ _ _ |- _ => rename H into HS2 end.
      lazymatch goal with H : RYajlRep.lexer_rep _ _ _ _ _ _ |- _ => rename H into LXR2 end.
      lazymatch goal with H : stk _ _ _ _ |- _ => rename H into STK2 end.
      lazymatch goal with H : mem_inv _ ?mx |- _ => rename H into MI2; rename mx into m2 end.
      (* [comment removed for export] *)
      pose proof (pmem_ranges _ HKB _ _ _ _ _ _ _ _ _ _ OK PM) as (_ & _ & R1 & R2 & S12 & _). rewrite EHA in R1, S12.
      pose proof (lexer_facts _ HKB _ _ _ _ _ _ _ _ _ _ OK PM) as (RL & RLB & _ & _ & _ & SL & SLB).
      unfold yhide in SC, FR, CXC.
      eapply (rw_cells_transport rsegs) in SC; [| exact MU| exact WM| cbn [disjoint_from fst snd cells_size csize Nat.add]; clear -S12 SL SLB L2 B3 EHA LO CEIL R2 USED Z0; rewrite <- ?EHA; lia].
      eapply (rw_cells_transport rsegs) in FR; [| exact MU| exact WM| cbn [disjoint_from fst snd cells_size csize Nat.add]; clear -R1 RL RLB LO CEIL; lia].
      eapply (rw_cells_transport rsegs) in CXC; [| exact MU| exact WM| cbn [disjoint_from fst snd cells_size csize Nat.add]; clear -R1 RL RLB LO CEIL SPC; lia].
      assert (PM2 : pmem E m2 mo s LK (h_set_lexer h (lex_reset (h_lexer h))) mh cx obw olw).
      { eapply pmem_updL; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| exact MI2| | reflexivity| reflexivity| | rewrite EHA in LXR2; exact LXR2| | exact (conj CXC CXB2)| exists padw; exact FR| exact STK2].
        - apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]; unfold ownL, ownA, pSP; cbn [fst snd]; [clear; lia| clear -EHA; rewrite <- EHA; lia| clear; lia| clear; lia].
        - destruct HS2 as ((pew2 & pad2 & HC2 & PW2) & HB2). split; [| exact HB2]. exists pew2, pad2. split; [exact HC2| exact PW2].
        - unfold RYajlRep.bs_rep. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC. }
      assert (YH1 : yleaf (lx <- ylex_realloc (h_lexer h) ;; YRet (h_set_lexer h lx)) (h_set_lexer h (lex_reset (h_lexer h)))).
      { eapply yleaf_bind; [apply ylex_realloc_leaf; rewrite LZ; reflexivity| apply yl_ret]. }
      zstep. if_cases KS; zify_cond KS.
      * (* [comment removed for export] *)
        destruct push as [stp|]; [| exfalso; revert ES8 KS; clear; intros -> KS; vm_compute in KS; lia].
        rewrite (ES6 stp eq_refl). apply evt_done.
        pose proof (push_tail E) as PT. unfold pstate, pH, wz in PT.
        eapply (PT _ mo s LK (h_set_lexer h (lex_reset (h_lexer h))) mh cx obw olw stp); clear PT; [exact OK| exact PM2| exact SZK| exact SZB| exact AG|].
        intros ok h2 YPU. apply YG. unfold ygot_value. rewrite (ybs_current_eq _ _ _ HST). cbn [ybind]. rewrite E0.
        eapply yleaf_bind; [exact YH1|]. cbv beta. eapply yleaf_bind; [exact YPU|]. cbv beta iota. destruct ok; apply yl_ret.
      * (* [comment removed for export] *)
        destruct push as [stp|]; [exfalso; revert ES8 KS; clear; intros -> KS; apply KS; vm_compute; reflexivity|].
        step. apply evt_done.
        pose proof (J_back HK HKS E) as JB. unfold pstate, pH in JB. eapply JB; [exact OK| exact PM2| | exact AG].
        apply YG. unfold ygot_value. rewrite (ybs_current_eq _ _ _ HST). cbn [ybind]. rewrite E0.
        eapply yleaf_bind; [exact YH1|]. cbv beta. apply yl_ret.
Qed.

End GV.
End S.
End RC__1.
