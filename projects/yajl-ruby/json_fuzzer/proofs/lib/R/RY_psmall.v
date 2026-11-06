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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMalloc_iface RYajlRep RYajl_iface RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlParser YajlFactsBuf YajlFactsLex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list MallocBlocks.block -> (word -> option byte) -> Model -> Prop.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

Lemma state_code_range : forall s, 0 <= state_code s < 12.
Proof. intros []; cbn; lia. Qed.


(* [comment removed for export] *)
Lemma ybs_set_spec : ybs_set_stmt.
Proof.
  unfold ybs_set_stmt. intros until m. intros HS BR HST BLK STK LO HLO SLO SEP MI A0 A1.
  destruct HS as ((pew & pad & HC & PW) & R1 & R2 & R3 & R4). unfold hand_cells, hand_head_cells, alloc_cells in HC.
  cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app] in HC.
  unfold bs_rep in BR. destruct (h_stack_blk h) as [sbk|] eqn:HB; [|congruence]. destruct BR as (SB0 & junk0 & SC).
  pose proof (rw_cells_bound _ _ _ _ HC) as HCB. cbn [cells_size csize Nat.add length] in HCB.
  pose proof (rw_cells_bound _ _ _ _ SC) as SCB. cbn [cells_size csize Nat.add] in SCB.
  assert (USED : h_used h = zlength rest + 1). { unfold h_used. rewrite HST. unfold zlength. cbn [length]. lia. }
  pose proof (state_code_range s') as CR.
  subst a0 a1. unfold RY_BS_SET, SIZEOF_HANDLE, wz in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (mh_stack mh + h_used h - 1, mh_stack mh + h_used h)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  pose proof L1 as L1'. rewrite zbytes_length, stack_bytes_length, HST in L1'. cbn [length] in L1'.
  assert (LEN : length (zbytes (stack_bytes (h_stack h)) ++ junk0) = Z.to_nat (h_stack_size h)) by (rewrite length_app; lia).
  pose proof (u8arr_bound _ _ _ _ ARR) as ARB.
  step. carve_frame 16%nat STK.
  step.
  step. rewrite ysx32_small by lia.
  step. if_cases K0; zify_cond K0. 1:{ kill K0. }
  step. rewrite ysx32_small by lia.
  step. if_cases K1; zify_cond K1. 1:{ kill K1. }
  zstep. zstep. zstep. zstep. zstep.
  rewrite (land_M32_small (h_used h + -1)) by lia.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at rsegs mx (mh_stack mh) _ (h_used h + -1) ARR ltac:(rewrite length_app; lia)) as SOK end.
  step.
  match type of ARR with Arr.u8arr _ ?mx _ _ =>
    pose proof (u8arr_write rsegs mx (mh_stack mh) _ (h_used h + -1) (Z_to_bv 8 (state_code s')) ARR ltac:(rewrite length_app; lia)) as ARR' end.
  rewrite le1_wz by lia. clear ARR. store_done.
  step. step. step.
  release_frame FR STK (bv_unsigned sp).
  unfold ybs_set_rpost. finish.
  - (* [comment removed for export] *) split; [| rewrite HB; repeat split; try lia; intros; congruence].
    exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
    cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. exact HC.
  - (* [comment removed for export] *)
    unfold bs_rep. cbn [h_stack_blk h_set_stack h_stack h_stack_size]. rewrite HB. split; [exact SB0|].
    exists junk0.
    replace (h_used (h_set_stack h (s' :: rest))) with (h_used h) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity).
    apply CB2_of_u8arr; [| rewrite zbytes_length, stack_bytes_length; cbn [length]; lia | exact L2].
    revert ARR'. rewrite HST, !stack_bytes_cons, !zbytes_app. cbn [zbytes map]. rewrite <- !app_assoc. cbn [app].
    rewrite (upd_app_len _ _ _ _ _) by (rewrite zbytes_length, stack_bytes_length; unfold zlength in USED; lia).
    intros ARR'. exact ARR'.
Qed.
(* [comment removed for export] *)
Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).

(* [comment removed for export] *)
Lemma yset_default_spec : yset_default_stmt.
Proof.
  unfold yset_default_stmt. intros until m. intros YC MI A0.
  pose proof (rw_cells_bound _ _ _ _ YC) as YCB. cbn [cells_size csize Nat.add] in YCB.
  subst a0. unfold RY_SET_DEFAULT, wz in *.
  pose proof (munch_refl [(YAF, YAF + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  do 6 step.
  step. lit_store. step. lit_store. step. lit_store. step. lit_store.
  step.
  unfold yset_default_rpost. finish.
Qed.

(* [comment removed for export] *)
Lemma ylex_realloc_spec : ybuf_clear_stmt -> ylex_realloc_stmt.
Proof.
  intros CLR. unfold ylex_realloc_stmt. intros until m. intros LR ST BI ND L0 B0 STK LO LLO BLO SEP MI A0.
  destruct LR as ((LC & L1 & L2 & L3 & L4 & L5 & L6) & BR). unfold lexer_cells in LC.
  destruct BR as (BS & BD & FB). destruct BS as (BC & DZ & RL & RU). pose proof (proj1 DZ ND) as D0.
  pose proof (rw_cells_bound _ _ _ _ BC) as BCB. rewrite buf_cells_size in BCB. unfold buf_cells in BC.
  pose proof (rw_cells_bound _ _ _ _ LC) as LCB. cbn [cells_size csize Nat.add] in LCB.
  subst a0. unfold RY_LEX_REALLOC, RY_LEX_REALLOC_STACK, RY_BUF_SMALL_STACK, SIZEOF_LEXER, SIZEOF_BUF, wz in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (L, L + 48); (mb_addr mbl, mb_addr mbl + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  assert (LC' : rw_cells rsegs m L
     [CB 8 (le4 (Z_to_bv 64 (lx_lineOff lx)) ++ le4 (Z_to_bv 64 (lx_charOff lx)));
      C4 (Z_to_bv 64 (lex_error_code (lx_error lx))); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (mb_addr mbl));
      CB 8 (le4 (Z_to_bv 64 (lx_bufOff lx)) ++ le4 (Z_to_bv 64 (lx_bufInUse lx)));
      C4 (Z_to_bv 64 (lx_allowComments lx)); C4 (Z_to_bv 64 (lx_validateUTF8 lx)); C8 (Z_to_bv 64 AF)]).
  { eapply rw_cells_recast; [exact LC| | |].
    - cbn [cells_wf cell_wf]. rewrite !length_app, !length_le4. repeat split; reflexivity.
    - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
    - reflexivity. }
  clear LC.
  step. carve_frame 16%nat STK.
  step. step. step. step.
  step. lit_store. step. lit_store.
  pose proof (proj1 STK) as LO0. pose proof (proj1 (proj2 STK)) as SPHI. cbn beta in LO0, SPHI.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  pose proof (CLR (mb_addr mbl) (mb_data mbl) AF lo (lx_buf lx)) as CLR'. unfold ybuf_clear_rpost in CLR'. rewrite ND in CLR'. cbn [app] in CLR'.
  step. call CLR'.
  1:{ split; [unfold buf_cells; exact BC| split; [exact DZ| lia]]. }
  1:{ unfold buf_data. rewrite ?ND. exact I. } 1:{ exact ST. } 1:{ exact BI. } 1:{ exact B0. }
  1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold RY_BUF_SMALL_STACK. lia. } 1:{ unfold SIZEOF_BUF. lia. }
  1:{ intros C. exfalso. apply C. first [exact ND| reflexivity]. } 1:{ assumption. } 1:{ reflexivity. }
  (* [comment removed for export] *)
  match goal with H : stk rsegs _ lo _ |- _ => rename H into STK2 end. rewrite ESP in STK2.
  match goal with H : buf_struct _ _ _ _ _ _ |- _ => destruct H as (BC2 & _ & _ & _); unfold buf_cells, buf_cleared in BC2; cbn [yb_state yb_len yb_used yb_data buf_state_code] in BC2 end.
  match goal with H : buf_data _ _ _ _ |- _ => clear H end.
  step. lit_store.
  step. step. step. step. step.
  release_frame FR STK2 (bv_unsigned sp).
  unfold ylex_realloc_rpost. finish.
  - reflexivity.
  - split.
    + split; [| cbn; lia]. unfold lexer_cells, lex_reset. cbn -[Z_to_bv rw_cells rsegs Z.add].
      eapply rw_cells_recast; [eassumption| | |].
      * cbn. repeat split; exact I.
      * reflexivity.
      * reflexivity.
    + split; [| split; [unfold buf_data, lex_reset, buf_cleared; cbn [yb_data lx_buf]; rewrite ND; exact I| unfold lex_reset, buf_cleared; cbn; constructor]].
      split; [| split; [cbn; exact DZ| cbn; lia]].
      unfold buf_cells, lex_reset, buf_cleared. cbn [yb_state yb_len yb_used yb_data buf_state_code lx_buf]. exact BC2.
Qed.
(* [comment removed for export] *)
Lemma yreset_parser_spec : ylex_realloc_stmt -> yreset_parser_stmt.
Proof.
  intros LRE. unfold yreset_parser_stmt. intros until m. intros HS LR ST BI ND H0 L0 B0 STK LO HLO LLO BLO SHL SHB SLB MI A0.
  destruct HS as ((pew & pad & HC & PW) & R1 & R2 & R3 & R4). unfold hand_cells, hand_head_cells, alloc_cells in HC.
  cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app] in HC.
  pose proof (rw_cells_bound _ _ _ _ HC) as HCB. cbn [cells_size csize Nat.add length] in HCB.
  destruct LR as ((LC & LRG) & (BS & BD & FB)). destruct BS as (BC & DZ & RL & RU).
  pose proof (proj1 DZ ND) as D0.
  pose proof (rw_cells_bound _ _ _ _ LC) as LCB. rewrite lexer_cells_size in LCB.
  pose proof (rw_cells_bound _ _ _ _ BC) as BCB. rewrite buf_cells_size in BCB.
  unfold lexer_cells in LC. unfold buf_cells in BC.
  pose proof (proj1 STK) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  subst a0. unfold RY_RESET, RY_RESET_STACK, RY_LEX_REALLOC_STACK, RY_BUF_SMALL_STACK, SIZEOF_HANDLE, SIZEOF_LEXER, SIZEOF_BUF, wz in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (mh_addr mh + 16, mh_addr mh + 24); (mh_lexer mh, mh_lexer mh + 48);
                          (mb_addr (mh_lexbuf mh), mb_addr (mh_lexbuf mh) + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  step. carve_frame 16%nat STK.
  step. step.
  step. if_cases K0; zify_cond K0. 1:{ kill K0. }
  step. step.
  step. call (LRE (mh_lexer mh) (mh_addr mh + 72) lo (h_lexer h) (mh_lexbuf mh)).
  1:{ split; [split; [unfold lexer_cells; exact LC| exact LRG]|]. split; [split; [unfold buf_cells; exact BC| split; [exact DZ|lia]]| split; [unfold buf_data; rewrite ND; exact I| exact FB]]. }
  1:{ exact ST. } 1:{ exact BI. } 1:{ exact ND. } 1:{ exact L0. } 1:{ exact B0. }
  1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold RY_LEX_REALLOC_STACK, RY_BUF_SMALL_STACK. lia. }
  1:{ unfold SIZEOF_LEXER. lia. } 1:{ unfold SIZEOF_BUF. lia. } 1:{ unfold SIZEOF_LEXER, SIZEOF_BUF. lia. }
  1:{ assumption. } 1:{ reflexivity. }
  match goal with H : stk rsegs _ lo _ |- _ => rename H into STK2 end. rewrite ESP in STK2.
  match goal with H : lexer_rep _ _ _ _ _ _ |- _ => rename H into LR2 end.
  destruct LR2 as ((LC2 & LRG2) & ((BC2 & BSR2) & _ & FB2)). unfold lexer_cells in LC2. unfold buf_cells in BC2.
  match goal with H : ?x = wz (mh_lexer mh) |- _ => subst x end. unfold wz in *.
  step. step. step. step. step.
  release_frame FR STK2 (bv_unsigned sp).
  unfold yreset_parser_rpost. finish.
  - split; [| repeat split; try lia; tauto].
    exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
    cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. exact HC.
  - split; [split; [unfold lexer_cells; exact LC2| exact LRG2]|].
    split; [split; [unfold buf_cells; exact BC2| exact BSR2]|].
    split; [| exact FB2]. unfold buf_data, lex_reset, buf_cleared. cbn [lx_buf yb_data]. rewrite ND. exact I.
Qed.
End S.
End RC__1.
