(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlDecode YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages LazyModel Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BI_shadow BI_lowshadow BI_globals2 BI_strlen_icp BI_asan_memcpy BYajlRep BYajl_iface BY_rz BY_acct_needs BY_cb BY_buf_small BY_buf_alloc BY_buf_free BY_buf_append5g BY_lex_realloc BY_reset BY_lex_allocg BY_lex_free BY_lex_top BY_wrap BY_bs_set BY_set_default BY_hex BY_client BY_alloc BY_yfree BY_decode BY_fuzz BY_parse_lex BY_parse_kitD2 BY_parse_gv BY_parse_top BY_parse_entry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition AY_URA : list Z :=
  [0x86ff8; 0x8710c;                                  (* [comment removed for export] *)
   0x87318; 0x873fc;                                  (* [comment removed for export] *)
   0x82cb8; 0x82cd8; 0x82f14;                        (* [comment removed for export] *)
   0x85ba0;                                            (* [comment removed for export] *)
   0x8b7e0; 0x8ba0c; 0x8b9c4; 0x8bb88;              (* [comment removed for export] *)
   0x824f8; 0x8259c; 0x825d8; 0x8269c;               (* [comment removed for export] *)
   0x82a50; 0x82a6c; 0x82a88;                        (* [comment removed for export] *)
   PUSH_RET; 0x87dcc; 0x87ed8; 0x87fd4; 0x881a0; 0x880a0; 0x88478; 0x88be4;  (* [comment removed for export] *)
   0x81e88; 0x81e98; 0x81ea0].                       (* [comment removed for export] *)

Section W.
Variable Y : ay_params.
(* [comment removed for export] *)
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis MIY : AHK_y_mem_inv_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis BSMALL : AHK_y_small_high_stmt Y.   (* [comment removed for export] *)
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis STATY : AHK_y_statics_stmt Y.
Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis AFLSEP : AHK_y_aflsep_stmt Y.
Hypothesis FLAGY : AHK_y_flag_cell_stmt Y.
Hypothesis FND : AHK_y_fnodup_stmt Y.
Hypothesis RELY : AHK_y_fake_release_stmt Y.
Hypothesis AYR2 : AHK_y_ayR_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis RREFL : ayR_refl_stmt Y.
Hypothesis ASM0 : astack_malloc_stmt Y 0 AY_STACK_MALLOC_0.
Hypothesis ASM1 : astack_malloc_stmt Y 1 AY_STACK_MALLOC_1.
(* [comment removed for export] *)
Variables (amalloc_rel : Z -> y_APS Y -> Model -> option Z -> y_APS Y -> Model -> Prop)
          (afree_rel : Z -> y_APS Y -> Model -> y_APS Y -> Model -> Prop)
          (arealloc_rel : Z -> Z -> y_APS Y -> Model -> option Z -> y_APS Y -> Model -> Prop).
Hypothesis AMAL : amalloc_rz_stmt bsegs ACONSTS (y_APS Y) (y_AHK Y) (y_SO Y) amalloc_rel (y_acredit Y) (y_acharge Y) (y_uanchor Y).
Hypothesis AFREE : afree_rz_stmt bsegs ACONSTS (y_APS Y) (y_AHK Y) (y_SO Y) afree_rel (y_acredit Y) (y_arefund Y) (y_uanchor Y).
Hypothesis AREA : arealloc_rz_stmt bsegs ACONSTS (y_APS Y) (y_AHK Y) (y_SO Y) arealloc_rel (y_acredit Y) (y_acharge Y) (y_arefund Y) (y_uanchor Y).
Hypothesis AREAN : arealloc_null_rz_stmt bsegs ACONSTS (y_APS Y) (y_AHK Y) (y_SO Y) arealloc_rel (y_acredit Y) (y_acharge Y) (y_uanchor Y).
Hypothesis AREF0 : forall n, 0 <= y_arefund Y n.
Hypothesis FREE1 : 1 <= y_free_cost Y.
(* [comment removed for export] *)
Variable URA : list Z.
Hypothesis URA_all : forall pc, In pc AY_URA -> In pc URA.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells bsegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.
(* [comment removed for export] *)
Hypothesis ICPG : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals bsegs m A_SB.
Hypothesis ICPG2 : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals2 bsegs m.
Hypothesis ICPB : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window bsegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ shw_hi A_SB A n <= 0x10007fff8000 /\ amem (ab_addr b) (ab_size b).   (* [comment removed for export] *)
Hypothesis ICPR : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n).
Hypothesis LOWSH : forall s LB LF m mo, y_AHK Y s LB LF m mo -> low_shadow_ok m.
Hypothesis SSH0 : forall s LB LF m mo A n, y_AHK Y s LB LF m mo -> alloc_ceiling <= A -> 1 <= n -> A + n <= 2^47 ->
    exists ws, shadow_window bsegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n) /\ ws = repeat (Z_to_bv 8 0) (length ws).
(* [comment removed for export] *)
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis YHM : yacct_hand_mono_stmt Y.
Hypothesis YFREE : yacct_free_stmt Y.
Hypothesis YACNEW : yacct_new_stmt Y.
Hypothesis YSHAPE : yphi_shape_stmt Y.
Hypothesis YPHI_grow : yphi_grow_stmt Y.
Hypothesis YPHI_err : forall len u (d : yptr) bs, y_phi_buf Y (mkBuf BS_overflow 0 0 None []) <= y_phi_buf Y (mkBuf BS_ok len u (Some d) bs).
Hypothesis YPHI_first : yphi_first_stmt Y.
Hypothesis YFB : forall b, y_free_cost Y + y_free_cost Y <= y_phi_buf Y b.
Hypothesis YPHI_HF : yphi_hand_free_stmt Y.
Hypothesis YNEW : yphi_new_alloc_stmt Y.
Variable phr : Z -> Z -> Z -> Z -> Z.
Hypothesis YSPLIT : yphi_hand_split_stmt Y phr.

(* [comment removed for export] *)
Local Ltac ura := apply URA_all; unfold AY_URA, PUSH_RET; cbn; tauto.
Local Ltac inst thm := eapply thm; try eassumption; try ura.

Lemma URA_lexP : forall pc, lex_site pc -> In (pc + 48) URA.
Proof. intros pc H. unfold lex_site in H. destruct H as [-> |[-> |[-> |[-> | ->]]]]; ura. Qed.
Lemma URA_decP : forall pc, dec_site pc -> In pc URA.
Proof. intros pc H. unfold dec_site in H. destruct H as [-> | ->]; ura. Qed.
Lemma URA_pushP : In PUSH_RET URA.
Proof. ura. Qed.

(* [comment removed for export] *)
Lemma W_malloc : aywrap_malloc_stmt Y.          Proof. inst (aywrap_malloc_proof Y). Qed.
Lemma W_free : aywrap_free_stmt Y.              Proof. inst (aywrap_free_proof Y). Qed.
Lemma W_free_null : aywrap_free_null_stmt Y.    Proof. inst (aywrap_free_null_proof Y). Qed.
Lemma W_realloc : aywrap_realloc_stmt Y.        Proof. inst (aywrap_realloc_proof Y). Qed.
Lemma W_realloc_null : aywrap_realloc_null_stmt Y. Proof. inst (aywrap_realloc_null_proof Y). Qed.

(* [comment removed for export] *)
Lemma Y_lex_realloc : aylex_realloc_stmt.       Proof. exact (aylex_realloc_proof aybuf_clear_proof). Qed.
Lemma Y_reset_parser : ayreset_parser_stmt.     Proof. exact (ayreset_parser_proof Y_lex_realloc). Qed.

(* [comment removed for export] *)
Lemma Y_buf_alloc : aybuf_alloc_stmt Y.         Proof. pose proof W_malloc. inst (aybuf_alloc_proof Y). Qed.
Lemma Y_buf_free : aybuf_free_stmt Y.           Proof. pose proof W_free. inst (aybuf_free_proof Y). Qed.
Lemma Y_buf_append : aybuf_append_stmt Y.
Proof. pose proof W_malloc. pose proof W_free_null. pose proof W_realloc. inst (aybuf_append_proof Y). Qed.

(* [comment removed for export] *)
Lemma Y_lex_alloc : aylex_alloc_stmt Y.
Proof. pose proof W_malloc. pose proof W_free. pose proof Y_buf_alloc. pose proof aybuf_err_proof. inst (aylex_alloc_proof Y). Qed.
Lemma Y_lex_free : aylex_free_stmt Y.
Proof. pose proof W_free. pose proof Y_buf_free. inst (aylex_free_proof Y). Qed.
Lemma Y_lex_lex : aylex_lex_stmt Y.
Proof. pose proof aybuf_clear_proof. pose proof aybuf_err_proof. pose proof Y_buf_append. inst (aylex_lex_proof Y). Qed.

(* [comment removed for export] *)
Lemma Y_string_decode : aystring_decode_stmt Y.
Proof.
  pose proof Y_buf_append. pose proof ayhexToDigit_proof. inst (aystring_decode_proof Y).
Qed.

(* [comment removed for export] *)
Lemma Y_alloc : ayalloc_stmt Y.
Proof.
  pose proof W_malloc. pose proof W_free. pose proof W_realloc_null. pose proof Y_lex_alloc. pose proof Y_lex_free. pose proof Y_buf_alloc. pose proof Y_buf_free.
  pose proof aybuf_err_proof. inst (ayalloc_proof' Y).
Qed.
Lemma Y_free : ayfree_stmt Y.
Proof. pose proof W_free. pose proof Y_buf_free. pose proof Y_lex_free. inst (ayfree_proof Y). Qed.

(* [comment removed for export] *)
Lemma Y_do_parse : aydo_parse_stmt Y.
Proof.
  pose proof W_realloc. pose proof URA_pushP. pose proof URA_lexP. pose proof URA_decP. pose proof Y_reset_parser.
  pose proof aycb_null_proof. pose proof aycb_boolean_proof. pose proof aycb_number_proof. pose proof aycb_string_proof. pose proof aycb_start_map_proof.
  pose proof aycb_start_array_proof. pose proof aycb_end_array_proof. pose proof aycb_end_map_proof. pose proof aycb_map_key_proof.
  pose proof aybuf_clear_proof. pose proof aybuf_err_proof. pose proof aybuf_data_proof. pose proof aybuf_len_proof. pose proof aybs_set_proof. pose proof Y_lex_lex. pose proof Y_string_decode.
  inst (aydo_parse_proof Y).
Qed.
Lemma Y_parse : ayparse_stmt Y.
Proof. pose proof Y_do_parse. inst (ayparse_proof Y). Qed.

(* [comment removed for export] *)
Theorem ayfuzz_closed : ayfuzz_stmt Y.
Proof. pose proof Y_alloc. pose proof Y_parse. pose proof Y_free. inst (ayfuzz_proof Y). Qed.
End W.
End RC__1.
