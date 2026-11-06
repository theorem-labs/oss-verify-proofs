(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d): the
   LEAVES of the write_value walk: the three literals (null, false, true: cases 242 / 246 / 223, the tail `put` at
   slot 268), the string (case 182, the tail `put_string` at slot 207) and the number (case 226, `strlen` at slot 237,
   the tail `put` at slot 268). MEASURED on B' with the engine (WriteValueB's probe, the internal file zfb-20261029T184733Z.log): every
   tag reaches the switch's `jr` at slot 40 with no obligation left; the literal cases run to the tail call with
   a0 = the entry a0 (= o), a1 = the literal (A_OBJ 2 + its addend), a2 = its length, ra / sp / s0 .. s11 back at
   their entry atoms; the string and number cases stop once, at `bnez` on the text pointer (slot 189 / 233), whose
   NULL arm the ledger refutes.
   PORTED (not cited) from a Theorem Labs lane's image-A walk PRW_write_value.v (walk commit
   7819c4b4583, :2443-3440): B's slots and frame (192), the #102 ledger cells, and two changes of substance:
   - the granule gap comes from AR_laws_x's field alx_blocks_ceil8 (a live block's `p + req_size n + 8 <=
     alloc_ceiling`; until the batch cut the walk's named premise SRC-CEIL), used once here (wv_blk_ceil7), not A's per-call
     wv_gap. Since that cut, cstr_ok asks only `p + len + 1 <= alloc_ceiling` and src_rd `p + len <= alloc_ceiling`, which
     the granule bound gives;
   - the FLOAT FORM: the string leaf's tail put_string posts fpostWFmR at wle' SEGS RZ_cf (the draft's text), so it
     concludes write_value's fpostWFmR directly; the literal and number leaves end in put's fpostWmR at the entry float
     state, and the ONE float lemma WriteValueB_Defs.wv_fpostW_FR (in WriteValueB_Top.wv_leaf_F) closes write_value's fpostWFmR from the entry-frm hypothesis (FRM0-ENTRY).
   Numerals: 192 (LENGTH: write_value's frame), 200 (LENGTH: frame + 8), the slots (DERIVED). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import WriteValueB_Model WriteValueB_Base WriteValueB_Call.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Set Default Proof Using "All".
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Section f.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib B.
(* image facts of the instance, discharged at PI_prog_B (B_entry_write_value / B_prog_obj_img) *)
Hypothesis Hent : SIGMA AS_write_value = BASE + AF_write_value.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
(* ---- IMAGE FACTS OF THE INSTANCE (discharged at PI_prog_B, WriteValueB_Inst), both read off the generated
   listing ----
   the tag switch's seven table words: each is a ROM word of the read-only band, apart from the GOT word and from
   the shadow-base cell, and inside the image's low range *)
Hypothesis HJT : forall k : nat, (k < 7)%nat ->
  val_mem SEGS (fun _ => None) (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) 4 (WV_JTW k) /\
  0 <= WV_JTW k <= 2 ^ 31 - 1 /\
  0 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k /\
  VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= kLowMemEnd /\
  (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= VAL (A_OBJ 0) \/
   VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) /\
  (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= VAL (A_OBJ 12) \/
   VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) /\
  (forall i, 0 <= i < 4 -> in_img SEGS (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i) /\
     in_roP SEGS pa_relro_lo pa_relro_hi (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i) /\
     ~ Exists (in_zr (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i)) (as_owned_static B) /\
     ~ (as_errno B <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i < as_errno B + 4)).
(* and the literals: at any state of the run each is a legal put source whose home is kept (put_string's HLIT17
   shape), its bytes being the image's *)
Hypothesis HLIT : forall (k : nat) (bs : list Z) ly' S' Hp' (W' : world SEGS) m' md',
  In (k, bs) wv_lits ->
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m') ->
  src_rd W' m' (WV_STR k) bs /\ kept_at B [] (WV_STR k) (Z.of_nat (length bs)) /\
  (forall i, 0 <= i < Z.of_nat (length bs) -> in_img SEGS (WV_STR k + i)).
(* IMAGE FACT (discharged at PI_prog_B, WriteValueB_Inst): no static of alloc.c lies in the read-only band, so
   a journal's image clause keeps the band (the same text as put_string's and pj_write's walks) *)
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_B).

(* the memory invariant the m-form posts keep (the fQmn over YAkMemnorm, PRH_Base.v blob ee6c7a38d6b6): each walk
   lemma instantiates the runner's invariant ONCE as `fun m => memnorm mem0 -> memnorm m` (srr_inv_laws_imp at
   srr_inv_laws_memnorm_k); each callee keep comes from that callee's own m-form post. *)
Let RUN := @paj_run_x fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS.
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_B) (PI := PA).

(* WriteValueB_Base's lemmas at this Section's variables *)
Let wv_disj_img := @WriteValueB_Base.wv_disj_img fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_disj_img_n := @WriteValueB_Base.wv_disj_img_n fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_achain_at := @WriteValueB_Base.wv_achain_at fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_entry := @WriteValueB_Base.wv_entry fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_entry2 := @WriteValueB_Base.wv_entry2 fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_jr_step := @WriteValueB_Base.wv_jr_step fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_pi_at := @WriteValueB_Base.wv_pi_at fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_seat := @WriteValueB_Base.wv_seat fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_case_bounds := @WriteValueB_Base.wv_case_bounds fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_jr_target := @WriteValueB_Base.wv_jr_target fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ro_val := @WriteValueB_Base.wv_ro_val fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_rom_none := @WriteValueB_Base.wv_rom_none fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_mrestrict_of_aview := @WriteValueB_Base.wv_mrestrict_of_aview fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_agree_of_aview := @WriteValueB_Base.wv_agree_of_aview fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_nodeR_keep := @WriteValueB_Base.wv_nodeR_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_zz_dec := @WriteValueB_Base.wv_zz_dec fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_led_hbs := @WriteValueB_Base.wv_led_hbs fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_led_nodup := @WriteValueB_Base.wv_led_nodup fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_led_cnt := @WriteValueB_Base.wv_led_cnt fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_blk_keep := @WriteValueB_Base.wv_blk_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_foot_keep := @WriteValueB_Base.wv_foot_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_lit_home := @WriteValueB_Base.wv_lit_home fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_pow_facts := @WriteValueB_Base.wv_pow_facts fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_keep_frame := @WriteValueB_Base.wv_keep_frame fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_vm_keep := @WriteValueB_Base.wv_vm_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_shadow_low := @WriteValueB_Base.wv_shadow_low fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_hull_low := @WriteValueB_Base.wv_hull_low fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_led_keep := @WriteValueB_Base.wv_led_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_out_keep := @WriteValueB_Base.wv_out_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_tree_vis_keep := @WriteValueB_Base.wv_tree_vis_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ra_keep := @WriteValueB_Base.wv_ra_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_arodata_keep := @WriteValueB_Base.wv_arodata_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_awr := @WriteValueB_Base.wv_awr fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_loc := @WriteValueB_Base.wv_loc fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_foot_wr := @WriteValueB_Base.wv_foot_wr fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_pres_of_st := @WriteValueB_Base.wv_pres_of_st fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_aview_range := @WriteValueB_Base.wv_aview_range fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_rdword_nonneg := @WriteValueB_Base.wv_rdword_nonneg fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_chain1 := @WriteValueB_Base.wv_chain1 fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_chain1g := @WriteValueB_Base.wv_chain1g fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_rdword_ext := @WriteValueB_Base.wv_rdword_ext fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_reca_keep := @WriteValueB_Base.wv_reca_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_cfp_closed := @WriteValueB_Base.wv_cfp_closed fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_arodata_j := @WriteValueB_Base.wv_arodata_j fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_wmax_next := @WriteValueB_Base.wv_wmax_next fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_live_next := @WriteValueB_Base.wv_live_next fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_two_in_split := @WriteValueB_Base.wv_two_in_split fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_fresh_block := @WriteValueB_Base.wv_fresh_block fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_lam_keep := @WriteValueB_Base.wv_lam_keep fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_fp_sub := @WriteValueB_Base.wv_fp_sub fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_block_shadow_range := @WriteValueB_Base.wv_block_shadow_range fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_hblock_shadow := @WriteValueB_Base.wv_hblock_shadow fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ra_sub := @WriteValueB_Base.wv_ra_sub fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_fs_mod8 := @WriteValueB_Base.wv_fs_mod8 fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ra_cur := @WriteValueB_Base.wv_ra_cur fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_tvis_cur := @WriteValueB_Base.wv_tvis_cur fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ev_first := @WriteValueB_Base.wv_ev_first fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ret_pos_one := @WriteValueB_Base.wv_ret_pos_one fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ret_pos_app := @WriteValueB_Base.wv_ret_pos_app fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.

Section cl.
Variable CTX0 : list (list Z).
Hypothesis PUT : tput_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis PUTSTR : tput_string_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis INDENT : tindent_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling, discharged at the instance by the allocator-model owner's
   preset_head_wide, PALibB.exvi_eh_head): a high-memory user pointer is at least kHighMemBeg + 16, which
   YGcfStr.amem_range8 asks (cstr_ok) *)
Hypothesis HW : prh_head_wide.
(* callee text: the strlen wrapper (YGcallMxmn.astrlen_realizes_xrom, the engine's row, owner c-omx-alloc); its ONE
   use is aj_strlen_at_xrom in wv_leaf_num *)
Hypothesis STRLEN : YGcallMxmn.astrlen_realizes_xrom SEGS B ARx pa_relro_lo pa_relro_hi (SIGMA AS___wrap_strlen).

(* WriteValueB_Call's lemmas at this Section's variables *)
Let wv_neg_mod16 := @WriteValueB_Call.wv_neg_mod16 fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT.
Let wv_tail_put := @WriteValueB_Call.wv_tail_put fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT.
Let wv_put_close := @WriteValueB_Call.wv_put_close fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT.
Let wv_tail_gen := @WriteValueB_Call.wv_tail_gen fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT.
Let wv_s0_pres := @WriteValueB_Call.wv_s0_pres fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT.
Let wv_tail_put_string := @WriteValueB_Call.wv_tail_put_string fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT.
Let wv_call_put := @WriteValueB_Call.wv_call_put fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT.
Let wv_call_indent := @WriteValueB_Call.wv_call_indent fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT.
Let wv_call_put_string := @WriteValueB_Call.wv_call_put_string fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT.
Let wv_call_self := @WriteValueB_Call.wv_call_self fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT.

(* the keep of one run: the run's start state has ONE write window, the own frame [sp - 192, sp) at atom 2 (every
   other region's window is empty), so a run that starts from a memory kept outside P keeps every byte outside P *)
Ltac wv_keep_run HFr0 K0 K1 m0 P Usp :=
  lazymatch type of HFr0 with
  | frame_of ?E ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m2 a = aview SEGS H m0 a);
    [ refine (wv_keep_frame H E rs m0 m1 m2 P K0 HFr0 _);
      let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
      intros a (r & Hr & Ha);
      lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end;
      repeat (destruct Hr as [<- | Hr];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?Usp in Ha; unfold wv_wr; lia |]);
      destruct Hr
    | ]
  end.

(* the write premise of a run from a state whose only window is the own frame, the journal at sp0 = spZ regs + d *)
Ltac wv_awr_tac Usp d :=
  cbn [ss_mem]; repeat first
    [ apply awr_ok_nil
    | eapply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- d));
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?Usp; lia
      | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ].

(* a leaf's own stretch, from the entry to its tail call, crosses no call that can realloc (the number leaf's strlen
   call cannot): it runs at wle (the plain runners) to a state whose continuation, the tail call, runs at wle' SEGS RZ_cf (the callee may realloc) *)
Lemma wv_pre_lift : forall W c (Q : world SEGS -> config -> Prop),
  SRr SEGS W c (fun W' c' => SRr' SEGS RZ_cf W' c' Q) -> SRr' SEGS RZ_cf W c Q.
Proof.
intros W c Q H. apply (SRr'_bind SEGS RZ_cf W c _ Q (SRr_SRr' SEGS RZ_cf W c _ H)).
intros W' c' _ H'. exact H'.
Qed.

Lemma wv_leaf_lit : forall t, (t = PjTree.JNull \/ t = PjTree.JFalse \/ t = PjTree.JTrue) ->
  forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch o v pretty dep d buf (st : WriterApp.wst) D Lam peak ran gmo gow STKv,
  200 <= STKv -> STK_put <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wvpieces t (negb (pretty =? 0)) dep))) ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 dep ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) mem) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wvpieces t (negb (pretty =? 0)) dep)) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wvpieces t (negb (pretty =? 0)) dep))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs S (prhWriter_evs [] st (WriterValue.wvpieces t (negb (pretty =? 0)) dep)) ->
  SRr' SEGS RZ_cf W (cfg_at SEGS (SIGMA AS_write_value) regs mem md)
    (fpostWmR B ARx SK (wle' SEGS RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
          room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran gmo gow o buf st (WriterValue.wvpieces t (negb (pretty =? 0)) dep)
            ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
            (prhWriter_k ok st (WriterValue.wvpieces t (negb (pretty =? 0)) dep)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterValue.wvpieces t (negb (pretty =? 0)%Z) dep)))%nat rp_H0 hist' S')).
Proof.
intros t Ht rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch o v pretty dep d buf st D Lam peak ran gmo gow STKv
  HSTK HSTKp HPRE Hroom Hrp Hos Hcons Hcl H10 H11 H12 H13 Hcut Hch0 HWIN Ho1 Ho2 HOUT HLED Hev HNODE HLOC HRA HD Hoff
  Hwmax Hhead Hlive.
apply wv_pre_lift.
pose proof HPRE as (HPREx & HRO & HTOP).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
assert (HPF : 0 <= pi_frame F_put) by (vm_compute; congruence).
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wr (spZ regs) a) by (intros a Ha; unfold wv_wr; lia).
(* The location premise, its ONE use *)
destruct (wv_loc ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow buf v
  ltac:(lia) HPREx HLED HLOC) as (Hv4096 & Hv47 & Hvst & Hband & Hvimg).
(* the journal, widened to the caller window, and the memory invariant of the m-form post *)
assert (HJ : ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W mem md 0)
  by (eapply ajournal_x_init_W;
      [exact HPREx | split; [exact Hd0 | split; [exact Hd16 | split; [exact Hdtop | exact Hdpres]]]]).
assert (PLAWI : srr_inv_laws SEGS (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m))
  by (apply srr_inv_laws_imp; apply srr_inv_laws_memnorm_k).
assert (HPM : (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) mem) by (cbv beta; exact (fun h => h)).
pose proof HNODE as HNODE0.
(* the literal leaf at tag tg (jump-table index kn), the literal formed by the PAddHi at slot, of bytes bs: from the
   entry to the tail `put` and the post *)
let run tg kn slot bs := idtac;
  destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody);
  destruct Hhdr as ((Hv8 & Hrwr) & (Rtg & Vtg) & (Rnum & Vnum) & (Rstr & Vstr) & (Rkids & Vkids) &
    (Rkeys & Vkeys) & (Rnn & Vnn) & (Rcap & Vcap));
  destruct (HJT kn ltac:(lia)) as (HTv & HTr & HTlo & HThi & HTg & HTc & HTro);
  change (4 * Z.of_nat kn) with (4 * tg) in HTv, HTr, HTlo, HThi, HTg, HTc, HTro;
  assert (HTvm : val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 2) + WV_JT + 4 * tg) 4 (WV_JTW (Z.to_nat tg)))
    by (apply (wv_ro_val W mem _ 4%nat); [exact HRO | | exact HTv];
        intros i Hi; destruct (HTro i ltac:(lia)) as (_ & R1 & R2 & R3);
        split; [exact R1 | split; [exact R2 | exact R3]]);
  assert (HTn : VAL (A_OBJ 2) + WV_JT + 4 * tg + 4 <= v \/ v + 56 <= VAL (A_OBJ 2) + WV_JT + 4 * tg)
    by (destruct (wv_disj_img_n (VAL (A_OBJ 2) + WV_JT + 4 * tg) 4 v 56 ltac:(lia) ltac:(lia)
          ltac:(intros i Hi; exact (proj1 (HTro i Hi))) Hvimg) as [HL | HR]; [right; lia | left; lia]);
  (* the seated entry state at tag tg *)
  destruct (wv_seat ly S Hp W regs mem md ch STKv o v pretty dep tg str kids keys nn ltac:(lia) HPREx H10 H11 H12 H13
    Hv8 Hv4096 Hv47 Hvst Hband ltac:(intros a Ha; split; [exact (Hvimg a Ha) | exact (Hrwr a Ha)])
    Vtg ltac:(lia) Vstr Rstr Vkids Rkids Vkeys Rkeys Vnn Rnn HRA
    HTvm HTr ltac:(split; lia) ltac:(left; lia) HTg HTc HTn ltac:(vm_compute; reflexivity)) as [HS SHOK];
  set (E := wv_E regs v str kids keys nn (WV_JTW (Z.to_nat tg))) in *;
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wv_E; apply Eimg_env);
  assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat tg)))) k)
    by (intros k Hk; subst E; unfold wv_E; apply Eimg_low; exact Hk);
  assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
  assert (Usp : bv_unsigned (ew E 2) = spZ regs)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity);
  assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl));
  assert (HAE : env_agree 32 (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat tg)))) E)
    by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | reflexivity]);
  assert (K00 : forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a)
    by (intros; reflexivity);
  unfold cfg_at; rewrite Hent; change (w64 (BASE + AF_write_value)) with (Z_to_bv 64 (BASE + AF_write_value));
  (* entry -> the switch's jr *)
  paj_run_tok_x_inv (@paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
    (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS HJ SHOK HPM WV_Bspan;
  [ eapply (wv_awr E tg _ _ _ _ _ _ _ (spZ regs)); [exact Usp | lia | lia] | ];
  wv_keep_run HFr K00 K1 mem (wv_wr (spZ regs)) Usp; clear HF HFr HG;
  (* the switch's indirect jump, and the reseat at the case offset *)
  prreg HS (11%bv : bv 5) R11;
  assert (E38 : ew E 38 = Z_to_bv 64 (WV_JTW (Z.to_nat tg)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6));
  assert (EJ : ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)))
    by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia);
  destruct (wv_jr_target E (Z.to_nat tg) E38 EJ HTr) as (Ht & Hr & He);
  eapply (wv_jr_step E _ _ W _ _ (BASE + AF_wv_case kn) HS);
  [ vm_compute; reflexivity | reflexivity | rewrite R11; exact Ht | exact Hr | exact He | ];
  let mat' := fresh "mat" in let ms1 := fresh "ms" in let Hms1 := fresh "Hms" in let HS1 := fresh "HS1" in
  intros mat' ms1 Hms1 HS1; subst ms1;
  pose proof (wv_pi_at E _ (AF_wv_case kn) _ HS1) as HS2; clear HS1;
  assert (HJ2 := HJ);
  eapply (ajournal_x_materialize (SK := SK)) with (X := mat') in HJ2;
  [| first [exact LAWS | exact pa_segs_low | idtac] ..];
  clear HJ;
  (* the case to the tail put *)
  paj_run_to_tok_x_inv (@paj_run_to_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
    (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan
    (AF_write_value + 4 * 268);
  [ wv_awr_tac Usp d | ];
  wv_keep_run HFr K1 K2 mem (wv_wr (spZ regs)) Usp; clear HF HFr HG;
  (* the tail jump itself (A 0x86b00 `j put`): one more run step stops at put's entry *)
  paj_run_tok_x_inv (@paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
    (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan;
  [ wv_awr_tac Usp d | ];
  wv_keep_run HFr K2 K3 mem (wv_wr (spZ regs)) Usp; clear HF HFr HG;
  (* the registers at put's entry *)
  prreg HS2 (10%bv : bv 5) Ra0; prreg HS2 (11%bv : bv 5) Ra1; prreg HS2 (12%bv : bv 5) Ra2;
  prreg HS2 (1%bv : bv 5) Rra;
  lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?msx) =>
    assert (HAP : aregs_preserved regs (ms_regs msx))
      by (eapply (aregs_preserved_of_st_ok SEGS (w_H W) E _ _ regs _); [exact HS2 | exact HAE | vm_compute; reflexivity]);
    assert (Rrac : getr (ms_regs msx) 1 = getr regs 1) by (rewrite Rra; exact E1);
    assert (H10c : getr (ms_regs msx) 10 = w64 o) by (rewrite Ra0, E10; exact H10);
    assert (HAT : wv_addhi_atom slot = A_OBJ 2) by (vm_compute; reflexivity);
    assert (H11c : getr (ms_regs msx) 11 = w64 (WV_STR slot))
      by (rewrite Ra1; unfold WV_STR; rewrite HAT; rewrite HEI by (unfold A_OBJ, A_TEXT, A_LIM; lia);
          let off := eval vm_compute in (wv_addhi_off slot) in change (wv_addhi_off slot) with off; reflexivity);
    assert (H12c : getr (ms_regs msx) 12 = w64 (Z.of_nat (length bs))) by (rewrite Ra2; reflexivity);
    pose proof (proj1 HJ2) as HARc;
    assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem msx)))
      by (apply (wv_arodata_keep W W mem (ms_mem msx) (wv_wr (spZ regs))); [exact HRO | exact K3 | exact HLOW]);
    destruct (HLIT slot bs ly S Hp W (ms_mem msx) _
      ltac:(unfold wv_lits; cbn [In]; repeat (first [left; reflexivity | right])) HARc HROc)
      as (Hsrc & Hkept & Himg);
    pose proof (wv_lit_home ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow buf
      (WriterApp.w_cap st) (WV_STR slot) (Z.of_nat (length bs)) HAR HLED Hbufin (proj1 Hcap0) ltac:(vm_compute; reflexivity)
      Hkept ltac:(intros a Ha; replace a with (WV_STR slot + (a - WV_STR slot)) by lia; apply Himg; lia)) as Hhome;
    assert (Hch0c : spZ regs + 16 <= o ->
        exists ra, rdword (aview SEGS (w_H W) (ms_mem msx)) (o - 8) = Some ra /\
          exists nfp, rdword (aview SEGS (w_H W) (ms_mem msx)) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling)
      by (intros Hge; apply (wv_reca_keep (aview SEGS (w_H W) mem)); [| exact (Hch0 Hge)];
          intros a Ha; apply K3; [lia | unfold wv_wr; lia]);
    pmkst HS2; apply SRr_ret;
    exact (wv_put_close rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v _ D Lam peak ran gmo gow buf
      st (WV_STR slot) bs (ms_mem msx) _ (ms_regs msx) HSTK HSTKp HPRE Hroom Hrp Hos Hcons Hcl HWIN Ho1 Ho2 HLED HOUT
      HNODE0 HLOC HD Hoff HJ2 K3 HAP Rrac H10c H11c H12c Hcut Hch0c Hev Hsrc Hhome Hwmax Hhead Hlive HPM)
  end
in
destruct Ht as [-> | [-> | ->]];
[ run 0 0%nat 243%nat [110; 117; 108; 108]
| run 1 1%nat 247%nat [102; 97; 108; 115; 101]
| run 2 2%nat 224%nat [116; 114; 117; 101] ].
Qed.

(* ---- THE STRING LEAF (case 61) and THE NUMBER LEAF (case 105): the string / number text lives in a ledger block
   (pj_nodeR's pj_cstrR: In (str, k) Lam), whose user pointer the code loads from v + 16 and tests against 0 (the
   0 arm is refuted by the ledger: the block's base is at least 4096). The string tail-calls put_string (slot 86);
   the number calls the strlen wrapper (slot 116) and tail-calls put (slot 236). ---- *)

(* a ledger block's user range: 4096 or above, below alloc_ceiling *)
Lemma wv_lam_low : forall ly S Hp W mem md Lam peak cnt fail ran gmo gow a k,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran gmo gow -> In (a, k) Lam ->
  4096 <= a /\ 0 <= k /\ a + k <= YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran gmo gow a k HAR HLED Hin.
pose proof cf_head_nonneg as Hh0.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
pose proof (HF (a, k) Hin) as (Hk0 & Hbl & _). cbn [fst snd] in Hk0, Hbl.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hbl)
  as (_ & H4096 & Hpc & _).
assert (Hrq : k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
lia.
Qed.

(* the shadow hull of a sub-range (YGcfHeadSh.v's shadow_hull_vis_sub_cf, the same proof; that file is not Required
   here) *)
Lemma wv_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia))
  as D4.
lia.
Qed.

(* a byte list survives a change that keeps its bytes' view *)
Lemma wv_garr8_keep : forall (H H' : word -> bool) (m m' : word -> option byte) a l,
  (forall j, (j < length l)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
refine (wv_vm_keep H H' m m' (a + Z.of_nat j) 1%nat _ _ Hv).
intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat]. rewrite Z.add_0_r. exact (Hk j Hj).
Qed.

(* a ledger block's granule bound, by AR_laws_x's alx_blocks_ceil8 (its ONE use: a tree string / a number's text
   handed on as cstr_ok / src_rd): the block (a - cf_head, k + cf_head) is live, so
   a - cf_head + req_size (k + cf_head) + 8 <= alloc_ceiling *)
Lemma wv_blk_ceil7 : forall ly S Hp W mem md Lam peak cnt fail ran gmo gow a k,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran gmo gow -> In (a, k) Lam ->
  a + k + 7 <= YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran gmo gow a k HAR HLED Hin.
pose proof cf_head_nonneg as Hh0.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
pose proof (HF (a, k) Hin) as (Hk0 & Hbl & _). cbn [fst snd] in Hk0, Hbl.
pose proof (alx_blocks_ceil8 SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hbl) as Hc.
assert (Hrq : k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
clear - Hc Hrq. lia.
Qed.

(* THE TREE'S STRING IS A C STRING THE RUNTIME MAY READ: a ledger block (str, k) holding s and its NUL, with
   tree_vis_cf's facts for (str, k) and the granule gap `str + k + 7 <= alloc_ceiling`, is cstr_ok. amem_range8's
   high start: the block base and str are both 16-aligned (alx_blocks, prh_hblock), so 8 <= cf_head gives
   cf_head >= 16. *)
Lemma wv_cstr_blk : forall ly S Hp W0 mem0 md0 Lam peak cnt fail ran gmo gow (W : world SEGS) m str k s,
  ARx ly S Hp W0 mem0 md0 -> prh_ledger B ly S Hp W0 mem0 Lam peak cnt fail ran gmo gow ->
  In (str, k) Lam -> Z.of_nat (length s) + 1 <= k -> Z.of_nat (length s) + 1 < 2 ^ 32 ->
  Forall (fun c => 0 < c < 256) s -> garr8 SEGS (mrestrict (w_H W) m) str (s ++ [0]) ->
  str + k + 7 <= YM05.alloc_ceiling ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF str k ->
  (0 < k -> shadow_hull_vis (aview SEGS (w_H W) m) str k) ->
  (forall x, str <= x < (str + k + 7) / 8 * 8 -> aview SEGS (w_H W) m x <> None) ->
  cstr_ok W m str s.
Proof.
intros ly S Hp W0 mem0 md0 Lam peak cnt fail ran gmo gow W m str k s HAR HLED Hin Hlen Hlen32 Hrng Hg Hgap HRA HHULL HVIS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0. pose proof HW as HW8. unfold prh_head_wide in HW8.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
pose proof (HF (str, k) Hin) as (Hk0 & Hbl & _ & Ha16 & _). cbn [fst snd] in Hk0, Hbl, Ha16.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W0 mem0 md0 (str - cf_head) (k + cf_head) HAR Hbl)
  as (H16 & H4096 & Hpc & Happ & _).
assert (Hrq : k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
unfold cstr_ok, cstr. set (n := Z.of_nat (length s)) in *.
split; [split; [exact Hg | rewrite Forall_forall in Hrng |- *; intros c Hc; specialize (Hrng c Hc); lia] |].
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ unfold YGcfStr.amem_range8. rewrite C3, C4, C5.
  unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ. rewrite C3 in Happ.
  destruct Happ as (_ & [Hlo | (Hh1 & Hh2)]); [left; lia | right].
  apply Z.mod_divide in H16 as [q1 Hq1]; [|lia]. apply Z.mod_divide in Ha16 as [q2 Hq2]; [|lia].
  split; lia. }
split; [eapply range_addressable_sub; [exact HRA | lia | lia] |].
split; [apply (wv_hull_sub _ str k str (n + 1) (HHULL ltac:(lia))); lia |].
intros x Hx. apply HVIS.
assert (Hn0 : 0 <= n) by (subst n; lia). clearbody n.
pose proof (Z.div_mod (str + n) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (str + n) 8 ltac:(lia)) as D1b.
assert (D3 : (str + n) / 8 + 1 <= (str + k + 7) / 8).
{ replace ((str + n) / 8 + 1) with ((str + n + 1 * 8) / 8) by (rewrite Z.div_add by lia; reflexivity).
  apply Z.div_le_mono; lia. }
clear - Hx D1 D1b D3 Hn0 Hlen. lia.
Qed.

(* two distinct ledger blocks are apart (the sep half of alx_blocks), so a tree block other than the buffer misses it *)
Lemma wv_blk_apart : forall ly S Hp W mem md Lam peak cnt fail ran gmo gow a k buf cap n,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran gmo gow ->
  In (a, k) Lam -> a <> buf -> (cap <> 0 -> In (buf, cap) Lam) -> 0 <= n -> n <= k ->
  cap = 0 \/ a + n <= buf \/ buf + cap <= a.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran gmo gow a k buf cap n HAR HLED Hin Hab Hbuf Hn Hnk.
destruct (Z.eq_dec cap 0) as [->|Hc0]; [left; reflexivity|]. right.
pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HF.
pose proof (HF (a, k) Hin) as (Hk0 & Hbl & _). pose proof (HF (buf, cap) (Hbuf Hc0)) as (Hc00 & Hblb & _).
cbn [fst snd] in Hk0, Hbl, Hc00, Hblb.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hbl)
  as (_ & _ & _ & _ & _ & Hpw).
assert (Hrq : k + cf_head <= req_size (k + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
assert (Hrqb : cap + cf_head <= req_size (cap + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (cap + cf_head) 0); lia).
pose proof cf_head_nonneg as Hh0.
destruct (wv_pairwise_in2 zdisjoint _ (a - cf_head, req_size (k + cf_head))
    (buf - cf_head, req_size (cap + cf_head)) Hpw
    (in_map (fun b => (fst b, req_size (snd b))) _ _ Hbl)
    (in_map (fun b => (fst b, req_size (snd b))) _ _ Hblb)
    ltac:(intros E; injection E as E1 _; lia)) as [Hd|Hd];
  unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia.
Qed.

(* ---- FROM THE STATE AT THE TAIL put_string TO THE WHOLE POST (wv_put_close's twin): the leaf supplies the string's
   cstr_ok / kept_at / apartness at the call memory, the frames count and the room ---- *)
Lemma wv_put_string_close : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf (st : WriterApp.wst) s (bs : list Z)
    memc mdc regsc,
  200 <= STKv -> STK_put_string <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st (WriterSpec.spieces bs))) ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
  prhWriter_out W mem Lam o buf st ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  aregs_preserved regs regsc -> getr regsc 1 = getr regs 1 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  s0Z regs = o \/ s0Z regs < YM05.alloc_ceiling ->
  cstr_ok W memc s bs ->
  kept_at B Lam s (Z.of_nat (length bs) + 1) ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterSpec.spieces bs)) ->
  (WriterApp.w_cap st = 0 \/ s + Z.of_nat (length bs) + 1 <= buf \/ buf + WriterApp.w_cap st <= s) ->
  Z.of_nat (length (frames S)) < fs_frames 0 ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (WriterSpec.wstr bs)) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs S (prhWriter_evs [] st (WriterSpec.spieces bs)) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc) ->
  SRr' SEGS RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put_string)) memc (seg_rom SEGS)) mdc)
    (fpostWFmR B ARx SK (wle' SEGS RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' => room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran gmo gow o buf st (WriterSpec.spieces bs) ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (WriterSpec.spieces bs)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterSpec.spieces bs)))%nat rp_H0 hist' S')).
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf st s bs
  memc mdc regsc HSTK HSTKp HPRE Hroom Hrp Hos Hcl Hcons HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ HKEEP
  HAP Hrac H10 H11 Hcut Hch0 HS0e Hstr Hkept Hev Hapart Hfr0 Hwmax Hhead Hlive HMN.
pose proof HPRE as (HPREx & HRO & HTOP).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
assert (HLOW8 : forall a, 0 <= a < YM05.alloc_ceiling + 8 -> ~ wv_wr (spZ regs) a)
  by (intros a Ha; unfold wv_wr; lia).
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wr (spZ regs) a)
  by (intros a Ha; unfold wv_wr; lia).
assert (HOFF : forall a, o <= a < o + 32 -> 0 <= a < 2 ^ 64 /\ ~ wv_wr (spZ regs) a)
  by (intros a Ha; split; [lia | unfold wv_wr; lia]).
assert (Hsp : spZ regsc = spZ regs)
  by (unfold spZ; f_equal; exact (HAP 2 ltac:(unfold acallee_saved; lia))).
assert (Hgpc : getr regsc 3 = w64 (as_gp B))
  by (rewrite <- Hgp; exact (HAP 3 ltac:(unfold acallee_saved; lia))).
assert (Htpc : getr regsc 4 = w64 (as_tp B))
  by (rewrite <- Htp; exact (HAP 4 ltac:(unfold acallee_saved; lia))).
assert (Hs0c : s0Z regsc = s0Z regs)
  by (unfold s0Z; f_equal; exact (HAP 8 ltac:(unfold acallee_saved; lia))).
assert (HFOOT : forall x, pj_footR v D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ wv_wr (spZ regs) x)
  by (apply (wv_foot_wr ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow buf);
      [lia | exact HPREx | exact HLED | exact HLOC | exact HD]).
assert (HNODEc : pj_nodeR SEGS (mrestrict (w_H W) memc) (prh_lin Lam) v t D).
{ apply (wv_nodeR_keep W W mem memc Lam v t D HNODE).
  - intros x Hx. destruct (HFOOT x Hx) as (A1 & A2 & _). split; assumption.
  - intros x Hx. destruct (HFOOT x Hx) as (A1 & _ & A3). apply HKEEP; assumption. }
assert (HOUTc : prhWriter_out W memc Lam o buf st)
  by (apply (wv_out_keep ly S Hp W W mem memc md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow o buf st
        (wv_wr (spZ regs))); [exact HAR | exact HLED | exact HOUT | exact HKEEP | exact HLOW | exact HOFF]).
assert (HLEDc : prh_ledger B ly S Hp W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow)
  by (apply (wv_led_keep ly S Hp W md mem memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow
        (wv_wr (spZ regs))); [exact HAR | exact HLED | exact HKEEP | exact HLOW8]).
assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc))
  by (apply (wv_arodata_keep W W mem memc (wv_wr (spZ regs))); [exact HRO | exact HKEEP | exact HLOW]).
assert (HCHc : achain ly (aview SEGS (w_H W) memc) (spZ regs) (s0Z regsc) ch).
{ rewrite Hs0c. apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hchain);
    [lia | lia |]. intros a Ha. apply HKEEP; [lia | unfold wv_wr; lia]. }
exact (wv_tail_put_string rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow
  buf st s bs memc mdc regsc ltac:(lia) HSTKp HPRE Hroom Hrp Hos Hcl Hcons HWIN Ho1 Ho2 HLED HOUT HNODEc HLOC HD Hoff HJ
  ltac:(intros a Ha; apply HKEEP; [lia | unfold wv_wr; lia])
  HAP Hsp Hrac Hgpc Htpc HCHc HROc H10 H11 Hcut Hch0 ltac:(rewrite (wv_s0_pres _ _ HAP); exact HS0e)
  HOUTc HLEDc Hstr Hkept Hev Hapart Hfr0 Hwmax Hhead Hlive HMN).
Qed.

Lemma wv_leaf_str : forall s,
  forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch o v pretty dep d buf (st : WriterApp.wst) D Lam peak ran gmo gow STKv,
  200 <= STKv -> STK_put_string <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) dep))) ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 dep ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) mem) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  s0Z regs = o \/ s0Z regs < YM05.alloc_ceiling ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) dep)) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v (PjTree.JStr s) D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  prhWriter_tree_vis W mem D ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  Z.of_nat (length (frames S)) < fs_frames 0 ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) dep))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs S (prhWriter_evs [] st (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) dep)) ->
  SRr' SEGS RZ_cf W (cfg_at SEGS (SIGMA AS_write_value) regs mem md)
    (fpostWFmR B ARx SK (wle' SEGS RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
          room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v (PjTree.JStr s) D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran gmo gow o buf st
            (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) dep) ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
            (prhWriter_k ok st (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) dep)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)%Z) dep)))%nat
            rp_H0 hist' S')).
Proof.
intros s rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch o v pretty dep d buf st D Lam peak ran gmo gow STKv
  HSTK HSTKp HPRE Hroom Hrp Hos Hcons Hcl H10 H11 H12 H13 Hcut Hch0 HS0 HWIN Ho1 Ho2 HOUT HLED Hev HNODE HLOC HRA HTV HD Hoff
  Hfr0 Hwmax Hhead Hlive.
apply wv_pre_lift.
pose proof HPRE as (HPREx & HRO & HTOP).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
assert (HPF : 0 <= pi_frame F_put_string) by (vm_compute; congruence).
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wr (spZ regs) a) by (intros a Ha; unfold wv_wr; lia).
destruct (wv_loc ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow buf v
  ltac:(lia) HPREx HLED HLOC) as (Hv4096 & Hv47 & Hvst & Hband & Hvimg).
assert (HJ : ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W mem md 0)
  by (eapply ajournal_x_init_W;
      [exact HPREx | split; [exact Hd0 | split; [exact Hd16 | split; [exact Hdtop | exact Hdpres]]]]).
assert (PLAWI : srr_inv_laws SEGS (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m))
  by (apply srr_inv_laws_imp; apply srr_inv_laws_memnorm_k).
assert (HPM : (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) mem) by (cbv beta; exact (fun h => h)).
pose proof HNODE as HNODE0.
destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody).
destruct Hhdr as ((Hv8 & Hrwr) & (Rtg & Vtg) & (Rnum & Vnum) & (Rstr & Vstr) & (Rkids & Vkids) &
  (Rkeys & Vkeys) & (Rnn & Vnn) & (Rcap & Vcap)).
destruct Hbody as (_ & _ & _ & _ & k & Hcs & ->).
pose proof Hcs as (Hlam & Hlen & Hlen32 & Hrng & Hgs). unfold prh_lin in Hlam.
destruct (wv_lam_low ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow str k HAR HLED Hlam)
  as (Hs4096 & Hk0 & Hsk).
pose proof (wv_blk_ceil7 ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow str k
  HAR HLED Hlam) as Hgap1.
destruct (HJT 4%nat ltac:(lia)) as (HTv & HTr & HTlo & HThi & HTg & HTc & HTro).
change (4 * Z.of_nat 4) with (4 * 4) in HTv, HTr, HTlo, HThi, HTg, HTc, HTro.
assert (HTvm : val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 2) + WV_JT + 4 * 4) 4 (WV_JTW (Z.to_nat 4)))
  by (apply (wv_ro_val W mem _ 4%nat); [exact HRO | | exact HTv];
      intros i Hi; destruct (HTro i ltac:(lia)) as (_ & R1 & R2 & R3);
      split; [exact R1 | split; [exact R2 | exact R3]]).
assert (HTn : VAL (A_OBJ 2) + WV_JT + 4 * 4 + 4 <= v \/ v + 56 <= VAL (A_OBJ 2) + WV_JT + 4 * 4)
  by (destruct (wv_disj_img_n (VAL (A_OBJ 2) + WV_JT + 4 * 4) 4 v 56 ltac:(lia) ltac:(lia)
        ltac:(intros i Hi; exact (proj1 (HTro i Hi))) Hvimg) as [HL | HR]; [right; lia | left; lia]).
destruct (wv_seat ly S Hp W regs mem md ch STKv o v pretty dep 4 str kids keys nn ltac:(lia) HPREx H10 H11 H12 H13
  Hv8 Hv4096 Hv47 Hvst Hband ltac:(intros a Ha; split; [exact (Hvimg a Ha) | exact (Hrwr a Ha)])
  Vtg ltac:(lia) Vstr Rstr Vkids Rkids Vkeys Rkeys Vnn Rnn HRA
  HTvm HTr ltac:(split; lia) ltac:(left; lia) HTg HTc HTn ltac:(vm_compute; reflexivity)) as [HS SHOK].
set (E := wv_E regs v str kids keys nn (WV_JTW (Z.to_nat 4))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wv_E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat 4)))) k)
  by (intros k0 Hk; subst E; unfold wv_E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E34 : ew E 34 = Z_to_bv 64 str) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat 4)))) E)
  by (split; [intros k0 Hk; apply EL; unfold A_TEXT; lia | reflexivity]).
assert (K00 : forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a)
  by (intros; reflexivity).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_write_value)) with (Z_to_bv 64 (BASE + AF_write_value)).
(* entry -> the switch's jr *)
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS HJ SHOK HPM WV_Bspan;
[ eapply (wv_awr E 4 _ _ _ _ _ _ _ (spZ regs)); [exact Usp | lia | lia] | ].
wv_keep_run HFr K00 K1 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
prreg HS (11%bv : bv 5) R11.
assert (E38 : ew E 38 = Z_to_bv 64 (WV_JTW (Z.to_nat 4)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (EJ : ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)))
  by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
destruct (wv_jr_target E (Z.to_nat 4) E38 EJ HTr) as (Ht & Hr & He).
eapply (wv_jr_step E _ _ W _ _ (BASE + AF_wv_case 4) HS);
[ vm_compute; reflexivity | reflexivity | rewrite R11; exact Ht | exact Hr | exact He | ].
intros mat1 ms1 Hms1 HS1. subst ms1.
pose proof (wv_pi_at E _ (AF_wv_case 4) _ HS1) as HS2. clear HS1.
assert (HJ2 := HJ).
eapply (ajournal_x_materialize (SK := SK)) with (X := mat1) in HJ2;
[| first [exact LAWS | exact pa_segs_low | idtac] ..].
clear HJ.
(* the case: the shadow check of v + 16, the load of str, and the stop at `bnez a1` (MEASURED: the run stops at
   write_value + 4 * 68 with a1 = SOff 34 0, the str atom) *)
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan;
[ wv_awr_tac Usp d | ].
wv_keep_run HFr K1 K2 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
psrr_branch_tok (@paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) BR HS2 SHOK WV_Bspan.
2:{ (* str = 0: refuted, a ledger block's user pointer is at least 4096 *)
  exfalso.
  rewrite ?branch_ne_U, ?branch_eq_U, (U_atom E 34 str E34 Rstr), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
  assert (Hs0 : (str =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hs0' : (0 =? str) = false) by (apply Z.eqb_neq; lia).
  rewrite ?Hs0, ?Hs0' in Hc. cbn in Hc. discriminate Hc. }
(* str <> 0: the epilogue, then the tail `j put_string` (write_value + 4 * 86) and put_string's entry *)
paj_run_to_tok_x_inv (@paj_run_to_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan
  (AF_write_value + 4 * 207);
[ wv_awr_tac Usp d | ].
wv_keep_run HFr K2 K3 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan;
[ wv_awr_tac Usp d | ].
wv_keep_run HFr K3 K4 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
prreg HS2 (10%bv : bv 5) Ra0. prreg HS2 (11%bv : bv 5) Ra1. prreg HS2 (1%bv : bv 5) Rra.
lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HAP : aregs_preserved regs (ms_regs msx))
    by (eapply (aregs_preserved_of_st_ok SEGS (w_H W) E _ _ regs _); [exact HS2 | exact HAE | vm_compute; reflexivity]);
  assert (Rrac : getr (ms_regs msx) 1 = getr regs 1) by (rewrite Rra; exact E1);
  assert (H10c : getr (ms_regs msx) 10 = w64 o) by (rewrite Ra0, E10; exact H10);
  assert (H11c : getr (ms_regs msx) 11 = w64 str) by (rewrite Ra1, E34; reflexivity);
  (* the string at the call memory: the tree's block (str, k), kept below alloc_ceiling *)
  assert (HTVc : prhWriter_tree_vis W (ms_mem msx) [(str, k)])
    by (exact (wv_tree_vis_keep W W mem (ms_mem msx) [(str, k)] (wv_wr (spZ regs)) HTV K4 HLOW));
  destruct (HTVc str k (or_introl eq_refl)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7);
  assert (Hgsc : garr8 SEGS (mrestrict (w_H W) (ms_mem msx)) str (s ++ [0]))
    by (apply (wv_garr8_keep (w_H W) (w_H W) mem (ms_mem msx) str (s ++ [0])); [|exact Hgs];
        intros j Hj; rewrite length_app in Hj; cbn [length] in Hj; apply K4; [lia | unfold wv_wr; lia]);
  pose proof (wv_cstr_blk ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow W (ms_mem msx)
    str k s HAR HLED Hlam Hlen Hlen32 Hrng Hgsc Hgap1 T5 T6 T7) as Hcstr;
  assert (Hkept : kept_at B Lam str (Z.of_nat (length s) + 1)) by (left; exists str, k; split; [exact Hlam | lia]);
  pose proof (wv_blk_apart ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow str k buf
    (WriterApp.w_cap st) (Z.of_nat (length s) + 1) HAR HLED Hlam (proj2 (HD str k (or_introl eq_refl))) Hbufin
    ltac:(lia) Hlen) as Hapart; rewrite Z.add_assoc in Hapart;
  assert (Hch0c : spZ regs + 16 <= o ->
      exists ra, rdword (aview SEGS (w_H W) (ms_mem msx)) (o - 8) = Some ra /\
        exists nfp, rdword (aview SEGS (w_H W) (ms_mem msx)) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling)
    by (intros Hge; apply (wv_reca_keep (aview SEGS (w_H W) mem)); [| exact (Hch0 Hge)];
        intros a Ha; apply K4; [lia | unfold wv_wr; lia]);
  pmkst HS2; apply SRr_ret;
  exact (wv_put_string_close rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v _ _ Lam peak
    ran gmo gow buf st str s (ms_mem msx) _ (ms_regs msx) HSTK HSTKp HPRE Hroom Hrp Hos Hcl Hcons HWIN Ho1 Ho2 HLED HOUT
    HNODE0 HLOC HD Hoff HJ2 K4 HAP Rrac H10c H11c Hcut Hch0c HS0 Hcstr Hkept Hev Hapart Hfr0 Hwmax Hhead Hlive HPM)
end.
Qed.

(* ---- the number leaf's helpers: the strlen call's byte premises (FuzzStrdup.v's sd_garr8_aview / sd_first_byte /
   sd_src_ok, the same proofs), a put source from a C string, and the close after a call that wrote below the own
   frame ---- *)
Lemma wv_garr8_aview : forall (W : world SEGS) m p l j, garr8 SEGS (mrestrict (w_H W) m) p l -> (j < length l)%nat ->
  aview SEGS (w_H W) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m p l j H Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.

Lemma wv_first_byte : forall (W : world SEGS) m p cs, cstr W m p cs ->
  first_byte SEGS W m p (Z.of_nat (length cs) + 1) 0 (Z.of_nat (length cs)).
Proof.
intros W m p cs [Hg Hnz]. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) cs 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (wv_garr8_aview W m p (cs ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn; lia).
    rewrite app_nth1 by lia. reflexivity.
  + apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
- intros _.
  rewrite (wv_garr8_aview W m p (cs ++ [0]) (length cs) Hg) by (rewrite length_app; cbn; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma wv_src_ok : forall (W : world SEGS) regs m p l, garr8 SEGS (mrestrict (w_H W) m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
  src_ok SEGS W regs m p (Z.of_nat (length l)).
Proof.
intros W regs m p l H Hw a Ha. split; [|exact (Hw a Ha)].
replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (wv_garr8_aview W m p l (Z.to_nat (a - p)) H) by lia. discriminate.
Qed.

(* a C string the runtime may read is a put source *)
Lemma wv_src_of_cstr : forall (W : world SEGS) m p l, cstr_ok W m p l -> src_rd W m p l.
Proof.
intros W m p l ((Hg & _) & H4096 & Hb & H32 & Ham & HRA & HH & _).
split; [exact (proj1 (proj1 (garr8_app SEGS _ p l [0]) Hg)) |].
split; [exact H4096 |]. split; [lia |].
split; [unfold YGcfStr.amem_range8 in Ham; unfold amem_range; lia |].
split; [eapply range_addressable_sub; [exact HRA | lia | lia] |].
intros Hl. apply (wv_hull_sub _ p (Z.of_nat (length l) + 1) p (Z.of_nat (length l)) HH); lia.
Qed.

(* THE TREE'S FOOTPRINT IS AT OR ABOVE THE ENTRY sp OR BELOW alloc_ceiling: the three node locations and the
   ledger blocks of D *)
Lemma wv_foot_low : forall ly S Hp W regs mem md ch STKv Lam peak cnt fail ran gmo gow buf v D,
  afn_pre_x SEGS B ARx STKv ly S Hp W regs mem md ch ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran gmo gow ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  forall x, pj_footR v D x -> spZ regs <= x \/ x < YM05.alloc_ceiling.
Proof.
intros ly S Hp W regs mem md ch STKv Lam peak cnt fail ran gmo gow buf v D HPRE HLED HLOC HD x Hx.
pose proof HPRE as (HAR & _).
destruct Hx as [Hhdr | ([a k0] & HbD & Hb)].
- destruct HLOC as [(Hv1 & Hv2) | [(y0 & z0 & Hin & Hyb & Hyv & Hvy) | (cid & pos & Hfr & Hf1 & Hf2)]].
  + left. lia.
  + right. destruct (wv_lam_low ly S Hp W mem md Lam peak cnt fail ran gmo gow y0 z0 HAR HLED Hin) as (_ & _ & H). lia.
  + right. destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as (_ & Hfb).
    rewrite Forall_forall in Hfb. pose proof (Hfb (cid, pos) Hfr) as (_ & Hfc). cbn [fst snd] in Hfc. lia.
- right. unfold pj_holdsR in Hb. cbn [fst snd] in Hb. destruct (HD a k0 HbD) as (Hin & _).
  destruct (wv_lam_low ly S Hp W mem md Lam peak cnt fail ran gmo gow a k0 HAR HLED Hin) as (_ & _ & H). lia.
Qed.

(* ---- wv_put_close FOR A WIDER WRITE SET [lo, spZ regs) (the number leaf: its strlen call also writes the 2 * ESTACK
   below the own frame). Every keep is wv_put_close's over that set; lo above alloc_ceiling + 8 keeps the ledger, the
   struct, the read-only view and the tree (at or above the entry sp, or below alloc_ceiling: wv_foot_low). ---- *)
Lemma wv_put_close_x : forall lo rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf (st : WriterApp.wst) s (bs : list Z)
    memc mdc regsc,
  192 <= STKv -> STK_put <= STKv -> YM05.alloc_ceiling + 8 <= lo ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [bs])) ->
  prh_univ_closure B CTX0 ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
  prhWriter_out W mem Lam o buf st ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < spZ regs) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  aregs_preserved regs regsc -> getr regsc 1 = getr regs 1 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s -> getr regsc 12 = w64 (Z.of_nat (length bs)) ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st [bs]) ->
  src_rd W memc s bs ->
  prhWriter_src_home B ly S Lam buf (WriterApp.w_cap st) s (Z.of_nat (length bs)) ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length bs) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs S (prhWriter_evs [] st [bs]) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc) ->
  SRr' SEGS RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc)
    (fpostWmR B ARx SK (wle' SEGS RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' => room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran gmo gow o buf st [bs] ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st [bs]) /\
          exists hist',
            PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length (prhWriter_evs ok st [bs]))%nat rp_H0 hist' S')).
Proof.
intros lo rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf st s bs
  memc mdc regsc HSTK HSTKp Hlo HPRE Hroom Hrp Hos Hcons Hcl HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ HKEEP
  HAP Hrac H10 H11 H12 Hcut Hch0 Hev Hsrc Hhome Hwmax Hhead Hlive HMN.
pose proof HPRE as (HPREx & HRO & HTOP).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
assert (HLOW8 : forall a, 0 <= a < YM05.alloc_ceiling + 8 -> ~ (lo <= a < spZ regs)) by (intros a Ha; lia).
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (lo <= a < spZ regs)) by (intros a Ha; lia).
assert (HOFF : forall a, o <= a < o + 32 -> 0 <= a < 2 ^ 64 /\ ~ (lo <= a < spZ regs)) by (intros a Ha; split; lia).
assert (Hsp : spZ regsc = spZ regs)
  by (unfold spZ; f_equal; exact (HAP 2 ltac:(unfold acallee_saved; lia))).
assert (Hgpc : getr regsc 3 = w64 (as_gp B))
  by (rewrite <- Hgp; exact (HAP 3 ltac:(unfold acallee_saved; lia))).
assert (Htpc : getr regsc 4 = w64 (as_tp B))
  by (rewrite <- Htp; exact (HAP 4 ltac:(unfold acallee_saved; lia))).
assert (Hs0c : s0Z regsc = s0Z regs)
  by (unfold s0Z; f_equal; exact (HAP 8 ltac:(unfold acallee_saved; lia))).
assert (HFOOT : forall x, pj_footR v D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ (lo <= x < spZ regs)).
{ intros x Hx.
  destruct (wv_foot_wr ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow buf v D
    HSTK HPREx HLED HLOC HD x Hx) as (A1 & A2 & _).
  pose proof (wv_foot_low ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow buf
    v D HPREx HLED HLOC HD x Hx) as A3.
  split; [exact A1|]. split; [exact A2|]. lia. }
assert (HNODEc : pj_nodeR SEGS (mrestrict (w_H W) memc) (prh_lin Lam) v t D).
{ apply (wv_nodeR_keep W W mem memc Lam v t D HNODE).
  - intros x Hx. destruct (HFOOT x Hx) as (A1 & A2 & _). split; assumption.
  - intros x Hx. destruct (HFOOT x Hx) as (A1 & _ & A3). apply HKEEP; assumption. }
assert (HOUTc : prhWriter_out W memc Lam o buf st)
  by (apply (wv_out_keep ly S Hp W W mem memc md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow o buf st
        (fun a => lo <= a < spZ regs)); [exact HAR | exact HLED | exact HOUT | exact HKEEP | exact HLOW | exact HOFF]).
assert (HLEDc : prh_ledger B ly S Hp W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow)
  by (apply (wv_led_keep ly S Hp W md mem memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow
        (fun a => lo <= a < spZ regs)); [exact HAR | exact HLED | exact HKEEP | exact HLOW8]).
assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc))
  by (apply (wv_arodata_keep W W mem memc (fun a => lo <= a < spZ regs)); [exact HRO | exact HKEEP | exact HLOW]).
assert (HCHc : achain ly (aview SEGS (w_H W) memc) (spZ regs) (s0Z regsc) ch).
{ rewrite Hs0c. apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hchain);
    [lia | lia |]. intros a Ha. apply HKEEP; lia. }
exact (wv_tail_put rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf
  st s bs memc mdc regsc HSTK HSTKp HPRE Hroom Hrp Hos Hcons Hcl HWIN Ho1 Ho2 HLED HOUT HNODEc HLOC HD Hoff HJ
  ltac:(intros a Ha; apply HKEEP; lia)
  HAP Hsp Hrac Hgpc Htpc HCHc HROc H10 H11 H12 Hcut Hch0 HOUTc HLEDc Hev Hsrc Hhome Hwmax Hhead Hlive HMN).
Qed.

(* the write set of the number leaf: the own frame and the strlen call's 2 * ESTACK window below it *)
Definition wv_wrS (sp a : Z) : Prop := sp - 192 - STK_RT_STR <= a < sp.

(* wv_keep_run over wv_wrS *)
Ltac wv_keep_runS HFr0 K0 K1 m0 P Usp :=
  lazymatch type of HFr0 with
  | frame_of ?E ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m2 a = aview SEGS H m0 a);
    [ refine (wv_keep_frame H E rs m0 m1 m2 P K0 HFr0 _);
      let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
      intros a (r & Hr & Ha);
      lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in Hr end;
      repeat (destruct Hr as [<- | Hr];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?Usp in Ha; unfold wv_wrS; lia |]);
      destruct Hr
    | ]
  end.


Lemma wv_leaf_num : forall txt bits,
  forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch o v pretty dep d buf (st : WriterApp.wst) D Lam peak ran gmo gow STKv,
  200 + STK_RT_STR <= STKv -> STK_put <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)) dep))) ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 dep ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) mem) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
  prh_run_at rp_sm rp_x rp_os rp_i
    (prhWriter_evs [] st (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)) dep)) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v (PjTree.JNum txt bits) D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  prhWriter_tree_vis W mem D ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)) dep))) + 1
    <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs S (prhWriter_evs [] st (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)) dep)) ->
  SRr' SEGS RZ_cf W (cfg_at SEGS (SIGMA AS_write_value) regs mem md)
    (fpostWmR B ARx SK (wle' SEGS RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
          room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v (PjTree.JNum txt bits) D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran gmo gow o buf st
            (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)) dep) ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
            (prhWriter_k ok st (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)) dep)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterValue.wvpieces (PjTree.JNum txt bits) (negb (pretty =? 0)%Z) dep)))%nat
            rp_H0 hist' S')).
Proof.
intros txt bits rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch o v pretty dep d buf st D Lam peak ran gmo gow
  STKv HSTK HSTKp HPRE Hroom Hrp Hos Hcons Hcl H10 H11 H12 H13 Hcut Hch0 HWIN Ho1 Ho2 HOUT HLED Hev HNODE HLOC HRA HTV HD
  Hoff Hwmax Hhead Hlive.
apply wv_pre_lift.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSTR : STK_RT_STR = 2 * ESTACK) by reflexivity.
pose proof HPRE as (HPREx & HRO & HTOP).
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
assert (HPF : 0 <= pi_frame F_put) by (vm_compute; congruence).
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wr (spZ regs) a) by (intros a Ha; unfold wv_wr; lia).
assert (HLOWS : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wrS (spZ regs) a) by (intros a Ha; unfold wv_wrS; lia).
destruct (wv_loc ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow buf v
  ltac:(lia) HPREx HLED HLOC) as (Hv4096 & Hv47 & Hvst & Hband & Hvimg).
assert (HJ : ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W mem md 0)
  by (eapply ajournal_x_init_W;
      [exact HPREx | split; [exact Hd0 | split; [exact Hd16 | split; [exact Hdtop | exact Hdpres]]]]).
assert (PLAWI : srr_inv_laws SEGS (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m))
  by (apply srr_inv_laws_imp; apply srr_inv_laws_memnorm_k).
assert (HPM : (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) mem) by (cbv beta; exact (fun h => h)).
pose proof HNODE as HNODE0.
destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody).
destruct Hhdr as ((Hv8 & Hrwr) & (Rtg & Vtg) & (Rnum & Vnum) & (Rstr & Vstr) & (Rkids & Vkids) &
  (Rkeys & Vkeys) & (Rnn & Vnn) & (Rcap & Vcap)).
destruct Hbody as (_ & _ & _ & _ & _ & k & Hcs & ->).
pose proof Hcs as (Hlam & Hlen & Hlen32 & Hrng & Hgs). unfold prh_lin in Hlam.
destruct (wv_lam_low ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow str k HAR HLED Hlam)
  as (Hs4096 & Hk0 & Hsk).
pose proof (wv_blk_ceil7 ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow str k
  HAR HLED Hlam) as Hgap1.
destruct (HJT 3%nat ltac:(lia)) as (HTv & HTr & HTlo & HThi & HTg & HTc & HTro).
change (4 * Z.of_nat 3) with (4 * 3) in HTv, HTr, HTlo, HThi, HTg, HTc, HTro.
assert (HTvm : val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 2) + WV_JT + 4 * 3) 4 (WV_JTW (Z.to_nat 3)))
  by (apply (wv_ro_val W mem _ 4%nat); [exact HRO | | exact HTv];
      intros i Hi; destruct (HTro i ltac:(lia)) as (_ & R1 & R2 & R3);
      split; [exact R1 | split; [exact R2 | exact R3]]).
assert (HTn : VAL (A_OBJ 2) + WV_JT + 4 * 3 + 4 <= v \/ v + 56 <= VAL (A_OBJ 2) + WV_JT + 4 * 3)
  by (destruct (wv_disj_img_n (VAL (A_OBJ 2) + WV_JT + 4 * 3) 4 v 56 ltac:(lia) ltac:(lia)
        ltac:(intros i Hi; exact (proj1 (HTro i Hi))) Hvimg) as [HL | HR]; [right; lia | left; lia]).
destruct (wv_seat ly S Hp W regs mem md ch STKv o v pretty dep 3 str kids keys nn ltac:(lia) HPREx H10 H11 H12 H13
  Hv8 Hv4096 Hv47 Hvst Hband ltac:(intros a Ha; split; [exact (Hvimg a Ha) | exact (Hrwr a Ha)])
  Vtg ltac:(lia) Vstr Rstr Vkids Rkids Vkeys Rkeys Vnn Rnn HRA
  HTvm HTr ltac:(split; lia) ltac:(left; lia) HTg HTc HTn ltac:(vm_compute; reflexivity)) as [HS SHOK].
set (E := wv_E regs v str kids keys nn (WV_JTW (Z.to_nat 3))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wv_E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat 3)))) k)
  by (intros k0 Hk; subst E; unfold wv_E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E34 : ew E 34 = Z_to_bv 64 str) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat 3)))) E)
  by (split; [intros k0 Hk; apply EL; unfold A_TEXT; lia | reflexivity]).
assert (K00 : forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a)
  by (intros; reflexivity).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_write_value)) with (Z_to_bv 64 (BASE + AF_write_value)).
(* entry -> the switch's jr *)
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS HJ SHOK HPM WV_Bspan;
[ eapply (wv_awr E 3 _ _ _ _ _ _ _ (spZ regs)); [exact Usp | lia | lia] | ].
wv_keep_run HFr K00 K1 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
prreg HS (11%bv : bv 5) R11.
assert (E38 : ew E 38 = Z_to_bv 64 (WV_JTW (Z.to_nat 3)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (EJ : ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)))
  by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
destruct (wv_jr_target E (Z.to_nat 3) E38 EJ HTr) as (Ht & Hr & He).
eapply (wv_jr_step E _ _ W _ _ (BASE + AF_wv_case 3) HS);
[ vm_compute; reflexivity | reflexivity | rewrite R11; exact Ht | exact Hr | exact He | ].
intros mat1 ms1 Hms1 HS1. subst ms1.
pose proof (wv_pi_at E _ (AF_wv_case 3) _ HS1) as HS2. clear HS1.
assert (HJ2 := HJ).
eapply (ajournal_x_materialize (SK := SK)) with (X := mat1) in HJ2;
[| first [exact LAWS | exact pa_segs_low | idtac] ..].
clear HJ.
(* the case: the shadow check of v + 16, `ld s1, 16(v)` and the stop at `bnez s1` *)
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan;
[ wv_awr_tac Usp d | ].
wv_keep_run HFr K1 K2 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
psrr_branch_tok (@paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) BR HS2 SHOK WV_Bspan.
2:{ (* the text pointer = 0: refuted, a ledger block's user pointer is at least 4096 *)
  exfalso.
  rewrite ?branch_ne_U, ?branch_eq_U, (U_atom E 34 str E34 Rstr), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
  assert (Hs0 : (str =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hs0' : (0 =? str) = false) by (apply Z.eqb_neq; lia).
  rewrite ?Hs0, ?Hs0' in Hc. cbn in Hc. discriminate Hc. }
(* the text pointer <> 0: a0 = s1, the strlen call (write_value + 4 * 116) *)
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HS2 HJ2 SHOK HPM WV_Bspan;
[ wv_awr_tac Usp d | ].
wv_keep_run HFr K2 K3 mem (wv_wr (spZ regs)) Usp. clear HF HFr HG.
pmkst HS2.
prreg HS2 (10%bv : bv 5) Ra0. prreg HS2 (2%bv : bv 5) Rsp1. prreg HS2 (1%bv : bv 5) Rra1.
prreg HS2 (3%bv : bv 5) Rgp1. prreg HS2 (4%bv : bv 5) Rtp1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  assert (HspT : spZ rT = spZ regs - 192)
    by (unfold spZ at 1; rewrite Rsp1, Usp; rewrite unsigned_lit_small by lia; lia);
  (* the text at the call memory: the tree's block (str, k), kept below alloc_ceiling *)
  assert (HTVT : prhWriter_tree_vis W mT [(str, k)])
    by (exact (wv_tree_vis_keep W W mem mT [(str, k)] (wv_wr (spZ regs)) HTV K3 HLOW));
  destruct (HTVT str k (or_introl eq_refl)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7);
  assert (HgsT : garr8 SEGS (mrestrict (w_H W) mT) str (txt ++ [0]))
    by (apply (wv_garr8_keep (w_H W) (w_H W) mem mT str (txt ++ [0])); [|exact Hgs];
        intros j Hj; rewrite length_app in Hj; cbn [length] in Hj; apply K3; [lia | unfold wv_wr; lia]);
  pose proof (wv_cstr_blk ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow W mT
    str k txt HAR HLED Hlam Hlen Hlen32 Hrng HgsT Hgap1 T5 T6 T7) as HcsT;
  assert (HROT : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mT))
    by (apply (wv_arodata_keep W W mem mT (wv_wr (spZ regs))); [exact HRO | exact K3 | exact HLOW])
end.
pose proof HcsT as (HcT & _ & _ & _ & HamT & HraT & HhT & HtT).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (YGcallMxmn.aj_strlen_at_xrom (SK := SK) SEGS B (@prh_pst prh_img_B) ARx pa_relro_lo pa_relro_hi LAWS
    pa_segs_low (SIGMA AS___wrap_strlen) STRLEN W rT mT (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp dT 0 str (Z.of_nat (length txt))
    (- (d + 192)) _ HJ2) end.
  - rewrite Ra0, E34. reflexivity.
  - lia.
  - lia.
  - exact Hlen32.
  - lia.
  - rewrite HspT. lia.
  - apply wv_neg_mod16. rewrite Z.add_mod, Hd16 by lia. reflexivity.
  - lia.
  - lia.
  - rewrite Rgp1, E3. exact Hgp.
  - rewrite Rtp1, E4. exact Htp.
  - exact Rra1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - exact (wv_first_byte W _ str txt HcT).
  - replace (Z.of_nat (length txt) + 1) with (Z.of_nat (length (txt ++ [0])))
      by (rewrite length_app; cbn [length]; lia).
    apply (wv_src_ok W _ _ str (txt ++ [0]) (proj1 HcT)).
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite HspT. lia.
  - intros a Ha. lia.
  - exact HamT.
  - exact HraT.
  - exact HhT.
  - exact HtT.
  - exact HROT. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ3 & HP2 & Hlen2 & Hfr2 & Hpres2 & Hmn2).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
jafter_call_keep_pi HS2 39%nat regs2 (mrestrict (w_H W) mem2) HP2 [1]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ constructor; [|apply Forall_nil]. split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
    apply (mbyte_of_aview SEGS). apply Hfr2; lia.
  - intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
    apply (apresent_writable SEGS). apply Hpres3. lia. }
specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
remember (havoc E 39 (map (getr regs2) CLOB)) as E1' eqn:HE1 in HSX.
assert (HIM1 : img_env VAL A_LIM E1') by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall n, (n < 39)%nat -> ew E1' n = ew E n) by (intros n0 Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
assert (E1a0 : ew E1' 43 = w64 (Z.of_nat (length txt))) by (rewrite HE1, <- Hlen2; reflexivity).
assert (HAE1 : env_agree 32 (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat 3)))) E1')
  by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE1.
assert (Usp1 : bv_unsigned (ew E1' 2) = spZ regs) by (rewrite OLD1 by (cbv; lia); exact Usp).
assert (SHOK1 : sh_ok SEGS WV_Bx [] E1' (mrestrict (w_H W) mem2)) by (unfold sh_ok; apply Forall_nil).
assert (HPM1 : (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) mem2)
  by (cbv beta; intros h; exact (Hmn2 (HPM h))).
assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ wv_wrS (spZ regs) a ->
    aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. unfold wv_wrS in Hn. rewrite (Hfr2 a Ha ltac:(lia)). apply K3; [exact Ha | unfold wv_wr; lia]. }
(* after the call: a2 = len, a0 = s0, a1 = s1, the epilogue, and the tail `j put` (write_value + 4 * 236) *)
paj_run_to_tok_x_inv (@paj_run_to_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HSX HJ3 SHOK1 HPM1 WV_Bspan
  (AF_write_value + 4 * 268);
[ wv_awr_tac Usp1 d | ].
wv_keep_runS HFr KX K4 mem (wv_wrS (spZ regs)) Usp1. clear HF HFr HG.
paj_run_tok_x_inv (@paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PLAWI) HSX HJ3 SHOK1 HPM1 WV_Bspan;
[ wv_awr_tac Usp1 d | ].
wv_keep_runS HFr K4 K5 mem (wv_wrS (spZ regs)) Usp1. clear HF HFr HG.
prreg HSX (10%bv : bv 5) Rb0. prreg HSX (11%bv : bv 5) Rb1. prreg HSX (12%bv : bv 5) Rb2.
prreg HSX (1%bv : bv 5) Rbra.
lazymatch type of HSX with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HAP : aregs_preserved regs (ms_regs msx))
    by (eapply (aregs_preserved_of_st_ok SEGS (w_H W) E1' _ _ regs _); [exact HSX | exact HAE1 | vm_compute; reflexivity]);
  assert (Rrac : getr (ms_regs msx) 1 = getr regs 1) by (rewrite Rbra, OLD1, E1 by (cbv; lia); reflexivity);
  assert (H10c : getr (ms_regs msx) 10 = w64 o) by (rewrite Rb0, OLD1, E10 by (cbv; lia); exact H10);
  assert (H11c : getr (ms_regs msx) 11 = w64 str) by (rewrite Rb1, OLD1, E34 by (cbv; lia); reflexivity);
  assert (H12c : getr (ms_regs msx) 12 = w64 (Z.of_nat (length txt))) by (rewrite Rb2; exact E1a0);
  (* the text at the put's memory *)
  assert (HTVc : prhWriter_tree_vis W (ms_mem msx) [(str, k)])
    by (exact (wv_tree_vis_keep W W mem (ms_mem msx) [(str, k)] (wv_wrS (spZ regs)) HTV K5 HLOWS));
  destruct (HTVc str k (or_introl eq_refl)) as (U1 & U2 & U3 & U4 & U5 & U6 & U7);
  assert (Hgsc : garr8 SEGS (mrestrict (w_H W) (ms_mem msx)) str (txt ++ [0]))
    by (apply (wv_garr8_keep (w_H W) (w_H W) mem (ms_mem msx) str (txt ++ [0])); [|exact Hgs];
        intros j Hj; rewrite length_app in Hj; cbn [length] in Hj; apply K5; [lia | unfold wv_wrS; lia]);
  pose proof (wv_src_of_cstr W (ms_mem msx) str txt
    (wv_cstr_blk ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow W (ms_mem msx)
       str k txt HAR HLED Hlam Hlen Hlen32 Hrng Hgsc Hgap1 U5 U6 U7)) as Hsrc;
  assert (Hhome : prhWriter_src_home B ly S Lam buf (WriterApp.w_cap st) str (Z.of_nat (length txt)))
    by (split; [left; left; exists str, k; split; [exact Hlam | lia]
               | exact (wv_blk_apart ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow str k
                   buf (WriterApp.w_cap st) (Z.of_nat (length txt)) HAR HLED Hlam
                   (proj2 (HD str k (or_introl eq_refl))) Hbufin ltac:(lia) ltac:(lia))]);
  assert (Hwmax' : Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length txt) + 1 <= prhWriter_WMAX)
    by (cbn [WriterValue.wvpieces concat] in Hwmax; rewrite app_nil_r in Hwmax; exact Hwmax);
  assert (Hch0c : spZ regs + 16 <= o ->
      exists ra, rdword (aview SEGS (w_H W) (ms_mem msx)) (o - 8) = Some ra /\
        exists nfp, rdword (aview SEGS (w_H W) (ms_mem msx)) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling)
    by (intros Hge; apply (wv_reca_keep (aview SEGS (w_H W) mem)); [| exact (Hch0 Hge)];
        intros a Ha; apply K5; [lia | unfold wv_wrS; lia]);
  pmkst HSX; apply SRr_ret;
  exact (wv_put_close_x (spZ regs - 192 - STK_RT_STR) rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch
    STKv d o v _ _ Lam peak ran gmo gow buf st str txt (ms_mem msx) _ (ms_regs msx) ltac:(lia) HSTKp ltac:(lia) HPRE Hroom
    Hrp Hos Hcons Hcl HWIN Ho1 Ho2 HLED HOUT HNODE0 HLOC HD Hoff HJ3 K5 HAP Rrac H10c H11c H12c Hcut Hch0c Hev Hsrc Hhome
    Hwmax' Hhead Hlive HPM1)
end.
Qed.

End cl.
End h.
End f.
End d.
