(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d): the
   CONTAINER PREFIX of the write_value walk (B' 0x87348): from write_value's entry with an array or an object to the
   two join states WriteValueB_Defs fixes - the ITEM LOOP HEAD (write_value + 4 * 90, Defs' wv_headR) for a non-empty
   container and the CLOSE (write_value + 4 * 173, Defs' wv_clR) for an empty one - at the entry float state (the
   opening bracket's put keeps it). wv_cont discharges the head continuation wv_HEADKR at i = 0 and the close
   continuation wv_CLOSEKR, both at wle' SEGS RZ_cf: the opening bracket's put may realloc, so the walk's worlds are
   related by wle' and its journal is at wle' from the entry on.
   THE PATH, MEASURED with the engine on B's listing (scratch probe WriteValueBZCont1, the internal file zfb-20261029T193928Z.log): the
   entry run stops at the switch's `jr` (slot 40, Base's wv_jr_step, lifted by wvc_jr_step); from the case label
   (slot 41) the run resolves `beq tag, 6` (slot 42: the tag is a literal chunk), forms "[" (slot 44) or "{" (slot 47)
   and stops at the opening `jal put` (slot 50; Call's wv_call_put, return slot 51); after the call (regions kept: the
   own frame and the node) the run stops at `beqz s3` (slot 52, pretty); each arm forms the separator (": " slot 54 /
   ":" slot 57, stored at frame word 56), passes the 8-byte shadow check of v + 40 (slots 59-63: the engine reads its
   shadow byte as 0 from the node's shadow entry, rebuilt after the call from v's 56 bytes addressable at the current
   memory, Base's wv_ra_curR) and stops at `beqz n` (slot 65); n = 0 runs to slot 173 (the close), n <> 0 runs the
   loop init (slots 66-89) to slot 90 (the head), no obligation left on any path.
   TEMPLATE (ported, not cited): the kit owner's image-A walk lib/A/Prog/PRW_write_value.v (a working branch
   7819c4b4583, blob 051bfb4b3368), its wv_cont and the helpers wvp_*: B's frame is 192, the pretty branch comes
   before the n branch, the empty container joins the shared close at slot 173, s6 = addiw dep 1 and s10 =
   slt s6 dep (= 0), frame words 8 = 3 / 16 = 0, the shadow offset at frame word 72.
   Numerals: 4 (LENGTH: instruction bytes), 192 (LENGTH: write_value's own frame), 8 .. 184 (LENGTH: frame offsets),
   24 / 32 / 40 / 56 (LENGTH: the node's fields and size), 2 ^ 31 / 2 ^ 44 / 2 ^ 47 / 2 ^ 63 / 2 ^ 64 (LENGTH: ranges),
   the slots 41 .. 173 (DERIVED: (B pc - entry) / 4). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
WriteValueB_Model WriteValueB_Base WriteValueB_Call WriteValueB_Defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0s YO0f.
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
Let wv_foot_keepR := @WriteValueB_Base.wv_foot_keepR fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
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
Let wv_arodata_jR := @WriteValueB_Base.wv_arodata_jR fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
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
Let wv_ra_curR := @WriteValueB_Base.wv_ra_curR fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_tvis_cur := @WriteValueB_Base.wv_tvis_cur fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ev_first := @WriteValueB_Base.wv_ev_first fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ret_pos_one := @WriteValueB_Base.wv_ret_pos_one fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.
Let wv_ret_pos_app := @WriteValueB_Base.wv_ret_pos_app fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO.

Section cl.
Variable CTX0 : list (list Z).
(* the callee texts, the draft's texts (lib/A/PRH_FnWriter.v) at ANY float state; owners: put its own lane,
   put_string its own lane, indent a Theorem Labs lane / the indent lane *)
Hypothesis PUT : forall fx' : YK11.FPState, tput_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis PUTSTR : forall fx' : YK11.FPState, tput_string_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis INDENT : forall fx' : YK11.FPState, tindent_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling; the lane's Section shape, unused here) *)
Hypothesis HW : prh_head_wide.

(* WriteValueB_Call's lemmas at this Section's float state *)
Let wv_neg_mod16 := @WriteValueB_Call.wv_neg_mod16 fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_tail_put := @WriteValueB_Call.wv_tail_put fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_put_close := @WriteValueB_Call.wv_put_close fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_tail_gen := @WriteValueB_Call.wv_tail_gen fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_s0_pres := @WriteValueB_Call.wv_s0_pres fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_tail_put_string := @WriteValueB_Call.wv_tail_put_string fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_call_put := @WriteValueB_Call.wv_call_put fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_call_indent := @WriteValueB_Call.wv_call_indent fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_call_put_string := @WriteValueB_Call.wv_call_put_string fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).
Let wv_call_self := @WriteValueB_Call.wv_call_self fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 (PUT fx) (PUTSTR fx) (INDENT fx).

Section cont.
(* the runner's memory invariant, abstract (the top instantiates it once, the memnorm keep) *)
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.

Let RUNIR := @paj_run_x_invR fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS Pm PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Let RUNTOIR := @paj_run_to_x_invR fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS Pm PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Let BRR := paj_branchR (PI := PA) (wle' SEGS RZ_cf).

(* ---- helpers (prefix wvc_), ported from the image-A template's wvp_* ---- *)

(* the stack the container's prefix needs: its frame and the opening bracket's put below it *)
Lemma wvc_stk : forall n', 200 <= STK_write_value (S n') /\ STK_put + 192 <= STK_write_value (S n').
Proof.
intros n'. unfold STK_write_value.
assert (Hp : 0 <= STK_put) by (vm_compute; congruence).
assert (Hn : 2 <= Z.of_nat (S (S n'))) by lia.
lazymatch goal with |- context [Z.of_nat (S (S n')) * ?f + ?z] =>
  assert (Hf : 192 <= f) by (vm_compute; congruence);
  assert (Hz : STK_put <= z) by (vm_compute; congruence);
  set (ff := f) in *; set (zz := z) in *
end.
set (m := Z.of_nat (S (S n'))) in *. clearbody ff zz m. nia.
Qed.

(* a word the memory holds as val_mem is the word rdword reads *)
Lemma wvc_rdword_of_val_mem0 : forall (H : word -> bool) mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> rdword (aview SEGS H mem) a = Some (v mod 2 ^ 64).
Proof.
intros H mem a v Hv. set (u := v mod 2 ^ 64).
assert (Hu : 0 <= u < 2 ^ 64) by (unfold u; apply Z.mod_pos_bound; lia).
assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (YG0f.le_byte u 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold u, YO0f.le_byte, YG0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite !Z.mod_mod by lia. reflexivity. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply YG0s.le_bytes8. exact Hu.
Qed.

Lemma wvc_rdword_of_val_mem : forall (H : word -> bool) mem a v,
  0 <= v < 2 ^ 64 -> val_mem SEGS (mrestrict H mem) a 8 v -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv0 Hv. rewrite (wvc_rdword_of_val_mem0 H mem a v Hv). f_equal. apply Z.mod_small. exact Hv0.
Qed.

(* a word chunk of a region of the engine's state, read off the memory (the region's base an atom b) *)
Lemma wvc_chunk_rdb : forall (H : word -> bool) E ss ms i (b : nat) lo hi wlo whi cs off e v base a,
  st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some b) lo hi wlo whi cs) ->
  bv_unsigned (ew E b) = base -> a = base + off ->
  In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H (ms_mem ms)) a = Some v.
Proof.
intros H E ss ms i b lo hi wlo whi cs off e v base a HS Hi Hb Ha Hc He Hv.
pose proof (st_ok_mem_ok SEGS E _ _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
cbn [YP09.r_chunks YP09.r_base base_val] in Hcs.
subst a. apply wvc_rdword_of_val_mem; [exact Hv|].
pose proof (val_of_chunk_ok SEGS E _ _ off 8%N e v (proj1 (Forall_forall _ _) Hcs _ Hc) He
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as X.
rewrite Hb in X. exact X.
Qed.

Lemma wvc_chunk_rdp : forall (H : word -> bool) E ss ms i (b : nat) lo hi wlo whi cs off e v base a,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some b) lo hi wlo whi cs) ->
  bv_unsigned (ew E b) = base -> a = base + off ->
  In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H (ms_mem ms)) a = Some v.
Proof.
intros H E ss ms i b lo hi wlo whi cs off e v base a HS Hi.
exact (wvc_chunk_rdb H E (abs_ss VAL ss) ms i b lo hi wlo whi cs off e v base a HS Hi).
Qed.

(* eight visible bytes form a word *)
Lemma wvc_rdword_some : forall (rd : Z -> option Z) a, (forall j, 0 <= j < 8 -> rd (a + j) <> None) ->
  exists w, rdword rd a = Some w.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
pose proof (H 1 ltac:(lia)) as E1. pose proof (H 2 ltac:(lia)) as E2. pose proof (H 3 ltac:(lia)) as E3.
pose proof (H 4 ltac:(lia)) as E4. pose proof (H 5 ltac:(lia)) as E5. pose proof (H 6 ltac:(lia)) as E6.
pose proof (H 7 ltac:(lia)) as E7.
destruct (rd a) as [b0|]; [|exfalso; exact (E0 eq_refl)].
destruct (rd (a + 1)) as [b1|]; [|exfalso; exact (E1 eq_refl)].
destruct (rd (a + 2)) as [b2|]; [|exfalso; exact (E2 eq_refl)].
destruct (rd (a + 3)) as [b3|]; [|exfalso; exact (E3 eq_refl)].
destruct (rd (a + 4)) as [b4|]; [|exfalso; exact (E4 eq_refl)].
destruct (rd (a + 5)) as [b5|]; [|exfalso; exact (E5 eq_refl)].
destruct (rd (a + 6)) as [b6|]; [|exfalso; exact (E6 eq_refl)].
destruct (rd (a + 7)) as [b7|]; [|exfalso; exact (E7 eq_refl)].
eexists. reflexivity.
Qed.

(* a byte at or above the ceiling and below the struct is outside the caller footprint (the buffer is a block, below
   the ceiling) *)
Lemma wvc_nfp : forall ly S Hp W mem md o buf cap a,
  ARx ly S Hp W mem md -> (cap <> 0 -> In (buf - cf_head, cap + cf_head) (ablocks B ly S)) ->
  YM05.alloc_ceiling <= a -> a < o -> ~ inFP (prhWriter_cfp o buf cap) a.
Proof.
intros ly S Hp W mem md o buf cap a HAR Hbb Ha Hao Hf.
unfold prhWriter_cfp in Hf. apply inFP_cons in Hf. destruct Hf as [Hs | Hb]; [lia|].
unfold prhWriter_fp in Hb. destruct (Z.eqb_spec cap 0) as [_|Hc]; [exact (inFP_nil a Hb)|].
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR (Hbb Hc)) as (_ & _ & Hce & _).
unfold ablocks_fp in Hb. cbn [map] in Hb. destruct Hb as (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
Qed.

(* the engine's terms at the join states, read as values *)
Lemma wvc_den_off : forall E k c x, ew E k = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  sv_denot E (SOff k c) = w64 (x + c).
Proof. intros E k c x Hk Hx Hxc. cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hx. reflexivity. Qed.

Lemma wvc_den_sh : forall E k c x, ew E k = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff k c) (SLit 3)) (SOff 32 0)) = w64 (SHADOW_OFF + (x + c) / 8).
Proof.
intros E k c x Hk H32 Hx Hxc. pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
cbn [sv_denot]. rewrite Hk, H32.
rewrite (unsigned_lit_small x) by exact Hx. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
rewrite Z.add_0_r.
rewrite zalu64_sound. rewrite zalu64_sound. unfold zalu64, w64. rewrite Z_to_bv64_canon. f_equal.
cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
rewrite (YP0m.zcanon_small (x + c)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (D : 0 <= (x + c) / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | change (8 * 2 ^ 44) with (2 ^ 47); lia]]. }
rewrite !(YP0m.zcanon_small ((x + c) / 8)) by lia.
rewrite (YP0m.zcanon_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
lia.
Qed.

Lemma wvc_den_pr : forall E p, ew E 12 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 12 0)) (SLit 1)) = w64 (if p =? 0 then 1 else 2).
Proof.
intros E p H12 Hp. cbn [sv_denot]. rewrite H12, unsigned_lit_small by exact Hp. rewrite Z.add_0_r.
rewrite zalu64_sound. rewrite zalu64_sound. unfold zalu64, w64. rewrite Z_to_bv64_canon.
cbn [zalu_raw]. rewrite (YP0m.zcanon_small 0) by lia. rewrite (YP0m.zcanon_small p) by lia.
destruct (Z.eqb_spec p 0) as [->|Hp0].
- reflexivity.
- rewrite (proj2 (Z.ltb_lt 0 p)) by lia. reflexivity.
Qed.

Lemma wvc_den_addw : forall E dp, ew E 13 = Z_to_bv 64 dp -> 0 <= dp -> dp + 1 < 2 ^ 31 ->
  sv_denot E (SAluw ALU_ADD (SOff 13 0) (SLit 1)) = w64 (dp + 1).
Proof.
intros E dp H13 H0 H1. cbn [sv_denot]. rewrite H13, unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite zalu32_sound. unfold zalu32, w64. rewrite Z_to_bv64_canon.
cbn [zalu_raw]. unfold zu32, M32.
rewrite (Z.mod_small dp (2 ^ 32)) by lia. rewrite (Z.mod_small 1 (2 ^ 32)) by lia.
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia). reflexivity.
Qed.

(* s10 = slt (addiw dep 1) dep = 0: dep + 1 is no overflow below 2 ^ 31 *)
Lemma wvc_den_slt : forall E dp, ew E 13 = Z_to_bv 64 dp -> 0 <= dp -> dp + 1 < 2 ^ 31 ->
  sv_denot E (SAlu ALU_SLT (SAluw ALU_ADD (SOff 13 0) (SLit 1)) (SOff 13 0)) = w64 0.
Proof.
intros E dp H13 H0 H1.
assert (P31 : 2 ^ 31 = 2147483648) by reflexivity.
change (sv_denot E (SAlu ALU_SLT (SAluw ALU_ADD (SOff 13 0) (SLit 1)) (SOff 13 0)))
  with (alu64 ALU_SLT (sv_denot E (SAluw ALU_ADD (SOff 13 0) (SLit 1))) (sv_denot E (SOff 13 0))).
rewrite (wvc_den_addw E dp H13 H0 H1).
cbn [sv_denot]. rewrite H13. rewrite P31 in H1. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
unfold w64. rewrite zalu64_sound. unfold zalu64. f_equal.
cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small (dp + 1)) by lia. rewrite (Z.mod_small dp) by lia.
rewrite !bv_swrap_small by (change (bv_half_modulus 64) with 9223372036854775808; lia).
rewrite (proj2 (Z.ltb_ge (dp + 1) dp)) by lia. reflexivity.
Qed.

(* v's shadow entry from v's 56 bytes addressable at the current memory (wv_entry's sh_ok) *)
Lemma wvc_shok : forall (H : word -> bool) mem E v,
  range_addressable (aview SEGS H mem) SHADOW_OFF v 56 ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E 11 = Z_to_bv 64 v -> 4096 <= v -> v + 56 <= 2 ^ 47 ->
  (v + 56 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= v) ->
  sh_ok SEGS WV_Bx wv_SH E (mrestrict H mem).
Proof.
intros H mem E v Hra E32 E11 Hv0 Hv1 Hband. pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
unfold sh_ok, wv_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS H mem E WV_Bx 11 v 56 v 0 56 Hra).
- unfold U, WV_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- intros a Ha. unfold SHADOW_OFF in *. lia.
Qed.

(* the opening bracket's `jal put` (write_value + 4 * 50) returns to write_value + 4 * 51: below the ceiling (a
   CLOSED lemma: the slot lookup must not run inside the big proof) *)
Lemma wvc_ret51_ceil : bv_unsigned (Z_to_bv 64 (BASE + (AF_write_value + 4 * 51))) < YM05.alloc_ceiling.
Proof.
assert (HA : 0 <= AF_write_value + 4 * 51 < 2 ^ 40) by (split; vm_compute; congruence).
pose proof (PRW_StepKit.pa_slot_lt_ceil_b (L := B_prog_listing) (PL := PL_prog_B) (PI := PA)
  (AF_write_value + 4 * 51) HA ltac:(vm_compute; reflexivity)) as H.
rewrite unsigned_lit_small by (pose proof (@pa_B_ok _ _ PA); lia). exact H.
Qed.

(* the switch's `jr` (Base's wv_jr_step, one step at wle) inside the walk at wle' SEGS RZ_cf (the walk crosses the
   opening bracket's put): the step lifted once by SRr_SRr', its continuation at wle' *)
Lemma wvc_jr_step : forall E ss ms (W : world SEGS) md Q tgt,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  ss_pc ss = AF_write_value + 4 * 40 ->
  ss_resv ss = None ->
  getr (ms_regs ms) 11 = Z_to_bv 64 tgt ->
  0 <= tgt < 2 ^ 64 -> tgt mod 2 = 0 ->
  (forall mat' ms1,
     ms1 = mkst (ms_regs ms) (Z_to_bv 64 tgt) (ms_mem ms) (seg_rom SEGS) ->
     st_ok SEGS E (mkSST tgt (ss_regs ss) (ss_fregs ss) (ss_mem ss) None (ss_facts ss)) (restrict (w_H W) ms1) ->
     SRr' SEGS RZ_cf W (mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr' SEGS RZ_cf W (mkCfg ms md) Q.
Proof.
intros E ss ms W md Q tgt HS Hpc Hrv H11 Hr Hev HK.
apply (SRr'_bind SEGS RZ_cf W (mkCfg ms md) (fun W' c' => SRr' SEGS RZ_cf W' c' Q) Q);
  [| intros W' c' _ H; exact H].
apply (SRr_SRr' SEGS RZ_cf).
apply (wv_jr_step E ss ms W md (fun W' c' => SRr' SEGS RZ_cf W' c' Q) tgt HS Hpc Hrv H11 Hr Hev).
intros mat' ms1 Hms1 HS1. apply SRr_ret. exact (HK mat' ms1 Hms1 HS1).
Qed.

(* the keep of one run: the run's start state has ONE write window, the own frame [sp - 192, sp) at atom 2 (every
   other region's window is empty), so a run that starts from a memory kept outside P keeps every byte outside P
   (WriteValueB_Leaf's Ltac, the same text) *)
Ltac wvc_keep_run HFr0 K0 K1 m0 P Usp :=
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
Ltac wvc_awr_tac Usp d :=
  cbn [ss_mem]; repeat first
    [ apply awr_ok_nil
    | eapply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- d));
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?Usp; lia
      | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ].

(* a register of a state at a stop, as the denotation of the engine's term (no normalisation) *)
Ltac wvc_reg HS r :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
      rewrite (st_ok_pi_restrict_reg H E ss ms r HS);
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      rewrite (st_ok_restrict_reg segs H E ss ms r HS);
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e
  end.

(* a word of the own frame at a join state (region 0, base atom 2, the entry sp) *)
Ltac wvc_rd HS Usp off :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ _ => eapply (wvc_chunk_rdp _ _ _ _ 0%nat 2%nat _ _ _ _ _ off)
  | st_ok _ _ _ _ => eapply (wvc_chunk_rdb _ _ _ _ 0%nat 2%nat _ _ _ _ _ off)
  end;
  [ exact HS | reflexivity | exact Usp | lia | cbn [In]; repeat (first [left; reflexivity | right]) | | ].

(* ---- THE CONTAINER PREFIX: from write_value's entry with an array or an object, at the entry float state, to the
   loop head (n <> 0, i = 0) or the close (n = 0), through the opening bracket's put (which may realloc: the walk is
   at wle' SEGS RZ_cf, its journal widened from the entry on) ---- *)
Lemma wv_cont : forall (n' : nat) (X : wvx) ch,
  y_fx X = fx ->
  (exists l, y_t X = PjTree.JArr l) \/ (exists l, y_t X = PjTree.JObj l) ->
  STK_write_value (S n') <= y_STK X -> wv_pre B ARx CTX0 Pm X ch ->
  wv_HEADKR B ARx Pm (wle' SEGS RZ_cf) X -> wv_CLOSEKR B ARx Pm (wle' SEGS RZ_cf) X ->
  SRr' SEGS RZ_cf (y_W X) (cfg_at SEGS (SIGMA AS_write_value) (y_regs X) (y_mem X) (y_md X)) (wv_Qfin B ARx Pm X).
Proof.
intros n' X ch Hfx Ht HSTKn HPRE0 HLOOP HCLOSE.
pose proof (wvc_stk n') as (HS200 & HSput).
destruct X as [fx0 d STKv ly S Hp W regs mem md o v pretty dep buf st t D Lam peak ran gmo gow
  rpsm rpx rpos rpi rpH0 rphist].
cbn [y_fx] in Hfx. subst fx0.
unfold wv_pre, y_sp, y_p, y_FP in HPRE0.
cbn [y_fx y_d y_STK y_ly y_S y_Hp y_W y_regs y_mem y_md y_o y_v y_pretty y_dep y_buf y_st y_t y_D y_Lam y_peak
  y_ran y_most y_own y_rpsm y_rpx y_rpos y_rpi y_rpH0 y_rphist] in HPRE0, HSTKn, Ht |- *.
destruct HPRE0 as (HPRE & Hroom & Hrp & Hcl & H10 & H11 & H12 & H13 & Hpr & Hdep & Hdep2 & Hcut & Hch0 & Hs0 &
  HWIN & Ho1 & Ho2 & HOUT & HLED & Hev & HNODE & HLOC & HRA & HTV & HD & Hoff & Hfr0 & Hwmax & Hhead & Hlive & HPm &
  Hcons0 & Hlen4).
assert (Hpk0 : 0 <= peak)
  by (pose proof HLED as Hb0; apply prh_ledger_bounds in Hb0; destruct Hb0 as (Hb0 & _); lia).
pose proof HPRE as (HPREx & HRO & HTOP1 & HTOP2 & HFRM).
assert (HSTK : 192 <= STKv) by lia. assert (HSTKp : STK_put + 192 <= STKv) by lia.
pose proof HPREx as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wv_pow_facts as (PW1 & PW2 & PW3 & PW4).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
pose proof cf_head_nonneg as Hh0.
assert (HPF : 0 <= pi_frame F_put) by (vm_compute; congruence).
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
assert (Hbufb : WriterApp.w_cap st <> 0 -> In (buf - cf_head, WriterApp.w_cap st + cf_head) (ablocks B ly S)).
{ intros Hc. destruct (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED _ (Hbufin Hc)) as (_ & Hbl & _). exact Hbl. }
assert (Hclosed : ~ YI16.sink_open_fp (prhWriter_cfp o buf (WriterApp.w_cap st))).
{ apply wv_cfp_closed; [lia|]. intros Hc.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR (Hbufb Hc)) as (_ & H4096 & _). lia. }
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ wv_wr (spZ regs) a) by (intros a Ha; unfold wv_wr; lia).
assert (HLOW8 : forall a, 0 <= a < YM05.alloc_ceiling + 8 -> ~ wv_wr (spZ regs) a) by (intros a Ha; unfold wv_wr; lia).
assert (HOFF : forall a, o <= a < o + 32 -> 0 <= a < 2 ^ 64 /\ ~ wv_wr (spZ regs) a)
  by (intros a Ha; split; [lia | unfold wv_wr; lia]).
destruct (wv_loc ly S Hp W regs mem md ch STKv Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow buf v
  ltac:(lia) HPREx HLED HLOC) as (Hv4096 & Hv47 & Hvst & Hband & Hvimg).
assert (HJ0 : ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W mem md 0)
  by (eapply ajournal_x_init_W;
      [exact HPREx | split; [exact Hd0 | split; [exact Hd16 | split; [exact Hdtop | exact Hdpres]]]]).
assert (HJ : ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W mem md 0)
  by (exact (ajournal_xbR_mono (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (@wle SEGS) (wle' SEGS RZ_cf)
        (wle_wle' SEGS RZ_cf) (STKv + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S W mem md []
        ly S Hp W mem md 0 [] HJ0)).
clear HJ0.
(* the .rodata literals the prefix forms are image bytes (HLIT at the entry state) *)
assert (HIMG : forall (k : nat) (bs : list Z), In (k, bs) wv_lits -> (0 < length bs)%nat ->
    0 <= WV_STR k /\ WV_STR k < kLowMemEnd).
{ intros k bs Hin Hl. destruct (HLIT k bs ly S Hp W mem md Hin HAR HRO) as (_ & _ & Hi).
  pose proof (pa_segs_low _ (Hi 0 ltac:(lia))) as X. rewrite Z.add_0_r in X. exact X. }
(* what every join carries (Defs' wv_commonR at wle'), from the state at the join (HJc / K5) and the put's return
   (Hroom2, HOKS1 .. Hrp1); the float invariant at the entry float state *)
let common u :=
  split; [exact HJc |];
  split; [ intros a Ha Hf; rewrite (K5 a ltac:(lia) ltac:(unfold wv_wr; lia)), (HXT a ltac:(lia) Hf);
           apply K2; [lia | unfold wv_wr; lia] |];
  split; [exact HPM2 |];
  split;
  [ exists ok1, ran1, buf1, Lam1, peak1; split; [exact HOKS1 |]; split;
    [ eapply (wv_out_keep ly2 S2 Hp2 W2 W2 mem2 _ md2 Lam1 peak1 _ _ ran1 gmo gow o buf1 _ (wv_wr (spZ regs)));
      [exact HAR2 | exact HLED1 | exact HOUT1 | exact K5 | exact HLOW | exact HOFF] |];
    split;
    [ eapply (wv_led_keep ly2 S2 Hp2 W2 md2 mem2 _ Lam1 peak1 _ _ ran1 gmo gow (wv_wr (spZ regs)));
      [exact HAR2 | exact HLED1 | exact K5 | exact HLOW8]
    | split; [exact HBLK1 | exists rphist1; exact Hrp1] ] |];
  split; [exact Hroom2 |];
  split; [exact (wv_arodata_jR (wle' SEGS RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc Hclosed HRO) |];
  split; [exact HFRM | apply wv_fregs_kept_refl]
in
(* a saved register's frame word *)
let sreg off rn rb :=
  wvc_rd HS3 Usp3 off;
  [ cbn [sv_denot]; rewrite OLD3 by (cbv; lia); rewrite EL by (unfold A_TEXT; lia);
    rewrite (ew_Ereg_nat regs _ rn rb eq_refl), Z.add_0_r; reflexivity
  | exact (bv_unsigned_in_range 64 _) ] in
let sregs u :=
  split; [ sreg (-104) 27%nat (27%bv : bv 5) |];
  split; [ sreg (-96) 26%nat (26%bv : bv 5) |];
  split; [ sreg (-88) 25%nat (25%bv : bv 5) |];
  split; [ sreg (-80) 24%nat (24%bv : bv 5) |];
  split; [ sreg (-72) 23%nat (23%bv : bv 5) |];
  split; [ sreg (-64) 22%nat (22%bv : bv 5) |];
  split; [ sreg (-56) 21%nat (21%bv : bv 5) |];
  split; [ sreg (-48) 20%nat (20%bv : bv 5) |];
  split; [ sreg (-40) 19%nat (19%bv : bv 5) |];
  split; [ sreg (-32) 18%nat (18%bv : bv 5) |];
  split; [ sreg (-24) 9%nat (9%bv : bv 5) |];
  split; [ sreg (-16) 8%nat (8%bv : bv 5) |];
  sreg (-8) 1%nat (1%bv : bv 5) in
(* sp, gp, tp, s0 = o, s1 = v at a join *)
let regs5 u :=
  split; [ wvc_reg HS3 (2%bv : bv 5);
           rewrite (wvc_den_off EH 2 (-192) (spZ regs));
           [unfold w64; f_equal; lia | rewrite OLD3 by (cbv; lia); exact E2 | lia | lia] |];
  split; [ wvc_reg HS3 (3%bv : bv 5); cbn [sv_denot]; rewrite OLD3 by (cbv; lia); rewrite E3, Hgp;
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity |];
  split; [ wvc_reg HS3 (4%bv : bv 5); cbn [sv_denot]; rewrite OLD3 by (cbv; lia); rewrite E4, Htp;
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity |];
  split; [ wvc_reg HS3 (8%bv : bv 5); cbn [sv_denot]; rewrite OLD3 by (cbv; lia); rewrite E10, H10;
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity |];
  split; [ wvc_reg HS3 (9%bv : bv 5); rewrite (wvc_den_off EH 11 0 v);
           [rewrite Z.add_0_r; reflexivity | rewrite OLD3 by (cbv; lia); exact E11 | lia | lia] |] in
(* frame words 72 (the shadow offset) and 80 (v's shadow) *)
let fw72 u :=
  wvc_rd HS3 Usp3 (-120);
  [ cbn [sv_denot]; rewrite OLD3 by (cbv; lia); rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia);
    rewrite Z.add_0_r; reflexivity
  | unfold SHADOW_OFF; lia ] in
let fw80 u :=
  wvc_rd HS3 Usp3 (-112);
  [ rewrite (wvc_den_sh EH 11 0 v ltac:(rewrite OLD3 by (cbv; lia); exact E11)
             ltac:(rewrite OLD3 by (cbv; lia); exact E32) ltac:(lia) ltac:(lia));
    rewrite Z.add_0_r; reflexivity
  | pose proof (wv_shadow_low v ltac:(lia)); lia ] in
(* a literal of the listing as a frame word's engine term *)
let lit_word k :=
  unfold WV_STR;
  let HAT := fresh "HAT" in assert (HAT : wv_addhi_atom k = A_OBJ 2) by (vm_compute; reflexivity);
  rewrite HAT; cbn [sv_denot]; rewrite HEI3 by (unfold A_OBJ, A_TEXT, A_LIM; lia);
  let off := eval vm_compute in (wv_addhi_off k) in change (wv_addhi_off k) with off; reflexivity in
(* THE LOOP HEAD (slot 90) at i = 0: wv_HEADKR at wle', at the entry float state *)
let head ssep bso :=
  idtac;
  pmkst HS3;
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?c)] => replace c with WVH_PC by (vm_compute; reflexivity) end;
  lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst (ms_regs ?msH) _ _ _) ?mdH) _ =>
  lazymatch type of HJc with _ ?kH =>
    apply (HLOOP fx 0%nat [bso] ly2 S2 Hp2 W2 (ms_regs msH) (ms_mem msH) mdH kH);
    unfold wv_headR; cbv zeta;
    unfold wv_commonR, wv_done, wv_sep_slot, y_sp, y_FP, y_p;
    cbn [y_fx y_d y_STK y_ly y_S y_Hp y_W y_regs y_mem y_md y_o y_v y_pretty y_dep y_buf y_st y_t y_D y_Lam y_peak
      y_ran y_most y_own y_rpsm y_rpx y_rpos y_rpi y_rpH0 y_rphist wv_nitems];
    assert (Hdep1 : dep + 1 < 2 ^ 31)
      by (first [cbn [PjTree.depth] in Hdep2; lia | simpl in Hdep2; lia]);
    split; [ common () |];
    split; [lia |];
    split; [reflexivity |];
    (* the registers *)
    regs5 ();
    split; [ wvc_reg HS3 (18%bv : bv 5); rewrite (wvc_den_off EH 11 40 v);
             [reflexivity | rewrite OLD3 by (cbv; lia); exact E11 | lia | lia] |];
    split; [ wvc_reg HS3 (19%bv : bv 5); rewrite (wvc_den_off EH 12 0 pretty);
             [rewrite Z.add_0_r; reflexivity | exact E3_12 | lia | lia] |];
    split; [ wvc_reg HS3 (20%bv : bv 5);
             exact (wvc_den_sh EH 11 24 v ltac:(rewrite OLD3 by (cbv; lia); exact E11)
                      ltac:(rewrite OLD3 by (cbv; lia); exact E32) ltac:(lia) ltac:(lia)) |];
    split; [ wvc_reg HS3 (21%bv : bv 5); reflexivity |];
    split; [ wvc_reg HS3 (22%bv : bv 5);
             exact (wvc_den_addw EH dep ltac:(rewrite OLD3 by (cbv; lia); exact E13) ltac:(lia) ltac:(lia)) |];
    split; [ wvc_reg HS3 (23%bv : bv 5); reflexivity |];
    split; [ wvc_reg HS3 (24%bv : bv 5); rewrite (wvc_den_off EH 11 24 v);
             [reflexivity | rewrite OLD3 by (cbv; lia); exact E11 | lia | lia] |];
    split; [ wvc_reg HS3 (25%bv : bv 5); reflexivity |];
    split; [ wvc_reg HS3 (26%bv : bv 5);
             exact (wvc_den_slt EH dep ltac:(rewrite OLD3 by (cbv; lia); exact E13) ltac:(lia) ltac:(lia)) |];
    split; [ wvc_reg HS3 (27%bv : bv 5);
             exact (wvc_den_sh EH 11 40 v ltac:(rewrite OLD3 by (cbv; lia); exact E11)
                      ltac:(rewrite OLD3 by (cbv; lia); exact E32) ltac:(lia) ltac:(lia)) |];
    (* the own frame's words *)
    split; [ wvc_rd HS3 Usp3 (-184); [reflexivity | lia] |];
    split; [ wvc_rd HS3 Usp3 (-176); [reflexivity | lia] |];
    split; [ wvc_rd HS3 Usp3 (-168);
             [ cbn [sv_denot]; rewrite OLD3 by (cbv; lia); rewrite E13, Z.add_0_r, unsigned_lit_small by lia;
               reflexivity
             | lia ] |];
    split; [ wvc_rd HS3 Usp3 (-160);
             [ exact (wvc_den_pr EH pretty E3_12 Hpr) | destruct (pretty =? 0); lia ] |];
    split; [ wvc_rd HS3 Usp3 (-152);
             [ exact (wvc_den_sh EH 11 32 v ltac:(rewrite OLD3 by (cbv; lia); exact E11)
                        ltac:(rewrite OLD3 by (cbv; lia); exact E32) ltac:(lia) ltac:(lia))
             | pose proof (wv_shadow_low (v + 32) ltac:(lia)); lia ] |];
    split; [ wvc_rd HS3 Usp3 (-144);
             [ exact (wvc_den_off EH 11 32 v ltac:(rewrite OLD3 by (cbv; lia); exact E11) ltac:(lia) ltac:(lia))
             | lia ] |];
    split; [ let Hss := fresh "Hss" in
             assert (Hss : (if pretty =? 0 then 57%nat else 54%nat) = ssep)
               by (first [ rewrite (proj2 (Z.eqb_eq pretty 0) Hpz); reflexivity
                         | rewrite (proj2 (Z.eqb_neq pretty 0) Hpz); reflexivity ]);
             rewrite Hss;
             wvc_rd HS3 Usp3 (-136);
             [ lit_word ssep
             | pose proof (HIMG ssep _ ltac:(unfold wv_lits; cbn [In]; repeat (first [left; reflexivity | right]))
                 ltac:(cbn; lia)); lia ] |];
    split; [ wvc_rd HS3 Usp3 (-128);
             [ lit_word 88%nat
             | pose proof (HIMG 88%nat [44] ltac:(unfold wv_lits; cbn [In]; repeat (first [left; reflexivity | right]))
                 ltac:(cbn; lia)); lia ] |];
    split; [ fw72 () |];
    split; [ fw80 () |];
    sregs ()
  end end
in
(* THE CLOSE (slot 173) of the empty container: wv_CLOSEKR at wle', at the entry float state *)
let close bso :=
  idtac;
  pmkst HS3;
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?c)] => replace c with WVC_PC by (vm_compute; reflexivity) end;
  lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst (ms_regs ?msC) _ _ _) ?mdC) _ =>
  lazymatch type of HJc with _ ?kC =>
    apply (HCLOSE fx ly2 S2 Hp2 W2 (ms_regs msC) (ms_mem msC) mdC kC);
    unfold wv_clR; cbv zeta;
    lazymatch goal with |- context [wv_clP ?x] => change (wv_clP x) with [bso] end;
    unfold wv_commonR, y_sp, y_FP, y_p;
    cbn [y_fx y_d y_STK y_ly y_S y_Hp y_W y_regs y_mem y_md y_o y_v y_pretty y_dep y_buf y_st y_t y_D y_Lam y_peak
      y_ran y_most y_own y_rpsm y_rpx y_rpos y_rpi y_rpH0 y_rphist];
    split; [ common () |];
    regs5 ();
    split; [ wvc_rd HS3 Usp3 (-176); [reflexivity | lia] |];
    split; [ fw72 () |];
    split; [ fw80 () |];
    sregs ()
  end end
in
(* the n branch at slot 65 (`beqz n`), the separator literal's slot ssep *)
let narm ssep bso :=
  idtac;
  psrr_branch_tokR RUNIR BRR HS3 SHOK3 WV_Bspan;
  [ (* n = 0: the empty container joins the close *)
    rewrite branch_eq_U, (U_atom EH 37 nn E3_37 Rnn), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia);
    apply Z.eqb_eq in Hc;
    destruct l as [|x0 l0]; [| exfalso; cbn [length] in Hnn; lia];
    paj_run_to_tok_x_invR RUNTOIR HS3 HJc SHOK3 HPM2 WV_Bspan (AF_write_value + 4 * 173); [ wvc_awr_tac Usp3 d | ];
    wvc_keep_run HFr K4 K5 mem2 (wv_wr (spZ regs)) Usp3; clear HF HFr HG;
    close bso
  | (* n <> 0: the loop init, then the loop head *)
    rewrite branch_eq_U, (U_atom EH 37 nn E3_37 Rnn), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia);
    apply Z.eqb_neq in Hc;
    paj_run_to_tok_x_invR RUNTOIR HS3 HJc SHOK3 HPM2 WV_Bspan (AF_write_value + 4 * 90); [ wvc_awr_tac Usp3 d | ];
    wvc_keep_run HFr K4 K5 mem2 (wv_wr (spZ regs)) Usp3; clear HF HFr HG;
    head ssep bso ]
in
(* the container at tag tg (jump-table index kn), its opening bracket the literal at slot slo, bytes bso, tree tt *)
let run tg kn slo bso tt :=
  idtac;
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
  destruct (wv_seat ly S Hp W regs mem md ch STKv o v pretty dep tg str kids keys nn ltac:(lia) HPREx H10 H11 H12 H13
    Hv8 Hv4096 Hv47 Hvst Hband ltac:(intros a Ha; split; [exact (Hvimg a Ha) | exact (Hrwr a Ha)])
    Vtg ltac:(lia) Vstr Rstr Vkids Rkids Vkeys Rkeys Vnn Rnn HRA
    HTvm HTr ltac:(split; lia) ltac:(left; lia) HTg HTc HTn ltac:(vm_compute; reflexivity)) as [HS SHOK];
  set (E := wv_E regs v str kids keys nn (WV_JTW (Z.to_nat tg))) in *;
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold wv_E; apply Eimg_env);
  assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat tg)))) k)
    by (intros k0 Hk; subst E; unfold wv_E; apply Eimg_low; exact Hk);
  assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
  assert (Usp : bv_unsigned (ew E 2) = spZ regs)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity);
  assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); unfold spZ;
        symmetry; apply Z_to_bv_bv_unsigned);
  assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl));
  assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl));
  assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl));
  assert (E11 : ew E 11 = Z_to_bv 64 v)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11);
  assert (E12 : ew E 12 = Z_to_bv 64 pretty)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12);
  assert (E13 : ew E 13 = Z_to_bv 64 dep)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13);
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0));
  assert (E37 : ew E 37 = Z_to_bv 64 nn) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5));
  assert (HAE : env_agree 32 (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat tg)))) E)
    by (split; [intros k0 Hk; apply EL; unfold A_TEXT; lia | reflexivity]);
  assert (K00 : forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a)
    by (intros; reflexivity);
  unfold cfg_at; rewrite Hent; change (w64 (BASE + AF_write_value)) with (Z_to_bv 64 (BASE + AF_write_value));
  (* entry -> the switch's jr (slot 40) *)
  paj_run_tok_x_invR RUNIR HS HJ SHOK HPm WV_Bspan;
  [ eapply (wv_awr E tg _ _ _ _ _ _ _ (spZ regs)); [exact Usp | lia | lia] | ];
  wvc_keep_run HFr K00 K1 mem (wv_wr (spZ regs)) Usp; clear HF HFr HG;
  prreg HS (11%bv : bv 5) R11;
  assert (E38 : ew E 38 = Z_to_bv 64 (WV_JTW (Z.to_nat tg)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6));
  assert (EJ : ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)))
    by (subst E; unfold wv_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia);
  destruct (wv_jr_target E (Z.to_nat tg) E38 EJ HTr) as (Hjt & Hjr & Hje);
  eapply (wvc_jr_step E _ _ W _ _ (BASE + AF_wv_case kn) HS);
  [ vm_compute; reflexivity | reflexivity | rewrite R11; exact Hjt | exact Hjr | exact Hje | ];
  let mat1 := fresh "mat" in let ms1 := fresh "ms" in let Hms1 := fresh "Hms" in let HS1 := fresh "HS1" in
  intros mat1 ms1 Hms1 HS1; subst ms1;
  pose proof (wv_pi_at E _ (AF_wv_case kn) _ HS1) as HS2; clear HS1;
  assert (HJ2 := HJ);
  eapply (ajournal_x_materializeR (SK := SK)) with (X := mat1) in HJ2;
  [| first [exact LAWS | exact pa_segs_low | idtac] ..];
  clear HJ;
  (* case 41 -> `beq tag, 6` -> the opening bracket -> its `jal put` (slot 50) *)
  paj_run_tok_x_invR RUNIR HS2 HJ2 SHOK HPm WV_Bspan; [ wvc_awr_tac Usp d | ];
  wvc_keep_run HFr K1 K2 mem (wv_wr (spZ regs)) Usp; clear HF HFr HG;
  pmkst HS2;
  prreg HS2 (10%bv : bv 5) Ra0; prreg HS2 (11%bv : bv 5) Ra1; prreg HS2 (12%bv : bv 5) Ra2;
  prreg HS2 (1%bv : bv 5) Rra1; prreg HS2 (2%bv : bv 5) Rsp1; prreg HS2 (3%bv : bv 5) Rgp1;
  prreg HS2 (4%bv : bv 5) Rtp1; prreg HS2 (8%bv : bv 5) Rs01;
  lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
    assert (HspT : spZ rT = spZ regs - 192)
      by (unfold spZ at 1; rewrite Rsp1, Usp; rewrite unsigned_lit_small by lia; lia);
    pose proof (proj1 HJ2) as HARc;
    assert (HOUTc : prhWriter_out W mT Lam o buf st)
      by (apply (wv_out_keep ly S Hp W W mem mT md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow
            o buf st (wv_wr (spZ regs))); [exact HAR | exact HLED | exact HOUT | exact K2 | exact HLOW | exact HOFF]);
    assert (HLEDc : prh_ledger B ly S Hp W mT Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow)
      by (apply (wv_led_keep ly S Hp W md mem mT Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow
            (wv_wr (spZ regs))); [exact HAR | exact HLED | exact K2 | exact HLOW8]);
    assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mT))
      by (apply (wv_arodata_keep W W mem mT (wv_wr (spZ regs))); [exact HRO | exact K2 | exact HLOW]);
    destruct (HLIT slo bso ly S Hp W mT dT
      ltac:(unfold wv_lits; cbn [In]; repeat (first [left; reflexivity | right])) HARc HROc)
      as (Hsrc & Hkept & Himg);
    pose proof (wv_lit_home ly S Hp W mem md Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow buf
      (WriterApp.w_cap st) (WV_STR slo) (Z.of_nat (length bso)) HAR HLED Hbufin (proj1 Hcap0)
      ltac:(vm_compute; reflexivity) Hkept
      ltac:(intros a Ha; replace a with (WV_STR slo + (a - WV_STR slo)) by lia; apply Himg; lia)) as Hhome;
    (* The case-1 words (form (a)) at the call memory *)
    assert (HWD : exists ra1 nfp1, rdword (aview SEGS (w_H W) mT) (o - 8) = Some ra1 /\
        rdword (aview SEGS (w_H W) mT) (o - 16) = Some nfp1 /\ nfp1 < YM05.alloc_ceiling);
    [ destruct Hcut as [Hc1 | Hc2];
      [ destruct (wv_reca_keep (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mT) o
          ltac:(intros a Ha; apply K2; [lia | unfold wv_wr; lia]) (Hch0 Hc1)) as (ra1 & Hr1 & nfp1 & Hn1 & Hnl);
        exists ra1, nfp1; split; [exact Hr1 | split; [exact Hn1 | exact Hnl]]
      | destruct (wvc_rdword_some (aview SEGS (w_H W) mT) (spZ regs)) as (w & Hw);
        [ intros j Hj; rewrite (K2 (spZ regs + j)) by (unfold wv_wr; lia);
          apply (aview_some_of_apresent SEGS); apply Hdpres; lia |];
        exists w, (bv_unsigned (getr regs 1));
        split; [replace (o - 8) with (spZ regs) by lia; exact Hw |];
        split; [| unfold raZ in HTOP2; exact HTOP2];
        eapply (wvc_chunk_rdb _ _ _ _ 1%nat 2%nat _ _ _ _ _ (-8));
        [ exact HS2 | reflexivity | exact Usp | lia | cbn [In]; repeat (first [left; reflexivity | right])
        | cbn [sv_denot]; rewrite E1, Z.add_0_r; reflexivity
        | apply bv_unsigned_in_range ] ]
    | ];
    destruct HWD as (ra1 & nfp1 & Hwd8 & Hwd16 & Hwdc);
    assert (Hw1 : Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length bso) + 1 <= prhWriter_WMAX)
      by (pose proof (wv_wmax_next [] st [] [bso] (tl (WriterValue.wvpieces tt (negb (pretty =? 0)) dep)) Hwmax) as X;
          cbn [prhWriter_putN concat app] in X; rewrite ?app_nil_r in X; exact X);
    assert (Hl1 : prh_live_evs S (prhWriter_evs [] st [bso]))
      by (exact (prhW_live_pre S st [bso] (tl (WriterValue.wvpieces tt (negb (pretty =? 0)) dep)) Hlive));
    assert (Hc1 : PRH_Base.prh_cons_from rpsm rpx rpos rpi (length (prhWriter_evs [] st [bso])))
      by (exact (prhW_cons_pre rpsm rpx rpos rpi st [bso] (tl (WriterValue.wvpieces tt (negb (pretty =? 0)) dep))
            Hcons0));
    eapply (SRr'_bind SEGS RZ_cf);
    [ eapply (wv_call_put rpsm rpx rpos rpi rpH0 rphist (STKv + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st))
        ly S Hp W mem md [] ly S Hp W mT dT 0 rT _ ra1 nfp1 o (WV_STR slo) 1 buf st bso Lam peak ran gmo gow
        (- (192 + d)) HFRM HJ2);
      [ rewrite HspT; lia
      | apply wv_neg_mod16; rewrite Zplus_mod, Hd16; reflexivity
      | lia
      | lia
      | rewrite Rgp1, E3; exact Hgp
      | rewrite Rtp1, E4; exact Htp
      | exact Rra1
      | apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]
      | rewrite unsigned_lit_small by (pose proof (@pa_B_ok _ B_prog_listing PA) as (HB0 & HB1 & _); lia);
        pose proof (@pa_B_ok _ B_prog_listing PA); lia
      | lazymatch goal with |- bv_unsigned (Z_to_bv 64 (BASE + ?k)) < _ =>
          replace k with (AF_write_value + 4 * 51) by (vm_compute; reflexivity) end;
        exact wvc_ret51_ceil
      | unfold s0Z; rewrite Rs01, E10, H10; apply unsigned_lit_small; lia
      | exact Hwd8 | exact Hwd16 | exact Hwdc
      | exact HROc
      | lia
      | exact Hroom | exact Hrp | exact Hlen4 | exact Hc1 | exact Hcl
      | rewrite Ra0, E10; exact H10
      | rewrite Ra1; unfold WV_STR;
        let HAT := fresh "HAT" in
        assert (HAT : wv_addhi_atom slo = A_OBJ 2) by (vm_compute; reflexivity);
        rewrite HAT; rewrite HEI by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        let off := eval vm_compute in (wv_addhi_off slo) in change (wv_addhi_off slo) with off; reflexivity
      | rewrite Ra2; reflexivity
      | lia | lia
      | exact HOUTc | exact HLEDc | exact Hsrc | reflexivity | exact Hhome
      | exact (wv_ev_first rpsm rpx rpos rpi st bso (tl (WriterValue.wvpieces tt (negb (pretty =? 0)) dep)) Hev)
      | exact Hw1 | exact Hhead | exact Hl1
      | exact (wv_fp_sub (STKv + d) (spZ regs + d) ly S ly S Hp W mT dT o Lam peak buf st Lam peak buf st HARc
          (proj1 Hcap0) (or_introl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (Permutation_refl _)))))))
      ]
    | (* the put returned (slot 51) *)
      cbv beta;
      intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJc & HJ1 & HXT & HP2 &
        (Hroom2 & HPP1 & HRET1) & HMN2);
      pose proof (PCALL mT mem2 HMN2 HPm) as HPM2;
      pose proof (wv_ret_pos_one rpsm rpx rpos rpH0 rpi rphist ly S Hp W mT Lam peak ran gmo gow o buf st bso
        ly2 S2 Hp2 W2 regs2 mem2 md2 HOUTc HLEDc HPP1 HRET1) as HRP1;
      clear HPP1 HRET1;
      destruct HRP1 as (ok1 & HRET1 & HG1 & rphist1 & Hrp1);
      destruct (prhWriter_ret_ok_g B ok1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpk0 HG1 HRET1)
        as (ran1 & buf1 & Lam1 & peak1 & HOKS1 & HOUT1 & HLED1 & HBLK1);
      pose proof HJc as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _);
      replace (spZ regs + d + - (192 + d) + - - (192 + d)) with (spZ regs + d) in HJ1 by lia;
      assert (HFK : forall x, pj_footR v D x -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mT x)
        by (intros x Hx; exact (proj2 (wv_foot_keepR (wle' SEGS RZ_cf) ly S Hp W regs mT dT STKv
              (STK_put + - - (192 + d)) d o buf
              (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow v D
              ly2 S2 Hp2 W2 mem2 md2 k1
              ltac:(lia) Hd0 HARc Hstk HLEDc HLOC HD Hoff (proj1 Hcap0) Hbufin HJ1
              ltac:(intros a Ha Hf; apply HXT; [lia | exact Hf]) x Hx)));
      (* the after-call state: the own frame and the node kept (regions 1 and 4 of the call state) *)
      jafter_call_keep_pi HS2 39%nat regs2 (mrestrict (w_H W2) mem2) HP2 [1; 4]%nat HS3;
      lazymatch type of HS3 with ?T -> _ => assert (HRK : T) end;
      [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
        [ split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp;
          intros a Ha;
          [ apply (mbyte_of_aview SEGS); apply HXT;
            [lia | apply (wvc_nfp ly S Hp W mT dT o buf (WriterApp.w_cap st) a HARc Hbufb); lia]
          | intros _; apply (apresent_writable SEGS); apply Hpres2; lia ]
        | split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
          rewrite E11, unsigned_lit_small by lia; intros a Ha;
          [ apply (mbyte_of_aview SEGS); apply HFK; left; lia
          | exfalso; lia ] ]
      | ];
      specialize (HS3 HRK); clear HRK; rewrite <- restrict_mkst_fx in HS3;
      remember (havoc E 39 (map (getr regs2) CLOB)) as EH eqn:HE3 in HS3;
      assert (HEI3 : img_env VAL A_LIM EH) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]);
      assert (OLD3 : forall n, (n < 39)%nat -> ew EH n = ew E n)
        by (intros n0 Hn; rewrite HE3; apply ew_havoc_old; exact Hn);
      assert (HAE3 : env_agree 32 (Ereg regs (wv_extra v str kids keys nn (WV_JTW (Z.to_nat tg)))) EH)
        by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE]);
      clear HE3;
      assert (Usp3 : bv_unsigned (ew EH 2) = spZ regs) by (rewrite OLD3 by (cbv; lia); exact Usp);
      assert (HLK1 : forall a k, In (a, k) Lam -> a <> buf -> In (a, k) Lam1)
        by (intros a k0 Ha Hab; exact (proj1 (wv_lam_keep ly S Lam peak buf st ly2 S2 Lam1 peak1 buf1 _
              (wv_led_nodup _ _ _ _ _ _ _ _ _ _ _ _ HLED1) HBLK1 a k0 Ha Hab)));
      (* v's 56 bytes addressable at the after-call memory: the shadow entry of the node, for the shadow check of
         v + 40 (slots 59-63) *)
      assert (RA2 : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF v 56)
        by (exact (wv_ra_curR (wle' SEGS RZ_cf) ly S Hp W mem md Lam buf v regs STKv d o (WriterApp.w_cap st)
              ly2 S2 Hp2 W2 mem2 md2 (0 + k1) Lam1 peak1 _ _ ran1 gmo gow HAR Hstk HRA HLOC HJc HLED1 HLK1 ltac:(lia)
              Hbufb));
      assert (SHOK3 : sh_ok SEGS WV_Bx wv_SH EH (mrestrict (w_H W2) mem2))
        by (apply (wvc_shok (w_H W2) mem2 EH v RA2);
            [rewrite OLD3 by (cbv; lia); exact E32 | rewrite OLD3 by (cbv; lia); exact E11 | lia | lia | exact Hband]);
      assert (K20 : forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a) by (intros; reflexivity);
      (* slot 51 -> `beqz s3` (slot 52, pretty) *)
      paj_run_tok_x_invR RUNIR HS3 HJc SHOK3 HPM2 WV_Bspan; [ wvc_awr_tac Usp3 d | ];
      wvc_keep_run HFr K20 K3 mem2 (wv_wr (spZ regs)) Usp3; clear HF HFr HG;
      assert (E3_37 : ew EH 37 = Z_to_bv 64 nn) by (rewrite OLD3 by (cbv; lia); exact E37);
      assert (E3_12 : ew EH 12 = Z_to_bv 64 pretty) by (rewrite OLD3 by (cbv; lia); exact E12);
      psrr_branch_tokR RUNIR BRR HS3 SHOK3 WV_Bspan;
      [ (* pretty = 0: ":" (slot 57), then the shadow check of v + 40 and `beqz n` (slot 65) *)
        rename Hc into Hpz;
        rewrite branch_eq_U, (U_atom EH 12 pretty E3_12 Hpr), U_SLit, (zcanon_id 0) in Hpz by (unfold M64; lia);
        apply Z.eqb_eq in Hpz;
        paj_run_tok_x_invR RUNIR HS3 HJc SHOK3 HPM2 WV_Bspan; [ wvc_awr_tac Usp3 d | ];
        wvc_keep_run HFr K3 K4 mem2 (wv_wr (spZ regs)) Usp3; clear HF HFr HG;
        narm 57%nat bso
      | (* pretty <> 0: ": " (slot 54) *)
        rename Hc into Hpz;
        rewrite branch_eq_U, (U_atom EH 12 pretty E3_12 Hpr), U_SLit, (zcanon_id 0) in Hpz by (unfold M64; lia);
        apply Z.eqb_neq in Hpz;
        paj_run_tok_x_invR RUNIR HS3 HJc SHOK3 HPM2 WV_Bspan; [ wvc_awr_tac Usp3 d | ];
        wvc_keep_run HFr K3 K4 mem2 (wv_wr (spZ regs)) Usp3; clear HF HFr HG;
        narm 54%nat bso ] ]
  end
in
destruct Ht as [[l ->] | [l ->]];
[ pose proof HNODE as HNODE0;
  destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody);
  destruct Hbody as (_ & _ & Hnn & _);
  run 5 5%nat 44%nat [91] (PjTree.JArr l)
| pose proof HNODE as HNODE0;
  destruct HNODE as (HND & HAPt & num & str & kids & keys & nn & cap & Hhdr & Hbody);
  destruct Hbody as (_ & Hnn & _);
  run 6 6%nat 47%nat [123] (PjTree.JObj l) ].
Qed.

End cont.
End cl.
End h.
End f.
End d.
