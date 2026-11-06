(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d): the CALL
   SITES of the write_value walk: the two tail calls (put at slot 268, put_string at slot 207) and the inner calls of
   the item loop (put, indent, put_string, the recursive write_value), ONE lemma per callee, so a new premise of a
   callee's text threads through in one place. Over WriteValueB_Base's Section (the same variables, bound by `Let`)
   and the callee texts of the draft (lib/A/PRH_FnWriter.v) as this file's Section hypotheses
   PUT / PUTSTR / INDENT, at the Section's float state fx. Each call takes the callee's window prh_cons_from and its
   per-event live room prh_live_evs (supplied by the caller from its own, WriteValueB_Model.prhW_cons_mid /
   prhW_live_mid), and each callee post carries prh_granted.
   PORTED (not cited) from the kit owner's image-A walk PRW_write_value.v (a working branch
   7819c4b4583, Section cl, :1662-2441) with these changes: B's frame 192 (oc = - (d + 192)); the #102 ledger cells
   most / own threaded; tput_specX's NULL arm keyed on f' = 1; the engine's YCbqGcallW.aj_call_xW / aj_call_xWF and
   fp_sub_x (the core's, which superseded PRW_CallerJ's aj_call_xW / fp_sub_x); and the FLOAT FORM of the #102
   texts: put_string and write_value post fpostWFm, so the tail put_string concludes write_value's fpostWFm and the
   inner put_string / write_value calls go through aj_call_xWF and leave the continuation at the callee's fx'
   (frm_zero, fregs_kept_x).
   Numerals: 192 (LENGTH: write_value's frame), 16 (LENGTH: stack alignment), 24 / 4 / 32 (LENGTH: the out struct's
   failed field and size). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import WriteValueB_Model WriteValueB_Base.
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

(* Every callee may realloc, and a realloc may hide shadow again, so a run that crosses a call continues at
   wle' SEGS RZ_cf, not at wle: each conclusion below is SRr' SEGS RZ_cf and each journal after a call is at that
   relation. A journal of write_value's own stretch before its first call is at wle; this widens it. *)
Lemma wv_jR {STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k} :
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) STK sp0 FP ly S Hp W mem md own
    ly' S' Hp' W' mem' md' k.
Proof.
intros HJ.
exact (ajournal_xbR_mono (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (@wle SEGS) (wle' SEGS RZ_cf)
  (wle_wle' SEGS RZ_cf) STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k [] HJ).
Qed.

Section cl.
Variable CTX0 : list (list Z).
(* the callee texts, the draft's texts VERBATIM (lib/A/PRH_FnWriter.v), at this Section's float
   state fx; owners: put (tput_specX) its own lane, put_string (tput_string_specX) its own lane, indent
   (tindent_specX) a Theorem Labs lane / the indent lane (a Theorem Labs session assigns) *)
Hypothesis PUT : tput_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis PUTSTR : tput_string_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis INDENT : tindent_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.

Lemma wv_neg_mod16 : forall d, d mod 16 = 0 -> (- d) mod 16 = 0.
Proof.
intros d H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->].
apply Z.mod_divide; [lia|]. exists (- q). lia.
Qed.

Lemma wv_tail_put : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf (st : WriterApp.wst) s (bs : list Z)
    memc mdc regsc,
  192 <= STKv -> STK_put <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [bs])) ->
  prh_univ_closure B CTX0 ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
  prhWriter_out W mem Lam o buf st ->
  pj_nodeR SEGS (mrestrict (w_H W) memc) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
  (forall a, spZ regs <= a < spZ regs + d -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  aregs_preserved regs regsc -> spZ regsc = spZ regs -> getr regsc 1 = getr regs 1 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain ly (aview SEGS (w_H W) memc) (spZ regs) (s0Z regsc) ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s -> getr regsc 12 = w64 (Z.of_nat (length bs)) ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B ly S Hp W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
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
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf st s bs
  memc mdc regsc HSTK HSTKp HPRE Hroom Hrp Hos Hcons Hcl HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ HKEEPW
  HAP Hspc Hrac Hgpc Htpc Hchc Hroc H10 H11 H12 Hcut Hch0 HOUTc HLEDc Hev Hsrc Hhome Hwmax Hhead Hlive HMN.
pose proof HPRE as (HPREx & Hro & Htop).
pose proof HPREx as (HARe & Hret & Hra4 & _ & _ & Hstk & _).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
eapply (SRr'_mono SEGS RZ_cf).
- eapply (@aj_call_xWR fx rc SK SEGS B (@prh_pst prh_img_B) ARx _ LAWS pa_segs_low
    (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W regsc memc (SIGMA AS_put)
    (STKv + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp mdc 0
    STK_put d (prhWriter_cfp o buf (WriterApp.w_cap st)) (- d) (getr regs 1) ch
    (fun ly' S' Hp' W' regs' mem' md' => (room_live_cf S' /\
       (prhWriter_grows st bs = false -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S') /\
       (prhWriter_grows st bs = true -> forall f', val_mem SEGS (mrestrict (w_H W') mem') (o + 24) 4 f' ->
          (f' = 0 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S') /\
          (f' = 1 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S')) /\
       exists ok, prhWriter_ret_ok B ok ly S Lam peak ran gmo gow o buf st [bs] ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st [bs])) /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem')) (wv_jR HJ));
    [lia | apply wv_neg_mod16; exact Hd16 | lia | vm_compute; congruence | lia | lia | exact Hd16 | lia
    | exact Hgpc | exact Htpc | exact Hrac | exact Hret | unfold raZ in Hra4; exact Hra4
    | replace (spZ regs + d + - d) with (spZ regs) by lia; exact Hchc | | ].
  + intros Hpre Hwin.
    assert (Ho1' : spZ regsc <= o) by lia.
    assert (Ho2' : o + 32 <= spZ regsc + d) by lia.
    assert (Hfpre : fpre B ARx STK_put ly S Hp W regsc memc mdc ch).
    { split; [exact Hpre|]. split; [exact Hroc|].
      split; [rewrite Hspc; exact (proj1 Htop) | split; [unfold raZ; rewrite Hrac; exact (proj1 (proj2 Htop)) | exact (proj2 (proj2 Htop))]]. }
    exact (PUT rp_sm rp_x rp_os rp_i rp_H0 rp_hist gmo gow ly S Hp W regsc memc mdc ch o s (Z.of_nat (length bs)) d buf st
      bs Lam peak ran Hfpre Hroom Hrp Hos Hcons Hcl H10 H11 H12
      ltac:(rewrite Hspc; exact Hcut) ltac:(rewrite Hspc; exact Hch0) Hwin Ho1' Ho2'
      HOUTc HLEDc Hsrc eq_refl Hhome (wv_ev_first rp_sm rp_x rp_os rp_i st bs [] Hev) Hwmax Hhead Hlive).
  + intros a Ha. left. exact Ha.
- cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJ2 & HJc & HXT & HP2 & HQ).
  exists ly2, S2, Hp2, regs2, mem2, md2, (0 + k1)%Z.
  split; [exact Hc2|].
  split; [exact HJ2|].
  split.
  { intros a Ha Hf. rewrite (HXT a ltac:(lia) Hf). exact (HKEEPW a Ha). }
  split; [exact (aregs_preserved_trans regs regsc regs2 HAP HP2)|].
  destruct HQ as ((HQ1 & HQN & HQG & HQ3) & HQM).
  split; [|intros Hmn; exact (HQM (HMN Hmn))].
  split; [exact HQ1|].
  split; [|exact (wv_ret_pos_one rp_sm rp_x rp_os rp_H0 rp_i rp_hist ly S Hp W memc Lam peak ran gmo gow o buf st bs
             ly2 S2 Hp2 W2 regs2 mem2 md2 HOUTc HLEDc (conj HQN HQG) HQ3)].
  assert (HJc' : ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (STK_put + d) (spZ regs + d)
      (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1).
  { replace (spZ regs + d) with (spZ regs + d + - d + d) by lia. exact HJc. }
  apply (wv_nodeR_keep W W2 memc mem2 Lam v t D HNODE).
  + intros x Hx. exact (proj1 (wv_foot_keepR (wle' SEGS RZ_cf) ly S Hp W regs memc mdc STKv (STK_put + d) d o buf
      (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow v D
      ly2 S2 Hp2 W2 mem2 md2 k1 HSTK Hd0 ltac:(exact (proj1 HJ)) Hstk HLEDc HLOC HD Hoff ltac:(lia) Hbufin
      HJc' ltac:(intros a Ha Hf; apply HXT; [lia | exact Hf]) x Hx)).
  + intros x Hx. exact (proj2 (wv_foot_keepR (wle' SEGS RZ_cf) ly S Hp W regs memc mdc STKv (STK_put + d) d o buf
      (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow v D
      ly2 S2 Hp2 W2 mem2 md2 k1 HSTK Hd0 ltac:(exact (proj1 HJ)) Hstk HLEDc HLOC HD Hoff ltac:(lia) Hbufin
      HJc' ltac:(intros a Ha Hf; apply HXT; [lia | exact Hf]) x Hx)).
Qed.

(* ---- FROM THE STATE AT THE TAIL put TO THE WHOLE POST: between the entry and the tail call write_value writes
   only its own frame, so the writer struct, the ledger, the read-only view, the caller's chain and the tree are
   still the entry's at the call; what the leaf must supply is the source word (a literal, or a number's text) ---- *)
Lemma wv_put_close : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf (st : WriterApp.wst) s (bs : list Z)
    memc mdc regsc,
  200 <= STKv -> STK_put <= STKv ->
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
  (forall a, 0 <= a < 2 ^ 64 -> ~ wv_wr (spZ regs) a -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
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
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf st s bs
  memc mdc regsc HSTK HSTKp HPRE Hroom Hrp Hos Hcons Hcl HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ HKEEP
  HAP Hrac H10 H11 H12 Hcut Hch0 Hev Hsrc Hhome Hwmax Hhead Hlive HMN.
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
(* the callee-saved registers of the state at the call *)
assert (Hsp : spZ regsc = spZ regs)
  by (unfold spZ; f_equal; exact (HAP 2 ltac:(unfold acallee_saved; lia))).
assert (Hgpc : getr regsc 3 = w64 (as_gp B))
  by (rewrite <- Hgp; exact (HAP 3 ltac:(unfold acallee_saved; lia))).
assert (Htpc : getr regsc 4 = w64 (as_tp B))
  by (rewrite <- Htp; exact (HAP 4 ltac:(unfold acallee_saved; lia))).
assert (Hs0c : s0Z regsc = s0Z regs)
  by (unfold s0Z; f_equal; exact (HAP 8 ltac:(unfold acallee_saved; lia))).
(* the tree, the struct, the ledger, the read-only view and the chain at the call's memory *)
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
exact (wv_tail_put rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf
  st s bs memc mdc regsc ltac:(lia) HSTKp HPRE Hroom Hrp Hos Hcons Hcl HWIN Ho1 Ho2 HLED HOUT HNODEc HLOC HD Hoff HJ
  ltac:(intros a Ha; apply HKEEP; [lia | unfold wv_wr; lia])
  HAP Hsp Hrac Hgpc Htpc HCHc HROc H10 H11 H12 Hcut Hch0 HOUTc HLEDc Hev Hsrc Hhome Hwmax Hhead Hlive HMN).
Qed.

(* ---- THE TAIL put FROM A MID STATE (the closing bracket of a container): the state at the call is reached from the
   entry through write_value's own stretches and calls (the caller journal and the window keep from the entry), the
   writer has run the pieces P0 (opened, with no refusal: outcomes ok1, ledger Lam1 / peak1 / ran1, buffer buf1 at
   the call); the tail put's own run [bs] composes with it (prhWriter_ret_pos_step) into the text's post over P0 ++ [bs] ---- *)
Lemma wv_tail_gen : forall rp_sm rp_x rp_os rp_i rp_H0
    ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf (st : WriterApp.wst) (P0 : list (list Z)) s (bs : list Z)
    lyc Sc Hpc Wc memc mdc kc regsc ok1 ran1 buf1 Lam1 peak1 rp_i1 rp_hist1,
  192 <= STKv -> STK_put <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
  prhWriter_out W mem Lam o buf st ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc ->
  (forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
     aview SEGS (w_H Wc) memc a = aview SEGS (w_H W) mem a) ->
  room_live_cf Sc -> rp_i1 = (rp_i + length (prhWriter_evs ok1 st P0))%nat ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i1 rp_H0 rp_hist1 Sc ->
  (length rp_os <= 4)%nat ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i1 (length (prhWriter_evs [] (prhWriter_putN ok1 st P0) [bs])) ->
  prhW_oksg ok1 (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok1 st P0) ran ran1 ->
  prhWriter_out Wc memc Lam1 o buf1 (prhWriter_putN ok1 st P0) ->
  prh_ledger B lyc Sc Hpc Wc memc Lam1 peak1 (WriterApp.w_cnt (prhWriter_putN ok1 st P0))
    (WriterApp.w_fail (prhWriter_putN ok1 st P0)) ran1 gmo gow ->
  prhWriter_blk B ly S Lam peak buf st lyc Sc Lam1 peak1 buf1 (prhWriter_putN ok1 st P0) ->
  aregs_preserved regs regsc -> spZ regsc = spZ regs -> getr regsc 1 = getr regs 1 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain lyc (aview SEGS (w_H Wc) memc) (spZ regs) (s0Z regsc) ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) memc) ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s -> getr regsc 12 = w64 (Z.of_nat (length bs)) ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H Wc) memc) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H Wc) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (P0 ++ [bs])) ->
  src_rd Wc memc s bs ->
  prhWriter_src_home B lyc Sc Lam1 buf1 (WriterApp.w_cap (prhWriter_putN ok1 st P0)) s (Z.of_nat (length bs)) ->
  Z.of_nat (length (WriterApp.w_text (prhWriter_putN ok1 st P0))) + Z.of_nat (length bs) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs Sc (prhWriter_evs [] (prhWriter_putN ok1 st P0) [bs]) ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc)
    (fpostWR B ARx SK (wle' SEGS RZ_cf) STKv d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' => (room_live_cf S' /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) v t D /\
          exists ok, prhWriter_ret_ok B ok ly S Lam peak ran gmo gow o buf st (P0 ++ [bs]) ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (P0 ++ [bs])) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (P0 ++ [bs])))%nat rp_H0 hist' S') /\
          (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem'))).
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf st P0 s bs
  lyc Sc Hpc Wc memc mdc kc regsc ok1 ran1 buf1 Lam1 peak1 rp_i1 rp_hist1
  HSTK HSTKp HPRE Hcl HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ HKW Hroom Hrpeq Hrp Hos Hcons1 Hoks1 HOUT1 HLED1 HBLK1
  HAP Hspc Hrac Hgpc Htpc Hchc Hroc H10 H11 H12 Hcut Hch0 Hev Hsrc Hhome Hwmax Hhead Hlive.
pose proof HPRE as (HPREx & Hro & Htop).
pose proof HPREx as (HARe & Hret & Hra4 & _ & _ & Hstk & _).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
assert (Hc0e : 0 <= WriterApp.w_cnt st)
  by exact (wv_led_cnt _ _ _ _ _ _ _ _ _ _ _ _ HLED).
assert (Hpk0 : 0 <= peak)
  by (pose proof HLED as Hb0; apply prh_ledger_bounds in Hb0; destruct Hb0 as (Hb0 & _); lia).
pose proof (proj1 HJ) as HARc.
eapply (SRr'_mono SEGS RZ_cf).
- eapply (@aj_call_xWR fx rc SK SEGS B (@prh_pst prh_img_B) ARx _ LAWS pa_segs_low
    (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) Wc regsc memc (SIGMA AS_put)
    (STKv + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] lyc Sc Hpc mdc kc
    STK_put d (prhWriter_cfp o buf1 (WriterApp.w_cap (prhWriter_putN ok1 st P0))) (- d) (getr regs 1) ch
    (fun ly' S' Hp' W' regs' mem' md' => (room_live_cf S' /\
       (prhWriter_grows (prhWriter_putN ok1 st P0) bs = false ->
          PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i1 rp_H0 rp_hist1 S') /\
       (prhWriter_grows (prhWriter_putN ok1 st P0) bs = true ->
          forall f', val_mem SEGS (mrestrict (w_H W') mem') (o + 24) 4 f' ->
          (f' = 0 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i1) rp_H0 hist' S') /\
          (f' = 1 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i1 rp_H0 hist' S')) /\
       exists ok, prhWriter_ret_ok B ok lyc Sc Lam1 peak1 ran1 gmo gow o buf1 (prhWriter_putN ok1 st P0) [bs]
          ly' S' Hp' W' regs' mem' md' /\
          prh_granted ok (WriterApp.w_cnt (prhWriter_putN ok1 st P0)) (WriterApp.w_fail (prhWriter_putN ok1 st P0))
            (prhWriter_k ok (prhWriter_putN ok1 st P0) [bs])) /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem')) HJ);
    [lia | apply wv_neg_mod16; exact Hd16 | lia | vm_compute; congruence | lia | lia | exact Hd16 | lia
    | exact Hgpc | exact Htpc | exact Hrac | exact Hret | unfold raZ in Hra4; exact Hra4
    | replace (spZ regs + d + - d) with (spZ regs) by lia; exact Hchc | | ].
  + intros Hpre Hwin.
    assert (Ho1' : spZ regsc <= o) by lia.
    assert (Ho2' : o + 32 <= spZ regsc + d) by lia.
    assert (Hfpre : fpre B ARx STK_put lyc Sc Hpc Wc regsc memc mdc ch).
    { split; [exact Hpre|]. split; [exact Hroc|].
      pose proof HJ as (_ & Hly & _).
      assert (Eshi : ly_stk_hi lyc = ly_stk_hi ly)
        by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _); exact Eshi).
      split; [rewrite Hspc, Eshi; exact (proj1 Htop) | split; [unfold raZ; rewrite Hrac; exact (proj1 (proj2 Htop)) | exact (proj2 (proj2 Htop))]]. }
    pose proof HOUT1 as HOUT1'.
    exact (PUT rp_sm rp_x rp_os rp_i1 rp_H0 rp_hist1 gmo gow lyc Sc Hpc Wc regsc memc mdc ch o s (Z.of_nat (length bs)) d buf1
      (prhWriter_putN ok1 st P0) bs Lam1 peak1 ran1 Hfpre Hroom Hrp Hos Hcons1 Hcl H10 H11 H12
      ltac:(rewrite Hspc; exact Hcut) ltac:(rewrite Hspc; exact Hch0) Hwin Ho1' Ho2'
      HOUT1' HLED1 Hsrc eq_refl Hhome
      (fun Hg Hcf => prhWriter_ev_at rp_sm rp_x rp_os rp_i rp_i1 st P0 bs [] ok1 Hev Hrpeq Hg Hcf)
      Hwmax Hhead Hlive).
  + apply (wv_fp_sub (STKv + d) (spZ regs + d) ly S lyc Sc Hpc Wc memc mdc o Lam peak buf st Lam1 peak1 buf1
      (prhWriter_putN ok1 st P0) HARc (proj1 Hcap0) HBLK1).
- cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJ2 & HJc & HXT & HP2 & HQ).
  exists ly2, S2, Hp2, regs2, mem2, md2, (kc + k1)%Z.
  split; [exact Hc2|].
  split; [exact HJ2|].
  assert (HKW2 : forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
      aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hf. rewrite <- (HKW a Ha Hf). apply HXT; [lia|].
    intros Hf1. apply Hf. unfold prhWriter_cfp in Hf1 |- *. apply inFP_cons in Hf1. apply inFP_cons.
    destruct Hf1 as [Hs | Hb]; [left; exact Hs|]. exfalso.
    unfold prhWriter_fp in Hb. destruct (Z.eqb_spec (WriterApp.w_cap (prhWriter_putN ok1 st P0)) 0) as [_|Hc1];
      [exact (inFP_nil a Hb)|].
    destruct HOUT1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin1 & _)]); [lia|].
    pose proof (wv_led_hbs _ _ _ _ _ _ _ _ _ _ _ _ HLED1) as HF1.
    destruct (HF1 _ Hin1) as (_ & Hbl1 & _). cbn [fst snd] in Hbl1.
    destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hbl1) as (_ & _ & Hce & _).
    destruct Hb as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
    pose proof Hstk as (_ & _ & Hceil & Hslo & _). lia. }
  split; [exact HKW2|].
  split; [exact (aregs_preserved_trans regs regsc regs2 HAP HP2)|].
  destruct HQ as ((HQ1 & HQN & HQG & HQ3) & HQM).
  split; [|exact HQM].
  split; [exact HQ1|]. split.
  + apply (wv_nodeR_keep W W2 mem mem2 Lam v t D HNODE).
    * intros x Hx. exact (proj1 (wv_foot_keepR (wle' SEGS RZ_cf) ly S Hp W regs mem md STKv (STKv + d) d o buf
        (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow v D
        ly2 S2 Hp2 W2 mem2 md2 (kc + k1) ltac:(lia) Hd0 HARe Hstk HLED HLOC HD Hoff (proj1 Hcap0) Hbufin
        HJ2 HKW2 x Hx)).
    * intros x Hx. exact (proj2 (wv_foot_keepR (wle' SEGS RZ_cf) ly S Hp W regs mem md STKv (STKv + d) d o buf
        (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow v D
        ly2 S2 Hp2 W2 mem2 md2 (kc + k1) ltac:(lia) Hd0 HARe Hstk HLED HLOC HD Hoff (proj1 Hcap0) Hbufin
        HJ2 HKW2 x Hx)).
  + exact (prhWriter_ret_pos_step B rp_sm rp_x rp_os rp_H0 rp_i rp_i1 rp_hist1 ly S Lam peak ran gmo gow o buf st P0 bs
      ok1 ran1 buf1 Lam1 peak1 lyc Sc Hpc Wc memc ly2 S2 Hp2 W2 regs2 mem2 md2 Hc0e Hpk0 Hrpeq Hoks1 HOUT1 HLED1 HBLK1
      (conj HQN HQG) HQ3).
Qed.

(* s0 is callee-saved *)
Lemma wv_s0_pres : forall regs regs', aregs_preserved regs regs' -> s0Z regs' = s0Z regs.
Proof. intros regs regs' H. unfold s0Z. exact (f_equal bv_unsigned (H 8 ltac:(unfold acallee_saved; lia))). Qed.


Lemma wv_tail_put_string : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist
    ly S Hp W regs mem md ch STKv d o v t D Lam peak ran gmo gow buf (st : WriterApp.wst) s (bs : list Z)
    memc mdc regsc,
  192 <= STKv -> STK_put_string <= STKv ->
  fpre B ARx STKv ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st (WriterSpec.spieces bs))) ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
  prhWriter_out W mem Lam o buf st ->
  pj_nodeR SEGS (mrestrict (w_H W) memc) (prh_lin Lam) v t D ->
  ((spZ regs <= v /\ v + 56 <= ly_stk_hi ly) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y) \/ prhWriter_in_frame ly S v) ->
  (forall a k0, In (a, k0) D -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v D x) ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (STKv + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
  (forall a, spZ regs <= a < spZ regs + d -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  aregs_preserved regs regsc -> spZ regsc = spZ regs -> getr regsc 1 = getr regs 1 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain ly (aview SEGS (w_H W) memc) (spZ regs) (s0Z regsc) ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  s0Z regsc = o \/ s0Z regsc < YM05.alloc_ceiling ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B ly S Hp W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
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
  memc mdc regsc HSTK HSTKp HPRE Hroom Hrp Hos Hcl Hcons HWIN Ho1 Ho2 HLED HOUT HNODE HLOC HD Hoff HJ HKEEPW
  HAP Hspc Hrac Hgpc Htpc Hchc Hroc H10 H11 Hcut Hch0 Hs0c HOUTc HLEDc Hstr Hkept Hev Hapart Hfr0 Hwmax Hhead Hlive HMN.
pose proof HPRE as (HPREx & Hro & Htop).
pose proof HPREx as (HARe & Hret & Hra4 & _ & _ & Hstk & _).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HOUT as (Hoal & Hbuf0 & Hcap0 & _).
assert (Hbufin : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hc0 & _) | (_ & Hin & _)]); [lia | exact Hin]. }
eapply (SRr'_mono SEGS RZ_cf).
- eapply (@aj_call_xWFR fx rc SK SEGS B (@prh_pst prh_img_B) ARx _ LAWS pa_segs_low
    (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W regsc memc
    (SIGMA AS_put_string)
    (STKv + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly S Hp mdc 0
    STK_put_string d (prhWriter_cfp o buf (WriterApp.w_cap st)) (- d) (getr regs 1) ch
    (fun ly' S' Hp' W' regs' mem' md' => (room_live_cf S' /\
       exists ok, prhWriter_ret_ok B ok ly S Lam peak ran gmo gow o buf st (WriterSpec.spieces bs) ly' S' Hp' W' regs' mem' md' /\
       prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (WriterSpec.spieces bs)) /\
       exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
         (rp_i + length (prhWriter_evs ok st (WriterSpec.spieces bs)))%nat rp_H0 hist' S') /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem')) (wv_jR HJ));
    [lia | apply wv_neg_mod16; exact Hd16 | lia | vm_compute; congruence | lia | lia | exact Hd16 | lia
    | exact Hgpc | exact Htpc | exact Hrac | exact Hret | unfold raZ in Hra4; exact Hra4
    | replace (spZ regs + d + - d) with (spZ regs) by lia; exact Hchc | | ].
  + intros Hpre Hwin.
    assert (Ho1' : spZ regsc <= o) by lia.
    assert (Ho2' : o + 32 <= spZ regsc + d) by lia.
    assert (Hfpre : fpre B ARx STK_put_string ly S Hp W regsc memc mdc ch).
    { split; [exact Hpre|]. split; [exact Hroc|].
      split; [rewrite Hspc; exact (proj1 Htop) | split; [unfold raZ; rewrite Hrac; exact (proj1 (proj2 Htop)) | exact (proj2 (proj2 Htop))]]. }
    exact (PUTSTR rp_sm rp_x rp_os rp_i rp_H0 rp_hist gmo gow ly S Hp W regsc memc mdc ch o s d buf st bs Lam peak ran
      Hfpre Hroom Hrp Hcl Hos Hcons H10 H11 ltac:(rewrite Hspc; exact Hcut) ltac:(rewrite Hspc; exact Hch0)
      Hs0c Hwin Ho1' Ho2' HOUTc HLEDc Hstr Hkept Hev Hapart Hfr0 Hwmax Hhead Hlive).
  + intros a Ha. left. exact Ha.
- cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HFZ & HFK & HJ2 & HJc & HXT & HP2 & HQ).
  exists fx', ly2, S2, Hp2, regs2, mem2, md2, (0 + k1)%Z.
  split; [exact Hc2|]. split; [exact HFZ|]. split; [exact HFK|].
  split; [exact HJ2|].
  split.
  { intros a Ha Hf. rewrite (HXT a ltac:(lia) Hf). exact (HKEEPW a Ha). }
  split; [exact (aregs_preserved_trans regs regsc regs2 HAP HP2)|].
  destruct HQ as ((HQ1 & HQ2) & HQM).
  split; [|intros Hmn; exact (HQM (HMN Hmn))].
  split; [exact HQ1|]. split; [|exact HQ2].
  assert (HJc' : ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (STK_put_string + d) (spZ regs + d)
      (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1).
  { replace (spZ regs + d) with (spZ regs + d + - d + d) by lia. exact HJc. }
  apply (wv_nodeR_keep W W2 memc mem2 Lam v t D HNODE).
  + intros x Hx. exact (proj1 (wv_foot_keepR (wle' SEGS RZ_cf) ly S Hp W regs memc mdc STKv (STK_put_string + d) d o buf
      (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow v D
      ly2 S2 Hp2 W2 mem2 md2 k1 HSTK Hd0 ltac:(exact (proj1 HJ)) Hstk HLEDc HLOC HD Hoff ltac:(lia) Hbufin
      HJc' ltac:(intros a Ha Hf; apply HXT; [lia | exact Hf]) x Hx)).
  + intros x Hx. exact (proj2 (wv_foot_keepR (wle' SEGS RZ_cf) ly S Hp W regs memc mdc STKv (STK_put_string + d) d o buf
      (WriterApp.w_cap st) Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow v D
      ly2 S2 Hp2 W2 mem2 md2 k1 HSTK Hd0 ltac:(exact (proj1 HJ)) Hstk HLEDc HLOC HD Hoff ltac:(lia) Hbufin
      HJc' ltac:(intros a Ha Hf; apply HXT; [lia | exact Hf]) x Hx)).
Qed.

(* ---- THE INNER CALLS (the loop's put / indent / put_string and the recursive write_value): the callee runs at
   write_value's own frame base sp - 192, so oc = - (d + 192) and its window e1 = - oc reaches the caller's window top
   (which holds the struct). The conclusion is the engine's after-call shape; the walk goes on from the return site.
   ONE lemma per callee, so a new premise of a callee's text threads through in one place. ---- *)

Lemma wv_call_put : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k regsc raw ra1 nfp1 o s n buf (st : WriterApp.wst) (bs : list Z) Lam peak ran gmo gow oc,
  (* FRM0-ENTRY: the rounding mode at the call (the kit's fpre, f97c8b2f046b) *)
  frm_zero (@YK11.fp_csr fx) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + oc -> oc mod 16 = 0 -> oc <= 0 -> STK_put - oc <= STKc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  s0Z regsc = o -> rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra1 ->
  rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp1 -> nfp1 < YM05.alloc_ceiling ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) -> sp0 + oc + 64 <= ly_stk_hi lyc ->
  room_live_cf Sc -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sc ->
  (length rp_os <= 4)%nat ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [bs])) ->
  prh_univ_closure B CTX0 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s -> getr regsc 12 = w64 n ->
  sp0 + oc + 16 <= o -> o + 32 <= sp0 ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B lyc Sc Hpc W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
  src_rd W memc s bs -> Z.of_nat (length bs) = n ->
  prhWriter_src_home B lyc Sc Lam buf (WriterApp.w_cap st) s n ->
  (prhWriter_grows st bs = true -> WriterApp.w_cnt st <> WriterApp.w_fail st ->
     nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some (prhWriter_ev st bs)) ->
  Z.of_nat (length (WriterApp.w_text st)) + n + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs Sc (prhWriter_evs [] st [bs]) ->
  fp_sub_x B STKc sp0 FP (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S own lyc Sc ->
  SRr' SEGS RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) STKc sp0 FP ly S Hp W0 mem0 md0 own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (STK_put + - oc) (sp0 + oc + - oc)
         (prhWriter_cfp o buf (WriterApp.w_cap st)) lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + oc <= a < sp0 + oc + - oc ->
          ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\
       (room_live_cf S2 /\ prhWriter_put_pos rp_sm rp_x rp_os rp_H0 rp_i rp_hist st bs o W2 mem2 S2 /\
       exists ok, prhWriter_ret_ok B ok lyc Sc Lam peak ran gmo gow o buf st [bs] ly2 S2 Hp2 W2 regs2 mem2 md2 /\
         prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st [bs])) /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2)).
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regsc raw
  ra1 nfp1 o s n buf st bs Lam peak ran gmo gow oc
  Hfrm HJ Hsp Hoc16 Hoc0 HSTK Hgp Htp Hra Hraw Hra4 Hrab Hs0 Hra1 Hnfp1 Hnfpc Hro Hhi Hroom Hrp Hos Hcons Hcl H10 H11 H12 Ho1 Ho2 Hout Hled Hsrc
  Hlen Hhome Hevp Hwmax Hhead Hlive Hfp.
assert (HPF : 0 <= pi_frame F_put) by (vm_compute; congruence).
destruct (wv_chain1g lyc (aview SEGS (w_H W) memc) (sp0 + oc) o ra1 nfp1 Hra1 Hnfp1
  (wv_rdword_nonneg _ _ _ _ Hra1) Hnfpc ltac:(lia)) as [ch1 Hch].
eapply (SRr'_mono SEGS RZ_cf).
{ eapply (@aj_call_xWR fx rc SK SEGS B (@prh_pst prh_img_B) ARx _ LAWS pa_segs_low
    (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W regsc memc (SIGMA AS_put)
    STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc mdc k STK_put (- oc)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) oc raw ch1
    (fun ly' S' Hp' W' regs' mem' md' => (room_live_cf S' /\
       (prhWriter_grows st bs = false -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S') /\
       (prhWriter_grows st bs = true -> forall f', val_mem SEGS (mrestrict (w_H W') mem') (o + 24) 4 f' ->
          (f' = 0 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S') /\
          (f' = 1 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S')) /\
       exists ok, prhWriter_ret_ok B ok lyc Sc Lam peak ran gmo gow o buf st [bs] ly' S' Hp' W' regs' mem' md' /\
         prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st [bs])) /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem')));
    [ exact HJ | exact Hsp | exact Hoc16 | exact Hoc0 | vm_compute; congruence | exact HSTK | lia
    | apply wv_neg_mod16; exact Hoc16 | lia | exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hra4
    | rewrite Hs0; exact Hch | | ].
  - intros Hpre Hwin.
    assert (Ho1' : spZ regsc <= o) by lia.
    assert (Ho2' : o + 32 <= spZ regsc + - oc) by lia.
    assert (Htop' : spZ regsc + 64 <= ly_stk_hi lyc /\ raZ regsc < YM05.alloc_ceiling /\ frm_zero (@YK11.fp_csr fx))
      by (split; [lia | split; [unfold raZ; rewrite Hra; exact Hrab | exact Hfrm]]).
    exact (PUT rp_sm rp_x rp_os rp_i rp_H0 rp_hist gmo gow lyc Sc Hpc W regsc memc mdc ch1 o s n (- oc) buf st bs Lam peak
      ran (conj Hpre (conj Hro Htop')) Hroom Hrp Hos Hcons Hcl H10 H11 H12
      ltac:(left; lia) ltac:(intros _; exists ra1; split; [exact Hra1 | exists nfp1; split; [exact Hnfp1 | exact Hnfpc]])
      Hwin Ho1' Ho2' Hout Hled Hsrc Hlen Hhome Hevp Hwmax Hhead Hlive).
  - exact Hfp. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJ2 & HJc & HXT & HP2 &
  (HQ1 & HQN & HQG & HQ3) & HQM).
exists ly2, S2, Hp2, regs2, mem2, md2, k1.
split; [exact Hc2|]. split; [exact HJ2|]. split; [exact HJc|]. split; [exact HXT|]. split; [exact HP2|].
split; [|exact HQM]. split; [exact HQ1|]. split; [exact (conj HQN HQG) | exact HQ3].
Qed.

Lemma wv_call_indent : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k regsc raw ra1 nfp1 o pretty depth buf (st : WriterApp.wst) Lam peak ran gmo gow oc,
  (* FRM0-ENTRY: the rounding mode at the call (the kit's fpre, f97c8b2f046b) *)
  frm_zero (@YK11.fp_csr fx) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + oc -> oc mod 16 = 0 -> oc <= 0 -> STK_indent - oc <= STKc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  s0Z regsc = o -> rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra1 ->
  rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp1 -> nfp1 < YM05.alloc_ceiling ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) -> sp0 + oc + 64 <= ly_stk_hi lyc ->
  room_live_cf Sc -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sc ->
  (length rp_os <= 4)%nat ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wind (negb (pretty =? 0)) depth))) ->
  prh_univ_closure B CTX0 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 pretty -> getr regsc 12 = w64 depth ->
  0 <= pretty < 2 ^ 64 -> - 2 ^ 31 <= depth < 2 ^ 31 ->
  sp0 + oc + 16 <= o -> o + 32 <= sp0 ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B lyc Sc Hpc W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wind (negb (pretty =? 0)) depth)) ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wind (negb (pretty =? 0)) depth))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs Sc (prhWriter_evs [] st (WriterValue.wind (negb (pretty =? 0)) depth)) ->
  fp_sub_x B STKc sp0 FP (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S own lyc Sc ->
  SRr' SEGS RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_indent)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) STKc sp0 FP ly S Hp W0 mem0 md0 own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (STK_indent + - oc) (sp0 + oc + - oc)
         (prhWriter_cfp o buf (WriterApp.w_cap st)) lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + oc <= a < sp0 + oc + - oc ->
          ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\
       (room_live_cf S2 /\
          exists ok, prhWriter_ret_ok B ok lyc Sc Lam peak ran gmo gow o buf st (WriterValue.wind (negb (pretty =? 0)) depth)
            ly2 S2 Hp2 W2 regs2 mem2 md2 /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
            (prhWriter_k ok st (WriterValue.wind (negb (pretty =? 0)) depth)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterValue.wind (negb (pretty =? 0)%Z) depth)))%nat rp_H0 hist' S2) /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2)).
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regsc raw
  ra1 nfp1 o pretty depth buf st Lam peak ran gmo gow oc
  Hfrm HJ Hsp Hoc16 Hoc0 HSTK Hgp Htp Hra Hraw Hra4 Hrab Hs0 Hra1 Hnfp1 Hnfpc Hro Hhi Hroom Hrp Hos Hcons Hcl H10 H11 H12 Hpr Hdep Ho1 Ho2 Hout
  Hled Hev Hwmax Hhead Hlive Hfp.
assert (HPF : 0 <= pi_frame F_indent) by (vm_compute; congruence).
destruct (wv_chain1g lyc (aview SEGS (w_H W) memc) (sp0 + oc) o ra1 nfp1 Hra1 Hnfp1
  (wv_rdword_nonneg _ _ _ _ Hra1) Hnfpc ltac:(lia)) as [ch1 Hch].
eapply (@aj_call_xWR fx rc SK SEGS B (@prh_pst prh_img_B) ARx _ LAWS pa_segs_low
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W regsc memc (SIGMA AS_indent)
  STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc mdc k STK_indent (- oc)
  (prhWriter_cfp o buf (WriterApp.w_cap st)) oc raw ch1);
  [ exact HJ | exact Hsp | exact Hoc16 | exact Hoc0 | vm_compute; congruence | exact HSTK | lia
  | apply wv_neg_mod16; exact Hoc16 | lia | exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hra4
  | rewrite Hs0; exact Hch | | ].
- intros Hpre Hwin.
  assert (Ho1' : spZ regsc <= o) by lia.
  assert (Ho2' : o + 32 <= spZ regsc + - oc) by lia.
  assert (Htop' : spZ regsc + 64 <= ly_stk_hi lyc /\ raZ regsc < YM05.alloc_ceiling /\ frm_zero (@YK11.fp_csr fx))
    by (split; [lia | split; [unfold raZ; rewrite Hra; exact Hrab | exact Hfrm]]).
  exact (INDENT rp_sm rp_x rp_os rp_i rp_H0 rp_hist gmo gow lyc Sc Hpc W regsc memc mdc ch1 o pretty depth (- oc) buf st
    Lam peak ran (conj Hpre (conj Hro Htop')) Hroom Hrp Hos Hcons Hcl H10 H11 H12 Hpr Hdep
    ltac:(lia) (ex_intro _ ra1 (conj Hra1 (ex_intro _ nfp1 (conj Hnfp1 Hnfpc))))
    Hwin Ho1' Ho2' Hout Hled Hev Hwmax Hhead Hlive).
- exact Hfp.
Qed.

(* the loop's put_string call (an object's key, A 0x86a20) *)
Lemma wv_call_put_string : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k regsc raw ra1 nfp1 o s buf (st : WriterApp.wst) (bs : list Z) Lam peak ran gmo gow oc,
  (* FRM0-ENTRY: the rounding mode at the call (the kit's fpre, f97c8b2f046b) *)
  frm_zero (@YK11.fp_csr fx) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + oc -> oc mod 16 = 0 -> oc <= 0 -> STK_put_string - oc <= STKc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  s0Z regsc = o -> rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra1 ->
  rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp1 -> nfp1 < YM05.alloc_ceiling ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) -> sp0 + oc + 64 <= ly_stk_hi lyc ->
  room_live_cf Sc -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sc ->
  (length rp_os <= 4)%nat ->
  prh_univ_closure B CTX0 ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st (WriterSpec.spieces bs))) ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s ->
  sp0 + oc + 16 <= o -> o + 32 <= sp0 ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B lyc Sc Hpc W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
  cstr_ok W memc s bs ->
  kept_at B Lam s (Z.of_nat (length bs) + 1) ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterSpec.spieces bs)) ->
  (WriterApp.w_cap st = 0 \/ s + Z.of_nat (length bs) + 1 <= buf \/ buf + WriterApp.w_cap st <= s) ->
  Z.of_nat (length (frames Sc)) < fs_frames 0 ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (WriterSpec.wstr bs)) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs Sc (prhWriter_evs [] st (WriterSpec.spieces bs)) ->
  fp_sub_x B STKc sp0 FP (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S own lyc Sc ->
  SRr' SEGS RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put_string)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@mkst fx2 regs2 raw mem2 (seg_rom SEGS)) md2 /\
       frm_zero (@YK11.fp_csr fx2) /\ fregs_kept_x fx fx2 /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) STKc sp0 FP ly S Hp W0 mem0 md0 own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (STK_put_string + - oc) (sp0 + oc + - oc)
         (prhWriter_cfp o buf (WriterApp.w_cap st)) lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + oc <= a < sp0 + oc + - oc ->
          ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\
       (room_live_cf S2 /\
          exists ok, prhWriter_ret_ok B ok lyc Sc Lam peak ran gmo gow o buf st (WriterSpec.spieces bs) ly2 S2 Hp2 W2 regs2 mem2 md2 /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st (WriterSpec.spieces bs)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterSpec.spieces bs)))%nat rp_H0 hist' S2) /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2)).
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regsc raw
  ra1 nfp1 o s buf st bs Lam peak ran gmo gow oc
  Hfrm HJ Hsp Hoc16 Hoc0 HSTK Hgp Htp Hra Hraw Hra4 Hrab Hs0 Hra1 Hnfp1 Hnfpc Hro Hhi Hroom Hrp Hos Hcl Hcons H10 H11 Ho1 Ho2 Hout Hled Hstr
  Hkept Hev Hapart Hfr0 Hwmax Hhead Hlive Hfp.
assert (HPF : 0 <= pi_frame F_put_string) by (vm_compute; congruence).
destruct (wv_chain1g lyc (aview SEGS (w_H W) memc) (sp0 + oc) o ra1 nfp1 Hra1 Hnfp1
  (wv_rdword_nonneg _ _ _ _ Hra1) Hnfpc ltac:(lia)) as [ch1 Hch].
eapply (@aj_call_xWFR fx rc SK SEGS B (@prh_pst prh_img_B) ARx _ LAWS pa_segs_low
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W regsc memc
  (SIGMA AS_put_string) STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc mdc k STK_put_string (- oc)
  (prhWriter_cfp o buf (WriterApp.w_cap st)) oc raw ch1);
  [ exact HJ | exact Hsp | exact Hoc16 | exact Hoc0 | vm_compute; congruence | exact HSTK | lia
  | apply wv_neg_mod16; exact Hoc16 | lia | exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hra4
  | rewrite Hs0; exact Hch | | ].
- intros Hpre Hwin.
  assert (Ho1' : spZ regsc <= o) by lia.
  assert (Ho2' : o + 32 <= spZ regsc + - oc) by lia.
  assert (Htop' : spZ regsc + 64 <= ly_stk_hi lyc /\ raZ regsc < YM05.alloc_ceiling /\ frm_zero (@YK11.fp_csr fx))
    by (split; [lia | split; [unfold raZ; rewrite Hra; exact Hrab | exact Hfrm]]).
  exact (PUTSTR rp_sm rp_x rp_os rp_i rp_H0 rp_hist gmo gow lyc Sc Hpc W regsc memc mdc ch1 o s (- oc) buf st bs Lam peak
    ran (conj Hpre (conj Hro Htop')) Hroom Hrp Hcl Hos Hcons H10 H11
    ltac:(left; lia) ltac:(intros _; exists ra1; split; [exact Hra1 | exists nfp1; split; [exact Hnfp1 | exact Hnfpc]])
    (or_introl Hs0) Hwin Ho1' Ho2' Hout Hled Hstr Hkept Hev Hapart Hfr0 Hwmax Hhead Hlive).
- exact Hfp.
Qed.

(* THE RECURSIVE CALL (A 0x86a50) at depth n - 1: the induction hypothesis is the callee's text *)
Lemma wv_call_self : forall (n' : nat) rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k regsc raw ra1 nfp1 o v2 pretty dep buf (st : WriterApp.wst) (t2 : PjTree.jv) D2
    Lam peak ran gmo gow oc,
  twrite_value_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n' ->
  (* FRM0-ENTRY: the rounding mode at the call (the kit's fpre, f97c8b2f046b) *)
  frm_zero (@YK11.fp_csr fx) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) STKc sp0 FP ly S Hp W0 mem0 md0 own
    lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + oc -> oc mod 16 = 0 -> oc <= 0 -> STK_write_value n' - oc <= STKc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  s0Z regsc = o -> rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra1 ->
  rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp1 -> nfp1 < YM05.alloc_ceiling ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) -> sp0 + oc + 64 <= ly_stk_hi lyc ->
  room_live_cf Sc -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sc ->
  (length rp_os <= 4)%nat ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep))) ->
  prh_univ_closure B CTX0 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 v2 -> getr regsc 12 = w64 pretty -> getr regsc 13 = w64 dep ->
  0 <= pretty < 2 ^ 64 -> 0 <= dep < 2 ^ 31 -> dep + Z.of_nat (PjTree.depth t2) <= 2 ^ 31 - 1 ->
  (PjTree.depth t2 <= n')%nat ->
  sp0 + oc + 16 <= o -> o + 32 <= sp0 ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B lyc Sc Hpc W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran gmo gow ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep)) ->
  pj_nodeR SEGS (mrestrict (w_H W) memc) (prh_lin Lam) v2 t2 D2 ->
  ((sp0 + oc <= v2 /\ v2 + 56 <= ly_stk_hi lyc) \/
   (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v2 /\ v2 + 56 <= x + y) \/ prhWriter_in_frame lyc Sc v2) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v2 56 ->
  prhWriter_tree_vis W memc D2 ->
  (forall a k0, In (a, k0) D2 -> In (a, k0) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_footR v2 D2 x) ->
  Z.of_nat (length (frames Sc)) < fs_frames 0 ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs Sc (prhWriter_evs [] st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep)) ->
  fp_sub_x B STKc sp0 FP (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S own lyc Sc ->
  SRr' SEGS RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_write_value)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@mkst fx2 regs2 raw mem2 (seg_rom SEGS)) md2 /\
       frm_zero (@YK11.fp_csr fx2) /\ fregs_kept_x fx fx2 /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) STKc sp0 FP ly S Hp W0 mem0 md0 own
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ_cf) (STK_write_value n' + - oc) (sp0 + oc + - oc)
         (prhWriter_cfp o buf (WriterApp.w_cap st)) lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + oc <= a < sp0 + oc + - oc ->
          ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\
       (room_live_cf S2 /\ pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam) v2 t2 D2 /\
          exists ok, prhWriter_ret_ok B ok lyc Sc Lam peak ran gmo gow o buf st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep)
            ly2 S2 Hp2 W2 regs2 mem2 md2 /\
          prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st)
            (prhWriter_k ok st (WriterValue.wvpieces t2 (negb (pretty =? 0)) dep)) /\
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhWriter_evs ok st (WriterValue.wvpieces t2 (negb (pretty =? 0)%Z) dep)))%nat rp_H0 hist' S2) /\
       (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2)).
Proof.
intros n' rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regsc
  raw ra1 nfp1 o v2 pretty dep buf st t2 D2 Lam peak ran gmo gow oc
  IH Hfrm HJ Hsp Hoc16 Hoc0 HSTK Hgp Htp Hra Hraw Hra4 Hrab Hs0 Hra1 Hnfp1 Hnfpc Hro Hhi Hroom Hrp Hos Hcons Hcl H10 H11 H12 H13 Hpr Hdep Hdep2
  Hdn Ho1 Ho2 Hout Hled Hev Hnode Hloc Hra56 Hvis HD Hoff Hfr0 Hwmax Hhead Hlive Hfp.
assert (HPF : 0 <= pi_frame F_write_value) by (vm_compute; congruence).
destruct (wv_chain1g lyc (aview SEGS (w_H W) memc) (sp0 + oc) o ra1 nfp1 Hra1 Hnfp1
  (wv_rdword_nonneg _ _ _ _ Hra1) Hnfpc ltac:(lia)) as [ch1 Hch].
eapply (@aj_call_xWFR fx rc SK SEGS B (@prh_pst prh_img_B) ARx _ LAWS pa_segs_low
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W regsc memc
  (SIGMA AS_write_value) STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc mdc k (STK_write_value n') (- oc)
  (prhWriter_cfp o buf (WriterApp.w_cap st)) oc raw ch1);
  [ exact HJ | exact Hsp | exact Hoc16 | exact Hoc0 | unfold STK_write_value; vm_compute; congruence
  | exact HSTK | lia | apply wv_neg_mod16; exact Hoc16 | lia | exact Hgp | exact Htp | exact Hra | exact Hraw
  | exact Hra4 | rewrite Hs0; exact Hch | | ].
- intros Hpre Hwin.
  assert (Ho1' : spZ regsc <= o) by lia.
  assert (Ho2' : o + 32 <= spZ regsc + - oc) by lia.
  assert (Htop' : spZ regsc + 64 <= ly_stk_hi lyc /\ raZ regsc < YM05.alloc_ceiling /\ frm_zero (@YK11.fp_csr fx))
    by (split; [lia | split; [unfold raZ; rewrite Hra; exact Hrab | exact Hfrm]]).
  assert (Hloc' : (spZ regsc <= v2 /\ v2 + 56 <= ly_stk_hi lyc) \/
     (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v2 /\ v2 + 56 <= x + y) \/ prhWriter_in_frame lyc Sc v2)
    by (rewrite Hsp; exact Hloc).
  exact (IH rp_sm rp_x rp_os rp_i rp_H0 rp_hist gmo gow lyc Sc Hpc W regsc memc mdc ch1 o v2 pretty dep (- oc) buf st t2
    D2 Lam peak ran (conj Hpre (conj Hro Htop')) Hroom Hrp Hos Hcons Hcl H10 H11 H12 H13 Hpr Hdep Hdep2 Hdn
    ltac:(left; lia) ltac:(intros _; exists ra1; split; [exact Hra1 | exists nfp1; split; [exact Hnfp1 | exact Hnfpc]])
    (or_introl Hs0) Hwin Ho1' Ho2' Hout Hled Hev Hnode Hloc' Hra56 Hvis HD Hoff Hfr0 Hwmax Hhead Hlive).
- exact Hfp.
Qed.


End cl.
End h.
End f.
End d.
