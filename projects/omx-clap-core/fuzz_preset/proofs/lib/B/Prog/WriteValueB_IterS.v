(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d), segment
   WvbIter: THE ITEM LOOP's SEGMENTS of write_value's container walk, each from a join of the loop body at this
   Section's float state fx to the container's final post wv_Qfin, given the continuations at the two float-state
   changes (wvs_K130R after an object's key, wvs_K156R after the item's value, each at ANY float state) and, after the
   value, the head at i + 1 and the close (wv_CLOSEKR). Every join comes after one of the container's calls, and a call
   may realloc, so each segment concludes SRr' SEGS RZ_cf and names the continuations at wle' SEGS RZ_cf. The joins
   (slots of write_value): 90 the head, 95 after the comma, 100 after the indent, 130 after an object's key, 134 before
   the value, 156 after the value. MEASURED with the
   engine on B's listing (WvbIter's probe, log, the internal file zfb-20261029T194028Z.log): every stop is a call site or one of the branches the engine leaves
   (WriteValueB_IterL's wvi_br lemmas). WriteValueB_Iter chains them across float states by induction on the items left.
   PORTED (not cited) from the image-A loop writer's scratch (PRW_write_value_lp.v, wvl_seg_153 .. wvl_seg_193).
   Numerals: 192 (LENGTH: the frame), the slots (DERIVED). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import WriteValueB_Model WriteValueB_Base
  WriteValueB_Call WriteValueB_Defs WriteValueB_IterL.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCem.
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

Section cl.
Variable CTX0 : list (list Z).
Hypothesis PUT : forall fx' : YK11.FPState, tput_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis PUTSTR : forall fx' : YK11.FPState, tput_string_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis INDENT : forall fx' : YK11.FPState, tindent_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling; at the instance the allocator-model owner's preset_head_wide):
   a key string handed to put_string is cstr_ok (wvi_cstr_blk) *)
Hypothesis HW : prh_head_wide.

Section cont.
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.

(* WriteValueB_IterL's lemmas at this Section's variables *)
Let wvi_head_st := @WriteValueB_IterL.wvi_head_st fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_st_head := @WriteValueB_IterL.wvi_st_head fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_pre_facts := @WriteValueB_IterL.wvi_pre_facts fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_nowin_gen := @WriteValueB_IterL.wvi_nowin_gen fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_agree_ext := @WriteValueB_IterL.wvi_agree_ext fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_agree_set := @WriteValueB_IterL.wvi_agree_set fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_ew_agree := @WriteValueB_IterL.wvi_ew_agree fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_common_run := @WriteValueB_IterL.wvi_common_run fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_stk := @WriteValueB_IterL.wvi_stk fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_item_facts := @WriteValueB_IterL.wvi_item_facts fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_node_facts := @WriteValueB_IterL.wvi_node_facts fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_blk_facts := @WriteValueB_IterL.wvi_blk_facts fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_seat_join := @WriteValueB_IterL.wvi_seat_join fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_E_at := @WriteValueB_IterL.wvi_E_at fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_reg_mv := @WriteValueB_IterL.wvi_reg_mv fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_reg_sv := @WriteValueB_IterL.wvi_reg_sv fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_reg_lit := @WriteValueB_IterL.wvi_reg_lit fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_reg_ret := @WriteValueB_IterL.wvi_reg_ret fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_ew_reg := @WriteValueB_IterL.wvi_ew_reg fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_st_run := @WriteValueB_IterL.wvi_st_run fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_rf_next := @WriteValueB_IterL.wvi_rf_next fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_site_put := @WriteValueB_IterL.wvi_site_put fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_site_indent := @WriteValueB_IterL.wvi_site_indent fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_site_put_string := @WriteValueB_IterL.wvi_site_put_string fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_site_self := @WriteValueB_IterL.wvi_site_self fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_br90 := @WriteValueB_IterL.wvi_br90 fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_br162 := @WriteValueB_IterL.wvi_br162 fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_br116 := @WriteValueB_IterL.wvi_br116 fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_br117 := @WriteValueB_IterL.wvi_br117 fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_br144 := @WriteValueB_IterL.wvi_br144 fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_br150 := @WriteValueB_IterL.wvi_br150 fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_rd_u64_det := @WriteValueB_IterL.wvi_rd_u64_det fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_st_cl := @WriteValueB_IterL.wvi_st_cl fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let wvi_p1_denot := @WriteValueB_IterL.wvi_p1_denot fx rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.

(* the runners and the branch over wle' SEGS RZ_cf: every join of the loop comes after one of the container's calls,
   and a call may realloc *)
Let RUNI := @paj_run_x_invR fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS Pm PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Let RUNTOI := @paj_run_to_x_invR fx rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS Pm PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Let BR := paj_branchR (PI := PA) (wle' SEGS RZ_cf).

Local Notation WST := (WriteValueB_IterL.wvi_st B ARx Pm).

(* the write premise of a run from a seated (or seated-then-run) state: no write window *)
Local Ltac wvs_awr := try unfold wvi_ss, wvi_mem; cbn [ss_mem add_cond];
  repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]].

(* the memory a run from a seat leaves: every byte kept *)
Local Ltac wvs_kept K HF HFr HG :=
  lazymatch type of HFr with frame_of ?E0 ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) =>
    pose proof (wvi_nowin_gen E0 rs m0 m1 H ltac:(vm_compute; reflexivity) HFr) as K end;
  clear HF HFr HG.

(* the env after a run agrees with the seat's below 55 *)
Local Ltac wvs_agree :=
  repeat (apply wvi_agree_set; [lia|]); first [apply env_agree_refl | apply wvi_agree_ext; lia].

(* ---- THE CONTINUATIONS OF THE BODY ACROSS A FLOAT-STATE CHANGE: after an object's key (put_string returns to slot
   130) and after the item's value (write_value returns to slot 156), each at ANY float state fx2 (the callee's exit) ---- *)
Definition wvs_K130 (X : wvx) (i : nat) : Prop :=
  wv_tagc (y_t X) = 6 ->
  forall (fx2 : YK11.FPState) ly2 S2 Hp2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2 k2,
    WST X fx2 i (wvi_Pk X i) ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
    SRr SEGS W2 (mkCfg (@mkst fx2 regs2 (Z_to_bv 64 (BASE + WVI_PC 130)) mem2 (seg_rom SEGS)) md2)
      (wv_Qfin B ARx Pm X).
Definition wvs_K156 (X : wvx) (i : nat) : Prop :=
  forall (fx2 : YK11.FPState) ly2 S2 Hp2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2 k2,
    WST X fx2 i (wv_done X (S i)) ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
    SRr SEGS W2 (mkCfg (@mkst fx2 regs2 (Z_to_bv 64 (BASE + WVI_PC 156)) mem2 (seg_rom SEGS)) md2)
      (wv_Qfin B ARx Pm X).
(* the two continuations over a world relation Rw (the free / realloc move): COPIES of the bodies above with SRr read
   as SRrG at Rw; the loop names them at Rw := wle' SEGS RZ_cf. X_R_wle checks by reflexivity that the old name is the
   R form at wle *)
Definition wvs_K130R (Rw : world SEGS -> world SEGS -> Prop) (X : wvx) (i : nat) : Prop :=
  wv_tagc (y_t X) = 6 ->
  forall (fx2 : YK11.FPState) ly2 S2 Hp2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2 k2,
    WST X fx2 i (wvi_Pk X i) ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
    SRrG SEGS Rw W2 (mkCfg (@mkst fx2 regs2 (Z_to_bv 64 (BASE + WVI_PC 130)) mem2 (seg_rom SEGS)) md2)
      (wv_Qfin B ARx Pm X).
Lemma wvs_K130_R_wle : forall X i, wvs_K130 X i = wvs_K130R (@wle SEGS) X i.
Proof. reflexivity. Qed.
Definition wvs_K156R (Rw : world SEGS -> world SEGS -> Prop) (X : wvx) (i : nat) : Prop :=
  forall (fx2 : YK11.FPState) ly2 S2 Hp2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2 k2,
    WST X fx2 i (wv_done X (S i)) ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
    SRrG SEGS Rw W2 (mkCfg (@mkst fx2 regs2 (Z_to_bv 64 (BASE + WVI_PC 156)) mem2 (seg_rom SEGS)) md2)
      (wv_Qfin B ARx Pm X).
Lemma wvs_K156_R_wle : forall X i, wvs_K156 X i = wvs_K156R (@wle SEGS) X i.
Proof. reflexivity. Qed.

(* ---- BEFORE THE VALUE (write_value + 4 * 134; arrays come from slot 105, objects from the separator's put):
   shadow (v + 24) (slots 134-135), kids = the word at v + 24 (slot 136), 56 i (137-139), kids + 56 i (140); the
   UBSan arms on kids + 56 i: slot 143 `beq` (the engine: kids >= 4096 and kids + 56 i >= 4096, both NOT zero),
   slot 144 `bltu kids + 56 i, kids` and slot 150 `bnez (mulh (i, 56) ^ (56 i >> 63))` (wvi_br144 / wvi_br150, by
   hand: no wrap, 56 i < 2 ^ 63), each NOT taken; kids + 56 i again (151, the alias atom 41); the recursive call at
   slot 155 (return 156) on the child at depth n' ---- *)
Lemma wvs_seg_134 : forall n' X ch i lyc Sc Hpc Wc regs memc mdc kc,
  twrite_value_specX (fx := fx) (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n' ->
  STK_write_value (S n') <= y_STK X -> (PjTree.depth (y_t X) <= S n')%nat ->
  wv_pre B ARx CTX0 Pm X ch -> (i < wv_nitems (y_t X))%nat ->
  WST X fx i (wvi_PD X i) lyc Sc Hpc Wc regs memc mdc kc -> wvs_K156R (wle' SEGS RZ_cf) X i ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regs (Z_to_bv 64 (BASE + WVI_PC 134)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin B ARx Pm X).
Proof.
intros n' X ch i lyc Sc Hpc Wc regs memc mdc kc IH HSTKn Hdn Hpre Hi Hst K156.
destruct (wvi_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 192 <= y_STK X) by lia.
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof (@alloc_ceiling_lt rc) as HCL.
pose proof Hst as (Hcom & Hrf).
pose proof Hrf as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & _).
destruct (wvi_item_facts X ch fx _ lyc Sc Hpc Wc memc mdc kc i HSTK Hpre Hcom Hi) as
  (kids & keys & nn & cap & D1 & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & HN1 & HD1 & Hk5 & Hk6).
destruct (wvi_blk_facts X ch kids (56 * cap) HSTK Hpre Hkb) as (_ & Hk4096 & _ & Hkc & _).
destruct (wvi_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVI_PC 134) false kids keys nn cap 0 HSTKn
  Hpre Hst Hi Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 (fun H => proj1 (Hk6 H)) ltac:(discriminate))
  as (HEI & Hregs & HS & SHOK).
set (E := wvi_E X i regs kids keys nn 0) in *.
pose proof (wvi_E_at X i regs kids keys nn 0) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41).
fold E in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41.
assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (wvi_ew_reg E regs 21%bv 21%nat Hregs eq_refl); exact G21).
pose proof Hcom as (HJ & _ & HPM & _).
assert (Hi42 : Z.of_nat i <= 2 ^ 42) by (clear - Hi Hnn Hncap Hkc Hk4096 HCL; wvi_zl).
assert (Hka : kids + 56 * Z.of_nat i < 2 ^ 64) by (clear - Hi Hnn Hncap Hkc Hk4096 HCL; wvi_zl).
assert (Ho0 : 0 <= y_o X) by (clear - Ho1 Hsp1 HCV; unfold y_sp in *; lia).
assert (Ho64 : y_o X + 32 <= 2 ^ 64) by (clear - Ho2 Hdtop Htop2 H47; unfold y_sp in *; wvi_zl).
assert (Htg : wv_tagc (y_t X) = 5 \/ wv_tagc (y_t X) = 6) by (unfold wv_tagc; destruct (y_t X); auto).
destruct Htg as [Ht | Ht]; rewrite Ht in HS.
(* 134 .. 143; stuck at the overflow `bltu` at 144 *)
all: paj_run_tok_x_invR RUNI HS HJ SHOK HPM WV_Bspan; [wvs_awr | ].
all: wvs_kept K1 HF HFr HG.
all: lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => assert (HA1 : env_agree 55 E E1) by wvs_agree end.
all: psrr_branch_tokR RUNI BR HS SHOK WV_Bspan.
all: rewrite (wvi_br144 _ i kids (wvi_ew_agree E _ 21%nat _ HA1 ltac:(lia) E21)
       (wvi_ew_agree E _ 36%nat _ HA1 ltac:(lia) E36) ltac:(lia) Hka) in Hc.
1, 3: discriminate Hc.
all: clear Hc.
(* 145 .. 149; stuck at the overflow `bnez` at 150 *)
all: paj_run_tok_x_invR RUNI HS HJ SHOK HPM WV_Bspan; [wvs_awr | ].
all: wvs_kept K2 HF HFr HG.
all: lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => assert (HA2 : env_agree 55 E E1) by wvs_agree end.
all: psrr_branch_tokR RUNI BR HS SHOK WV_Bspan.
all: rewrite (wvi_br150 _ i (wvi_ew_agree E _ 21%nat _ HA2 ltac:(lia) E21) Hi42) in Hc.
1, 3: discriminate Hc.
(* 151 .. 155: the recursive call *)
all: paj_run_tok_x_invR RUNI HS HJ SHOK HPM WV_Bspan; [wvs_awr | ].
all: wvs_kept K3 HF HFr HG.
all: pmkst HS.
all: lazymatch type of HS with st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
  pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
  assert (HA : env_agree 55 E E2) by wvs_agree;
  assert (HEIr : img_env VAL A_LIM E2) by assumption;
  assert (KM : forall a, aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
    by (intros a; rewrite K3, K2; apply K1);
  pose proof (wvi_st_run X fx i _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _
    Hst Ho0 Ho64 Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM KM) as Hst2;
  destruct (wvi_item_facts X ch fx _ lyc Sc Hpc Wc (ms_mem ms2) _ kc i HSTK Hpre (proj1 Hst2) Hi) as
    (kids' & keys' & nn' & cap' & D1' & Vtg' & Rkids' & Rkeys' & Rnn' & Hnn' & Hncap' & Hcap' & Hkb' & HN1' & HD1' &
     _ & _);
  pose proof (wvi_rd_u64_det (w_H Wc) memc (ms_mem ms2) (y_v X + 24) kids kids' KM Rkids Rkids') as Ekids;
  subst kids';
  assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
    by (rewrite (wvi_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G8);
  assert (H11 : getr (ms_regs ms2) 11 = w64 (kids + 56 * Z.of_nat i))
    by exact (wvi_reg_sv E E2 (ss_regs ss2) (ms_regs ms2) 11%bv 41%nat _ HRG HA ltac:(vm_compute; reflexivity)
          ltac:(lia) E41);
  assert (H12 : getr (ms_regs ms2) 12 = w64 (y_pretty X))
    by (rewrite (wvi_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 12%bv 19%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G19);
  assert (H13 : getr (ms_regs ms2) 13 = w64 (y_dep X + 1))
    by (rewrite (wvi_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 13%bv 22%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G22);
  assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + WVI_PC 156))
    by exact (wvi_reg_ret E2 (ss_regs ss2) (ms_regs ms2) 156 HRG HEIr ltac:(vm_compute; reflexivity));
  assert (Hv2 : exists x y, In (x, y) (y_D X) /\ x <= kids + 56 * Z.of_nat i /\
      kids + 56 * Z.of_nat i + 56 <= x + y)
    by (exists kids, (56 * cap'); split; [exact Hkb' | clear - Hi Hnn' Hncap'; split; lia]);
  destruct (wvi_ret_ok 156 ltac:(lia)) as (Hr4096 & Hrok);
  apply (wvi_site_self n' X ch i (wvi_PD X i) (wvi_rest X (S i)) (kids + 56 * Z.of_nat i) (wvi_child X i) D1'
    (WVI_PC 156) lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc IH HSTKn Hdn Hpre Hst2 (wvi_pcs_D X i Hi) HN1'
    (wvi_child_depth X i Hi) HD1' Hv2 H10 H11 H12 H13 Hra Hrok Hr4096 wvi_ceil_156);
  intros fx2 ly2 S2' Hp2 W2 regs2 mem2 md2 k2 Hst3;
  rewrite <- (wvi_done_D X i Hi) in Hst3;
  exact (K156 fx2 ly2 S2' Hp2 W2 regs2 mem2 md2 k2 Hst3)
end.
Qed.

(* ---- AFTER AN OBJECT'S KEY (write_value + 4 * 130, put_string's return): the separator put at slot 133 (return 134),
   its literal from the frame word R + 56 and its length (pretty <> 0) + 1 from R + 32 ---- *)
Lemma wvs_seg_130 : forall n' X ch i lyc Sc Hpc Wc regs memc mdc kc,
  twrite_value_specX (fx := fx) (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n' ->
  STK_write_value (S n') <= y_STK X -> (PjTree.depth (y_t X) <= S n')%nat ->
  wv_pre B ARx CTX0 Pm X ch -> (i < wv_nitems (y_t X))%nat -> wv_tagc (y_t X) = 6 ->
  WST X fx i (wvi_Pk X i) lyc Sc Hpc Wc regs memc mdc kc -> wvs_K156R (wle' SEGS RZ_cf) X i ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regs (Z_to_bv 64 (BASE + WVI_PC 130)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin B ARx Pm X).
Proof.
intros n' X ch i lyc Sc Hpc Wc regs memc mdc kc IH HSTKn Hdn Hpre Hi Ht Hst K156.
destruct (wvi_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 192 <= y_STK X) by lia.
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof (@alloc_ceiling_lt rc) as HCL.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hpr & _).
pose proof Hst as (Hcom & Hrf).
pose proof Hrf as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & _).
destruct (wvi_node_facts X ch fx _ lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom ltac:(lia)) as
  (kids & keys & nn & cap & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & Hk5 & Hk6).
destruct (wvi_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVI_PC 130) false kids keys nn cap 0 HSTKn
  Hpre Hst Hi Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 Hk6 ltac:(discriminate))
  as (HEI & Hregs & HS & SHOK).
set (E := wvi_E X i regs kids keys nn 0) in *.
pose proof (wvi_E_at X i regs kids keys nn 0) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41).
fold E in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41.
pose proof Hcom as (HJ & _ & HPM & _).
assert (E19 : ew E 19 = Z_to_bv 64 (y_pretty X))
  by (rewrite (wvi_ew_reg E regs 19%bv 19%nat Hregs eq_refl); exact G19).
assert (Ho0 : 0 <= y_o X) by (clear - Ho1 Hsp1 HCV; unfold y_sp in *; lia).
assert (Ho64 : y_o X + 32 <= 2 ^ 64) by (clear - Ho2 Hdtop Htop2 H47; unfold y_sp in *; wvi_zl).
rewrite Ht in HS.
paj_run_tok_x_invR RUNI HS HJ SHOK HPM WV_Bspan; [wvs_awr | ].
wvs_kept K1 HF HFr HG.
pmkst HS.
lazymatch type of HS with st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
  pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
  assert (HA : env_agree 55 E E2) by wvs_agree;
  assert (HEIr : img_env VAL A_LIM E2) by assumption;
  pose proof (wvi_st_run X fx i _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _
    Hst Ho0 Ho64 Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM K1) as Hst2;
  assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
    by (rewrite (wvi_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G8);
  assert (H11 : getr (ms_regs ms2) 11 = w64 (WV_STR (wv_sep_slot X)))
    by exact (wvi_reg_sv E E2 (ss_regs ss2) (ms_regs ms2) 11%bv 34%nat _ HRG HA ltac:(vm_compute; reflexivity)
          ltac:(lia) E34);
  assert (H12 : getr (ms_regs ms2) 12 = w64 (Z.of_nat (length (WriterValue.wsep (y_p X)))));
  [ rewrite HRG;
    replace (sr_get (ss_regs ss2) 12%bv) with (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 19 0)) (SLit 1))
      by (vm_compute; reflexivity);
    try rewrite (sv_denot_agree 55 E E2 (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 19 0)) (SLit 1)) HA eq_refl);
    rewrite (wvi_p1_denot E (y_pretty X) E19 Hpr);
    unfold y_p, WriterValue.wsep; destruct (y_pretty X =? 0); reflexivity
  | ];
  assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + WVI_PC 134))
    by exact (wvi_reg_ret E2 (ss_regs ss2) (ms_regs ms2) 134 HRG HEIr ltac:(vm_compute; reflexivity));
  destruct (wvi_ret_ok 134 ltac:(lia)) as (Hr4096 & Hrok);
  apply (wvi_site_put n' X ch i (wvi_Pk X i)
    (WriterValue.wvpieces (wvi_child X i) (y_p X) (y_dep X + 1) ++ wvi_rest X (S i)) (wv_sep_slot X)
    (WriterValue.wsep (y_p X)) (WVI_PC 134) lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc HSTKn Hpre Hst2
    (wvi_sep_lit X) (wvi_pcs_k X i Hi Ht) H10 H11 H12 Hra Hrok Hr4096 wvi_ceil_134);
  intros ly2 S2' Hp2 W2 regs2 mem2 md2 k2 Hst3;
  rewrite <- (wvi_PD_obj X i Ht) in Hst3;
  exact (wvs_seg_134 n' X ch i ly2 S2' Hp2 W2 regs2 mem2 md2 k2 IH HSTKn Hdn Hpre Hi Hst3 K156)
end.
Qed.

(* ---- AFTER THE INDENT (write_value + 4 * 100): v's shadow check (slots 100-102: the slow_block GUARD at slot 102,
   old B 0x86ff0, its report at slot 167 / old B 0x870f4: NOT taken, the engine reads v's shadow byte as 0 off the
   seat's shadow entry mkSHE 9 0 56, whose sh_ok is shent_ok_of_range on range_addressable v 56 at the join memory,
   wvi_node_cur from WriteValueB_Base.wv_ra_cur), the tag test (slots 103-105): an array runs on to slot 134; an
   object: shadow (v + 32) (106-108), keys (109-110), keys + 8 i (111, the alias atom 39), the UBSan arms on keys + 8 i
   (slot 114 `beq`, slot 118 `beqz keys`, slot 121 `bnez ((8 i + keys) & 7)`: the engine, from keys >= 4096 and the
   alignments; slot 116 `bnez (i >> 60)` and slot 117 `bltu keys + 8 i, keys`: wvi_br116 / wvi_br117, by hand), each
   NOT taken, shadow (keys + 8 i) (122-126, the seat's key-slot entry), the key string (127) and put_string at slot 129
   (return 130, at the callee's exit float state) ---- *)
Lemma wvs_seg_100 : forall n' X ch i lyc Sc Hpc Wc regs memc mdc kc,
  twrite_value_specX (fx := fx) (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n' ->
  STK_write_value (S n') <= y_STK X -> (PjTree.depth (y_t X) <= S n')%nat ->
  wv_pre B ARx CTX0 Pm X ch -> (i < wv_nitems (y_t X))%nat ->
  WST X fx i (wvi_PB X i) lyc Sc Hpc Wc regs memc mdc kc -> wvs_K130R (wle' SEGS RZ_cf) X i ->
  wvs_K156R (wle' SEGS RZ_cf) X i ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regs (Z_to_bv 64 (BASE + WVI_PC 100)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin B ARx Pm X).
Proof.
intros n' X ch i lyc Sc Hpc Wc regs memc mdc kc IH HSTKn Hdn Hpre Hi Hst K130 K156.
destruct (wvi_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 192 <= y_STK X) by lia.
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof (@alloc_ceiling_lt rc) as HCL.
pose proof Hst as (Hcom & Hrf).
pose proof Hrf as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & _).
destruct (wvi_item_facts X ch fx _ lyc Sc Hpc Wc memc mdc kc i HSTK Hpre Hcom Hi) as
  (kids & keys & nn & cap & D1 & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & _ & _ & Hk5 & Hk6).
destruct (wvi_blk_facts X ch kids (56 * cap) HSTK Hpre Hkb) as (_ & Hk4096 & _ & Hkc & _).
pose proof Hcom as (HJ & _ & HPM & _).
assert (Hi42 : Z.of_nat i <= 2 ^ 42) by (clear - Hi Hnn Hncap Hkc Hk4096 HCL; wvi_zl).
assert (Ho0 : 0 <= y_o X) by (clear - Ho1 Hsp1 HCV; unfold y_sp in *; lia).
assert (Ho64 : y_o X + 32 <= 2 ^ 64) by (clear - Ho2 Hdtop Htop2 H47; unfold y_sp in *; wvi_zl).
assert (Htg : wv_tagc (y_t X) = 5 \/ wv_tagc (y_t X) = 6) by (unfold wv_tagc; destruct (y_t X); auto).
destruct Htg as [Ht | Ht].
- (* an array: the tag test sends the run on to slot 134 *)
  destruct (wvi_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVI_PC 100) false kids keys nn cap 0 HSTKn
    Hpre Hst Hi Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 (fun H => proj1 (Hk6 H)) ltac:(discriminate))
    as (HEI & Hregs & HS & SHOK).
  set (E := wvi_E X i regs kids keys nn 0) in *.
  rewrite Ht in HS.
  paj_run_to_tok_x_invR RUNTOI HS HJ SHOK HPM WV_Bspan (WVI_PC 134); [wvs_awr | ].
  wvs_kept K1 HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) =>
    pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E2 ss2 ms2 r HS) as HRG;
    assert (HA : env_agree 55 E E2) by wvs_agree;
    pose proof (wvi_st_run X fx i _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _
      Hst Ho0 Ho64 Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM K1) as Hst2
  end.
  rewrite <- (wvi_PD_arr X i Ht) in Hst2.
  lazymatch goal with |- context [mkCfg (mkst _ (Z_to_bv 64 (BASE + ?c)) _ _) _] =>
    replace c with (WVI_PC 134) by (unfold WVI_PC; vm_compute; reflexivity) end.
  exact (wvs_seg_134 n' X ch i lyc Sc Hpc Wc _ _ _ kc IH HSTKn Hdn Hpre Hi Hst2 K156).
- (* an object: keys[i] (the seat's key slot, its word x the key string) and the put_string call (slot 129) *)
  destruct (Hk6 Ht) as (Hkb6 & x & k & HxD & Rx & Hcs).
  destruct (wvi_blk_facts X ch keys (8 * cap) HSTK Hpre Hkb6) as (_ & Hq4096 & _ & Hqc & _).
  destruct (wvi_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVI_PC 100) true kids keys nn cap x HSTKn
    Hpre Hst Hi Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 (fun H => proj1 (Hk6 H)) (fun _ => conj Ht Rx))
    as (HEI & Hregs & HS & SHOK).
  set (E := wvi_E X i regs kids keys nn x) in *.
  pose proof (wvi_E_at X i regs kids keys nn x) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41).
  fold E in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41.
  assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat i))
    by (rewrite (wvi_ew_reg E regs 21%bv 21%nat Hregs eq_refl); exact G21).
  rewrite Ht in HS.
  (* 100 .. 115: the guard (not taken), the tag test, keys, keys + 8 i; stuck at `bnez (i >> 60)` at 116 *)
  paj_run_tok_x_invR RUNI HS HJ SHOK HPM WV_Bspan; [wvs_awr | ].
  wvs_kept K1 HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => assert (HA1 : env_agree 55 E E1) by wvs_agree end.
  psrr_branch_tokR RUNI BR HS SHOK WV_Bspan.
  all: rewrite (wvi_br116 _ i (wvi_ew_agree E _ 21%nat _ HA1 ltac:(lia) E21) Hi42) in Hc.
  1: discriminate Hc.
  clear Hc.
  (* stuck at `bltu keys + 8 i, keys` at 117 *)
  paj_run_tok_x_invR RUNI HS HJ SHOK HPM WV_Bspan; [wvs_awr | ].
  wvs_kept K2 HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => assert (HA2 : env_agree 55 E E1) by wvs_agree end.
  psrr_branch_tokR RUNI BR HS SHOK WV_Bspan.
  all: rewrite (wvi_br117 _ keys i (wvi_ew_agree E _ 39%nat _ HA2 ltac:(lia) E39)
         (wvi_ew_agree E _ 37%nat _ HA2 ltac:(lia) E37) ltac:(lia) ltac:(clear - Hi Hnn Hncap Hqc HCL; wvi_zl)) in Hc.
  1: discriminate Hc.
  (* 118 .. 129: the rest of the arms (the engine), the key slot's shadow, the key, put_string *)
  paj_run_tok_x_invR RUNI HS HJ SHOK HPM WV_Bspan; [wvs_awr | ].
  wvs_kept K3 HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
    pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
    assert (HA : env_agree 55 E E2) by wvs_agree;
    assert (HEIr : img_env VAL A_LIM E2) by assumption;
    assert (KM : forall a, aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
      by (intros a; rewrite K3, K2; apply K1);
    pose proof (wvi_st_run X fx i _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _
      Hst Ho0 Ho64 Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM KM) as Hst2;
    assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
      by (rewrite (wvi_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
            ltac:(vm_compute; reflexivity)); exact G8);
    assert (H11 : getr (ms_regs ms2) 11 = w64 x)
      by (exact (wvi_reg_sv E E2 (ss_regs ss2) (ms_regs ms2) 11%bv 40%nat _ HRG HA ltac:(vm_compute; reflexivity)
            ltac:(lia) E40));
    assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + WVI_PC 130))
      by (exact (wvi_reg_ret E2 (ss_regs ss2) (ms_regs ms2) 130 HRG HEIr ltac:(vm_compute; reflexivity)));
    assert (Hcs2 : pj_cstrR SEGS (mrestrict (w_H Wc) (ms_mem ms2)) (prh_lin (y_Lam X)) x k (wvi_key X i))
      by (eapply pj_cstrR_frame; [exact Hcs | intros a _; apply (mbyte_of_aview SEGS); apply KM]);
    destruct (wvi_ret_ok 130 ltac:(lia)) as (Hr4 & Hrok);
    exact (wvi_site_put_string n' X ch i (wvi_PB X i) _ x k (WVI_PC 130) lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc
      HSTKn Hpre Hst2 (wvi_pcs_B X i Hi Ht) HxD Hcs2 H10 H11 Hra Hrok Hr4 wvi_ceil_130 (K130 Ht))
  end.
Qed.

(* ---- AFTER THE COMMA (write_value + 4 * 95): `bnez s10` (s10 = 0: the engine, NOT taken), indent (o, pretty,
   dep + 1) at slot 99 (return 100) ---- *)
Lemma wvs_seg_95 : forall n' X ch i lyc Sc Hpc Wc regs memc mdc kc,
  twrite_value_specX (fx := fx) (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n' ->
  STK_write_value (S n') <= y_STK X -> (PjTree.depth (y_t X) <= S n')%nat ->
  wv_pre B ARx CTX0 Pm X ch -> (i < wv_nitems (y_t X))%nat ->
  WST X fx i (wvi_PA X i) lyc Sc Hpc Wc regs memc mdc kc -> wvs_K130R (wle' SEGS RZ_cf) X i ->
  wvs_K156R (wle' SEGS RZ_cf) X i ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regs (Z_to_bv 64 (BASE + WVI_PC 95)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin B ARx Pm X).
Proof.
intros n' X ch i lyc Sc Hpc Wc regs memc mdc kc IH HSTKn Hdn Hpre Hi Hst K130 K156.
destruct (wvi_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 192 <= y_STK X) by lia.
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hpr & Hdep & Hdd & _).
assert (Hdep1 : - 2 ^ 31 <= y_dep X + 1 < 2 ^ 31)
  by (pose proof (wvi_depth_pos (y_t X) ltac:(lia)) as Hd1; clear - Hdep Hdd Hd1; wvi_zl).
pose proof Hst as (Hcom & Hrf).
pose proof Hrf as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & _).
destruct (wvi_node_facts X ch fx _ lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom ltac:(lia)) as
  (kids & keys & nn & cap & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & Hk5 & Hk6).
destruct (wvi_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVI_PC 95) false kids keys nn cap 0 HSTKn
  Hpre Hst Hi Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 Hk6 ltac:(discriminate))
  as (HEI & Hregs & HS & SHOK).
set (E := wvi_E X i regs kids keys nn 0) in *.
pose proof Hcom as (HJ & _ & HPM & _).
assert (Ho0 : 0 <= y_o X) by (clear - Ho1 Hsp1 HCV; unfold y_sp in *; lia).
assert (Ho64 : y_o X + 32 <= 2 ^ 64) by (clear - Ho2 Hdtop Htop2 H47; unfold y_sp in *; wvi_zl).
assert (Htg : wv_tagc (y_t X) = 5 \/ wv_tagc (y_t X) = 6) by (unfold wv_tagc; destruct (y_t X); auto).
destruct Htg as [Ht | Ht]; rewrite Ht in HS.
all: paj_run_tok_x_invR RUNI HS HJ SHOK HPM WV_Bspan; [wvs_awr | ].
all: wvs_kept K1 HF HFr HG.
all: pmkst HS.
all: lazymatch type of HS with st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
  pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
  assert (HA : env_agree 55 E E2) by wvs_agree;
  assert (HEIr : img_env VAL A_LIM E2) by assumption;
  pose proof (wvi_st_run X fx i _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _
    Hst Ho0 Ho64 Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM K1) as Hst2;
  assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
    by (rewrite (wvi_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G8);
  assert (H11 : getr (ms_regs ms2) 11 = w64 (y_pretty X))
    by (rewrite (wvi_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 11%bv 19%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G19);
  assert (H12 : getr (ms_regs ms2) 12 = w64 (y_dep X + 1))
    by (rewrite (wvi_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 12%bv 22%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G22);
  assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + WVI_PC 100))
    by exact (wvi_reg_ret E2 (ss_regs ss2) (ms_regs ms2) 100 HRG HEIr ltac:(vm_compute; reflexivity));
  destruct (wvi_ret_ok 100 ltac:(lia)) as (Hr4096 & Hrok);
  apply (wvi_site_indent n' X ch i (wvi_PA X i) _ (y_dep X + 1) (WVI_PC 100)
    lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc HSTKn Hpre Hst2 (wvi_pcs_A X i Hi) Hdep1 H10 H11 H12 Hra
    Hrok Hr4096 wvi_ceil_100);
  intros ly2 S2' Hp2 W2 regs2 mem2 md2 k2 Hst3;
  exact (wvs_seg_100 n' X ch i ly2 S2' Hp2 W2 regs2 mem2 md2 k2 IH HSTKn Hdn Hpre Hi Hst3 K130 K156)
end.
Qed.

(* ---- THE HEAD (write_value + 4 * 90): `beqz s5`: item 0 goes to slot 95 directly; item i > 0 first puts the comma
   (the literal at R + 64, slot 94, return 95) ---- *)
Lemma wvs_seg_90 : forall n' X ch i P lyc Sc Hpc Wc regs memc mdc kc,
  twrite_value_specX (fx := fx) (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n' ->
  STK_write_value (S n') <= y_STK X -> (PjTree.depth (y_t X) <= S n')%nat ->
  wv_pre B ARx CTX0 Pm X ch -> wv_headR B ARx Pm (wle' SEGS RZ_cf) X fx i P lyc Sc Hpc Wc regs memc mdc kc ->
  wvs_K130R (wle' SEGS RZ_cf) X i -> wvs_K156R (wle' SEGS RZ_cf) X i ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regs (Z_to_bv 64 (BASE + WVH_PC)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin B ARx Pm X).
Proof.
intros n' X ch i P lyc Sc Hpc Wc regs memc mdc kc IH HSTKn Hdn Hpre Hh K130 K156.
destruct (wvi_head_st X fx i P lyc Sc Hpc Wc regs memc mdc kc Hh) as (Hst & Hi & HP). subst P.
destruct (wvi_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 192 <= y_STK X) by lia.
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof (@alloc_ceiling_lt rc) as HCL.
pose proof Hst as (Hcom & Hrf).
pose proof Hrf as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & _).
destruct (wvi_node_facts X ch fx _ lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom ltac:(lia)) as
  (kids & keys & nn & cap & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & Hk5 & Hk6).
destruct (wvi_blk_facts X ch kids (56 * cap) HSTK Hpre Hkb) as (_ & Hk4096 & _ & Hkc & _).
destruct (wvi_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVI_PC 90) false kids keys nn cap 0 HSTKn
  Hpre Hst Hi Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 Hk6 ltac:(discriminate))
  as (HEI & Hregs & HS & SHOK).
set (E := wvi_E X i regs kids keys nn 0) in *.
pose proof (wvi_E_at X i regs kids keys nn 0) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41).
fold E in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41.
pose proof Hcom as (HJ & _ & HPM & _).
assert (Hi64 : Z.of_nat i < 2 ^ 64) by (clear - Hi Hnn Hncap Hkc Hk4096 HCL; wvi_zl).
assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat i))
  by (rewrite (wvi_ew_reg E regs 21%bv 21%nat Hregs eq_refl); exact G21).
assert (Ho0 : 0 <= y_o X) by (clear - Ho1 Hsp1 HCV; unfold y_sp in *; lia).
assert (Ho64 : y_o X + 32 <= 2 ^ 64) by (clear - Ho2 Hdtop Htop2 H47; unfold y_sp in *; wvi_zl).
change (BASE + WVH_PC) with (BASE + WVI_PC 90).
assert (Htg : wv_tagc (y_t X) = 5 \/ wv_tagc (y_t X) = 6) by (unfold wv_tagc; destruct (y_t X); auto).
destruct Htg as [Ht | Ht]; rewrite Ht in HS.
all: paj_run_tok_x_invR RUNI HS HJ SHOK HPM WV_Bspan; [wvs_awr | ].
all: wvs_kept K1 HF HFr HG.
all: lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => assert (HA1 : env_agree 55 E E1) by wvs_agree end.
all: psrr_branch_tokR RUNI BR HS SHOK WV_Bspan.
all: rewrite (wvi_br90 _ i (wvi_ew_agree E _ 21%nat _ HA1 ltac:(lia) E21) Hi64) in Hc.
(* item 0: on to slot 95 *)
1, 3: apply Z.eqb_eq in Hc; assert (Hi0 : i = 0%nat) by lia; subst i;
  paj_run_to_tok_x_invR RUNTOI HS HJ SHOK HPM WV_Bspan (WVI_PC 95); [wvs_awr | ];
  wvs_kept K2 HF HFr HG;
  pmkst HS;
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?c)] =>
    replace c with (WVI_PC 95) by (unfold WVI_PC; vm_compute; reflexivity) end;
  lazymatch type of HS with st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) =>
    pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E2 ss2 ms2 r HS) as HRG;
    assert (HA : env_agree 55 E E2) by wvs_agree;
    assert (KM : forall a, aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
      by (intros a; rewrite K2; apply K1);
    pose proof (wvi_st_run X fx 0 _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _
      Hst Ho0 Ho64 Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM KM) as Hst2;
    rewrite <- (wvi_PA_0 X) in Hst2;
    exact (wvs_seg_95 n' X ch 0 lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc IH HSTKn Hdn Hpre Hi Hst2 K130 K156)
  end.
(* item i > 0: the comma *)
all: apply Z.eqb_neq in Hc; assert (Hi0 : i <> 0%nat) by lia.
all: paj_run_tok_x_invR RUNI HS HJ SHOK HPM WV_Bspan; [wvs_awr | ].
all: wvs_kept K2 HF HFr HG.
all: pmkst HS.
all: lazymatch type of HS with st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
  pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
  assert (HA : env_agree 55 E E2) by wvs_agree;
  assert (HEIr : img_env VAL A_LIM E2) by assumption;
  assert (KM : forall a, aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
    by (intros a; rewrite K2; apply K1);
  pose proof (wvi_st_run X fx i _ lyc Sc Hpc Wc regs memc mdc kc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) _
    Hst Ho0 Ho64 Hregs HA HRG ltac:(vm_compute; reflexivity) HJ HPM KM) as Hst2;
  assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
    by (rewrite (wvi_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
          ltac:(vm_compute; reflexivity)); exact G8);
  assert (H11 : getr (ms_regs ms2) 11 = w64 (WV_STR 88))
    by exact (wvi_reg_sv E E2 (ss_regs ss2) (ms_regs ms2) 11%bv 35%nat _ HRG HA ltac:(vm_compute; reflexivity)
          ltac:(lia) E35);
  assert (H12 : getr (ms_regs ms2) 12 = w64 (Z.of_nat (length [44])))
    by exact (wvi_reg_lit E2 (ss_regs ss2) (ms_regs ms2) 12%bv 1 HRG ltac:(vm_compute; reflexivity));
  assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + WVI_PC 95))
    by exact (wvi_reg_ret E2 (ss_regs ss2) (ms_regs ms2) 95 HRG HEIr ltac:(vm_compute; reflexivity));
  destruct (wvi_ret_ok 95 ltac:(lia)) as (Hr4096 & Hrok);
  apply (wvi_site_put n' X ch i (wv_done X i) _ 88%nat [44] (WVI_PC 95)
    lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc HSTKn Hpre Hst2 wvi_comma_lit (wvi_pcs_comma X i Hi Hi0)
    H10 H11 H12 Hra Hrok Hr4096 wvi_ceil_95);
  intros ly2 S2' Hp2 W2 regs2 mem2 md2 k2 Hst3;
  rewrite (wvi_PA_comma X i Hi0) in Hst3;
  exact (wvs_seg_95 n' X ch i ly2 S2' Hp2 W2 regs2 mem2 md2 k2 IH HSTKn Hdn Hpre Hi Hst3 K130 K156)
end.
Qed.

(* ---- AFTER THE VALUE (write_value + 4 * 156, write_value's return): shadow (v + 40) (156-157), n (158), the
   increments (159-161), the back edge `bltu s5 + 1, n` (slot 162, wvi_br162): to the head at i + 1 (HNEXT), or past
   the last item: `j` (163), `beqz n` (168: n <> 0, the engine), the closing indent (o, pretty, dep) at slot 172
   (return 173 = the close, wv_cl, HCL) ---- *)
Lemma wvs_seg_156 : forall n' X ch i lyc Sc Hpc Wc regs memc mdc kc,
  STK_write_value (S n') <= y_STK X -> wv_pre B ARx CTX0 Pm X ch -> (i < wv_nitems (y_t X))%nat ->
  WST X fx i (wv_done X (S i)) lyc Sc Hpc Wc regs memc mdc kc ->
  (forall P lyc' Sc' Hpc' (Wc' : world SEGS) (regs' : bvmap 5 word) mem' md' kc',
     wv_headR B ARx Pm (wle' SEGS RZ_cf) X fx (S i) P lyc' Sc' Hpc' Wc' regs' mem' md' kc' ->
     SRr' SEGS RZ_cf Wc' (mkCfg (@mkst fx regs' (Z_to_bv 64 (BASE + WVH_PC)) mem' (seg_rom SEGS)) md')
       (wv_Qfin B ARx Pm X)) ->
  wv_CLOSEKR B ARx Pm (wle' SEGS RZ_cf) X ->
  SRr' SEGS RZ_cf Wc (mkCfg (@mkst fx regs (Z_to_bv 64 (BASE + WVI_PC 156)) memc (seg_rom SEGS)) mdc)
    (wv_Qfin B ARx Pm X).
Proof.
intros n' X ch i lyc Sc Hpc Wc regs memc mdc kc HSTKn Hpre Hi Hst HNEXT HCL.
destruct (wvi_stk n') as (S1 & S2 & S3 & S4 & S5).
assert (HSTK : 192 <= y_STK X) by lia.
destruct (wvi_pre_facts X ch Hpre HSTK) as (HAR0 & Hsp1 & Hsp2 & Hsp16 & Hd0 & Hd16 & Hdtop & Htop2 & H47 & H64 &
  Hoal & Ho1 & Ho2 & HRAZ & Hcnt & Hbufin & Hcap0).
pose proof (@alloc_ceiling_value rc) as HCV. pose proof (@alloc_ceiling_lt rc) as HCL0.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hpr & Hdep & Hdd & _).
pose proof Hst as (Hcom & Hrf).
pose proof Hrf as (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & _).
assert (Hn : (0 < wv_nitems (y_t X))%nat) by lia.
destruct (wvi_node_facts X ch fx _ lyc Sc Hpc Wc memc mdc kc HSTK Hpre Hcom Hn) as
  (kids & keys & nn & cap & Vtg & Rkids & Rkeys & Rnn & Hnn & Hncap & Hcap & Hkb & Hk5 & Hk6).
destruct (wvi_blk_facts X ch kids (56 * cap) HSTK Hpre Hkb) as (_ & Hk4096 & _ & Hkc & _).
destruct (wvi_seat_join n' X ch i _ lyc Sc Hpc Wc regs memc mdc kc (WVI_PC 156) false kids keys nn cap 0 HSTKn
  Hpre Hst Hi Vtg Rkids Rkeys Rnn Hnn Hncap Hcap Hkb Hk5 Hk6 ltac:(discriminate))
  as (HEI & Hregs & HS & SHOK).
set (E := wvi_E X i regs kids keys nn 0) in *.
pose proof (wvi_E_at X i regs kids keys nn 0) as (E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41).
fold E in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41.
pose proof Hcom as (HJ & _ & HPM & _).
assert (Hnn64 : 0 <= nn < 2 ^ 64) by (clear - Hnn Hncap Hkc Hk4096 HCL0; wvi_zl).
assert (Hb56 : 56 * Z.of_nat (S i) < 2 ^ 64) by (clear - Hi Hnn Hncap Hkc Hk4096 HCL0; wvi_zl).
assert (Ho0 : 0 <= y_o X) by (clear - Ho1 Hsp1 HCV; unfold y_sp in *; lia).
assert (Ho64 : y_o X + 32 <= 2 ^ 64) by (clear - Ho2 Hdtop Htop2 H47; unfold y_sp in *; wvi_zl).
assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat i))
  by (rewrite (wvi_ew_reg E regs 21%bv 21%nat Hregs eq_refl); exact G21).
assert (Htg : wv_tagc (y_t X) = 5 \/ wv_tagc (y_t X) = 6) by (unfold wv_tagc; destruct (y_t X); auto).
destruct Htg as [Ht | Ht]; rewrite Ht in HS.
(* 156 .. 161: shadow (v + 40), n, the increments; stuck at the back edge `bltu` at 162 *)
all: paj_run_tok_x_invR RUNI HS HJ SHOK HPM WV_Bspan; [wvs_awr | ].
all: wvs_kept K1 HF HFr HG.
all: lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => assert (HA1 : env_agree 55 E E1) by wvs_agree end.
all: psrr_branch_tokR RUNI BR HS SHOK WV_Bspan.
all: rewrite (wvi_br162 _ i nn (wvi_ew_agree E _ 21%nat _ HA1 ltac:(lia) E21)
       (wvi_ew_agree E _ 38%nat _ HA1 ltac:(lia) E38) Hnn64 ltac:(clear - Hb56; wvi_zl)) in Hc.
all: lazymatch type of Hc with
     | _ = true =>
         apply Z.ltb_lt in Hc;
         paj_run_to_tok_x_invR RUNTOI HS HJ SHOK HPM WV_Bspan (WVI_PC 90); [wvs_awr | ]
     | _ = false =>
         apply Z.ltb_ge in Hc;
         paj_run_tok_x_invR RUNI HS HJ SHOK HPM WV_Bspan; [wvs_awr | ]
     end.
all: wvs_kept K2 HF HFr HG.
all: pmkst HS.
all: lazymatch type of HS with
     | st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) =>
       (* the back edge: the head at i + 1 *)
       lazymatch goal with |- context [Z_to_bv 64 (BASE + ?c)] =>
         replace c with WVH_PC by (unfold WVH_PC; vm_compute; reflexivity) end;
       pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E2 ss2 ms2 r HS) as HRG;
       assert (HA : env_agree 55 E E2) by wvs_agree;
       assert (KM : forall a, aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
         by (intros a; rewrite K2; apply K1);
       apply (HNEXT (wv_done X (S i)) lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) _ kc);
       apply wvi_st_head; [ split | clear - Hc Hnn; lia | reflexivity ];
       [ exact (wvi_common_run X fx _ lyc Sc Hpc Wc memc mdc kc (ms_mem ms2) _ Hcom Ho0 Ho64 HJ HPM KM)
       | exact (wvi_rf_next X i Wc regs memc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) Hrf Hregs HA HRG
           ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) Hb56 KM) ]
     | st_ok _ ?E2 ?ss2 (restrict _ ?ms2) =>
       (* the exit: the closing indent at depth dep, then the close *)
       assert (HSi : S i = wv_nitems (y_t X)) by (clear - Hc Hi Hnn; lia);
       pose proof (fun r => st_ok_restrict_reg SEGS (w_H Wc) E2 ss2 ms2 r HS) as HRG;
       assert (HA : env_agree 55 E E2) by wvs_agree;
       assert (HEIr : img_env VAL A_LIM E2) by assumption;
       assert (KM : forall a, aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
         by (intros a; rewrite K2; apply K1);
       lazymatch goal with |- context [mkCfg _ ?md2] =>
       assert (Hst2 : WST X fx (S i) (wv_done X (S i)) lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2) md2 kc)
         by (split;
             [ exact (wvi_common_run X fx _ lyc Sc Hpc Wc memc mdc kc (ms_mem ms2) _ Hcom Ho0 Ho64 HJ HPM KM)
             | exact (wvi_rf_next X i Wc regs memc E E2 (ss_regs ss2) (ms_regs ms2) (ms_mem ms2) Hrf Hregs HA HRG
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity) Hb56 KM) ]);
       rewrite HSi in Hst2;
       assert (H10 : getr (ms_regs ms2) 10 = w64 (y_o X))
         by (rewrite (wvi_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 10%bv 8%bv HRG Hregs HA
               ltac:(vm_compute; reflexivity)); exact G8);
       assert (H11 : getr (ms_regs ms2) 11 = w64 (y_pretty X))
         by (rewrite (wvi_reg_mv E E2 (ss_regs ss2) regs (ms_regs ms2) 11%bv 19%bv HRG Hregs HA
               ltac:(vm_compute; reflexivity)); exact G19);
       assert (H12 : getr (ms_regs ms2) 12 = w64 (y_dep X))
         by (exact (wvi_reg_sv E E2 (ss_regs ss2) (ms_regs ms2) 12%bv 33%nat _ HRG HA ltac:(vm_compute; reflexivity)
               ltac:(lia) E33));
       assert (Hra : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + WVI_PC 173))
         by (exact (wvi_reg_ret E2 (ss_regs ss2) (ms_regs ms2) 173 HRG HEIr ltac:(vm_compute; reflexivity)));
       destruct (wvi_ret_ok 173 ltac:(lia)) as (Hr4096 & Hrok);
       apply (wvi_site_indent n' X ch (wv_nitems (y_t X)) (wv_done X (wv_nitems (y_t X)))
         [[if wv_tagc (y_t X) =? 6 then 125 else 93]] (y_dep X) (WVI_PC 173) lyc Sc Hpc Wc (ms_regs ms2) (ms_mem ms2)
         md2 kc HSTKn Hpre Hst2 (wvi_pcs_end X Hn) ltac:(clear - Hdep; wvi_zl) H10 H11 H12 Hra Hrok Hr4096 wvi_ceil_173);
       intros ly4 S4' Hp4 W4 regs4 mem4 md4 k4 Hst4;
       rewrite <- (wvi_clP_eq X Hn) in Hst4;
       exact (HCL fx ly4 S4' Hp4 W4 regs4 mem4 md4 k4 (wvi_st_cl X fx _ ly4 S4' Hp4 W4 regs4 mem4 md4 k4 Hst4))
       end
     end.
Qed.

End cont.
End cl.
End h.
End f.
End d.
