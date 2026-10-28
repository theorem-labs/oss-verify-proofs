(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup QRjH QHnV QCcH QfLs Q0Ek QjDH Qsw7 QJjn QKQo UPIU U9Mh QnCn Q6q3 Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply Lib.GwApply2 Lib.GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn QKQo.
Import UPIU.Mq6.
Import U9Mh.Mq2.
Import QnCn.Mq0.
Import UPIU.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition jonewarray_code (w_4 w_7 w_9 w_21 w_26 : Z) : list Z :=
[0xff010113; 0x00113423; 0x00813023; 0x03000513; w_4; 0x04050e63; 0x00100593; w_7; 0x02059593; w_9; 0x00558593; 0x00b53023; 0x00c53423; 0x00053823; 0x00053c23; 0x02053023; 0x00000597; 0x04058613; 0x02000593; 0x00050413; 0x00060513; w_21; 0x00050593; 0x00040513; 0x02b43423; 0x00059663; w_26; 0x00000513; 0x00813083; 0x00013403; 0x01010113; 0x00008067]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_4 w_7 w_9 w_21 w_26 : Z).
Variables (hi_7 : bv 20).
Variables (lo_9 : bv 12).
Variables (joff_4 joff_21 joff_26 : bv 21).
Variables (e_alnew : Z).
Context {RC__ : Q6q3.RunConsts}.
Variables (e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC : Z) (gVOL gCS : Z -> Prop) (gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI : Z).
Hypothesis gH1 : forall a, gCS a -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH2 : gl_range_ok gIMG_LO gIMG_HI.
Hypothesis gH3 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH4 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> ~ gCS a.
Hypothesis gH5 : forall c a, In c [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))] -> (fst c <= a < fst c + Z.of_nat (length (snd c)))%Z ->
~ gCS a /\ ~ (gTP - 164 <= a < gTP - 160)%Z /\ (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis LAY_gIMG_LO : (gIMG_LO = 65536)%Z.
Hypothesis LAY_TPLO : gw_le gIMG_LO (gTP - 164).
Hypothesis LAY_TPHI : gw_le (gTP - 160) gIMG_HI.
#[using="gH2 gH3 LAY_gIMG_LO"] Lemma gLAYF : ((0 <= gIMG_LO /\ gIMG_HI <= alloc_ceiling) /\ (gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - gH2 gH3 LAY_gIMG_LO gTP gIMG_LO gIMG_HI. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.

Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Hypothesis CODE : code_at segs base (jonewarray_code w_4 w_7 w_9 w_21 w_26).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 128.
Hypothesis D_4 : decode_any (Z_to_bv 32 w_4) = Some (Jal 1 joff_4, 4%Z).
Hypothesis E_4 : is_ecall (Z_to_bv 32 w_4) = false.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 12 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_9 : decode_any (Z_to_bv 32 w_9) = Some (OpImm ALU_ADD 12 12 lo_9, 4%Z).
Hypothesis E_9 : is_ecall (Z_to_bv 32 w_9) = false.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Jal 1 joff_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Jal 1 joff_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis ANCH_9 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_9)%Z e_fn_arr_to_json_string.
Hypothesis LINK_4 : gw_anch (base + 16 + bv_signed joff_4)%Z e_malloc.
Hypothesis LINK_21 : gw_anch (base + 84 + bv_signed joff_21)%Z (e_alnew + 0)%Z.
Hypothesis LINK_26 : gw_anch (base + 104 + bv_signed joff_26)%Z e_free.

Hypothesis array_list_new2_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@UPIU.Mq1.gw_all) (@UPIU.Mq1.array_list_new2_cps) e_alnew)) in exact T).

Let e_blk_17684 : Z := base.
Definition jo_post_frame := ltac:(let t := constr:(ltac:(gw_ctx2 (@U9Mh.Mq2.jo_post_frame))) in let t := eval cbv beta delta [U9Mh.Mq2.jo_post_frame] in t in let t := eval cbv delta [e_blk_17684] in t in exact t).
Definition jo_new_container_stmt := ltac:(let t := constr:(ltac:(gw_ctx2 (@U9Mh.Mq2.jo_new_container_stmt))) in let t := eval cbv beta delta [U9Mh.Mq2.jo_new_container_stmt] in t in let t := eval cbv delta [e_blk_17684] in t in let x := constr:(ltac:(gw_ctx2 (@U9Mh.Mq2.jo_post_frame))) in let t := gw_subst t x jo_post_frame in exact t).

Let S4L : heap_layout :=
{| hl_segs := segs;
hl_malloc := e_malloc; hl_free := e_free; hl_calloc := e_calloc; hl_realloc := e_realloc; hl_malloc2 := e_malloc2; hl_free2 := e_free2;
hl_tp := gTP;
hl_got_guard := gGOTG; hl_guard := gGUARD; hl_auxv := gAUXV; hl_libc := gLIBC; hl_volatile := gVOL;
hl_stack := 8256;
hl_client_static := gCS;
hl_scratch := fun a => (gTP - 164 <= a < gTP - 160)%Z;
hl_consts := [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))];
hl_img_lo := gIMG_LO; hl_img_hi := gIMG_HI;
hl_static_in_img := gH1; hl_img_range := gH2; hl_scratch_in_img := gH3; hl_scratch_not_static := gH4; hl_consts_ok := gH5 |}.
Let S4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
Hypothesis ANCH_R17 : gw_anch (0 + (base + 64) + 64)%Z e_fn_arr_entry_free.
Hypothesis AL_e_fn_arr_to_json_string : gw_b4 e_fn_arr_to_json_string.
Hypothesis RNG_e_fn_arr_to_json_string : gw_br e_fn_arr_to_json_string 4.
Hypothesis LAY_POS_e_fn_arr_to_json_string : gw_le 1 e_fn_arr_to_json_string.
Hypothesis LAY_HI_e_fn_arr_to_json_string : gw_le (e_fn_arr_to_json_string + 4) 1099511627776.
#[using="w_4 w_7 w_9 w_21 w_26 hi_7 lo_9 joff_4 joff_21 joff_26 e_alnew RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_4 E_4 D_7 E_7 D_9 E_9 D_21 E_21 D_26 E_26 ANCH_9 LINK_4 LINK_21 LINK_26 array_list_new2_cps ANCH_R17 AL_e_fn_arr_to_json_string RNG_e_fn_arr_to_json_string LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Ltac g_ra_even := lazymatch goal with |- (bv_unsigned (Z_to_bv 64 (?b + ?k)) mod 2 = 0)%Z =>
let X := fresh in let Y := fresh in pose proof BASE4 as X; pose proof BASER as Y; unfold gw_b4, gw_br in X, Y; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia end.
Ltac alloc_side ::=
try (progress fold S4L); try (progress fold S4F);
simpl hl_segs; simpl hl_stack; simpl hl_tp; simpl hl_malloc; simpl hl_free; simpl hl_calloc; simpl hl_realloc;
rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- forall _, _ => idtac
| |- _ \/ _ => idtac
| |- (bv_unsigned (Z_to_bv 64 (_ + _)) mod 2 = 0)%Z => first [ g_ra_even | lia ]
| |- _ =>
lazymatch goal with
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ _ _ => eassumption
| |- @eq (bv _) _ _ => first [ reflexivity | eassumption | symmetry; eassumption | apply bv_eq; rewrite ?unsigned_lit by lia; lia ]
| |- (_ mod 16 = 0)%Z =>
first [ assumption
| match goal with H : (bv_unsigned ?sp mod 16 = 0)%Z |- ((bv_unsigned ?sp + ?k) mod 16 = 0)%Z =>
rewrite <- Zplus_mod_idemp_l, H; reflexivity end
| lia ]
| |- _ => first [ lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia ]
end end.
Ltac gj_fold := try (progress fold S4L); repeat match goal with H : _ |- _ => progress fold S4L in H end; try (progress fold S4F); repeat match goal with H : _ |- _ => progress fold S4F in H end.
Ltac unfold_consts ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
Ltac clia ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
Ltac unfold_consts_goal ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size.
Ltac gj_fn_cbn := try (progress cbn [S4F fn_arr_to_json_string]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section RC__1.

Section JoNewArray.
Variable HIx : heap_iface S4L.

#[using="w_4 w_7 w_9 w_21 w_26 hi_7 lo_9 joff_4 joff_21 joff_26 e_alnew LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_4 E_4 D_7 E_7 D_9 E_9 D_21 E_21 D_26 E_26 ANCH_9 LINK_4 LINK_21 LINK_26 array_list_new2_cps ANCH_R17 LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string"] Lemma json_object_new_array_cps : (jo_new_container_stmt S4L HIx S4F (fun _ => True) (base + 0x0) (32 + 32 + 8256) (Sarr [])).
Proof. clear - w_4 w_7 w_9 w_21 w_26 hi_7 lo_9 joff_4 joff_21 joff_26 e_alnew LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_4 E_4 D_7 E_7 D_9 E_9 D_21 E_21 D_26 E_26 ANCH_9 LINK_4 LINK_21 LINK_26 array_list_new2_cps ANCH_R17 LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string base S4F HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_arr_to_json_string as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_arr_to_json_string as gL3_; unfold gw_le in gL3_.
unfold jo_new_container_stmt. intros until errv. intros PRE _ K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA). cbn [hl_segs hl_tp S4L] in *.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. subst tp.
carve_frame 16%nat ST.
do 5 step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 mA md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] mA) as MU.
pose proof (wmono_refl segs mA) as WM.
reenter MOK2.
step. if_truex. do 4 step.
apply evt_RZ_done. apply (K _ md2 mA 0).
+ unfold jo_post_frame. cbn [hl_segs hl_tp S4L].
split; [apply ret_statew_same|]. split; [exact VM2|]. split; [|split; [exact HPR | exists e2; exact ERR2]].
release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ left. split; [reflexivity|]. exists A2. exact HP2.
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] mA) as MU.
pose proof (wmono_refl segs mA) as WM.
reenter MOK2.
step. if_falsex.
do 5 step. stepz. stepz. stepz. stepz. stepz.
do 5 step. step.

apply evt_RZ_done.
eapply (array_list_new2_cps HIx) with (LB := (r, 48) :: LB) (isz := 32) (lo := lo);
[ heap_now S4L HIx HP2 MU WM MI | .. ]; try alloc_side.
intros ms3 md3 (mB & A3 & r2 & e3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR3 by lia.
extend_pres S4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
clear MU WM MI.
destruct OUT3 as [(-> & HP3) | (Hr2 & BS2 & AL3 & HP3)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl segs mB) as WM.
reenter MOK3.
step. step. stepz. step. if_false. step.

alloc_call (hi_free S4L HIx) S4L HIx HP3 MU WM MI.
{ right. exists 48. left. reflexivity. }
intros ms4 mC md4 A4 r4 RS4 VM4 ST4 HPR4 ERR4 HP4. open_ret RS4. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR4, HP4.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR4 by lia.
extend_pres S4L HIx HPR MU WM HP3 HPR4.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] mC) as MU. pose proof (wmono_refl segs mC) as WM.
reenter MOK4.
step. do 4 step.
apply evt_RZ_done. apply (K _ md4 mC 0).
* unfold jo_post_frame. cbn [hl_segs hl_tp S4L].
split; [| split; [| split; [| split; [exact HPR | exists e3; exact ERR4]]]].
-- apply ret_statew_intro; [exact FS3 | exact FRM3].
-- eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3 | exact VM4].
-- release_frame FR ST4 (bv_unsigned sp). exact ST4.
* left. split; [reflexivity|]. exists A4. exact HP4.
+
pose proof AL3 as (arr & size & ajunk & EBS & Hlen & Hsz & AHDR & AARR). subst BS2. cbn [app] in HP3.
pose proof (rw_cells_bound segs mB r2 _ AHDR) as R2B. cbn [cells_size csize Nat.add] in R2B.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk_img S4L HIx _ _ _ _ r2 32 HP3 ltac:(left; reflexivity)) as Himg_r2. cbn [hl_img_lo hl_img_hi S4L] in Himg_r2.
pose proof (heap_blk_img S4L HIx _ _ _ _ arr (8 * size) HP3 ltac:(right; left; reflexivity)) as Himg_arr. cbn [hl_img_lo hl_img_hi S4L] in Himg_arr.
pose proof (heap_blk S4L HIx _ _ _ _ r2 32 HP3 ltac:(left; reflexivity)) as (_ & Hr2al & Hr2lo & Hr2hi & _).
pose proof (heap_blk S4L HIx _ _ _ _ arr (8 * size) HP3 ltac:(right; left; reflexivity)) as (_ & Haal & Halo & Hahi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hr2hi, Hahi.
assert (Hr2r : r2 <> r) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ 48 HP3 ltac:(right; left; reflexivity))).
assert (Harr : arr <> r).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP3) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. apply Hni'. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ r2 32 r 48 HP3 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) Hr2r) as Hdj1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ arr (8 * size) r 48 HP3 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) Harr) as Hdj2.
clear AHDR AARR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl segs mB) as WM.
reenter MOK3.
step. step. step. step. if_truex. do 4 step.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ => apply (K _ md3 mf r) end.
* unfold jo_post_frame. cbn [hl_segs hl_tp S4L].
split; [| split; [| split; [| split; [ | exists e3; exact ERR3]]]].
-- apply ret_statew_intro; [exact FS3 | exact FRM3].
-- eapply model_vm_only_trans; [exact VM2 | exact VM3].
-- release_frame FR ST3 (bv_unsigned sp). exact ST3.
-- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros b Hb; right; right; right; exact Hb | clia |]. solve_clientW S4L HIx HP3.
* right. split; [exact Hr|]. exists A3, [(r, 48); (r2, 32); (arr, 8 * size)]. split.
-- jhdr_split BLK.
cbn [jval]. exists 0, [], [(r, 48); (r2, 32); (arr, 8 * size)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists r2, [(r2, 32); (arr, 8 * size)], [], []. split; [reflexivity|]. split; [| split; [| split; [reflexivity | split; [reflexivity | exact I]]]].
++ unfold jhdr_cells. cbn [fn_arr_to_json_string S4F app]. exact BLK.
++ eapply (alist_agree segs S4F); [exact AL3 | | apply incl_refl].
eapply (agree_of_munch segs); [exact MU | exact WM |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia.
-- cbn [app]. eapply (heap_perm S4L HIx).
++ eapply (heap_frame S4L HIx); [ exact HP3 | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU). solve_frameW_with HP3.
++ perm.
Qed.
End JoNewArray.

End RC__1.

End G.
End Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3 Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn QKQo.
Import UPIU.Mq6.
Import U9Mh.Mq2.
Import UPIU.Mqd.
Import QSL3.
Import U9Mh.Mq4.
Import Qvbw.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.

Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition jonewobject_code (w_4 w_7 w_9 w_20 w_28 w_30 w_31 : Z) : list Z :=
[0xff010113; 0x00113423; 0x00813023; 0x03000513; w_4; 0x06050e63; 0x00100593; w_7; 0x02059593; w_9; 0x00458593; 0x00b53023; 0x00c53423; 0x00053823; 0x00053c23; 0x02053023; 0x00000597; 0x06058593; 0x00050413; 0x01000513; w_20; 0x00050593; 0x00040513; 0x02b43423; 0x02059863; 0x01053583; 0x00050413; 0x00058513; w_28; 0x00040513; w_30; w_31; 0x00050593; 0x00000513; 0x00c00613; 0x00c5a023; 0x00813083; 0x00013403; 0x01010113; 0x00008067]%Z.

Definition blk_194bc_code : list Z := [0x00020513; 0xf5c50513; 0x00008067]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_4 w_7 w_9 w_20 w_28 w_30 w_31 : Z).
Variables (hi_7 : bv 20).
Variables (lo_9 : bv 12).
Variables (joff_4 joff_20 joff_28 joff_30 joff_31 : bv 21).
Variables (GGOT4 GHASH4 GVDSO4 : Z).
Variables (e_pbfree e_lhnew e_194bc : Z).
Context {RC__ : Q6q3.RunConsts}.
Variables (e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC : Z) (gVOL gCS : Z -> Prop) (gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI : Z).
Hypothesis gH1 : forall a, gCS a -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH2 : gl_range_ok gIMG_LO gIMG_HI.
Hypothesis gH3 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH4 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> ~ gCS a.
Hypothesis gH5 : forall c a, In c [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))] -> (fst c <= a < fst c + Z.of_nat (length (snd c)))%Z ->
~ gCS a /\ ~ (gTP - 164 <= a < gTP - 160)%Z /\ (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis LAY_gIMG_LO : (gIMG_LO = 65536)%Z.
Hypothesis LAY_TPLO : gw_le gIMG_LO (gTP - 164).
Hypothesis LAY_TPHI : gw_le (gTP - 160) gIMG_HI.
#[using="gH2 gH3 LAY_gIMG_LO"] Lemma gLAYF : ((0 <= gIMG_LO /\ gIMG_HI <= alloc_ceiling) /\ (gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - gH2 gH3 LAY_gIMG_LO gTP gIMG_LO gIMG_HI. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.

Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Variables (JG_CGT_P gRDATA_LO : Z).
Let vdso_ok4 : Z -> Prop := fun vf => (vf = JG_CGT_P \/ vf = 0)%Z.
Hypothesis CODE : code_at segs base (jonewobject_code w_4 w_7 w_9 w_20 w_28 w_30 w_31).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 160.
Hypothesis D_4 : decode_any (Z_to_bv 32 w_4) = Some (Jal 1 joff_4, 4%Z).
Hypothesis E_4 : is_ecall (Z_to_bv 32 w_4) = false.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 12 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_9 : decode_any (Z_to_bv 32 w_9) = Some (OpImm ALU_ADD 12 12 lo_9, 4%Z).
Hypothesis E_9 : is_ecall (Z_to_bv 32 w_9) = false.
Hypothesis D_20 : decode_any (Z_to_bv 32 w_20) = Some (Jal 1 joff_20, 4%Z).
Hypothesis E_20 : is_ecall (Z_to_bv 32 w_20) = false.
Hypothesis D_28 : decode_any (Z_to_bv 32 w_28) = Some (Jal 1 joff_28, 4%Z).
Hypothesis E_28 : is_ecall (Z_to_bv 32 w_28) = false.
Hypothesis D_30 : decode_any (Z_to_bv 32 w_30) = Some (Jal 1 joff_30, 4%Z).
Hypothesis E_30 : is_ecall (Z_to_bv 32 w_30) = false.
Hypothesis D_31 : decode_any (Z_to_bv 32 w_31) = Some (Jal 1 joff_31, 4%Z).
Hypothesis E_31 : is_ecall (Z_to_bv 32 w_31) = false.
Hypothesis ANCH_9 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_9)%Z e_fn_obj_to_json_string.
Hypothesis LINK_4 : gw_anch (base + 16 + bv_signed joff_4)%Z e_malloc.
Hypothesis LINK_20 : gw_anch (base + 80 + bv_signed joff_20)%Z (e_lhnew + 0)%Z.
Hypothesis LINK_28 : gw_anch (base + 112 + bv_signed joff_28)%Z (e_pbfree + 0)%Z.
Hypothesis LINK_30 : gw_anch (base + 120 + bv_signed joff_30)%Z e_free.
Hypothesis LINK_31 : gw_anch (base + 124 + bv_signed joff_31)%Z (e_194bc + 0)%Z.
Hypothesis RNG_GGOT4 : gw_br GGOT4 8.
Hypothesis AL_GGOT4 : gw_al GGOT4 8.
Hypothesis RNG_GHASH4 : gw_br GHASH4 8.
Hypothesis AL_GHASH4 : gw_al GHASH4 8.
Hypothesis RNG_GVDSO4 : gw_br GVDSO4 8.
Hypothesis AL_GVDSO4 : gw_al GVDSO4 8.
Hypothesis LAY_GGOT4_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASH4_GVDSO4 : gw_le (GHASH4 + 8) GVDSO4.

Hypothesis printbuf_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@UPIU.Mqd.gw_all) (@UPIU.Mqd.printbuf_free_cps) e_pbfree)) in exact T).

Hypothesis lh_kchar_table_new_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@U9Mh.Mq4.gw_all) (@U9Mh.Mq4.lh_kchar_table_new_cps) e_lhnew)) in exact T).

Let e_blk_16e24 : Z := base.
Definition jo_post_frame := ltac:(let t := constr:(ltac:(gw_ctx2 (@U9Mh.Mq2.jo_post_frame))) in let t := eval cbv beta delta [U9Mh.Mq2.jo_post_frame] in t in let t := eval cbv delta [e_blk_16e24] in t in exact t).
Definition jo_new_container_stmt := ltac:(let t := constr:(ltac:(gw_ctx2 (@U9Mh.Mq2.jo_new_container_stmt))) in let t := eval cbv beta delta [U9Mh.Mq2.jo_new_container_stmt] in t in let t := eval cbv delta [e_blk_16e24] in t in let x := constr:(ltac:(gw_ctx2 (@U9Mh.Mq2.jo_post_frame))) in let t := gw_subst t x jo_post_frame in exact t).

Let S4L : heap_layout :=
{| hl_segs := segs;
hl_malloc := e_malloc; hl_free := e_free; hl_calloc := e_calloc; hl_realloc := e_realloc; hl_malloc2 := e_malloc2; hl_free2 := e_free2;
hl_tp := gTP;
hl_got_guard := gGOTG; hl_guard := gGUARD; hl_auxv := gAUXV; hl_libc := gLIBC; hl_volatile := gVOL;
hl_stack := 8256;
hl_client_static := gCS;
hl_scratch := fun a => (gTP - 164 <= a < gTP - 160)%Z;
hl_consts := [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))];
hl_img_lo := gIMG_LO; hl_img_hi := gIMG_HI;
hl_static_in_img := gH1; hl_img_range := gH2; hl_scratch_in_img := gH3; hl_scratch_not_static := gH4; hl_consts_ok := gH5 |}.
Let S4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
Hypothesis CS_GHASH4 : forall a, (GHASH4 <= a < GHASH4 + 12)%Z -> gCS a.
Hypothesis CS_GGOT4 : forall a, (GGOT4 <= a < GGOT4 + 8)%Z -> gCS a.
Hypothesis CS_GVDSO4 : forall a, (GVDSO4 <= a < GVDSO4 + 8)%Z -> gCS a.
Hypothesis LAY_RDATA_GGOT4 : gw_le gRDATA_LO GGOT4.
Hypothesis LAY_GHASH4x12_GVDSO4 : gw_le (GHASH4 + 12) GVDSO4.
Hypothesis LAY_IMG_GGOT4 : gw_le gIMG_LO GGOT4.
Hypothesis LAY_GVDSO4_IMG : gw_le (GVDSO4 + 8) gIMG_HI.
Hypothesis ANCH_R17 : gw_anch (0 + (base + 64) + 96)%Z e_fn_lh_entry_free.
Hypothesis CODE_e_194bc : code_at segs e_194bc blk_194bc_code.
Hypothesis AL_e_fn_obj_to_json_string : gw_b4 e_fn_obj_to_json_string.
Hypothesis RNG_e_fn_obj_to_json_string : gw_br e_fn_obj_to_json_string 4.
Hypothesis LAY_POS_e_fn_obj_to_json_string : gw_le 1 e_fn_obj_to_json_string.
Hypothesis LAY_HI_e_fn_obj_to_json_string : gw_le (e_fn_obj_to_json_string + 4) 1099511627776.
#[using="w_4 w_7 w_9 w_20 w_28 w_30 w_31 hi_7 lo_9 joff_4 joff_20 joff_28 joff_30 joff_31 GGOT4 GHASH4 GVDSO4 e_pbfree e_lhnew e_194bc RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free JG_CGT_P gRDATA_LO CODE BASE4 BASER D_4 E_4 D_7 E_7 D_9 E_9 D_20 E_20 D_28 E_28 D_30 E_30 D_31 E_31 ANCH_9 LINK_4 LINK_20 LINK_28 LINK_30 LINK_31 RNG_GGOT4 AL_GGOT4 RNG_GHASH4 AL_GHASH4 RNG_GVDSO4 AL_GVDSO4 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 printbuf_free_cps lh_kchar_table_new_cps CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG ANCH_R17 CODE_e_194bc AL_e_fn_obj_to_json_string RNG_e_fn_obj_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Ltac g_ra_even := lazymatch goal with |- (bv_unsigned (Z_to_bv 64 (?b + ?k)) mod 2 = 0)%Z =>
let X := fresh in let Y := fresh in pose proof BASE4 as X; pose proof BASER as Y; unfold gw_b4, gw_br in X, Y; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia end.
Ltac alloc_side ::=
try (progress fold S4L); try (progress fold S4F);
simpl hl_segs; simpl hl_stack; simpl hl_tp; simpl hl_malloc; simpl hl_free; simpl hl_calloc; simpl hl_realloc;
rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- forall _, _ => idtac
| |- _ \/ _ => idtac
| |- (bv_unsigned (Z_to_bv 64 (_ + _)) mod 2 = 0)%Z => first [ g_ra_even | lia ]
| |- _ =>
lazymatch goal with
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ _ _ => eassumption
| |- @eq (bv _) _ _ => first [ reflexivity | eassumption | symmetry; eassumption | apply bv_eq; rewrite ?unsigned_lit by lia; lia ]
| |- (_ mod 16 = 0)%Z =>
first [ assumption
| match goal with H : (bv_unsigned ?sp mod 16 = 0)%Z |- ((bv_unsigned ?sp + ?k) mod 16 = 0)%Z =>
rewrite <- Zplus_mod_idemp_l, H; reflexivity end
| lia ]
| |- _ => first [ lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia ]
end end.
Ltac gj_fold := try (progress fold S4L); repeat match goal with H : _ |- _ => progress fold S4L in H end; try (progress fold S4F); repeat match goal with H : _ |- _ => progress fold S4F in H end.
Ltac unfold_consts ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
Ltac clia ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
Ltac unfold_consts_goal ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size.
Ltac gj_fn_cbn := try (progress cbn [S4F fn_obj_to_json_string]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].
Definition jc_glob_P := ltac:(let p := constr:(ltac:(gw_ctx2 (@UPIU.Mq6.jc_glob_P))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@U9Mh.Mq2.jo_post_frame))) in let T := gw_subst T x jo_post_frame in let x := constr:(ltac:(gw_ctx2 (@U9Mh.Mq2.jo_new_container_stmt))) in let T := gw_subst T x jo_new_container_stmt in exact (p : T)).
Definition jc_glob_P_pres := ltac:(let p := constr:(ltac:(gw_ctx2 (@UPIU.Mq6.jc_glob_P_pres))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@U9Mh.Mq2.jo_post_frame))) in let T := gw_subst T x jo_post_frame in let x := constr:(ltac:(gw_ctx2 (@U9Mh.Mq2.jo_new_container_stmt))) in let T := gw_subst T x jo_new_container_stmt in exact (p : T)).
Definition jc_glob_P_munch := ltac:(let p := constr:(ltac:(gw_ctx2 (@UPIU.Mq6.jc_glob_P_munch))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@U9Mh.Mq2.jo_post_frame))) in let T := gw_subst T x jo_post_frame in let x := constr:(ltac:(gw_ctx2 (@U9Mh.Mq2.jo_new_container_stmt))) in let T := gw_subst T x jo_new_container_stmt in exact (p : T)).

Section RC__1.

Section JoNewObject.
Variable HIx : heap_iface S4L.
Notation lh_glob4 := (lh_glob segs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).

#[using="Type"] Lemma jc_glob_P_lh : forall m, jc_glob_P m -> lh_glob4 m.
Proof. clear - HIx. intros m G. exact G. Qed.

#[using="w_4 w_7 w_9 w_20 w_28 w_30 w_31 hi_7 lo_9 joff_4 joff_20 joff_28 joff_30 joff_31 e_pbfree e_lhnew e_194bc LAY_gIMG_LO LAY_TPLO LAY_TPHI JG_CGT_P gRDATA_LO CODE BASE4 BASER D_4 E_4 D_7 E_7 D_9 E_9 D_20 E_20 D_28 E_28 D_30 E_30 D_31 E_31 ANCH_9 LINK_4 LINK_20 LINK_28 LINK_30 LINK_31 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 printbuf_free_cps lh_kchar_table_new_cps CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG ANCH_R17 CODE_e_194bc LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string"] Lemma json_object_new_object_cps : (jo_new_container_stmt S4L HIx S4F jc_glob_P (base + 0x0) (48 + 48 + 8256) (Sobj [])).
Proof. clear - w_4 w_7 w_9 w_20 w_28 w_30 w_31 hi_7 lo_9 joff_4 joff_20 joff_28 joff_30 joff_31 e_pbfree e_lhnew e_194bc LAY_gIMG_LO LAY_TPLO LAY_TPHI JG_CGT_P gRDATA_LO CODE BASE4 BASER D_4 E_4 D_7 E_7 D_9 E_9 D_20 E_20 D_28 E_28 D_30 E_30 D_31 E_31 ANCH_9 LINK_4 LINK_20 LINK_28 LINK_30 LINK_31 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 printbuf_free_cps lh_kchar_table_new_cps CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG ANCH_R17 CODE_e_194bc LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string base S4F HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_RDATA_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GHASH4x12_GVDSO4 as gL5_; unfold gw_le in gL5_. pose proof LAY_IMG_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GVDSO4_IMG as gL7_; unfold gw_le in gL7_. pose proof LAY_POS_e_fn_obj_to_json_string as gL8_; unfold gw_le in gL8_. pose proof LAY_HI_e_fn_obj_to_json_string as gL9_; unfold gw_le in gL9_.
unfold jo_new_container_stmt. intros until errv. intros PRE G K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA). cbn [hl_segs hl_tp S4L] in *.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
assert (Gk : True -> jc_glob_P m) by (intros _; exact G). clear G.
apply rz_evt; [exact MOK|]. subst tp.
carve_frame 16%nat ST.
do 5 step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 mA md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
pose proof (jc_glob_P_pres _ _ _ _ HPR (Gk I)) as G2. clear Gk.
clear MU WM MI ST.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] mA) as MU.
pose proof (wmono_refl segs mA) as WM.
reenter MOK2.
step. if_truex. do 4 step.
apply evt_RZ_done. apply (K _ md2 mA 0).
+ unfold jo_post_frame. cbn [hl_segs hl_tp S4L].
split; [apply ret_statew_same|]. split; [exact VM2|]. split; [|split; [exact HPR | exists e2; exact ERR2]].
release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ left. split; [reflexivity|]. exists A2. exact HP2.
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] mA) as MU.
pose proof (wmono_refl segs mA) as WM.
stash G2.
reenter MOK2.
step. if_falsex.
do 5 step. stepz. stepz. stepz. stepz. stepz.
do 4 step. step.
unstash G2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (G3 : jc_glob_P mx) by
(eapply jc_glob_P_munch; [exact G2 | exact MU | exact WM |];
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia) end.
apply evt_RZ_done.
eapply (lh_kchar_table_new_cps HIx) with (LB := (r, 48) :: LB) (lo := lo);
[ heap_now S4L HIx HP2 MU WM MI | exact G3 | .. ]; try alloc_side.
intros ms3 md3 (mB & A3 & r2 & e3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & G4 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR3 by lia.
extend_pres S4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
clear MU WM MI G2 G3.
destruct OUT3 as [(-> & HP3) | (Hr2 & BS2 & TAB & HP3)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl segs mB) as WM.
reenter MOK3.
step. step. stepz. step. if_false. step. step. step. step.

apply evt_RZ_done.
eapply (printbuf_free_cps HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md3 T A3 ((r, 48) :: LB) [] 0 lo e3);
[ cbn [app]; heap_now S4L HIx HP3 MU WM MI | left; split; reflexivity | .. ]; try alloc_side.
intros ms5 md5 (mC & A5 & r5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & HP5).
destruct RS5 as (x0 & x1' & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & F5 & fc5 & -> & FS5 & FRM5).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR5 by lia.
extend_pres S4L HIx HPR MU WM HP3 HPR5.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] mC) as MU. pose proof (wmono_refl segs mC) as WM.
reenter MOK5.
step. step.

alloc_call (hi_free S4L HIx) S4L HIx HP5 MU WM MI.
{ right. exists 48. left. reflexivity. }
intros ms6 mD md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6. open_ret RS6. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR6, HP6.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST6 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR6 by lia.
extend_pres S4L HIx HPR MU WM HP5 HPR6.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI.
pose proof (heap_model_ok _ _ _ _ _ _ HP6) as MOK6.
pose proof (heap_mem_inv _ _ _ _ _ _ HP6) as MI. cbn [hl_segs S4L] in MI.
change (gTP - 164) with (gTP + -164) in ERR6.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); ((gTP + -164), (gTP + -160))] mD) as MU. pose proof (wmono_refl segs mD) as WM.
reenter MOK6.
do 4 step. step. step. step. stepz.
do 4 step.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ => apply (K _ md6 mf 0) end.
* unfold jo_post_frame. cbn [hl_segs hl_tp S4L].
split; [| split; [| split; [| split; [ | eexists; eassumption]]]].
-- apply ret_statew_intro; [eapply fsaved_trans; [exact FS3 | exact FS5] | intros Hf; apply FRM5; apply FRM3; exact Hf].
-- eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3|]. eapply model_vm_only_trans; [exact VM5 | exact VM6].
-- release_frame FR ST6 (bv_unsigned sp). exact ST6.
-- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP6 | intros bb Hbb; exact Hbb | clia |]. solve_clientW S4L HIx HP6.
* left. split; [reflexivity|]. exists A6.
eapply (heap_frame S4L HIx); [exact HP6 | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP6 MU). solve_frameW_with HP6.
+
pose proof TAB as (tbl & size & es & svs & Hkvs & EBS2 & OPEN).
destruct es as [|e0 es']; [| cbn in Hkvs; discriminate]. subst BS2. unfold lh_blocks in HP3. cbn [map app] in HP3.
pose proof (proj1 OPEN) as THDR. unfold lh_hdrf in THDR.
pose proof (rw_cells_bound segs mB r2 _ THDR) as R2B. cbn [cells_size csize Nat.add] in R2B. clear THDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk_img S4L HIx _ _ _ _ r2 56 HP3 ltac:(left; reflexivity)) as Himg_r2. cbn [hl_img_lo hl_img_hi S4L] in Himg_r2.
pose proof (heap_blk_img S4L HIx _ _ _ _ tbl (40 * size) HP3 ltac:(right; left; reflexivity)) as Himg_tbl. cbn [hl_img_lo hl_img_hi S4L] in Himg_tbl.
pose proof (heap_blk S4L HIx _ _ _ _ r2 56 HP3 ltac:(left; reflexivity)) as (_ & Hr2al & Hr2lo & Hr2hi & _).
pose proof (heap_blk S4L HIx _ _ _ _ tbl (40 * size) HP3 ltac:(right; left; reflexivity)) as (_ & Htal & Htlo & Hthi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hr2hi, Hthi.
assert (Hr2r : r2 <> r) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ 48 HP3 ltac:(right; left; reflexivity))).
assert (Htbr : tbl <> r).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP3) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. apply Hni'. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ r2 56 r 48 HP3 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) Hr2r) as Hdj1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tbl (40 * size) r 48 HP3 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) Htbr) as Hdj2.
stash TAB. clear OPEN.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl segs mB) as WM.
reenter MOK3.
step. step. step. step. if_truex. do 4 step.
unstash TAB.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ => apply (K _ md3 mf r) end.
* unfold jo_post_frame. cbn [hl_segs hl_tp S4L].
split; [| split; [| split; [| split; [ | exists e3; exact ERR3]]]].
-- apply ret_statew_intro; [exact FS3 | exact FRM3].
-- eapply model_vm_only_trans; [exact VM2 | exact VM3].
-- release_frame FR ST3 (bv_unsigned sp). exact ST3.
-- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros b Hb; right; right; right; exact Hb | clia |]. solve_clientW S4L HIx HP3.
* right. split; [exact Hr|]. exists A3, [(r, 48); (r2, 56); (tbl, 40 * size)]. split.
-- jhdr_split BLK.
eapply (sobj_close segs S4F) with (TBS := [(r2, 56); (tbl, 40 * size)]) (KBS := []) (PBS := []) (pb := 0) (kvs := []) (t := r2); try reflexivity.
++ left. split; reflexivity.
++ unfold jhdr_cells. cbn [fn_obj_to_json_string S4F app]. exact BLK.
++ eapply (lhtab2_agree segs S4F); [exact TAB | | apply incl_refl].
eapply (agree_of_munch segs); [exact MU | exact WM |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia.
-- cbn [app]. eapply (heap_perm S4L HIx).
++ eapply (heap_frame S4L HIx); [ exact HP3 | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU). solve_frameW_with HP3.
++ perm.
Qed.
End JoNewObject.

End RC__1.

End G.
End Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn Q8tj.
Import QSL3.
Import U9Mh.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Definition lhfree_code (w_15 w_21 : Z) : list Z :=
[0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00050413; 0x02053503; 0x02050063; 0x00843483; 0x00048c63; 0x02043583; 0x00048513; 0x000580e7; 0x0184b483; 0xfe0498e3; 0x01843503; w_15; 0x00040513; 0x01813083; 0x01013403; 0x00813483; 0x02010113; w_21]%Z.

Definition blk_16ec4_code (wb16ec4_11 wb16ec4_13 : Z) : list Z :=
[0xff010113; 0x00113423; 0x00813023; 0x00852583; 0x01053403; 0x00058e63; 0x02040263; 0x00040513; 0x00813083; 0x00013403; 0x01010113; wb16ec4_11; 0x00053503; wb16ec4_13; 0xfe0412e3; 0x00813083; 0x00013403; 0x01010113; 0x00008067]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_2 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_4 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_15 w_21 : Z).
Variables (joff_15 joff_21 : bv 21).
Context {RC__ : Q6q3.RunConsts}.
Variables (e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC : Z) (gVOL gCS : Z -> Prop) (gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI : Z).
Hypothesis gH1 : forall a, gCS a -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH2 : gl_range_ok gIMG_LO gIMG_HI.
Hypothesis gH3 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH4 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> ~ gCS a.
Hypothesis gH5 : forall c a, In c [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))] -> (fst c <= a < fst c + Z.of_nat (length (snd c)))%Z ->
~ gCS a /\ ~ (gTP - 164 <= a < gTP - 160)%Z /\ (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis LAY_gIMG_LO : (gIMG_LO = 65536)%Z.
Hypothesis LAY_TPLO : gw_le gIMG_LO (gTP - 164).
Hypothesis LAY_TPHI : gw_le (gTP - 160) gIMG_HI.
#[using="gH2 gH3 LAY_gIMG_LO"] Lemma gLAYF : ((0 <= gIMG_LO /\ gIMG_HI <= alloc_ceiling) /\ (gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - gH2 gH3 LAY_gIMG_LO gTP gIMG_LO gIMG_HI. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.

Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Hypothesis CODE : code_at segs base (lhfree_code w_15 w_21).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 88.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Jal 1 joff_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Jal 0 joff_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis LINK_15 : gw_anch (base + 60 + bv_signed joff_15)%Z e_free.
Hypothesis LINK_21 : gw_anch (base + 84 + bv_signed joff_21)%Z e_free.
Variable e_16158 : Z.
Variable wb16ec4_11 : Z.  Variable joffb16ec4_11 : bv 21.
Hypothesis D_b16ec4_11 : decode_any (Z_to_bv 32 wb16ec4_11) = Some (Jal 0 joffb16ec4_11, 4%Z).
Hypothesis E_b16ec4_11 : is_ecall (Z_to_bv 32 wb16ec4_11) = false.
Hypothesis LINK_b16ec4_11 : gw_anch (e_fn_lh_entry_free + 44 + bv_signed joffb16ec4_11)%Z (e_16158 + 0)%Z.
Variable wb16ec4_13 : Z.  Variable joffb16ec4_13 : bv 21.
Hypothesis D_b16ec4_13 : decode_any (Z_to_bv 32 wb16ec4_13) = Some (Jal 1 joffb16ec4_13, 4%Z).
Hypothesis E_b16ec4_13 : is_ecall (Z_to_bv 32 wb16ec4_13) = false.
Hypothesis LINK_b16ec4_13 : gw_anch (e_fn_lh_entry_free + 52 + bv_signed joffb16ec4_13)%Z e_free.
Hypothesis CODE_e_blk_16ec4 : code_at segs e_fn_lh_entry_free (blk_16ec4_code wb16ec4_11 wb16ec4_13).
Hypothesis AL_e_blk_16ec4_b4 : gw_b4 e_fn_lh_entry_free.
Hypothesis RNG_e_blk_16ec4_code : gw_br e_fn_lh_entry_free 76.

Let S4L : heap_layout :=
{| hl_segs := segs;
hl_malloc := e_malloc; hl_free := e_free; hl_calloc := e_calloc; hl_realloc := e_realloc; hl_malloc2 := e_malloc2; hl_free2 := e_free2;
hl_tp := gTP;
hl_got_guard := gGOTG; hl_guard := gGUARD; hl_auxv := gAUXV; hl_libc := gLIBC; hl_volatile := gVOL;
hl_stack := 8256;
hl_client_static := gCS;
hl_scratch := fun a => (gTP - 164 <= a < gTP - 160)%Z;
hl_consts := [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))];
hl_img_lo := gIMG_LO; hl_img_hi := gIMG_HI;
hl_static_in_img := gH1; hl_img_range := gH2; hl_scratch_in_img := gH3; hl_scratch_not_static := gH4; hl_consts_ok := gH5 |}.
Let S4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
Hypothesis LAY_POS_e_fn_lh_entry_free : gw_le 1 e_fn_lh_entry_free.
Hypothesis LAY_HI_e_fn_lh_entry_free : gw_le (e_fn_lh_entry_free + 4) 1099511627776.
Hypothesis AL_e_fn_lh_char_equal : gw_b4 e_fn_lh_char_equal.
Hypothesis RNG_e_fn_lh_char_equal : gw_br e_fn_lh_char_equal 4.
Hypothesis LAY_POS_e_fn_lh_char_equal : gw_le 1 e_fn_lh_char_equal.
Hypothesis LAY_HI_e_fn_lh_char_equal : gw_le (e_fn_lh_char_equal + 4) 1099511627776.
Hypothesis AL_e_fn_lh_char_hash : gw_b4 e_fn_lh_char_hash.
Hypothesis RNG_e_fn_lh_char_hash : gw_br e_fn_lh_char_hash 4.
Hypothesis LAY_POS_e_fn_lh_char_hash : gw_le 1 e_fn_lh_char_hash.
Hypothesis LAY_HI_e_fn_lh_char_hash : gw_le (e_fn_lh_char_hash + 4) 1099511627776.
#[using="w_15 w_21 joff_15 joff_21 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_15 E_15 D_21 E_21 LINK_15 LINK_21 e_16158 wb16ec4_11 joffb16ec4_11 D_b16ec4_11 E_b16ec4_11 LINK_b16ec4_11 wb16ec4_13 joffb16ec4_13 D_b16ec4_13 E_b16ec4_13 LINK_b16ec4_13 CODE_e_blk_16ec4 AL_e_blk_16ec4_b4 RNG_e_blk_16ec4_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal AL_e_fn_lh_char_hash RNG_e_fn_lh_char_hash LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Ltac g_ra_even := lazymatch goal with |- (bv_unsigned (Z_to_bv 64 (?b + ?k)) mod 2 = 0)%Z =>
let X := fresh in let Y := fresh in pose proof BASE4 as X; pose proof BASER as Y; unfold gw_b4, gw_br in X, Y; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia end.
Ltac alloc_side ::=
try (progress fold S4L); try (progress fold S4F);
simpl hl_segs; simpl hl_stack; simpl hl_tp; simpl hl_malloc; simpl hl_free; simpl hl_calloc; simpl hl_realloc;
rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- forall _, _ => idtac
| |- _ \/ _ => idtac
| |- (bv_unsigned (Z_to_bv 64 (_ + _)) mod 2 = 0)%Z => first [ g_ra_even | lia ]
| |- _ =>
lazymatch goal with
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ _ _ => eassumption
| |- @eq (bv _) _ _ => first [ reflexivity | eassumption | symmetry; eassumption | apply bv_eq; rewrite ?unsigned_lit by lia; lia ]
| |- (_ mod 16 = 0)%Z =>
first [ assumption
| match goal with H : (bv_unsigned ?sp mod 16 = 0)%Z |- ((bv_unsigned ?sp + ?k) mod 16 = 0)%Z =>
rewrite <- Zplus_mod_idemp_l, H; reflexivity end
| lia ]
| |- _ => first [ lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia ]
end end.
Ltac gj_fold := try (progress fold S4L); repeat match goal with H : _ |- _ => progress fold S4L in H end; try (progress fold S4F); repeat match goal with H : _ |- _ => progress fold S4F in H end.
Ltac unfold_consts ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
Ltac clia ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
Ltac unfold_consts_goal ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size.
Ltac gj_fn_cbn := try (progress cbn [S4F fn_lh_char_equal fn_lh_char_hash fn_lh_entry_free]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section RC__1.

Section LhFree.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition lh_entry_free_entry : Z := (e_fn_lh_entry_free + 0x0).
Definition lh_table_free_entry : Z := (base + 0x0).

Definition lh_entry_free_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : word),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv] /\
HEAPx A' LB m' md'.

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_char_hash e_fn_lh_char_equal wb16ec4_11 wb16ec4_13 D_b16ec4_13 E_b16ec4_13 LINK_b16ec4_13 CODE_e_blk_16ec4 AL_e_blk_16ec4_b4 RNG_e_blk_16ec4_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash joffb16ec4_13"] Lemma lh_entry_free_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (p k kn pad nx pv lo : Z) (errv : word),
HEAPx A ((k, kn) :: LB) m md ->
rw_cells segs m p [C8 (Z_to_bv 64 k); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 pad); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 pv)] ->
p + 40 <= alloc_ceiling -> (p + 40 <= 0x10000 \/ gIMG_HI <= p) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 p ->
(forall ms' md', lh_entry_free_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo errv ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_entry_free_entry) fc None m (seg_rom segs)) md) T.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_char_hash e_fn_lh_char_equal wb16ec4_11 wb16ec4_13 D_b16ec4_13 E_b16ec4_13 LINK_b16ec4_13 CODE_e_blk_16ec4 AL_e_blk_16ec4_b4 RNG_e_blk_16ec4_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash joffb16ec4_13 segs gTP gIMG_HI HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_entry_free as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_equal as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_equal as gL5_; unfold gw_le in gL5_. pose proof LAY_POS_e_fn_lh_char_hash as gL6_; unfold gw_le in gL6_. pose proof LAY_HI_e_fn_lh_char_hash as gL7_; unfold gw_le in gL7_.
intros until errv. intros HP ENT Php Pimg ST LO LOS SPA HT ERR TP RA A0 K.
unfold_consts. word_range sp SPR.
pose proof (rw_cells_bound segs m p _ ENT) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. unfold lh_entry_free_entry. subst a0.
carve_frame 16%nat ST.
do 3 step.
step. norm_sx32. step. step. if_true.
step. step.

alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ right. exists kn. left. reflexivity. }
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR2, HP2.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST ENT.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_false. do 4 step.
apply evt_RZ_done. apply K. unfold lh_entry_free_post.
exists m2, A2. eexists.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | exact HP2]]]]].
- unfold ret_state. cbn [hl_segs S4L]. repeat eexists; reflexivity.
- release_frame FR ST2 (bv_unsigned sp). exact ST2.
Qed.

Variables (sp gp : word) (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo t tbl size : Z) (es : list lent) (svs : list slotv) (T : TSet).
Variables (s0c s1c rac : word).

Definition free_frame (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells segs m (bv_unsigned sp + -32) [CB 8 junk8; C8 s1c; C8 s0c; C8 rac].

Definition free_exit (errv : word) (K0 : machine_state -> Model -> Prop) : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (md : Model) (A : AS S4L HIx) (junk8 : list byte)
(hsz hcnt hhd htl : Z),
HEAPx A ((t, 56) :: (tbl, 40 * size) :: LB) m md ->
rw_cells segs m t [C4 (Z_to_bv 64 hsz); C4 (Z_to_bv 64 hcnt); C8 (Z_to_bv 64 hhd); C8 (Z_to_bv 64 htl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 (fn_lh_entry_free S4F)); C8 (Z_to_bv 64 (fn_lh_char_hash S4F)); C8 (Z_to_bv 64 (fn_lh_char_equal S4F))] ->
stk segs m lo (bv_unsigned sp + -32) ->
free_frame m junk8 ->
rw_cells segs m (gTP - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
K0 (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x38)) fc None m (seg_rom segs)) md.

#[using="Type"] Lemma ent_addr_pos : forall i, 0 < tbl -> 0 < ent_addr tbl i.
Proof. clear - HIx sp gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo t tbl size es svs T s0c s1c rac. intros. unfold ent_addr. lia. Qed.

#[using="w_15 w_21 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER wb16ec4_11 wb16ec4_13 D_b16ec4_13 E_b16ec4_13 LINK_b16ec4_13 CODE_e_blk_16ec4 AL_e_blk_16ec4_b4 RNG_e_blk_16ec4_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash joffb16ec4_13"] Lemma lh_free_loop :
forall (k j : nat) (e : lent) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (errv : word) (junk8 : list byte) (hsz hcnt hhd htl : Z),
(k = length es - S j)%nat -> nth_error es j = Some e ->
HEAPx A (map kblk (skipn j es) ++ (t, 56) :: (tbl, 40 * size) :: LB) m md ->
lh_slots segs m tbl svs -> lh_link tbl es svs -> Z.of_nat (length svs) = size ->
(forall e, In e es -> le_v e = 0) ->
rw_cells segs m t [C4 (Z_to_bv 64 hsz); C4 (Z_to_bv 64 hcnt); C8 (Z_to_bv 64 hhd); C8 (Z_to_bv 64 htl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 (fn_lh_entry_free S4F)); C8 (Z_to_bv 64 (fn_lh_char_hash S4F)); C8 (Z_to_bv 64 (fn_lh_char_equal S4F))] ->
stk segs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
free_frame m junk8 ->
rw_cells segs m (gTP - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
free_exit errv (fun ms md => realizes segs (mkCfg ms md) T) ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 (ent_addr tbl (le_ix e))) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x24)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_15 w_21 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER wb16ec4_11 wb16ec4_13 D_b16ec4_13 E_b16ec4_13 LINK_b16ec4_13 CODE_e_blk_16ec4 AL_e_blk_16ec4_b4 RNG_e_blk_16ec4_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash joffb16ec4_13 segs base gTP S4F HIx sp gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo t tbl size es svs T s0c s1c rac. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_entry_free as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_equal as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_equal as gL5_; unfold gw_le in gL5_. pose proof LAY_POS_e_fn_lh_char_hash as gL6_; unfold gw_le in gL6_. pose proof LAY_HI_e_fn_lh_char_hash as gL7_; unfold gw_le in gL7_.
induction k as [|k IH]; intros until htl; intros Hk Hj HP SL LINK Hlen VZ HDR ST LO LOS SPA HT FR ERR VM0 HPR KX.
-
pose proof (proj1 (nth_error_Some es j) ltac:(rewrite Hj; discriminate)) as Hjlt.
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (LK1 j e Hj) as (sv & Esv & Ek & Ekc & Ev & Enx & Epv).
pose proof (SL (le_ix e) sv Esv) as C. unfold slot_cells in C. rewrite Ek, Ekc, Ev, Enx, Epv in C.
rewrite (VZ e (nth_error_In _ _ Hj)) in C.
assert (NX : nx_of tbl es j = 0).
{ unfold nx_of. destruct (nth_error es (S j)) eqn:E2; [|reflexivity].
pose proof (proj1 (nth_error_Some es (S j)) ltac:(rewrite E2; discriminate)). lia. }
rewrite NX in C.
unfold free_frame in FR. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
replace (skipn j es) with [e] in HP.
2:{ symmetry. rewrite <- (firstn_skipn j es) in Hj. rewrite nth_error_app2 in Hj by (rewrite length_firstn; lia).
rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hj by lia.
destruct (skipn j es) as [|e' tl] eqn:ES; [discriminate|]. cbn in Hj. injection Hj as ->.
apply (f_equal (@length lent)) in ES. rewrite length_skipn in ES. cbn in ES. destruct tl; [reflexivity | cbn in ES; lia]. }
cbn [map app kblk] in HP.
pose proof (heap_blk S4L HIx _ _ _ _ t 56 HP ltac:(right; left; reflexivity)) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ tbl (40 * size) HP ltac:(right; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tbl (40 * size) HP ltac:(right; right; left; reflexivity)) as Hbimg. cbn [hl_img_lo hl_img_hi S4L] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi.
pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Esv; discriminate)) as Hix.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|].
step. step. step.

cbn [fn_lh_entry_free S4F]. gw_ret_pc_var_tac.
apply evt_RZ_done.
eapply (lh_entry_free_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md T A ((t, 56) :: (tbl, 40 * size) :: LB)
(ent_addr tbl (le_ix e)) (le_k e) (le_kn e) (sv_pad sv) 0 (pv_of tbl es j) lo errv);
[ heap_now S4L HIx HP MU WM MI | ..]; try alloc_side.
{ unfold ent_addr in *. clia. }
{ unfold ent_addr in *. destruct Hbimg; [left; nia | right; lia]. }
intros ms2 md2 (m2 & A2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->). cbn [hl_segs S4L] in *.
rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2 by lia. rewrite (unsigned_lit (bv_unsigned sp + -32)) in HPR2 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in C; [| eapply client_range_block; [right; left; reflexivity | unfold ent_addr; lia | cbn; unfold ent_addr; nia]]. cbn [hl_segs S4L] in C.
assert (HPR' : heap_pres S4L LB (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; right; right; exact Hb]. }
clear MU WM MI ST.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. step. if_false.
apply evt_RZ_done. eapply KX; [exact HP2 | exact HDR | exact ST2 | exact FR | exact ERR2 | eapply model_vm_only_trans; eassumption | exact HPR'].
-
pose proof (proj1 (nth_error_Some es j) ltac:(rewrite Hj; discriminate)) as Hjlt.
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (LK1 j e Hj) as (sv & Esv & Ek & Ekc & Ev & Enx & Epv).
pose proof (SL (le_ix e) sv Esv) as C. unfold slot_cells in C. rewrite Ek, Ekc, Ev, Enx, Epv in C.
rewrite (VZ e (nth_error_In _ _ Hj)) in C.
destruct (nth_error es (S j)) as [e'|] eqn:E2.
2:{ exfalso. apply nth_error_None in E2. lia. }
assert (NX : nx_of tbl es j = ent_addr tbl (le_ix e')) by (unfold nx_of; rewrite E2; reflexivity).
rewrite NX in C.
destruct (LK1 (S j) e' E2) as (sv' & Esv' & _). pose proof (proj1 (nth_error_Some svs (le_ix e')) ltac:(rewrite Esv'; discriminate)) as Hix'.
unfold free_frame in FR. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
assert (SK : skipn j es = e :: skipn (S j) es).
{ rewrite <- (firstn_skipn j es) in Hj. rewrite nth_error_app2 in Hj by (rewrite length_firstn; lia).
rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hj by lia.
remember (skipn j es) as sk eqn:ES. destruct sk as [|e0 tl]; [discriminate|]. cbn in Hj. injection Hj as ->.
f_equal. change tl with (skipn 1 (e :: tl)). rewrite ES, skipn_skipn. reflexivity. }
rewrite SK in HP. cbn [map app] in HP. unfold kblk at 1 in HP.
pose proof (heap_blk S4L HIx _ _ _ _ t 56 HP ltac:(right; apply in_or_app; right; left; reflexivity)) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ tbl (40 * size) HP ltac:(right; apply in_or_app; right; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tbl (40 * size) HP ltac:(right; apply in_or_app; right; right; left; reflexivity)) as Hbimg. cbn [hl_img_lo hl_img_hi S4L] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi.
pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Esv; discriminate)) as Hix.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|].
step. step. step.

cbn [fn_lh_entry_free S4F]. gw_ret_pc_var_tac.
apply evt_RZ_done.
eapply (lh_entry_free_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md T A (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB)
(ent_addr tbl (le_ix e)) (le_k e) (le_kn e) (sv_pad sv) (ent_addr tbl (le_ix e')) (pv_of tbl es j) lo errv);
[ heap_now S4L HIx HP MU WM MI | ..]; try alloc_side.
{ unfold ent_addr in *. clia. }
{ unfold ent_addr in *. destruct Hbimg; [left; nia | right; lia]. }
intros ms2 md2 (m2 & A2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->). cbn [hl_segs S4L] in *.
rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2 by lia. rewrite (unsigned_lit (bv_unsigned sp + -32)) in HPR2 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [apply in_or_app; right; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in C; [| eapply client_range_block; [apply in_or_app; right; right; left; reflexivity | unfold ent_addr; lia | cbn; unfold ent_addr; nia]]. cbn [hl_segs S4L] in C.
assert (HPR' : heap_pres S4L LB (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; apply in_or_app; right; right; right; exact Hb]. }
clear MU WM MI ST.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. step. unfold ent_addr. if_truex.
apply evt_RZ_done.
eapply (IH (S j) e'); first [exact E2 | exact HP2 | exact HDR | exact ST2 | exact FR | exact ERR2 | exact HPR' | exact KX | idtac].
+ lia.
+ eapply (lh_slots_pres S4L); [exact HPR2 | apply in_or_app; right; right; left; reflexivity | exact Hlen | exact SL].
+ split; [exact LK1 | split; [exact LK2 | split; [exact LK3 | exact LK4]]].
+ exact Hlen.
+ exact VZ.
+ clia.
+ lia.
+ exact SPA.
+ exact HT.
+ eapply model_vm_only_trans; eassumption.
Qed.

Definition lh_table_free_post (errv : word) (ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : word),
ret_statew S4L rac sp gp (Z_to_bv 64 gTP) s0c s1c s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md0 md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m0 m' /\
rw_cells segs m' (gTP - 164) [C4 errv] /\
HEAPx A' LB m' md'.

#[using="w_15 w_21 joff_15 joff_21 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_15 E_15 D_21 E_21 LINK_15 LINK_21 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash"] Lemma lh_free_exit_ok : forall errv,
alloc_ceiling <= lo -> lo <= bv_unsigned sp + -32 - 16 - 8256 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
bv_unsigned rac mod 2 = 0 -> 0 <= size ->
(forall ms' md', lh_table_free_post errv ms' md' -> realizes segs (mkCfg ms' md') T) ->
free_exit errv (fun ms md => realizes segs (mkCfg ms md) T).
Proof. clear - w_15 w_21 joff_15 joff_21 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_15 E_15 D_21 E_21 LINK_15 LINK_21 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash segs HIx sp gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo t tbl size es svs T s0c s1c rac. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_entry_free as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_equal as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_equal as gL5_; unfold gw_le in gL5_. pose proof LAY_POS_e_fn_lh_char_hash as gL6_; unfold gw_le in gL6_. pose proof LAY_HI_e_fn_lh_char_hash as gL7_; unfold gw_le in gL7_.
intros errv LO LOS SPA HT RA Hsz K. unfold free_exit. intros until htl. intros HP HDR ST FR ERR VM0 HPR.
unfold free_frame in FR. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (blocks2 S4L HIx _ _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
cbn [hl_img_lo hl_img_hi S4L] in Himg, Himg2. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hne.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|].
step. step.

alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ right. exists (40 * size). right; left. reflexivity. }
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite lb_remove_other in HPR2, HP2 by (cbn; lia). rewrite lb_remove_head in HPR2, HP2.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST HDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
do 5 step.
release_frame FR ST2 (bv_unsigned sp).
step.

alloc_call (hi_free S4L HIx) S4L HIx HP2 MU WM MI.
{ right. exists 56. left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HP3, HPR3.
extend_pres S4L HIx HPR MU WM HP2 HPR3.
apply K. unfold lh_table_free_post.
exists m3, A3, r3.
split; [| split; [| split; [exact ST3 | split; [exact HPR | split; [exact ERR3 | exact HP3]]]]].
+ apply ret_statew_same.
+ eapply model_vm_only_trans; [| exact VM3]. eapply model_vm_only_trans; eassumption.
Qed.

#[using="w_15 w_21 joff_15 joff_21 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_15 E_15 D_21 E_21 LINK_15 LINK_21 wb16ec4_11 wb16ec4_13 D_b16ec4_13 E_b16ec4_13 LINK_b16ec4_13 CODE_e_blk_16ec4 AL_e_blk_16ec4_b4 RNG_e_blk_16ec4_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash joffb16ec4_13"] Lemma lh_table_free_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : AS S4L HIx) (kvs : list (Z * Z)) (errv : word),
HEAPx A (lh_blocks t tbl size es ++ LB) m0 md0 ->
lh_open segs S4F m0 t tbl size es svs ->
(forall e, In e es -> le_v e = 0) ->
stk segs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m0 (gTP - 164) [C4 errv] ->
bv_unsigned rac mod 2 = 0 ->
a0 = Z_to_bv 64 t ->
(forall ms' md', lh_table_free_post errv ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR rac sp gp (Z_to_bv 64 gTP) t0 t1 t2 s0c s1c a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_table_free_entry) fc None m0 (seg_rom segs)) md0) T.
Proof. clear - w_15 w_21 joff_15 joff_21 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_15 E_15 D_21 E_21 LINK_15 LINK_21 wb16ec4_11 wb16ec4_13 D_b16ec4_13 E_b16ec4_13 LINK_b16ec4_13 CODE_e_blk_16ec4 AL_e_blk_16ec4_b4 RNG_e_blk_16ec4_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash joffb16ec4_13 segs gTP S4F HIx sp gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo t tbl size es svs T s0c s1c rac. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_entry_free as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_equal as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_equal as gL5_; unfold gw_le in gL5_. pose proof LAY_POS_e_fn_lh_char_hash as gL6_; unfold gw_le in gL6_. pose proof LAY_HI_e_fn_lh_char_hash as gL7_; unfold gw_le in gL7_.
intros until errv. intros HP OPEN VZ ST LO LOS SPA HT ERR RA A0 K.
destruct OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. unfold lh_blocks in HP. cbn [app] in HP.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (blocks2 S4L HIx _ _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
cbn [hl_img_lo hl_img_hi S4L] in Himg, Himg2. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl segs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m0) as MU.
apply rz_evt; [exact MOK|]. unfold lh_table_free_entry. subst a0.
carve_frame 32%nat ST.
do 4 step. step. step. cbn [fn_lh_entry_free S4F]. step. if_false.
step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPx A ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) m1 md0).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP. }
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m0 m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; right; right; apply in_or_app; right; exact Hb | clia |].
solve_clientW S4L HIx HP. }
pose proof (lh_free_exit_ok errv ltac:(clia) ltac:(lia) SPA HT RA ltac:(lia) K) as EXIT.
assert (SL1 : lh_slots segs m1 tbl svs).
{ eapply (lh_slots_frame segs m0 m1 tbl svs _ SL MU WM). intros i Hi. apply Forall_cons; [|apply Forall_nil].
cbn. unfold ent_addr. left. lia. }
rewrite hd_of_nth in *.
destruct (nth_error es 0) as [e0|] eqn:E0.
2:{
step. if_true.
apply evt_RZ_done.
assert (ES : es = []) by (destruct es; [reflexivity | discriminate]). rewrite ES in HP1. cbn [map app] in HP1.
eapply EXIT; [exact HP1 | exact HDR | exact ST | exact FR | exact ERR | apply model_vm_only_refl | exact HPR1]. }
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (LK1 0%nat e0 E0) as (sv0 & Esv0 & _).
pose proof (proj1 (nth_error_Some svs (le_ix e0)) ltac:(rewrite Esv0; discriminate)) as Hix0.
pose proof (proj1 (nth_error_Some es 0) ltac:(rewrite E0; discriminate)) as Hes0.
step. unfold ent_addr. if_falsex.
apply evt_RZ_done.
eapply (lh_free_loop (length es - 1) 0 e0);
first [ exact HDR | exact ST | exact FR | exact ERR | exact HPR1 | exact EXIT | exact SL1 | exact Hlen | exact VZ | exact SPA | exact HT
| apply model_vm_only_refl | exact E0 | idtac ].
all: lazymatch goal with
| |- HEAP _ _ _ _ _ _ =>
cbn [skipn]; eapply heap_perm; [exact HP1|];
change ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) with ([(t, 56); (tbl, 40 * size)] ++ (map kblk es ++ LB));
change (map kblk es ++ (t, 56) :: (tbl, 40 * size) :: LB) with (map kblk es ++ [(t, 56); (tbl, 40 * size)] ++ LB);
apply Permutation_app_swap_app
| |- lh_link _ _ _ => split; [exact LK1 | split; [exact LK2 | split; [exact LK3 | exact LK4]]]
| |- _ => first [clia | lia]
end.
Qed.
End LhFree.

End RC__1.

End G.
End Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QCcH Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QSL3.
Import U9Mh.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Definition lhprobe_code (w_10 w_11 : Z) : list Z :=
[0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x00052803; 0x00452783; w_10; w_11; 0xd2078753; 0xd20806d3; 0x12f6f7d3; 0xa2e787d3; 0x0a079263; 0x01853783; 0x0306f6b3; 0x02800293; 0x025688b3; 0x011788b3; 0x0008b303; 0xffd00393; 0x0263e863; 0xffe00313; 0x00168893; 0x0016869b; 0x00d846b3; 0x0016b693; 0xfff68693; 0x0116f6b3; 0x025688b3; 0x011788b3; 0x0008b383; 0xfc63eee3; 0x00b8b023; 0x00477713; 0x025685b3; 0x00b785b3; 0x00452803; 0x00853283; 0x00e5a423; 0x00c5b823; 0x00180813; 0x01052223; 0x00000413; 0x08028263; 0x01053583; 0x02800613; 0x02c68633; 0x00c78633; 0x0115bc23; 0x00063c23; 0x02b63023; 0x01153823; 0x07c0006f; 0x800007b7; 0xfff7879b; 0xfff00413; 0x06f80663; 0x400008b7; 0x00068493; 0x00058993; 0x00070913; 0x00060a13; 0xfff8889b; 0x0108c463; 0x0018179b; 0x00050a93; 0x00078593; 0xd85ff0ef; 0x02051e63; 0x000a8513; 0x000aa803; 0x000a0613; 0x00090713; 0x00098593; 0x00048693; 0xf09ff06f; 0x01153423; 0x01153823; 0x02800513; 0x02a68533; 0x00a78533; 0x00053c23; 0x02053023; 0x00040513; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x04010113; 0x00008067]%Z.

Lemma free_slot_exists : forall (l : list nat) (size : nat),
List.NoDup l -> (length l < size)%nat -> exists f, (f < size)%nat /\ ~ In f l.
Proof.
intros l size ND Hlen.
destruct (find (fun i => if in_dec Nat.eq_dec i l then false else true) (seq 0 size)) as [f|] eqn:E.
- apply find_some in E. destruct E as [Hin Hf]. apply in_seq in Hin.
exists f. split; [lia|]. destruct (in_dec Nat.eq_dec f l); [discriminate | assumption].
- exfalso. assert (INC : incl (seq 0 size) l).
{ intros i Hi. pose proof (find_none _ _ E i Hi) as X. cbn in X. destruct (in_dec Nat.eq_dec i l); [assumption | discriminate]. }
pose proof (NoDup_incl_length (seq_NoDup size 0) INC) as L. rewrite length_seq in L. lia.
Qed.

Lemma moddist_zero : forall n f size, 0 <= n < size -> 0 <= f < size -> (f - n) mod size = 0 -> f = n.
Proof.
intros n f size Hn Hf H.
destruct (Z.lt_trichotomy f n) as [L|[E|G]]; [| exact E |].
- rewrite <- (Z.mod_unique (f - n) size (-1) (f - n + size)) in H; lia.
- rewrite Z.mod_small in H by lia. lia.
Qed.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_2 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_10 w_11 : Z).
Variables (hi_10 : bv 20).
Variables (lo_11 : bv 12).
Variables (G_10770 : Z).
Context {RC__ : Q6q3.RunConsts}.
Variables (e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC : Z) (gVOL gCS : Z -> Prop) (gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI : Z).
Hypothesis gH1 : forall a, gCS a -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH2 : gl_range_ok gIMG_LO gIMG_HI.
Hypothesis gH3 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH4 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> ~ gCS a.
Hypothesis gH5 : forall c a, In c [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))] -> (fst c <= a < fst c + Z.of_nat (length (snd c)))%Z ->
~ gCS a /\ ~ (gTP - 164 <= a < gTP - 160)%Z /\ (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis LAY_gIMG_LO : (gIMG_LO = 65536)%Z.
Hypothesis LAY_TPLO : gw_le gIMG_LO (gTP - 164).
Hypothesis LAY_TPHI : gw_le (gTP - 160) gIMG_HI.

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma gLAYF0 : ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gTP gIMG_LO gIMG_HI. pose proof LAY_TPLO as X1; pose proof LAY_TPHI as X2; unfold gw_le in X1, X2. split; [split; [exact X1 | exact X2] | exact LAY_gIMG_LO]. Qed.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Hypothesis CODE : code_at segs base (lhprobe_code w_10 w_11).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 388.
Hypothesis D_10 : decode_any (Z_to_bv 32 w_10) = Some (Auipc 17 hi_10, 4%Z).
Hypothesis E_10 : is_ecall (Z_to_bv 32 w_10) = false.
Hypothesis D_11 : decode_any (Z_to_bv 32 w_11) = Some (FLoad FMT_D 15 17 lo_11, 4%Z).
Hypothesis E_11 : is_ecall (Z_to_bv 32 w_11) = false.
Hypothesis ANCH_11 : gw_anch (Z.shiftl (bv_signed hi_10) 12 + (base + 40) + bv_signed lo_11)%Z G_10770.
Hypothesis RNG_G_10770 : gw_br G_10770 8.
Hypothesis ROM_G_10770 : ro_bytes segs G_10770 [Z_to_bv 8 31; Z_to_bv 8 133; Z_to_bv 8 235; Z_to_bv 8 81; Z_to_bv 8 184; Z_to_bv 8 30; Z_to_bv 8 229; Z_to_bv 8 63].

Let S4L : heap_layout :=
{| hl_segs := segs;
hl_malloc := e_malloc; hl_free := e_free; hl_calloc := e_calloc; hl_realloc := e_realloc; hl_malloc2 := e_malloc2; hl_free2 := e_free2;
hl_tp := gTP;
hl_got_guard := gGOTG; hl_guard := gGUARD; hl_auxv := gAUXV; hl_libc := gLIBC; hl_volatile := gVOL;
hl_stack := 8256;
hl_client_static := gCS;
hl_scratch := fun a => (gTP - 164 <= a < gTP - 160)%Z;
hl_consts := [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))];
hl_img_lo := gIMG_LO; hl_img_hi := gIMG_HI;
hl_static_in_img := gH1; hl_img_range := gH2; hl_scratch_in_img := gH3; hl_scratch_not_static := gH4; hl_consts_ok := gH5 |}.
Let S4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.

Definition next_ix := ltac:(let t := constr:(ltac:(gw_callee_stmt (@U9Mh.Mq3.gw_all) (@U9Mh.Mq3.next_ix) 0%Z)) in let t := eval cbv beta delta [U9Mh.Mq3.next_ix] in t in exact t).
#[using="w_10 w_11 hi_10 lo_11 G_10770 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_10 E_10 D_11 E_11 ANCH_11 RNG_G_10770 ROM_G_10770 S4F"] Lemma gw_all : True. Proof. exact I. Qed.

#[using="Type"] Lemma moddist_step : forall n f size, 0 <= n < size -> 0 <= f < size -> n <> f ->
(f - next_ix size n) mod size = (f - n) mod size - 1.
Proof. clear - segs.
intros n f size Hn Hf NE. unfold next_ix. destruct (Z.eqb_spec (n + 1) size) as [EQ|NEQ].
- rewrite Z.sub_0_r, Z.mod_small by lia.
rewrite <- (Z.mod_unique (f - n) size (-1) (f + 1)); lia.
- destruct (Z.lt_trichotomy f n) as [L|[E|G]]; [| lia |].
+ rewrite <- (Z.mod_unique (f - (n + 1)) size (-1) (f - n - 1 + size)) by lia.
rewrite <- (Z.mod_unique (f - n) size (-1) (f - n + size)) by lia. lia.
+ rewrite !Z.mod_small by lia. lia.
Qed.

Section Probe.
Variables (sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v opts : Z) (svs : list slotv).

Definition is_free (s : slotv) : Prop := sv_k s = LH_EMPTYv \/ sv_k s = LH_FREEDv.

Definition ins_regs (x1 x6 x7 x8 x9 : word) (n : Z) (x17 x18 x19 x20 x21 x28 x29 x30 x31 : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 40) x6 x7 x8 x9
(Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 n) (Z_to_bv 64 opts) (Z_to_bv 64 tbl) (Z_to_bv 64 size) x17
x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31.

#[using="w_10 w_11 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE"] Lemma lh_probe_loop :
forall (d : nat) (n f : Z) (x1 x7 x8 x9 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word) (m : word -> option byte) (sf : slotv),
Z.of_nat d = (f - n) mod size ->
0 <= n < size -> 0 <= f < size -> In size lf_sizes -> Z.of_nat (length svs) = size ->
nth_error svs (Z.to_nat f) = Some sf -> is_free sf ->
(forall i s, nth_error svs i = Some s -> ~ is_free s -> 0 <= sv_k s < LH_FREEDv) ->
(exists sn, nth_error svs (Z.to_nat n) = Some sn /\ ~ is_free sn) ->
0 <= tbl -> tbl + 40 * size < 2^64 ->
mem_inv segs m -> lh_slots segs m tbl svs ->
evt segs (fun ms' => exists (g : Z) (sg : slotv),
0 <= g < size /\ nth_error svs (Z.to_nat g) = Some sg /\ is_free sg /\
ms' = MS (ins_regs x1 (Z_to_bv 64 (-2)) (Z_to_bv 64 (sv_k sg)) x8 x9 g (Z_to_bv 64 (tbl + g * 40)) x18 x19 x20 x21 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x90)) fc None m (seg_rom segs))
(MS (ins_regs x1 (Z_to_bv 64 (-2)) x7 x8 x9 n x17 x18 x19 x20 x21 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x68)) fc None m (seg_rom segs)).
Proof. clear - w_10 w_11 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE segs base sp gp tp s6 s7 s8 s9 s10 s11 F fc t tbl size k v opts svs. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
induction d as [|d IH]; intros until sf; intros Hd Hn Hf Hsz Hlen Esf FREE LIVEK (sn & Esn & NSN) Ht0 Htb MI SL.
- exfalso. assert (f = n) by (apply (moddist_zero n f size); lia). subst f.
rewrite Esf in Esn. injection Esn as ->. exact (NSN FREE).
- assert (NE : n <> f) by (intros ->; rewrite Esf in Esn; injection Esn as ->; exact (NSN FREE)).
pose proof (moddist_step n f size Hn Hf NE) as STEP.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
unfold ins_regs.
step. step. norm_w32. step. rewrite (unsigned_lit size), (unsigned_lit (n + 1)) by lia.

eapply evt_cut with (P := eq (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 40) (Z_to_bv 64 (-2)) x7 x8 x9
(Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 (next_ix size n)) (Z_to_bv 64 opts) (Z_to_bv 64 tbl) (Z_to_bv 64 size) (Z_to_bv 64 (n + 1))
x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 (base + 0x80)) fc None m (seg_rom segs))).
{ unfold next_ix. destruct (Z.eqb_spec (n + 1) size) as [EQ|NEQ].
- rewrite <- EQ, Z.lxor_nilpotent. step. rewrite (v_sltiu_1 (Z_to_bv 64 0) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. rewrite (unsigned_lit (n + 1)) by lia. rewrite Z.land_0_l. apply evt_done. reflexivity.
- pose proof (lxor_bound size (n + 1) 31 ltac:(lia) ltac:(lia) ltac:(lia)) as LB.
assert (LNZ : Z.lxor size (n + 1) <> 0) by (intros X; apply Z.lxor_eq in X; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (Z.lxor size (n + 1))) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615.
rewrite (unsigned_lit (n + 1)) by lia. rewrite land_ones64_l by lia. apply evt_done. reflexivity. }
intros ms' <-.
assert (Hn' : 0 <= next_ix size n < size) by (unfold next_ix; destruct (Z.eqb_spec (n + 1) size); lia).
destruct (nth_error svs (Z.to_nat (next_ix size n))) as [sn'|] eqn:Esn'.
2:{ exfalso. apply nth_error_None in Esn'. lia. }
pose proof (SL _ _ Esn') as C. unfold ent_addr, slot_cells in C. rewrite Z2Nat.id in C by lia.
step. rewrite (unsigned_lit (next_ix size n)) by lia. step.
replace (tbl + next_ix size n * 40) with (tbl + 40 * next_ix size n) by lia.
remember (tbl + 40 * next_ix size n) as B eqn:EB. step. subst B.
step. unfold bv_ltu. change (bv_unsigned (Z_to_bv 64 (-2))) with 18446744073709551614.
assert (FD : is_free sn' \/ ~ is_free sn').
{ unfold is_free. destruct (Z.eq_dec (sv_k sn') LH_EMPTYv); [left; left; assumption|].
destruct (Z.eq_dec (sv_k sn') LH_FREEDv); [left; right; assumption|]. right. intros [X|X]; contradiction. }
destruct FD as [FR' | NF].
+
assert (HK : sv_k sn' = LH_EMPTYv \/ sv_k sn' = LH_FREEDv) by exact FR'. unfold LH_EMPTYv, LH_FREEDv in HK.
rewrite (unsigned_lit (sv_k sn')) by lia. if_false.
apply evt_done. exists (next_ix size n), sn'. split; [exact Hn'|]. split; [exact Esn'|]. split; [exact FR'|].
unfold ins_regs. replace (next_ix size n * 40) with (next_ix size n * 40) by lia.
replace (tbl + 40 * next_ix size n) with (tbl + next_ix size n * 40) by lia. reflexivity.
+
pose proof (LIVEK _ _ Esn' NF) as HK. unfold LH_FREEDv in HK.
rewrite (unsigned_lit (sv_k sn')) by lia. if_true.
eapply (IH (next_ix size n) f); first [exact Esf | exact FREE | exact LIVEK | exact MI | exact SL | exact Hsz | exact Hlen | lia | idtac].
exists sn'. split; [exact Esn' | exact NF].
Qed.
End Probe.

End G.
End Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH.Mq0 Qsw7 QJjn.
Import UPIU.Mqd.
Import UPIU.Mqi.
Import U9Mh.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition tokfree1_code (w_19 w_24 w_34 w_36 w_44 : Z) : list Z :=
[0x0a050a63; 0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x00050413; 0x01452583; 0x0405ca63; 0x03843503; 0x00559593; 0x01058493; 0x00100913; 0x02091913; 0xff000993; 0x009505b3; 0x0005b503; 0xff25b823; w_19; 0x03843503; 0x009505b3; 0x0085b503; 0x0005b023; w_24; 0x03843503; 0x009505b3; 0xfe048493; 0x0005b423; 0xfd3496e3; 0x00843503; 0x00042a23; 0x02042223; 0x00050463; w_34; 0x03843503; w_36; 0x00040513; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x03010113; w_44; 0x00008067]%Z.

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_3 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_19 w_24 w_34 w_36 w_44 : Z).
Variables (joff_19 joff_24 joff_34 joff_36 joff_44 : bv 21).
Variables (e_pbfree e_blk_16158 : Z).
Context {RC__ : Q6q3.RunConsts}.
Variables (e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC : Z) (gVOL gCS : Z -> Prop) (gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI : Z).
Hypothesis gH1 : forall a, gCS a -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH2 : gl_range_ok gIMG_LO gIMG_HI.
Hypothesis gH3 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH4 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> ~ gCS a.
Hypothesis gH5 : forall c a, In c [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))] -> (fst c <= a < fst c + Z.of_nat (length (snd c)))%Z ->
~ gCS a /\ ~ (gTP - 164 <= a < gTP - 160)%Z /\ (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis LAY_gIMG_LO : (gIMG_LO = 65536)%Z.
Hypothesis LAY_TPLO : gw_le gIMG_LO (gTP - 164).
Hypothesis LAY_TPHI : gw_le (gTP - 160) gIMG_HI.
#[using="gH2 gH3 LAY_gIMG_LO"] Lemma gLAYF : ((0 <= gIMG_LO /\ gIMG_HI <= alloc_ceiling) /\ (gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - gH2 gH3 LAY_gIMG_LO gTP gIMG_LO gIMG_HI. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.

Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Variables (e_1411c : Z).
Hypothesis CODE : code_at segs base (tokfree1_code w_19 w_24 w_34 w_36 w_44).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 184.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (Jal 1 joff_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_24 : decode_any (Z_to_bv 32 w_24) = Some (Jal 1 joff_24, 4%Z).
Hypothesis E_24 : is_ecall (Z_to_bv 32 w_24) = false.
Hypothesis D_34 : decode_any (Z_to_bv 32 w_34) = Some (Jal 1 joff_34, 4%Z).
Hypothesis E_34 : is_ecall (Z_to_bv 32 w_34) = false.
Hypothesis D_36 : decode_any (Z_to_bv 32 w_36) = Some (Jal 1 joff_36, 4%Z).
Hypothesis E_36 : is_ecall (Z_to_bv 32 w_36) = false.
Hypothesis D_44 : decode_any (Z_to_bv 32 w_44) = Some (Jal 0 joff_44, 4%Z).
Hypothesis E_44 : is_ecall (Z_to_bv 32 w_44) = false.
Hypothesis LINK_19 : gw_anch (base + 76 + bv_signed joff_19)%Z (e_blk_16158 + 0)%Z.
Hypothesis LINK_24 : gw_anch (base + 96 + bv_signed joff_24)%Z e_free.
Hypothesis LINK_34 : gw_anch (base + 136 + bv_signed joff_34)%Z (e_pbfree + 0)%Z.
Hypothesis LINK_36 : gw_anch (base + 144 + bv_signed joff_36)%Z e_free.
Hypothesis LINK_44 : gw_anch (base + 176 + bv_signed joff_44)%Z e_free.

Hypothesis lb_remove_zero : ltac:(let T := constr:(ltac:(gw_callee_stmt2 (@U9Mh.Mq8.gw_all) (@U9Mh.Mq8.lb_remove_zero) (base + -8)%Z)) in let T := eval cbv beta delta [U9Mh.Mq8.lb_remove_zero U9Mh.Mq8.json_tokener_new_entry] in T in let T := gw_fold_pcs T base (-8)%Z [0]%Z in exact T).

Definition put_pre := ltac:(let t := constr:(ltac:(gw_ctx2 (@UPIU.Mqi.put_pre))) in let t := eval cbv beta delta [UPIU.Mqi.put_pre] in t in exact t).
Definition put_stmt := ltac:(let t := constr:(ltac:(gw_ctx2 (@UPIU.Mqi.put_stmt))) in let t := eval cbv beta delta [UPIU.Mqi.put_stmt] in t in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqi.put_pre))) in let t := gw_subst t x put_pre in exact t).
Definition put_stk_P := ltac:(let t := constr:(ltac:(gw_ctx2 (@UPIU.Mqi.put_stk_P))) in let t := eval cbv beta delta [UPIU.Mqi.put_stk_P] in t in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqi.put_pre))) in let t := gw_subst t x put_pre in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqi.put_stmt))) in let t := gw_subst t x put_stmt in exact t).

Let S4L : heap_layout :=
{| hl_segs := segs;
hl_malloc := e_malloc; hl_free := e_free; hl_calloc := e_calloc; hl_realloc := e_realloc; hl_malloc2 := e_malloc2; hl_free2 := e_free2;
hl_tp := gTP;
hl_got_guard := gGOTG; hl_guard := gGUARD; hl_auxv := gAUXV; hl_libc := gLIBC; hl_volatile := gVOL;
hl_stack := 8256;
hl_client_static := gCS;
hl_scratch := fun a => (gTP - 164 <= a < gTP - 160)%Z;
hl_consts := [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))];
hl_img_lo := gIMG_LO; hl_img_hi := gIMG_HI;
hl_static_in_img := gH1; hl_img_range := gH2; hl_scratch_in_img := gH3; hl_scratch_not_static := gH4; hl_consts_ok := gH5 |}.
Let S4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
#[using="w_19 w_24 w_34 w_36 w_44 joff_19 joff_24 joff_34 joff_36 joff_44 e_pbfree e_blk_16158 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free e_1411c CODE BASE4 BASER D_19 E_19 D_24 E_24 D_34 E_34 D_36 E_36 D_44 E_44 LINK_19 LINK_24 LINK_34 LINK_36 LINK_44 lb_remove_zero S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Ltac g_ra_even := lazymatch goal with |- (bv_unsigned (Z_to_bv 64 (?b + ?k)) mod 2 = 0)%Z =>
let X := fresh in let Y := fresh in pose proof BASE4 as X; pose proof BASER as Y; unfold gw_b4, gw_br in X, Y; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia end.
Ltac alloc_side ::=
try (progress fold S4L); try (progress fold S4F);
simpl hl_segs; simpl hl_stack; simpl hl_tp; simpl hl_malloc; simpl hl_free; simpl hl_calloc; simpl hl_realloc;
rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- forall _, _ => idtac
| |- _ \/ _ => idtac
| |- (bv_unsigned (Z_to_bv 64 (_ + _)) mod 2 = 0)%Z => first [ g_ra_even | lia ]
| |- _ =>
lazymatch goal with
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ _ _ => eassumption
| |- @eq (bv _) _ _ => first [ reflexivity | eassumption | symmetry; eassumption | apply bv_eq; rewrite ?unsigned_lit by lia; lia ]
| |- (_ mod 16 = 0)%Z =>
first [ assumption
| match goal with H : (bv_unsigned ?sp mod 16 = 0)%Z |- ((bv_unsigned ?sp + ?k) mod 16 = 0)%Z =>
rewrite <- Zplus_mod_idemp_l, H; reflexivity end
| lia ]
| |- _ => first [ lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia ]
end end.
Ltac gj_fold := try (progress fold S4L); repeat match goal with H : _ |- _ => progress fold S4L in H end; try (progress fold S4F); repeat match goal with H : _ |- _ => progress fold S4F in H end.
Ltac unfold_consts ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
Ltac clia ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
Ltac unfold_consts_goal ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size.

Section RC__1.

Definition lvblocks (levels : list tlevel) (i : nat) : list blk :=
concat (map lvl_blocks (rev (firstn i levels))).

#[using="Type"] Lemma firstn_S_nth : forall {A} (l : list A) i x, nth_error l i = Some x -> firstn (S i) l = firstn i l ++ [x].
Proof. clear - segs.
induction l as [|h t IH]; intros [|i] x H; cbn in H; try discriminate.
- injection H as ->. reflexivity.
- cbn. f_equal. apply IH. exact H.
Qed.

#[using="Type"] Lemma lvblocks_S : forall levels i l, nth_error levels i = Some l ->
lvblocks levels (S i) = lvl_blocks l ++ lvblocks levels i.
Proof. clear - segs.
intros levels i l H. unfold lvblocks. rewrite (firstn_S_nth _ _ _ H), rev_app_distr. cbn. reflexivity.
Qed.

#[using="Type"] Lemma lvblocks_0 : forall levels, lvblocks levels 0 = [].
Proof. clear - segs. reflexivity. Qed.

#[using="Type"] Lemma lvblocks_clean : forall levels i, (forall j l, nth_error levels j = Some l -> (j < i)%nat -> lvl_clean l) ->
lvblocks levels i = [].
Proof. clear - segs.
intros levels i. induction i as [|i IH]; intros H; [reflexivity|].
destruct (nth_error levels i) as [l|] eqn:E.
- rewrite (lvblocks_S _ _ _ E). rewrite (lvl_clean_blocks l) by (eapply H; [exact E|lia]). cbn. apply IH.
intros j l' Hj Hlt. eapply H; [exact Hj | lia].
- unfold lvblocks. rewrite firstn_all2 by (apply nth_error_None in E; lia).
unfold lvblocks in IH. rewrite firstn_all2 in IH by (apply nth_error_None in E; lia).
apply IH. intros j l' Hj Hlt. eapply H; [exact Hj | lia].
Qed.

#[using="Type"] Lemma tstack_pres : forall L LB SP m m' q levels,
heap_pres L LB SP m m' -> In (q, 1024) LB -> length levels = 32%nat ->
tstack (hl_segs L) m q levels -> tstack (hl_segs L) m' q levels.
Proof. clear - segs.
intros L LB SP m m' q levels HPR Hin LEN TS j l Hl.
pose proof (nth_error_Some_length Hl) as Hj.
eapply (heap_pres_rw_cells L); [exact HPR | exact (TS j l Hl) |].
eapply client_range_block; [exact Hin | lia | rewrite srec_cells_size; cbn [Z.of_nat]; lia].
Qed.

Definition srec_cells8 (stss : list byte) (cur name : Z) : list cell :=
[CB 8 stss; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 name)].

#[using="Type"] Lemma srec_to8 : forall segs_ m a l,
rw_cells segs_ m a (srec_cells l) ->
rw_cells segs_ m a (srec_cells8 (le4 (Z_to_bv 64 (tl_st l)) ++ le4 (Z_to_bv 64 (tl_ss l))) (tl_cur l) (tl_name l)).
Proof. clear - segs.
intros segs_ m a l H. eapply rw_cells_recast; [exact H | cbn; repeat split; reflexivity | reflexivity | reflexivity].
Qed.

#[using="Type"] Lemma srec_reset_of8 : forall segs_ m a,
rw_cells segs_ m a [C8 (Z_to_bv 64 4294967296); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
rw_cells segs_ m a (srec_cells lvl_reset).
Proof. clear - segs.
intros segs_ m a H. eapply rw_cells_recast; [exact H | cbn; repeat split | apply bytes_eq_by_unsigned; vm_compute; reflexivity | reflexivity].
Qed.

#[using="Type"] Lemma lupd_lupd : forall {A} (l : list A) i (x y : A), lupd (lupd l i x) i y = lupd l i y.
Proof. clear - segs. induction l; intros [|i] x y; cbn; auto. f_equal. apply IHl. Qed.

#[using="Type"] Lemma lvl_blocks_TL : forall st ss cur cs cbs name nbs, lvl_blocks (TL st ss cur cs cbs name nbs) = cbs ++ nbs.
Proof. clear - segs. reflexivity. Qed.

#[using="Type"] Lemma nodup_mid_notin : forall (A B P LB0 : list blk) r n q k k',
List.NoDup (map blk_addr (A ++ B ++ P ++ (r, n) :: (q, k) :: LB0)) -> ~ In (q, k') LB0.
Proof. clear - segs.
intros A B P LB0 r n q k k' ND Hin.
rewrite !map_app in ND. apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst] in ND. apply List.NoDup_cons_iff in ND as [_ ND]. apply List.NoDup_cons_iff in ND as [Hni _].
apply Hni. exact (in_map blk_addr _ _ Hin).
Qed.

#[using="Type"] Lemma nodup_mid_notin_r : forall (A B P LB0 : list blk) r n q k n',
List.NoDup (map blk_addr (A ++ B ++ P ++ (r, n) :: (q, k) :: LB0)) -> ~ In (r, n') LB0.
Proof. clear - segs.
intros A B P LB0 r n q k n' ND Hin.
rewrite !map_app in ND. apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst] in ND. apply List.NoDup_cons_iff in ND as [Hni _].
apply Hni. right. exact (in_map blk_addr _ _ Hin).
Qed.

#[using="Type"] Lemma nodup_P_notq : forall (X P LB0 : list blk) r n q k a j,
List.NoDup (map blk_addr (X ++ P ++ (r, n) :: (q, k) :: LB0)) -> In (a, j) P -> a <> q.
Proof. clear - segs.
intros X P LB0 r n q k a j ND Hin ->.
rewrite map_app in ND. apply NoDup_app_remove_l in ND.
refine (nodup_prefix_suffix P ((r, n) :: (q, k) :: LB0) q j k ND Hin _). right; left; reflexivity.
Qed.

Section TokFree.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : (put_stmt S4L HIx S4F (e_blk_16158 + 0x0) put_stk_P).

Definition json_tokener_free_entry : Z := (base + 0x0).
Definition tokfree_loop_pc : Z := (base + 0x40).

Definition tf_frame (m : word -> option byte) (sp : Z) (junk : list byte) (s3v s2v s1v s0v rav : word) : Prop :=
rw_cells segs m (sp - 48) [CB 8 junk; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Definition tf_body_post (x2 gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0v : word) (F : bvmap 5 word) (fc : bv 32)
(md : Model) (REST LB0 P : list blk) (SP : Z) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (junk : list byte) (s3v s2v s1v s0v rav : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) F' fc' x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 s0 (Z_to_bv 64 (32 * Z.of_nat i + 16 - 32)) a0v a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 (base + 0x74)) fc' None m' (seg_rom segs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only md md' /\
HEAPx A' REST m' md' /\
tstack segs m' q (lupd levels i lvl_reset) /\
rw_cells segs m' r (tok_cells pb depth q x) /\
tf_frame m' SP junk s3v s2v s1v s0v rav /\
stk segs m' lo (SP - 48) /\
heap_pres S4L LB0 SP me m' /\
rw_cells segs m' (gTP - 164) [C4 errv] /\
agree_on segs P mpre m'.

#[using="w_19 w_24 w_34 w_36 w_44 joff_19 joff_24 e_blk_16158 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_19 E_19 D_24 E_24 LINK_19 LINK_24 lb_remove_zero PUT"] Lemma tokfree_body :
forall (i : nat) (x1 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (REST LB0 P : list blk) (SP lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (l : tlevel) (junk : list byte) (s3v s2v s1v s0v rav : word),
nth_error levels i = Some l -> (i < 32)%nat -> length levels = 32%nat ->
HEAPx A (lvl_blocks l ++ REST) m md ->
REST = P ++ (r, 72) :: (q, 1024) :: LB0 ->
lvl_ok segs S4F m l ->
tstack segs m q levels ->
rw_cells segs m r (tok_cells pb depth q x) ->
tf_frame m SP junk s3v s2v s1v s0v rav ->
stk segs m lo (SP - 48) -> alloc_ceiling <= lo -> lo <= SP - 48 - put_stk_P ->
SP mod 16 = 0 -> SP <= hi_top S4L HIx -> 0 <= SP < 2^64 ->
heap_pres S4L LB0 SP me m ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP ->
(forall ms' md', tf_body_post (Z_to_bv 64 (SP - 48)) gp tp (Z_to_bv 64 r) (Z_to_bv 64 (2^32)) (Z_to_bv 64 (-16)) s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q)
F fc md REST LB0 P SP me m lo errv q r pb depth x levels i junk s3v s2v s1v s0v rav ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (SP - 48)) gp tp t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 (32 * Z.of_nat i + 16)) (Z_to_bv 64 q)
a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (2^32)) (Z_to_bv 64 (-16)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 tokfree_loop_pc) fc None m (seg_rom segs)) md) T.
Proof. clear - w_19 w_24 w_34 w_36 w_44 joff_19 joff_24 e_blk_16158 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_19 E_19 D_24 E_24 LINK_19 LINK_24 lb_remove_zero PUT segs gTP S4F HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until rav. intros Hl Hi LEN HP EREST LOK TS BLK FR ST LO LOS SPA HT SPR HPR ERR TP K.
unfold put_stk_P in LOS. unfold_consts.
assert (INrR : In (r, 72) REST) by (rewrite EREST; apply in_or_app; right; left; reflexivity).
assert (INqR : In (q, 1024) REST) by (rewrite EREST; apply in_or_app; right; right; left; reflexivity).
assert (INr : In (r, 72) (lvl_blocks l ++ REST)) by (rewrite EREST; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 1024) (lvl_blocks l ++ REST)) by (rewrite EREST; apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ r 72 HP INr) as (_ & Hral & Hrlo & Hrhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 72 HP INr) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
pose proof (heap_blk S4L HIx _ _ _ _ q 1024 HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q 1024 HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi, Hqhi.
assert (Hqr : q <> r).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. rewrite EREST, !map_app in ND. cbn [map blk_addr fst] in ND.
apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q 1024 r 72 HP INq INr Hqr) as Hdqr.

pose proof (srec_to8 _ _ _ _ (TS i l Hl)) as LV. unfold srec_cells8 in LV. cbn [le4 Z_to_le_bytes app] in LV.
remember (q + 32 * Z.of_nat i) as bse eqn:Hbse in LV.
pose proof (nth_error_Some_length Hl) as HiL.
unfold tf_frame in FR. unfold tok_cells in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
subst tp.
apply rz_evt; [exact MOK|]. unfold tokfree_loop_pc.
step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (rw_cells_recast_prefix segs mc bse [C8 (Z_to_bv 64 4294967296)] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))] LV
ltac:(cbn; repeat split) ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) ltac:(reflexivity)) as LV1 end.
cbn [app] in LV1.
set (l1 := TL 0 1 (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS1 : tstack segs mc q (lupd levels i l1)) end.
{ subst bse. eapply (tstack_put segs m _ q levels i l1 []); [exact TS | lia | exact MU | exact WM | intros; exact I | exact LV1]. }
clear LV TS.
assert (PDJ : forall a n, In (a, n) P -> a + n <= q \/ q + 1024 <= a).
{ intros a n Hin.
assert (Haq : a <> q) by (eapply (nodup_P_notq (lvl_blocks l)); [rewrite <- EREST; exact (heap_blk_nodup S4L HIx _ _ _ _ HP) | exact Hin]).
exact (heap_blk_disjoint S4L HIx _ _ _ _ a n q 1024 HP ltac:(apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hin) INq Haq). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGP : agree_on segs P m mc) by (eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]) end.

destruct LOK as [JO NM].
unfold lvl_blocks in HP. rewrite <- app_assoc in HP.
apply evt_RZ_done.
assert (INq2 : In (q, 1024) (tl_cbs l ++ tl_nbs l ++ REST)).
{ apply in_or_app; right; apply in_or_app; right. rewrite EREST. apply in_or_app; right; right; left; reflexivity. }
eapply PUT with (s := tl_cs l) (BS := tl_cbs l) (LB := tl_nbs l ++ REST) (p := tl_cur l) (rc := 1) (lo := lo) (errv := errv);
[ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU); apply Forall_cons; [right; left; exists q, 1024; split; [exact INq2 | cbn; lia] | apply Forall_nil]
| .. ]; try alloc_side.
{ assert (AG : agree_on segs (tl_cbs l) m m0).
{ eapply agree_of_munch; [exact MU | exact WM |]. intros a n Hin. cbn. split; [|exact I].
assert (Haq : a <> q).
{ intros ->. refine (nodup_prefix_suffix (tl_cbs l) (tl_nbs l ++ REST) q n 1024 (heap_blk_nodup S4L HIx _ _ _ _ HP) Hin _).
apply in_or_app; right. rewrite EREST. apply in_or_app; right; right; left; reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n q 1024 HP ltac:(apply in_or_app; left; exact Hin) INq2 Haq). lia. }
unfold put_pre. destruct (tl_cs l) as [s'|]; [|exact JO].
destruct JO as [Hc J]. split; [exact Hc|]. split; [lia|]. eapply jval_agree; [exact J | exact AG | apply incl_refl]. }
{ unfold put_stk_P. rewrite unsigned_lit by lia. lia. }
intros ms2 md2 (m2 & A2 & r2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (SP - 48)) in ST2 by lia. rewrite ?(unsigned_lit (SP - 48)) in HPR2 by lia.
destruct OUT2 as [[_ HP2] | (s2 & _ & Habs & _)]; [| lia].
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (INr2 : In (r, 72) (tl_nbs l ++ REST)) by (apply in_or_app; right; rewrite EREST; apply in_or_app; right; left; reflexivity).
assert (INq3 : In (q, 1024) (tl_nbs l ++ REST)) by (apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in BLK; [| eapply client_range_block; [exact INr2 | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in LV1; [| eapply client_range_block; [exact INq3 | lia | cbn; lia]]. cbn [hl_segs S4L] in LV1.
apply (tstack_pres S4L _ _ _ _ _ _ HPR2 INq3) in TS1; [| rewrite lupd_length; exact LEN].

assert (NQ0 : ~ In (q, 1024) LB0).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. rewrite EREST in ND. exact (nodup_mid_notin _ _ _ _ _ _ _ _ 1024 ND). }
assert (HPRa : heap_pres S4L LB0 SP me m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB0 SP); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; apply in_or_app; right; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, 1024. split; [exact INq2|]. split; [exact NQ0 | lia].
- eapply heap_pres_weaken; [exact HPR2 | lia | intros bb Hbb; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb]. }
assert (AGP2 : agree_on segs P m m2).
{ eapply agree_on_trans; [exact AGP|]. eapply (agree_of_heap_pres segs S4L); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hb]. }
clear MU WM MI HPR AGP.

destruct NM as [[Hn0 Hnbs] | [Hn0 [nn Hnbs]]].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs m2) as WM.
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
reenter MOK2.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step. stepz. step.

set (l2 := TL 0 1 0 None [] (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS2 : tstack segs mc q (lupd levels i l2)) end.
{ rewrite <- (lupd_lupd levels i l1 l2). subst bse.
eapply (tstack_put segs m2 _ q (lupd levels i l1) i l2 []); [exact TS1 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | exact LV1]. }
clear TS1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGP3 : agree_on segs P m mc) by (eapply agree_on_trans; [exact AGP2|]; eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]) end.
apply evt_RZ_done. eapply (hi_free S4L HIx) with (p := tl_name l) (lo := lo);
[ eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU); apply Forall_cons; [right; left; exists q, 1024; split; [exact INq3 | cbn; lia] | apply Forall_nil]
| .. ]; try alloc_side.
{ left. exact Hn0. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (SP - 48)) in ST3 by lia. rewrite ?(unsigned_lit (SP - 48)) in HPR3 by lia.
replace (lb_remove (tl_name l) (tl_nbs l ++ REST)) with (tl_nbs l ++ REST) in HPR3, HP3 by (rewrite Hn0; symmetry; exact (lb_remove_zero HIx _ _ _ _ HP2)).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [exact INr2 | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in LV1; [| eapply client_range_block; [exact INq3 | lia | cbn; lia]]. cbn [hl_segs S4L] in LV1.
apply (tstack_pres S4L _ _ _ _ _ _ HPR3 INq3) in TS2; [| rewrite lupd_length; exact LEN].
assert (HPRb : heap_pres S4L LB0 SP me m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB0 SP); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, 1024. split; [exact INq3|]. split; [exact NQ0 | lia].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb]. }
assert (AGP4 : agree_on segs P m m3).
{ eapply agree_on_trans; [exact AGP3|]. eapply (agree_of_heap_pres segs S4L); [exact HPR3 | reflexivity |].
intros b Hb. first [ rewrite EREST; apply in_or_app; left; exact Hb | apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hb ]. }
clear MU WM MI HPRa AGP3.

pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs m3) as WM.
pose proof (munch_refl [(bse, bse + 32)] m3) as MU.
reenter MOK3.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step. stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS3 : tstack segs mc q (lupd levels i lvl_reset)) end.
{ rewrite <- (lupd_lupd levels i l2 lvl_reset). subst bse.
eapply (tstack_put segs m3 _ q (lupd levels i l2) i lvl_reset []); [exact TS2 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | exact LV1]. }
apply evt_RZ_done. apply K. unfold tf_body_post.
replace (32 * Z.of_nat i + 16 - 32) with (32 * Z.of_nat i + -16) by lia.
do 19 eexists.
split; [reflexivity|].
split; [exact FS2|]. split; [exact FRM2|].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|].
split.
{ rewrite Hnbs in HP3. cbn [app] in HP3.
eapply (heap_frame S4L HIx); [exact HP3 | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
right; left. exists q, 1024. split; [rewrite EREST; apply in_or_app; right; right; left; reflexivity | lia]. }
split; [exact TS3|]. split; [exact BLK|]. split; [exact FR|]. split; [exact ST3|].
split; [| split; [exact ERR3 | eapply agree_on_trans; [exact AGP4|]; eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]]].
eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch S4L LB0 SP); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros bb Hbb; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, 1024. split; [exact INq3|]. split; [exact NQ0 | lia].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs m2) as WM.
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
reenter MOK2.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step. stepz. step.

set (l2 := TL 0 1 0 None [] (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS2 : tstack segs mc q (lupd levels i l2)) end.
{ rewrite <- (lupd_lupd levels i l1 l2). subst bse.
eapply (tstack_put segs m2 _ q (lupd levels i l1) i l2 []); [exact TS1 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | exact LV1]. }
clear TS1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGP3 : agree_on segs P m mc) by (eapply agree_on_trans; [exact AGP2|]; eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]) end.
apply evt_RZ_done. eapply (hi_free S4L HIx) with (p := tl_name l) (lo := lo);
[ eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU); apply Forall_cons; [right; left; exists q, 1024; split; [exact INq3 | cbn; lia] | apply Forall_nil]
| .. ]; try alloc_side.
{ right. exists nn. rewrite Hnbs. left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (SP - 48)) in ST3 by lia. rewrite ?(unsigned_lit (SP - 48)) in HPR3 by lia.
replace (lb_remove (tl_name l) (tl_nbs l ++ REST)) with REST in HPR3, HP3 by (rewrite Hnbs; cbn [app]; symmetry; apply lb_remove_head).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [exact INrR | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in LV1; [| eapply client_range_block; [exact INqR | lia | cbn; lia]]. cbn [hl_segs S4L] in LV1.
apply (tstack_pres S4L _ _ _ _ _ _ HPR3 INqR) in TS2; [| rewrite lupd_length; exact LEN].
assert (HPRb : heap_pres S4L LB0 SP me m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB0 SP); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, 1024. split; [exact INq3|]. split; [exact NQ0 | lia].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; rewrite EREST; apply in_or_app; right; right; right; exact Hbb]. }
assert (AGP4 : agree_on segs P m m3).
{ eapply agree_on_trans; [exact AGP3|]. eapply (agree_of_heap_pres segs S4L); [exact HPR3 | reflexivity |].
intros b Hb. first [ rewrite EREST; apply in_or_app; left; exact Hb | apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hb ]. }
clear MU WM MI HPRa AGP3.

pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs m3) as WM.
pose proof (munch_refl [(bse, bse + 32)] m3) as MU.
reenter MOK3.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step. stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS3 : tstack segs mc q (lupd levels i lvl_reset)) end.
{ rewrite <- (lupd_lupd levels i l2 lvl_reset). subst bse.
eapply (tstack_put segs m3 _ q (lupd levels i l2) i lvl_reset []); [exact TS2 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | exact LV1]. }
apply evt_RZ_done. apply K. unfold tf_body_post.
replace (32 * Z.of_nat i + 16 - 32) with (32 * Z.of_nat i + -16) by lia.
do 19 eexists.
split; [reflexivity|].
split; [exact FS2|]. split; [exact FRM2|].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|].
split.
{ eapply (heap_frame S4L HIx); [exact HP3 | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
right; left. exists q, 1024. split; [rewrite EREST; apply in_or_app; right; right; left; reflexivity | lia]. }
split; [exact TS3|]. split; [exact BLK|]. split; [exact FR|]. split; [exact ST3|].
split; [| split; [exact ERR3 | eapply agree_on_trans; [exact AGP4|]; eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]]].
eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch S4L LB0 SP); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros bb Hbb; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, 1024. split; [exact INqR|]. split; [exact NQ0 | lia].
Qed.
End TokFree.

End RC__1.

End G.
End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U9Mh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U9Mh.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwApply2 GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Section G.
Variables (segs : list Segment).

Context {RC__ : Q6q3.RunConsts}.
Variables (e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC : Z) (gVOL gCS : Z -> Prop) (gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI : Z).
Hypothesis gH1 : forall a, gCS a -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH2 : gl_range_ok gIMG_LO gIMG_HI.
Hypothesis gH3 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH4 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> ~ gCS a.
Hypothesis gH5 : forall c a, In c [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))] -> (fst c <= a < fst c + Z.of_nat (length (snd c)))%Z ->
~ gCS a /\ ~ (gTP - 164 <= a < gTP - 160)%Z /\ (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis LAY_gIMG_LO : (gIMG_LO = 65536)%Z.
Hypothesis LAY_TPLO : gw_le gIMG_LO (gTP - 164).
Hypothesis LAY_TPHI : gw_le (gTP - 160) gIMG_HI.

Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).

Let S4L : heap_layout :=
{| hl_segs := segs;
hl_malloc := e_malloc; hl_free := e_free; hl_calloc := e_calloc; hl_realloc := e_realloc; hl_malloc2 := e_malloc2; hl_free2 := e_free2;
hl_tp := gTP;
hl_got_guard := gGOTG; hl_guard := gGUARD; hl_auxv := gAUXV; hl_libc := gLIBC; hl_volatile := gVOL;
hl_stack := 8256;
hl_client_static := gCS;
hl_scratch := fun a => (gTP - 164 <= a < gTP - 160)%Z;
hl_consts := [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))];
hl_img_lo := gIMG_LO; hl_img_hi := gIMG_HI;
hl_static_in_img := gH1; hl_img_range := gH2; hl_scratch_in_img := gH3; hl_scratch_not_static := gH4; hl_consts_ok := gH5 |}.
Let S4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
#[using="RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Import Q6q3.
Section RC__1.

Definition libc_auxv_cell : Z := 0x3b0a8.

Definition auxv_at (m : word -> option byte) (aw : Z) (keys : list Z) : Prop :=
bytes_at segs m libc_auxv_cell (le8 (Z_to_bv 64 aw)) /\ aw mod 8 = 0 /\
Forall (fun k => 0 < k < 2^64 /\ k <> 33) keys /\
(forall i k, nth_error keys i = Some k -> bytes_at segs m (aw + 16 * Z.of_nat i) (le8 (Z_to_bv 64 k))) /\
bytes_at segs m (aw + 16 * Z.of_nat (length keys)) (le8 (Z_to_bv 64 0)).

End RC__1.

End G.
