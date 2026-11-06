(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo QPIU Q8tj Q6WR Q9Mh QAyu Q7mx Q6q3 Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply2 Lib.GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo.
Import QPIU.Mqd.
Import Q8tj.
Import Q6WR Q6WR.Mq0.
Import Q9Mh.Mq5.
Import QAyu.Mq4.
Import Q7mx.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition blk_187f8_code : list Z := [0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00050413; 0x02053503; 0x02050063; 0x00843483; 0x00048c63; 0x02043583; 0x00048513; 0x000580e7; 0x0184b483; 0xfe0498e3; 0x01843503]%Z.

Definition blk_17a68_code : list Z := [0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x01213023; 0x00050413; 0x00853583; 0x02058e63; 0x00000493; 0x00000913; 0x0100006f; 0x00190913; 0x00848493; 0x02b97263; 0x00043503; 0x00950533; 0x00053503; 0xfe0504e3; 0x01843583; 0x000580e7; 0x00843583; 0xfd9ff06f; 0x00043503]%Z.

Definition blk_17cb0_code : list Z := [0x00853503; 0x00008067]%Z.

Definition blk_18a54_code : list Z := [0x00452503; 0x00008067]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_30 w_34 w_39 w_41 w_43 w_51 w_55 : Z).
Variables (joff_30 joff_34 joff_39 joff_41 joff_43 joff_51 joff_55 : bv 21).
Variables (e_pbfree e_17a68 e_17cb0 e_187f8 e_18a54 : Z).
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
Variables (e_strcmp : Z).
Let e_blk_17cb0 : Z := e_17cb0.
Let e_blk_18a54 : Z := e_18a54.
Hypothesis CODE : code_at segs base (maybefree1_code w_30 w_34 w_39 w_41 w_43 w_51 w_55).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 236.
Hypothesis D_30 : decode_any (Z_to_bv 32 w_30) = Some (Jal 1 joff_30, 4%Z).
Hypothesis E_30 : is_ecall (Z_to_bv 32 w_30) = false.
Hypothesis D_34 : decode_any (Z_to_bv 32 w_34) = Some (Jal 1 joff_34, 4%Z).
Hypothesis E_34 : is_ecall (Z_to_bv 32 w_34) = false.
Hypothesis D_39 : decode_any (Z_to_bv 32 w_39) = Some (Jal 1 joff_39, 4%Z).
Hypothesis E_39 : is_ecall (Z_to_bv 32 w_39) = false.
Hypothesis D_41 : decode_any (Z_to_bv 32 w_41) = Some (Jal 1 joff_41, 4%Z).
Hypothesis E_41 : is_ecall (Z_to_bv 32 w_41) = false.
Hypothesis D_43 : decode_any (Z_to_bv 32 w_43) = Some (Jal 1 joff_43, 4%Z).
Hypothesis E_43 : is_ecall (Z_to_bv 32 w_43) = false.
Hypothesis D_51 : decode_any (Z_to_bv 32 w_51) = Some (Jal 1 joff_51, 4%Z).
Hypothesis E_51 : is_ecall (Z_to_bv 32 w_51) = false.
Hypothesis D_55 : decode_any (Z_to_bv 32 w_55) = Some (Jal 1 joff_55, 4%Z).
Hypothesis E_55 : is_ecall (Z_to_bv 32 w_55) = false.
Hypothesis LINK_30 : gw_anch (base + 120 + bv_signed joff_30)%Z (e_187f8 + 0)%Z.
Hypothesis LINK_34 : gw_anch (base + 136 + bv_signed joff_34)%Z (e_17a68 + 0)%Z.
Hypothesis LINK_39 : gw_anch (base + 156 + bv_signed joff_39)%Z e_free.
Hypothesis LINK_41 : gw_anch (base + 164 + bv_signed joff_41)%Z (e_pbfree + 0)%Z.
Hypothesis LINK_43 : gw_anch (base + 172 + bv_signed joff_43)%Z e_free.
Hypothesis LINK_51 : gw_anch (base + 204 + bv_signed joff_51)%Z (e_17cb0 + 0)%Z.
Hypothesis LINK_55 : gw_anch (base + 220 + bv_signed joff_55)%Z (e_18a54 + 0)%Z.

Hypothesis printbuf_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqd.gw_all) (@QPIU.Mqd.printbuf_free_cps) e_pbfree)) in exact T).
Hypothesis lh_table_length_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqb.gw_all) (@QPIU.Mqb.lh_table_length_spec) (base + 8444)%Z)) in let T := eval cbv beta delta [QPIU.Mqb.lh_table_length_entry QPIU.Mqb.lh_char_equal_entry] in T in let T := gw_fold_pcs T base (8444)%Z [0]%Z in exact T).
Hypothesis lh_table_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QAyu.Mq2.gw_all) (@QAyu.Mq2.lh_table_free_cps) e_187f8)) in exact T).
Hypothesis array_list_length_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mq2.gw_all) (@QPIU.Mq2.array_list_length_spec) (base + 6052)%Z)) in let T := eval cbv beta delta [QPIU.Mq2.array_list_length_entry QPIU.Mq2.array_list_get_idx_entry] in T in let T := gw_fold_pcs T base (6052)%Z [0]%Z in exact T).
Hypothesis array_list_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mq0.gw_all) (@QPIU.Mq0.array_list_free_cps) e_17a68)) in exact T).
Variable wb17544_1 : Z.  Variable joffb17544_1 : bv 21.
Hypothesis D_b17544_1 : decode_any (Z_to_bv 32 wb17544_1) = Some (Jal 0 joffb17544_1, 4%Z).
Hypothesis E_b17544_1 : is_ecall (Z_to_bv 32 wb17544_1) = false.
Hypothesis LINK_b17544_1 : gw_anch (e_fn_free_userdata + 4 + bv_signed joffb17544_1)%Z e_free.
Hypothesis CODE_e_blk_17544 : code_at segs e_fn_free_userdata (blk_17544_code wb17544_1).
Hypothesis AL_e_blk_17544_b4 : gw_b4 e_fn_free_userdata.
Hypothesis RNG_e_blk_17544_code : gw_br e_fn_free_userdata 8.
Hypothesis LAY_POS_e_fn_free_userdata : gw_le 1 e_fn_free_userdata.
Hypothesis LAY_HI_e_fn_free_userdata : gw_le (e_fn_free_userdata + 4) 1099511627776.
Hypothesis AL_e_fn_ud_to_json_string : gw_b4 e_fn_ud_to_json_string.
Hypothesis RNG_e_fn_ud_to_json_string : gw_br e_fn_ud_to_json_string 4.
Hypothesis LAY_POS_e_fn_ud_to_json_string : gw_le 1 e_fn_ud_to_json_string.
Hypothesis LAY_HI_e_fn_ud_to_json_string : gw_le (e_fn_ud_to_json_string + 4) 1099511627776.

Definition mf_post := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_post))) in let t := eval cbv beta delta [Q9Mh.Mq5.mf_post] in t in exact t).
Definition mf_scalar := ltac:(let p := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_scalar))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_post))) in let T := gw_subst T x mf_post in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq0.mf_post))) in let T := gw_subst T x mf_post in exact (p : T)).

Definition mf_str := ltac:(let p := constr:(ltac:(gw_ctx2 (@QAyu.Mq4.mf_str))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_post))) in let T := gw_subst T x mf_post in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq0.mf_post))) in let T := gw_subst T x mf_post in exact (p : T)).
Definition mf_dblu := ltac:(let p := constr:(ltac:(gw_ctx2 (@QAyu.Mq4.mf_dblu))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_post))) in let T := gw_subst T x mf_post in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq0.mf_post))) in let T := gw_subst T x mf_post in exact (p : T)).

Definition mf_obj := ltac:(let p := constr:(ltac:(gw_ctx2 (@Q7mx.Mq0.mf_obj))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_post))) in let T := gw_subst T x mf_post in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq0.mf_post))) in let T := gw_subst T x mf_post in exact (p : T)).
Definition mf_arr := ltac:(let p := constr:(ltac:(gw_ctx2 (@Q7mx.Mq0.mf_arr))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_post))) in let T := gw_subst T x mf_post in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq0.mf_post))) in let T := gw_subst T x mf_post in exact (p : T)).

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
Hypothesis CODE_e_187f8 : code_at segs e_187f8 blk_187f8_code.
Hypothesis CODE_e_17a68 : code_at segs e_17a68 blk_17a68_code.
Hypothesis CODE_e_17cb0 : code_at segs e_17cb0 blk_17cb0_code.
Hypothesis CODE_e_18a54 : code_at segs e_18a54 blk_18a54_code.
#[using="w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_30 joff_34 joff_39 joff_41 joff_43 joff_51 joff_55 e_pbfree e_17a68 e_17cb0 e_187f8 e_18a54 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free e_strcmp CODE BASE4 BASER D_30 E_30 D_34 E_34 D_39 E_39 D_41 E_41 D_43 E_43 D_51 E_51 D_55 E_55 LINK_30 LINK_34 LINK_39 LINK_41 LINK_43 LINK_51 LINK_55 printbuf_free_cps lh_table_length_spec lh_table_free_cps array_list_length_spec array_list_free_cps wb17544_1 joffb17544_1 D_b17544_1 E_b17544_1 LINK_b17544_1 CODE_e_blk_17544 AL_e_blk_17544_b4 RNG_e_blk_17544_code LAY_POS_e_fn_free_userdata LAY_HI_e_fn_free_userdata AL_e_fn_ud_to_json_string RNG_e_fn_ud_to_json_string LAY_POS_e_fn_ud_to_json_string LAY_HI_e_fn_ud_to_json_string CODE_e_187f8 CODE_e_17a68 CODE_e_17cb0 CODE_e_18a54 S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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
Section MF4.
Variable HIx : heap_iface S4L.
#[using="Type"] Lemma nodup_app_l : forall (BS LB : list blk), List.NoDup (map blk_addr (BS ++ LB)) -> List.NoDup (map blk_addr BS).
Proof. clear - HIx. intros BS LB ND. rewrite map_app in ND. exact (NoDup_app_remove_r _ _ ND). Qed.

#[using="w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_30 joff_34 joff_39 joff_41 joff_43 joff_51 joff_55 e_pbfree e_17a68 e_17cb0 e_187f8 e_18a54 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_30 E_30 D_34 E_34 D_39 E_39 D_41 E_41 D_43 E_43 D_51 E_51 D_55 E_55 LINK_30 LINK_34 LINK_39 LINK_41 LINK_43 LINK_51 LINK_55 printbuf_free_cps lh_table_length_spec lh_table_free_cps array_list_length_spec array_list_free_cps wb17544_1 D_b17544_1 E_b17544_1 LINK_b17544_1 CODE_e_blk_17544 AL_e_blk_17544_b4 RNG_e_blk_17544_code LAY_POS_e_fn_free_userdata LAY_HI_e_fn_free_userdata LAY_POS_e_fn_ud_to_json_string LAY_HI_e_fn_ud_to_json_string joffb17544_1"] Lemma maybe_free_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (s : jshape) (BS : list blk) (x rc : Z),
HEAP S4L HIx A (BS ++ LB) m md ->
x <> 0 -> 1 <= rc < 2^31 -> jval segs S4F s m BS x rc ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 0 ->
(forall ms1 md1, mf_post HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo errv s BS x rc ms1 md1 ->
realizes segs (mkCfg ms1 md1) T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_30 joff_34 joff_39 joff_41 joff_43 joff_51 joff_55 e_pbfree e_17a68 e_17cb0 e_187f8 e_18a54 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_30 E_30 D_34 E_34 D_39 E_39 D_41 E_41 D_43 E_43 D_51 E_51 D_55 E_55 LINK_30 LINK_34 LINK_39 LINK_41 LINK_43 LINK_51 LINK_55 printbuf_free_cps lh_table_length_spec lh_table_free_cps array_list_length_spec array_list_free_cps wb17544_1 D_b17544_1 E_b17544_1 LINK_b17544_1 CODE_e_blk_17544 AL_e_blk_17544_b4 RNG_e_blk_17544_code LAY_POS_e_fn_free_userdata LAY_HI_e_fn_free_userdata LAY_POS_e_fn_ud_to_json_string LAY_HI_e_fn_ud_to_json_string joffb17544_1 segs base gTP S4F HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until rc. intros HP Hx Hrc J ST LO LOS SPA HT ERR TP RA A0 A1 K.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (nodup_app_l BS LB (heap_blk_nodup S4L HIx _ _ _ _ HP)) as ND.
destruct (jval_hdr segs S4F s m BS x rc J ND) as (n & tojs & pb & udel & ud & rest & INx & SZ & N48 & HDR & CLOSE).
assert (INx2 : In (x, n) (BS ++ LB)) by (apply in_or_app; left; exact INx).
pose proof (heap_blk S4L HIx _ _ _ _ x n HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x n HP INx2) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (x + 4, x + 8)] m) as MU.
pose proof SZ as RSZ. rewrite cells_size_app in RSZ. cbn [cells_size csize jhdr_cells Nat.add] in RSZ.
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|]. subst a0 a1 tp.
carve_frame 32%nat ST.
step. step. step. step. step. step. norm_w32. step. norm_w32. stepz.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

assert (AG1 : agree_on segs (others x BS) m m1).
{ eapply (agree_others_gen segs); [exact MU | exact WM |].
intros a k Hin Hne.
pose proof (heap_blk S4L HIx _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ x n a k HP INx2 ltac:(apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
assert (HP1 : HEAP S4L HIx A (BS ++ LB) m1 md).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU).
apply Forall_cons; [cbn [fst snd]; left; split; [clia | pose proof (hi_top_hi S4L HIx); lia] |].
apply Forall_cons; [cbn [fst snd]; right; left; exists x, n; split; [exact INx2 | lia] | apply Forall_nil]. }
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |].
apply Forall_cons; [cbn [fst snd] | apply Forall_nil]. right; left. exists x, n. split; [exact INx2|]. split; [| lia].
exact (nodup_prefix_suffix BS LB x n n (heap_blk_nodup S4L HIx _ _ _ _ HP) INx). }
step.
destruct (Z.eq_dec rc 1) as [Hrc1 | Hrc2].
-
subst rc. if_true.
assert (J1 : jval segs S4F s m1 BS x 0).
{ apply (CLOSE m1 0); [| exact AG1]. unfold jhdr_cells. cbn [app]. replace (1 + -1) with 0 in HDR by lia. exact HDR. }
clear HDR CLOSE AG1 MU WM J.
pose proof (wmono_refl segs m1) as WM. pose proof (munch_refl [] m1) as MU.
destruct s as [|u| |h|kids|kids].
+
destruct J1 as (pb1 & PBS & REST & EBS & OPB & b & junkb & ER & HDR1). subst REST BS. cbn [app] in HP1.
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
step. step. if_true.
apply evt_RZ_done. eapply (mf_scalar HIx) with (n := 48);
[exact HP1 | unfold jhdr_cells; cbn [app]; exact HDR1 | reflexivity | left; reflexivity | exact OPB | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | exact K].
+ destruct u.
*
destruct J1 as (pb1 & PBS & REST & EBS & OPB & bits & ud1 & udn & uds & ER & HU & HDR1 & HC). subst REST.
apply evt_RZ_done. eapply (mf_dblu HIx);
[reflexivity | exact EBS | exact HP1 | exact OPB | exact HDR1 | exact HC | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | exact K].
*
destruct J1 as (pb1 & PBS & REST & EBS & OPB & bits & ER & HSP & HDR1). subst REST BS. cbn [app] in HP1.
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
step. step. if_true.
apply evt_RZ_done. eapply (mf_scalar HIx) with (n := 48);
[exact HP1 | unfold jhdr_cells; cbn [app]; exact HDR1 | reflexivity | right; left; reflexivity | exact OPB | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | exact K].
+
destruct J1 as (pb1 & PBS & REST & EBS & OPB & cty & v & junki & ER & HC & HDR1). subst REST BS. cbn [app] in HP1.
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
step. step. if_true.
apply evt_RZ_done. eapply (mf_scalar HIx) with (n := 56);
[exact HP1 | unfold jhdr_cells; cbn [app]; exact HDR1 | reflexivity | right; right; reflexivity | exact OPB | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | exact K].
+
pose proof J1 as J2. destruct h.
* destruct J2 as (pb1 & PBS & REST & EBS & OPB & len & pd & pdn & str & junk2 & ER & HL & HS & HPD & HDR1 & HD).
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
step. step. if_true.
apply evt_RZ_done. eapply (mf_str HIx) with (h := true);
[reflexivity | exact HP1 | exact J1 | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | exact K].
* destruct J2 as (pb1 & PBS & REST & EBS & OPB & len & str & junks & ER & HL & HS & HDR1).
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
step. step. if_true.
apply evt_RZ_done. eapply (mf_str HIx) with (h := false);
[reflexivity | exact HP1 | exact J1 | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | exact K].
+
destruct (jval_obj_open segs S4F kids m1 BS x 0 J1) as (pb1 & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR1 & LT & OK).
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
step. step. if_true.
apply evt_RZ_done. eapply (mf_obj HIx);
[reflexivity | exact HP1 | exact J1 | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | exact K].
+
destruct (jval_arr_open segs S4F kids m1 BS x 0 J1) as (pb1 & PBS & a & ABS & ps & KBS & EBS & OPB & HDR1 & AL & OK).
unfold jhdr_cells in HDR1. cbn [app] in HDR1.
step. step. if_true.
apply evt_RZ_done. eapply (mf_arr HIx);
[reflexivity | exact HP1 | exact J1 | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | exact K].
-
if_falsex. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp). step.
apply evt_RZ_done. apply K. unfold mf_post.
exists m1, A, 0.
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|]. split; [exact ST|]. split; [exact HPR1|]. split; [exact ERR|].
left. split; [reflexivity|]. split; [lia|]. split; [| exact HP1].
apply (CLOSE m1 (rc - 1)); [| exact AG1]. unfold jhdr_cells. cbn [app]. replace (rc - 1) with (rc + -1) by lia. exact HDR.
Qed.
End MF4.

End RC__1.

End G.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import Q6WR Q6WR.Mq0.
Import Q9Mh.Mq7.
Import Q9Mh.Mq5.
Import Q7mx.Mq1.
Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
Import Q0Hd.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition blk_18a54_code : list Z := [0x00452503; 0x00008067]%Z.

Definition blk_17cb0_code : list Z := [0x00853503; 0x00008067]%Z.

Definition blk_17bbc_code : list Z := [0x00050693; 0x00853503; 0x00a5fe63; 0x00000513; 0x0006b683; 0x00359593; 0x00b685b3; 0x00c5b023; 0x00008067; 0xfff00513; 0x00008067]%Z.

Definition blk_18934_code : list Z := [0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x01613023; 0x00058413; 0x00050493; 0x01053903; 0xffd00993; 0xffe00a13; 0x0184b583; 0x40b90b33; 0xfff00513; 0x0a0b4a63; 0x01658633; 0x00063603; 0x0ac9e463; 0x0044a503; 0x0204b603; 0x02093a83; 0xfff50513; 0x00a4a223; 0x00060863; 0x00090513; 0x000600e7; 0x0184b583; 0x0104b683; 0x0084b603; 0x01658533; 0x01453023; 0x00053823; 0x00a68e63; 0x02a60663; 0x01853583; 0x02053603; 0x00b63c23; 0x02c5b023; 0x0300006f; 0x02a60263; 0x0206b583; 0x0005bc23; 0x00b4b823; 0x01c0006f; 0x01863583]%Z.

Definition blk_17cb8_code : list Z := [0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x00060413; 0x00050493; 0xfff64613; 0xfff00513; 0x08b66063; 0x0084b603; 0x06c5fc63; 0x00b40933; 0x07266863; 0x00359993; 0x0325fe63; 0x00098a13; 0x00040a93; 0x0100006f; 0xfffa8a93; 0x008a0a13; 0x020a8063; 0x0004b503; 0x01450533; 0x00053503; 0xfe0504e3; 0x0184b583; 0x000580e7; 0xfddff06f; 0x0084b603; 0x0004b583; 0x00391693; 0x41260633; 0x01358533; 0x00d585b3; 0x00361613]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 : Z).
Variables (joff_24 joff_26 joff_28 joff_34 joff_39 joff_57 joff_63 joff_89 joff_97 joff_101 joff_106 : bv 21).
Variables (e_pbfree e_alfree e_alread e_17bbc e_17cb0 e_17cb8 e_lhfree e_18934 e_18a54 : Z).
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
Hypothesis CODE : code_at segs base (putloop1_code w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 488.
Hypothesis D_24 : decode_any (Z_to_bv 32 w_24) = Some (Jal 1 joff_24, 4%Z).
Hypothesis E_24 : is_ecall (Z_to_bv 32 w_24) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Jal 1 joff_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_28 : decode_any (Z_to_bv 32 w_28) = Some (Jal 1 joff_28, 4%Z).
Hypothesis E_28 : is_ecall (Z_to_bv 32 w_28) = false.
Hypothesis D_34 : decode_any (Z_to_bv 32 w_34) = Some (Jal 1 joff_34, 4%Z).
Hypothesis E_34 : is_ecall (Z_to_bv 32 w_34) = false.
Hypothesis D_39 : decode_any (Z_to_bv 32 w_39) = Some (Jal 1 joff_39, 4%Z).
Hypothesis E_39 : is_ecall (Z_to_bv 32 w_39) = false.
Hypothesis D_57 : decode_any (Z_to_bv 32 w_57) = Some (Jal 1 joff_57, 4%Z).
Hypothesis E_57 : is_ecall (Z_to_bv 32 w_57) = false.
Hypothesis D_63 : decode_any (Z_to_bv 32 w_63) = Some (Jal 1 joff_63, 4%Z).
Hypothesis E_63 : is_ecall (Z_to_bv 32 w_63) = false.
Hypothesis D_89 : decode_any (Z_to_bv 32 w_89) = Some (Jal 1 joff_89, 4%Z).
Hypothesis E_89 : is_ecall (Z_to_bv 32 w_89) = false.
Hypothesis D_97 : decode_any (Z_to_bv 32 w_97) = Some (Jal 1 joff_97, 4%Z).
Hypothesis E_97 : is_ecall (Z_to_bv 32 w_97) = false.
Hypothesis D_101 : decode_any (Z_to_bv 32 w_101) = Some (Jal 1 joff_101, 4%Z).
Hypothesis E_101 : is_ecall (Z_to_bv 32 w_101) = false.
Hypothesis D_106 : decode_any (Z_to_bv 32 w_106) = Some (Jal 1 joff_106, 4%Z).
Hypothesis E_106 : is_ecall (Z_to_bv 32 w_106) = false.
Hypothesis LINK_24 : gw_anch (base + 96 + bv_signed joff_24)%Z (e_alfree + 0)%Z.
Hypothesis LINK_26 : gw_anch (base + 104 + bv_signed joff_26)%Z (e_pbfree + 0)%Z.
Hypothesis LINK_28 : gw_anch (base + 112 + bv_signed joff_28)%Z e_free.
Hypothesis LINK_34 : gw_anch (base + 136 + bv_signed joff_34)%Z (e_18a54 + 0)%Z.
Hypothesis LINK_39 : gw_anch (base + 156 + bv_signed joff_39)%Z (e_17cb0 + 0)%Z.
Hypothesis LINK_57 : gw_anch (base + 228 + bv_signed joff_57)%Z (e_alread + 0)%Z.
Hypothesis LINK_63 : gw_anch (base + 252 + bv_signed joff_63)%Z (e_17bbc + 0)%Z.
Hypothesis LINK_89 : gw_anch (base + 356 + bv_signed joff_89)%Z (e_lhfree + 0)%Z.
Hypothesis LINK_97 : gw_anch (base + 388 + bv_signed joff_97)%Z (e_18934 + 0)%Z.
Hypothesis LINK_101 : gw_anch (base + 404 + bv_signed joff_101)%Z (e_17cb8 + 0)%Z.
Hypothesis LINK_106 : gw_anch (base + 424 + bv_signed joff_106)%Z e_free.

Hypothesis lh_table_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QAyu.Mq2.gw_all) (@QAyu.Mq2.lh_table_free_cps) e_lhfree)) in exact T).

Definition next_post := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let t := eval cbv beta delta [Q7mx.Mq1.next_post] in t in exact t).

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
Hypothesis CODE_e_18a54 : code_at segs e_18a54 blk_18a54_code.
Hypothesis CODE_e_17cb0 : code_at segs e_17cb0 blk_17cb0_code.
Hypothesis CODE_e_17bbc : code_at segs e_17bbc blk_17bbc_code.
Hypothesis CODE_e_18934 : code_at segs e_18934 blk_18934_code.
Hypothesis CODE_e_17cb8 : code_at segs e_17cb8 blk_17cb8_code.
Hypothesis AL_e_fn_arr_to_json_string : gw_b4 e_fn_arr_to_json_string.
Hypothesis RNG_e_fn_arr_to_json_string : gw_br e_fn_arr_to_json_string 4.
Hypothesis LAY_POS_e_fn_arr_to_json_string : gw_le 1 e_fn_arr_to_json_string.
Hypothesis LAY_HI_e_fn_arr_to_json_string : gw_le (e_fn_arr_to_json_string + 4) 1099511627776.
Hypothesis AL_e_fn_obj_to_json_string : gw_b4 e_fn_obj_to_json_string.
Hypothesis RNG_e_fn_obj_to_json_string : gw_br e_fn_obj_to_json_string 4.
Hypothesis LAY_POS_e_fn_obj_to_json_string : gw_le 1 e_fn_obj_to_json_string.
Hypothesis LAY_HI_e_fn_obj_to_json_string : gw_le (e_fn_obj_to_json_string + 4) 1099511627776.
#[using="w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 joff_24 joff_26 joff_28 joff_34 joff_39 joff_57 joff_63 joff_89 joff_97 joff_101 joff_106 e_pbfree e_alfree e_alread e_17bbc e_17cb0 e_17cb8 e_lhfree e_18934 e_18a54 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_24 E_24 D_26 E_26 D_28 E_28 D_34 E_34 D_39 E_39 D_57 E_57 D_63 E_63 D_89 E_89 D_97 E_97 D_101 E_101 D_106 E_106 LINK_24 LINK_26 LINK_28 LINK_34 LINK_39 LINK_57 LINK_63 LINK_89 LINK_97 LINK_101 LINK_106 lh_table_free_cps CODE_e_18a54 CODE_e_17cb0 CODE_e_17bbc CODE_e_18934 CODE_e_17cb8 AL_e_fn_arr_to_json_string RNG_e_fn_arr_to_json_string LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string AL_e_fn_obj_to_json_string RNG_e_fn_obj_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

Section Loop2.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (sp gp s10 s11 : word) (lo : Z) (errv : word).

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -96)).
Notation TP := (Z_to_bv 64 gTP).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation NEXT := (next_post HIx sp gp s10 s11 lo errv).

Definition tyof (isobj : bool) : Z := if isobj then 4 else 5.

Definition zhead (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (XBS : list blk) : Prop :=
if isobj then zobjc segs S4F m x q kids XBS else zarrc segs S4F m x q kids XBS.

Definition head_stmt (isobj : bool) (kids : list (option jshape)) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS : list blk) (x q : Z) (T : TSet),
HEAPx A (XBS ++ LB) m md ->
zhead isobj m x q kids XBS ->
stk segs m lo (bv_unsigned sp + -96) -> rw_cells segs m (gTP - 164) [C4 errv] ->
(forall ms' md', NEXT q F1 fc1 m md LB ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x7c)) fc1 None m (seg_rom segs)) md) T.

Definition desc_stmt (c : jshape) : Prop :=
match c with Sobj kids => head_stmt true kids | Sarr kids => head_stmt false kids | _ => True end.
Definition desc_opt (k : option jshape) : Prop := match k with Some c => desc_stmt c | None => True end.
Definition kids_desc (kids : list (option jshape)) : Prop := forall k, In k kids -> desc_opt k.

Definition zcont (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (nz : nat) (cur : Z) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs, zobj segs S4F m x q kids nz t tbl size es svs XBS /\
(forall kids1 kl, kids = kids1 ++ [kl] -> exists e, nth_error es (length kids1) = Some e /\ cur = ent_addr tbl (le_ix e))
else exists a arr size, zarr segs S4F m x q kids nz a arr size XBS.

Definition cont_stmt (isobj : bool) (kids : list (option jshape)) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS : list blk) (x q : Z) (T : TSet) (nz : nat) (cur : Z),
HEAPx A (XBS ++ LB) m md ->
zcont isobj m x q kids nz cur XBS ->
stk segs m lo (bv_unsigned sp + -96) -> rw_cells segs m (gTP - 164) [C4 errv] ->
(forall ms' md', NEXT q F1 fc1 m md LB ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 (Z_to_bv 64 (tyof isobj)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz))
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0xb8)) fc1 None m (seg_rom segs)) md) T.

Definition zbodyp (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (k : option jshape) (nz : nat) (cur : Z) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs e, zobj segs S4F m x q (kids ++ [k]) nz t tbl size es svs XBS /\
nth_error es (length kids) = Some e /\ cur = ent_addr tbl (le_ix e)
else exists a arr size, zarr segs S4F m x q (kids ++ [k]) nz a arr size XBS.

Definition body_stmt (isobj : bool) (kids : list (option jshape)) (k : option jshape) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS : list blk) (x q : Z) (T : TSet) (nz : nat) (cur : Z),
HEAPx A (XBS ++ LB) m md ->
zbodyp isobj m x q kids k nz cur XBS ->
stk segs m lo (bv_unsigned sp + -96) -> rw_cells segs m (gTP - 164) [C4 errv] ->
(forall ms' md', NEXT q F1 fc1 m md LB ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 (Z_to_bv 64 (tyof isobj)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0xc4)) fc1 None m (seg_rom segs)) md) T.

Definition tojs_of (isobj : bool) : Z := if isobj then fn_obj_to_json_string S4F else fn_arr_to_json_string S4F.

#[using="Type"] Lemma zhead_hdr : forall isobj m x q kids XBS,
zhead isobj m x q kids XBS -> List.NoDup (map blk_addr XBS) ->
exists pb cf, In (x, 48) XBS /\
rw_cells segs m x (jhdr_cells (tyof isobj) 0 (tojs_of isobj) pb 0 q ++ [C8 (Z_to_bv 64 cf)]) /\
(forall m' q', rw_cells segs m' x (jhdr_cells (tyof isobj) 0 (tojs_of isobj) pb 0 q' ++ [C8 (Z_to_bv 64 cf)]) ->
agree_on segs (others x XBS) m m' -> zhead isobj m' x q' kids XBS).
Proof. clear - segs HIx sp gp s10 s11 lo errv. intros isobj. destruct isobj; [apply zobjc_hdr | apply zarrc_hdr]. Qed.

#[using="Type"] Lemma zhead_agree : forall isobj BS m m' x q kids XBS,
zhead isobj m x q kids XBS -> agree_on segs BS m m' -> incl XBS BS -> zhead isobj m' x q kids XBS.
Proof. clear - segs HIx sp gp s10 s11 lo errv. intros isobj. destruct isobj; [apply zobjc_agree | apply zarrc_agree]. Qed.

#[using="Type"] Lemma zomb_zhead : forall c m v bs, zomb segs S4F c m v bs -> desc_stmt c ->
exists isobj ck, zhead isobj m v 0 ck bs /\ head_stmt isobj ck.
Proof. clear - segs S4F HIx sp gp s10 s11 lo errv.
intros c m v bs ZC KD. destruct c as [| | | |ck|ck]; cbn in ZC; try contradiction.
- exists true, ck. split; [exact (proj2 ZC) | exact KD].
- exists false, ck. split; [exact (proj2 ZC) | exact KD].
Qed.

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string"] Lemma next_post_w : forall q F1 fc1 F2 fc2 m1 m2 md1 md2 LB ms md,
fsaved F1 F2 -> (frm0 fc1 -> frm0 fc2) -> model_vm_only md1 md2 ->
heap_pres S4L LB (bv_unsigned sp + -96) m1 m2 ->
NEXT q F2 fc2 m2 md2 LB ms md -> NEXT q F1 fc1 m1 md1 LB ms md.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string HIx sp gp s10 s11 lo errv. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_arr_to_json_string as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_arr_to_json_string as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_obj_to_json_string as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_obj_to_json_string as gL5_; unfold gw_le in gL5_.
intros until md. intros FS FRM VM HPR NP. unfold next_post in *.
destruct NP as (m' & A' & F' & fc' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & E & FS' & FRM' & VM' & HP' & ST' & HPR' & ERR').
exists m', A', F', fc'. do 20 eexists. split; [exact E|].
split; [eapply fsaved_trans; [exact FS | exact FS']|]. split; [intros Hf; exact (FRM' (FRM Hf))|].
split; [eapply model_vm_only_trans; [exact VM | exact VM']|]. split; [exact HP'|]. split; [exact ST'|].
split; [eapply heap_pres_trans; [exact HPR | exact HPR'] | exact ERR'].
Qed.
End Loop2.

End RC__1.

End G.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7mx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7mx.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma nx_of_app_lt : forall tbl es e' j, (S j < length es)%nat -> nx_of tbl (es ++ [e']) j = nx_of tbl es j.
Proof. intros. unfold nx_of. rewrite nth_error_app1 by lia. reflexivity. Qed.

Lemma nx_of_app_new : forall tbl es e' j, (j = length es)%nat -> nx_of tbl (es ++ [e']) j = 0.
Proof. intros. unfold nx_of. rewrite nth_error_app2 by lia. replace (S j - length es)%nat with 1%nat by lia. reflexivity. Qed.
Lemma nx_of_last : forall tbl es j, (S j = length es)%nat -> nx_of tbl es j = 0.
Proof. intros. unfold nx_of. destruct (nth_error es (S j)) eqn:E; [|reflexivity].
exfalso. pose proof (proj1 (nth_error_Some es (S j)) ltac:(rewrite E; discriminate)). lia. Qed.
Lemma pv_of_app_le : forall tbl es e' j, (j <= length es)%nat -> pv_of tbl (es ++ [e']) j = pv_of tbl es j.
Proof. intros. unfold pv_of. destruct j; [reflexivity|]. rewrite nth_error_app1 by lia. reflexivity. Qed.

Lemma last_nth_error : forall (es : list lent) j e d, nth_error es j = Some e -> (S j = length es)%nat -> last es d = e.
Proof.
induction es as [|a es IH]; intros j e d E Hj; [discriminate|].
destruct es as [|b es'].
- cbn in Hj. assert (j = 0%nat) by lia. subst j. cbn in E. injection E as ->. reflexivity.
- destruct j as [|j]; [cbn in Hj; lia|]. cbn in E. change (last (a :: b :: es') d) with (last (b :: es') d).
eapply IH; [exact E|]. cbn in Hj |- *. lia.
Qed.
Lemma tl_of_last : forall tbl es j e, nth_error es j = Some e -> (S j = length es)%nat -> tl_of tbl es = ent_addr tbl (le_ix e).
Proof.
intros tbl es j e E Hj. unfold tl_of. destruct es as [|e0 es'] eqn:EES; [discriminate|]. rewrite <- EES in *.
rewrite (last_nth_error es j e _ E Hj). reflexivity.
Qed.
Lemma tl_of_app : forall tbl es e', tl_of tbl (es ++ [e']) = ent_addr tbl (le_ix e').
Proof. intros. unfold tl_of. destruct (es ++ [e']) eqn:E; [destruct es; discriminate|]. rewrite <- E, last_last. reflexivity. Qed.

Section Snoc.
Variables (tbl : Z) (es : list lent) (svs : list slotv) (g : nat) (sg : slotv) (k kn : Z) (ks : list byte) (v : Z).
Let e' := LE g k kn ks v.

Hypothesis LINK : lh_link tbl es svs.
Hypothesis Hg : (g < length svs)%nat.
Hypothesis Esg : nth_error svs g = Some sg.
Hypothesis FREE : ~ In g (map le_ix es).
Hypothesis Hk : 0 < k /\ k + kn < LH_FREEDv /\ kn <= 2^31.
Hypothesis Hv : 0 <= v < 2^64.
Hypothesis Htbl : 0 < tbl.

End Snoc.

Section OpenSnoc.
Variable segs : list Segment.
Variable fn : fnaddrs.

End OpenSnoc.
