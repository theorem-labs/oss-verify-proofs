(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo QPIU Q8tj QSL3 QAyu QnCn Q6WR Q9Mh Q6q3 Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply2 Lib.GwApplyJ.
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
Import QSL3.
Import QPIU.Mqb.
Import QAyu.Mq2.
Import QnCn.Mq0.
Import QPIU.Mq2.
Import QPIU.Mq0.
Import Q6WR Q6WR.Mq0.
Import Q9Mh.Mq5.
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

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

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
#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma gLAYF0 : ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gTP gIMG_LO gIMG_HI. pose proof LAY_TPLO as X1; pose proof LAY_TPHI as X2; unfold gw_le in X1, X2. split; [split; [exact X1 | exact X2] | exact LAY_gIMG_LO]. Qed.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Variables (e_strcmp : Z).
Let e_blk_18a54 : Z := e_18a54.
Let e_blk_17cb0 : Z := e_17cb0.
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

Hypothesis lh_table_length_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqb.gw_all) (@QPIU.Mqb.lh_table_length_spec) (base + 8444)%Z)) in let T := eval cbv beta delta [QPIU.Mqb.lh_table_length_entry QPIU.Mqb.lh_char_equal_entry] in T in let T := gw_fold_pcs T base (8444)%Z [0]%Z in exact T).

Hypothesis lh_table_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QAyu.Mq2.gw_all) (@QAyu.Mq2.lh_table_free_cps) e_187f8)) in exact T).

Hypothesis array_list_length_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mq2.gw_all) (@QPIU.Mq2.array_list_length_spec) (base + 6052)%Z)) in let T := eval cbv beta delta [QPIU.Mq2.array_list_length_entry QPIU.Mq2.array_list_get_idx_entry] in T in let T := gw_fold_pcs T base (6052)%Z [0]%Z in exact T).

Hypothesis array_list_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mq0.gw_all) (@QPIU.Mq0.array_list_free_cps) e_17a68)) in exact T).

Hypothesis printbuf_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqd.gw_all) (@QPIU.Mqd.printbuf_free_cps) e_pbfree)) in exact T).

Definition mf_post := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_post))) in let t := eval cbv beta delta [Q9Mh.Mq5.mf_post] in t in exact t).
Definition mf_frame := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_frame))) in let t := eval cbv beta delta [Q9Mh.Mq5.mf_frame] in t in let x := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_post))) in let t := gw_subst t x mf_post in exact t).
Definition KPOST := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.KPOST))) in let t := eval cbv beta delta [Q9Mh.Mq5.KPOST] in t in let x := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_post))) in let t := gw_subst t x mf_post in let x := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_frame))) in let t := gw_subst t x mf_frame in exact t).
Definition mf_gen := ltac:(let p := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_gen))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_post))) in let T := gw_subst T x mf_post in let x := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.mf_frame))) in let T := gw_subst T x mf_frame in let x := constr:(ltac:(gw_ctx2 (@Q9Mh.Mq5.KPOST))) in let T := gw_subst T x KPOST in exact (p : T)).

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
#[using="w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_30 joff_34 joff_39 joff_41 joff_43 joff_51 joff_55 e_pbfree e_17a68 e_17cb0 e_187f8 e_18a54 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free e_strcmp CODE BASE4 BASER D_30 E_30 D_34 E_34 D_39 E_39 D_41 E_41 D_43 E_43 D_51 E_51 D_55 E_55 LINK_30 LINK_34 LINK_39 LINK_41 LINK_43 LINK_51 LINK_55 lh_table_length_spec lh_table_free_cps array_list_length_spec array_list_free_cps printbuf_free_cps CODE_e_187f8 CODE_e_17a68 CODE_e_17cb0 CODE_e_18a54 S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

Section MF3.
Variable HIx : heap_iface S4L.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo : Z) (errv : word) (s : jshape) (BS : list blk) (x rc : Z) (T : TSet).

#[using="w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_30 joff_41 joff_43 joff_55 e_pbfree e_17cb0 e_187f8 e_18a54 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_30 E_30 D_41 E_41 D_43 E_43 D_55 E_55 LINK_30 LINK_41 LINK_43 LINK_55 lh_table_length_spec lh_table_free_cps printbuf_free_cps"] Lemma mf_obj : forall (kids : list (option jshape))
(x1 t0 t1 t2 x9 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (junk8 : list byte),
s = Sobj kids ->
HEAP S4L HIx A (BS ++ LB) m md ->
jval segs S4F s m BS x 0 ->
mf_frame ra sp s0 s1 m junk8 ->
stk segs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -32 - 32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
KPOST HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo errv s BS x rc T ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x4c)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_30 joff_41 joff_43 joff_55 e_pbfree e_17cb0 e_187f8 e_18a54 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_30 E_30 D_41 E_41 D_43 E_43 D_55 E_55 LINK_30 LINK_41 LINK_43 LINK_55 lh_table_length_spec lh_table_free_cps printbuf_free_cps segs base gTP S4F HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo errv s BS x rc T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until junk8. intros Hs HP J FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc K.
unfold mf_frame in FR. unfold_consts. word_range sp SPR. subst s.
destruct (jval_obj_open segs S4F kids m BS x 0 J) as (pb & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR & LT & OK). clear J.
rewrite EBS, <- app_assoc in HP. cbn [app] in HP.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(x, x + 40)] m) as MU.
unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 L2]. rewrite length_map in L1.
apply rz_evt; [exact MOK|].
step. norm_w32. step. stepz. stepz. step. if_falsex. step. step. if_falsex. step. step. if_falsex. step. if_true. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp) HP MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; in_sub Hb) ltac:(clia))
as (HP2 & AG2 & HPR2).
assert (LT2 : lhtab2 segs S4F m2 TBS t kvs).
{ eapply lhtab2_agree; [exact LT | exact AG2 | intros b Hb; in_sub Hb]. }
call lh_table_length_spec; [exact MI | exact LT2 | reflexivity |].
clear HP2 AG2 HPR2 LT2. rename x0 into m3. rename MI0 into MI.
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp) HP MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; in_sub Hb) ltac:(clia))
as (HP3 & AG3 & HPR3).
step.
destruct kids as [|k0 kids1].
- destruct kvs as [|kv kvs1]; [| cbn in L1; discriminate]. destruct KBS as [|bs KBS1]; [| cbn in L2; discriminate].
cbn [length Z.of_nat]. if_true. step. step.
assert (LT3 : lhtab2 segs S4F m3 TBS t []) by (eapply lhtab2_agree; [exact LT | exact AG3 | intros b Hb; in_sub Hb]).
destruct LT3 as (tbl & size & es & svs & Ekvs & ETBS & OPEN).
destruct es as [|e0 es1]; [| cbn in Ekvs; discriminate]. subst TBS. cbn [concat app] in HP3.
apply evt_RZ_done.
eapply (lh_table_free_cps HIx) with (LB := (x, 48) :: PBS ++ LB) (lo := lo) (kvs:=[]) (tbl := tbl) (size := size) (es := []) (svs := svs);
[ eapply (heap_perm S4L HIx); [exact HP3 | unfold lh_blocks; cbn [map app]; perm] | exact OPEN | intros e He; destruct He | .. ]; try alloc_side.
intros ms4 md4 (m4 & A4 & r4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & HP4).
destruct RS4 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F4 & fc4 & -> & FS4 & FRM4).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR4 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
assert (OPB4 : opt_pbuf segs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
- eapply agree_on_incl; [exact AG3 | intros b Hb; in_sub Hb].
- eapply (agree_of_heap_pres segs S4L); [exact HPR4 | reflexivity | intros b Hb; in_sub Hb]. }
assert (HPRb : heap_pres S4L LB (bv_unsigned sp) m0 m4).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans; [exact HPR3|].
eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; in_sub Hb]. }
clear MU WM MI ST HPR HPR3 AG3 HP3.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
reenter MOK4. step.
apply evt_RZ_done.
eapply mf_gen; [exact HP4 | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB4 | exact FR | exact ST4 | clia | clia | exact SPA | exact HT
| exact ERR4 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM4] | exact HPRb
| eapply fsaved_trans; [exact FS | exact FS4] | intros Hf; exact (FRM4 (FRM Hf)) | exact Hrc | ].
subst BS. exact K.
- assert (LT3 : lhtab2 segs S4F m3 TBS t kvs) by (eapply lhtab2_agree; [exact LT | exact AG3 | intros b Hb; in_sub Hb]).
assert (OK3 : okids segs S4F m3 (k0 :: kids1) (map snd kvs) KBS) by (eapply okids_agree; [exact OK | exact AG3 | intros b Hb; in_sub Hb]).
assert (OPB3 : opt_pbuf segs m3 PBS pb) by (eapply opt_pbuf_agree; [exact OPB | exact AG3 | intros b Hb; in_sub Hb]).
clear LT OK OPB.
destruct LT3 as (tbl & size & es & svs & Ekvs & ETBS & OPEN).
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & _).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
assert (LK : length kvs = length es) by (rewrite Ekvs; apply length_map).
cbn [length] in L1. rewrite L1 in LK.
if_falsex.
step. step. step. step. step. step. release_frame FR ST (bv_unsigned sp). step.
apply evt_RZ_done. apply K. unfold mf_post.
exists m3, A, 2.
split; [apply ret_statew_intro; [exact FS | exact FRM] |].
split; [exact VM0|]. split; [exact ST|]. split; [eapply heap_pres_trans; [exact HPR | exact HPR3]|]. split; [exact ERR|].
right; right. split; [reflexivity|]. split; [exact Hrc|]. split.
+ split; [discriminate|]. exists t, tbl, size, es, svs. exists pb, PBS, KBS, es, (@nil lent).
split; [rewrite app_nil_r; reflexivity|]. split; [reflexivity|]. split; [apply Forall_nil|].
split; [rewrite EBS, ETBS; reflexivity|]. split; [exact OPB3|]. split; [unfold jhdr_cells; cbn [app]; exact HDR|]. split; [exact OPEN|].
replace (map le_v es) with (map snd kvs); [exact OK3|]. rewrite Ekvs, map_map. reflexivity.
+ rewrite EBS, <- app_assoc. cbn [app]. exact HP3.
Qed.

#[using="w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_34 joff_41 joff_43 joff_51 e_pbfree e_17a68 e_17cb0 e_18a54 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_34 E_34 D_41 E_41 D_43 E_43 D_51 E_51 LINK_34 LINK_41 LINK_43 LINK_51 array_list_length_spec array_list_free_cps printbuf_free_cps"] Lemma mf_arr : forall (kids : list (option jshape))
(x1 t0 t1 t2 x9 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (junk8 : list byte),
s = Sarr kids ->
HEAP S4L HIx A (BS ++ LB) m md ->
jval segs S4F s m BS x 0 ->
mf_frame ra sp s0 s1 m junk8 ->
stk segs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -32 - 32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
KPOST HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo errv s BS x rc T ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x4c)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_34 joff_41 joff_43 joff_51 e_pbfree e_17a68 e_17cb0 e_18a54 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_34 E_34 D_41 E_41 D_43 E_43 D_51 E_51 LINK_34 LINK_41 LINK_43 LINK_51 array_list_length_spec array_list_free_cps printbuf_free_cps segs base gTP S4F HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo errv s BS x rc T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until junk8. intros Hs HP J FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc K.
unfold mf_frame in FR. unfold_consts. word_range sp SPR. subst s.
destruct (jval_arr_open segs S4F kids m BS x 0 J) as (pb & PBS & a & ABS & ps & KBS & EBS & OPB & HDR & AL & OK). clear J.
rewrite EBS, <- app_assoc in HP. cbn [app] in HP.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(x, x + 40)] m) as MU.
unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 L2].
apply rz_evt; [exact MOK|].
step. norm_w32. step. stepz. stepz. step. if_falsex. step. step. if_truex. step. if_true. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp) HP MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; in_sub Hb) ltac:(clia))
as (HP2 & AG2 & HPR2).
assert (AL2 : alist segs S4F m2 ABS a ps).
{ eapply alist_agree; [exact AL | exact AG2 | intros b Hb; in_sub Hb]. }
call array_list_length_spec; [exact MI | exact AL2 | reflexivity |].
clear HP2 AG2 HPR2 AL2. rename x0 into m3. rename MI0 into MI.
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp) HP MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; in_sub Hb) ltac:(clia))
as (HP3 & AG3 & HPR3).
assert (AL3 : alist segs S4F m3 ABS a ps) by (eapply alist_agree; [exact AL | exact AG3 | intros b Hb; in_sub Hb]).
assert (OK3 : okids segs S4F m3 kids ps KBS) by (eapply okids_agree; [exact OK | exact AG3 | intros b Hb; in_sub Hb]).
assert (OPB3 : opt_pbuf segs m3 PBS pb) by (eapply opt_pbuf_agree; [exact OPB | exact AG3 | intros b Hb; in_sub Hb]).
clear AL OK OPB.
step.
destruct kids as [|k0 kids1].
- destruct ps as [|p0 ps1]; [| cbn in L1; discriminate]. destruct KBS as [|bs KBS1]; [| cbn in L2; discriminate].
cbn [length Z.of_nat]. if_false. step. step. step. cbn [concat app] in HP3.
apply evt_RZ_done.
eapply (array_list_free_cps HIx) with (LB := (x, 48) :: PBS ++ LB) (lo := lo) (BS := ABS) (ps := []);
[ eapply (heap_perm S4L HIx); [exact HP3 | perm] | exact AL3 | apply Forall_nil | .. ]; try alloc_side.
intros ms4 md4 (m4 & A4 & r4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & HP4).
destruct RS4 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F4 & fc4 & -> & FS4 & FRM4).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR4 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
assert (OPB4 : opt_pbuf segs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB3 | | apply incl_refl].
eapply (agree_of_heap_pres segs S4L); [exact HPR4 | reflexivity | intros b Hb; in_sub Hb]. }
assert (HPRb : heap_pres S4L LB (bv_unsigned sp) m0 m4).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans; [exact HPR3|].
eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; in_sub Hb]. }
clear MU WM MI ST HPR HPR3 AG3 HP3.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
reenter MOK4. step.
apply evt_RZ_done.
eapply mf_gen; [exact HP4 | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB4 | exact FR | exact ST4 | clia | clia | exact SPA | exact HT
| exact ERR4 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM4] | exact HPRb
| eapply fsaved_trans; [exact FS | exact FS4] | intros Hf; exact (FRM4 (FRM Hf)) | exact Hrc | ].
subst BS. exact K.
- pose proof AL3 as (arr & size & junk & EABS & Hlen & Hsz & _).
cbn [length] in L1.
if_truex.
step. step. step. step. step. step. release_frame FR ST (bv_unsigned sp). step.
apply evt_RZ_done. apply K. unfold mf_post.
exists m3, A, 2.
split; [apply ret_statew_intro; [exact FS | exact FRM] |].
split; [exact VM0|]. split; [exact ST|]. split; [eapply heap_pres_trans; [exact HPR | exact HPR3]|]. split; [exact ERR|].
right; right. split; [reflexivity|]. split; [exact Hrc|]. split.
+ split; [discriminate|]. exists a, arr, size. exists pb, PBS, KBS, ps.
split; [rewrite EBS, EABS; reflexivity|]. split; [exact OPB3|]. split; [unfold jhdr_cells; cbn [app]; exact HDR|].
split; [cbn [repeat]; rewrite app_nil_r; rewrite <- EABS; exact AL3 | exact OK3].
+ rewrite EBS, <- app_assoc. cbn [app]. exact HP3.
Qed.
End MF3.

End RC__1.

End G.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg Q8Q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo.
Import QPIU.Mqd.
Import Q8tj.
Import QSL3.
Import QPIU.Mqb.
Import QAyu.Mq2.
Import Q8Q3.
Import QnCn.Mq0.
Import QPIU.Mq2.
Import QPIU.Mq0.
Import Q6WR Q6WR.Mq0.
Import Q9Mh.Mq7.
Import Q9Mh.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition putloop1_code (w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 : Z) : list Z :=
[0x1e050263; 0xfa010113; 0x04113c23; 0x04813823; 0x04913423; 0x05213023; 0x03313c23; 0x03413823; 0x03513423; 0x03613023; 0x01713c23; 0x01813823; 0x01913423; 0x00050413; 0x00000593; 0x1ac000ef; 0x00200a93; 0x17551863; 0x00400b13; 0x00600b93; 0x00500c13; 0xfff00c93; 0x0240006f; 0x02843503; w_24; 0x01043503; w_26; 0x00040513; w_28; 0x00048413; 0x12048c63; 0x00042583; 0x02843503; 0x01659c63; w_34; 0x02843583; 0x0105b903; 0x00051a63; 0x0900006f; w_39; 0x00000913; 0x08050263; 0x00042583; 0xfff50993; 0x00100a13; 0x0100006f; 0xfff98993; 0x001a0a13; 0x07998463; 0x01858c63; 0xff6598e3; 0x01093483; 0x00093823; 0x02049863; 0x03c0006f; 0x02843503; 0x00098593; w_57; 0x02843583; 0x00050493; 0x00058513; 0x00098593; 0x00000613; w_63; 0x00048a63; 0x00048513; 0x00000593; 0x0dc000ef; 0x05550e63; 0x00042583; 0xfb6590e3; 0x02093903; 0x00400593; 0xf95ff06f; 0x00442503; 0x02043483; 0xf40512e3; 0x01843603; 0x00060863; 0x00040513; 0x00048593; 0x000600e7; 0x00042503; 0x00043c23; 0x02043023; 0x05750463; 0xf18502e3; 0xf16514e3; 0x02843503; w_89; 0xefdff06f; 0x0004bc23; 0x0284b023; 0x00042583; 0x02843503; 0x01659863; 0x00090593; w_97; 0xeedff06f; 0x00098593; 0x000a0613; w_101; 0xeddff06f; 0x02843503; 0xec0552e3; 0x03043503; w_106; 0xeb9ff06f; 0x00100513; 0x05813083; 0x05013403; 0x04813483; 0x04013903; 0x03813983; 0x03013a03; 0x02813a83; 0x02013b03; 0x01813b83; 0x01013c03; 0x00813c83; 0x06010113; 0x00008067]%Z.

Definition blk_18a54_code : list Z := [0x00452503; 0x00008067]%Z.

Definition blk_17cb0_code : list Z := [0x00853503; 0x00008067]%Z.

Definition blk_17bbc_code : list Z := [0x00050693; 0x00853503; 0x00a5fe63; 0x00000513; 0x0006b683; 0x00359593; 0x00b685b3; 0x00c5b023; 0x00008067; 0xfff00513; 0x00008067]%Z.

Definition blk_18934_code : list Z := [0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x01613023; 0x00058413; 0x00050493; 0x01053903; 0xffd00993; 0xffe00a13; 0x0184b583; 0x40b90b33; 0xfff00513; 0x0a0b4a63; 0x01658633; 0x00063603; 0x0ac9e463; 0x0044a503; 0x0204b603; 0x02093a83; 0xfff50513; 0x00a4a223; 0x00060863; 0x00090513; 0x000600e7; 0x0184b583; 0x0104b683; 0x0084b603; 0x01658533; 0x01453023; 0x00053823; 0x00a68e63; 0x02a60663; 0x01853583; 0x02053603; 0x00b63c23; 0x02c5b023; 0x0300006f; 0x02a60263; 0x0206b583; 0x0005bc23; 0x00b4b823; 0x01c0006f; 0x01863583]%Z.

Definition blk_17cb8_code : list Z := [0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x00060413; 0x00050493; 0xfff64613; 0xfff00513; 0x08b66063; 0x0084b603; 0x06c5fc63; 0x00b40933; 0x07266863; 0x00359993; 0x0325fe63; 0x00098a13; 0x00040a93; 0x0100006f; 0xfffa8a93; 0x008a0a13; 0x020a8063; 0x0004b503; 0x01450533; 0x00053503; 0xfe0504e3; 0x0184b583; 0x000580e7; 0xfddff06f; 0x0084b603; 0x0004b583; 0x00391693; 0x41260633; 0x01358533; 0x00d585b3; 0x00361613]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

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
#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma gLAYF0 : ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gTP gIMG_LO gIMG_HI. pose proof LAY_TPLO as X1; pose proof LAY_TPHI as X2; unfold gw_le in X1, X2. split; [split; [exact X1 | exact X2] | exact LAY_gIMG_LO]. Qed.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Variables (e_strcmp : Z).
Let e_blk_18a54 : Z := e_18a54.
Let e_blk_17cb0 : Z := e_17cb0.
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

Hypothesis printbuf_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqd.gw_all) (@QPIU.Mqd.printbuf_free_cps) e_pbfree)) in exact T).

Hypothesis lh_table_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QAyu.Mq2.gw_all) (@QAyu.Mq2.lh_table_free_cps) e_lhfree)) in exact T).

Hypothesis array_list_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mq0.gw_all) (@QPIU.Mq0.array_list_free_cps) e_alfree)) in exact T).

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
#[using="w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 joff_24 joff_26 joff_28 joff_34 joff_39 joff_57 joff_63 joff_89 joff_97 joff_101 joff_106 e_pbfree e_alfree e_alread e_17bbc e_17cb0 e_17cb8 e_lhfree e_18934 e_18a54 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free e_strcmp CODE BASE4 BASER D_24 E_24 D_26 E_26 D_28 E_28 D_34 E_34 D_39 E_39 D_57 E_57 D_63 E_63 D_89 E_89 D_97 E_97 D_101 E_101 D_106 E_106 LINK_24 LINK_26 LINK_28 LINK_34 LINK_39 LINK_57 LINK_63 LINK_89 LINK_97 LINK_101 LINK_106 printbuf_free_cps lh_table_free_cps array_list_free_cps CODE_e_18a54 CODE_e_17cb0 CODE_e_17bbc CODE_e_18934 CODE_e_17cb8 S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

Section Loop.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (sp gp s10 s11 : word) (lo : Z) (errv : word).

Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -96 - (32 + 32 + 16 + 8256).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -96)).
Notation TP := (Z_to_bv 64 gTP).
Notation CM1 := (Z_to_bv 64 18446744073709551615).

Definition next_post (q : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (m : word -> option byte) (md : Model) (LB : list blk)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (F' : bvmap 5 word) (fc' : bv 32)
(x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word),
ms' = MS (mkR x1 SPR gp TP t0 t1 t2 x8 (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 (base + 0x74)) fc' None m' (seg_rom segs) /\
fsaved F1 F' /\ (frm0 fc1 -> frm0 fc') /\ model_vm_only md md' /\
HEAPx A' LB m' md' /\ stk segs m' lo (bv_unsigned sp + -96) /\
heap_pres S4L LB (bv_unsigned sp + -96) m m' /\ rw_cells segs m' (gTP - 164) [C4 errv].

#[using="w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 joff_26 joff_28 e_pbfree e_17cb0 e_18a54 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_26 E_26 D_28 E_28 LINK_26 LINK_28 printbuf_free_cps LO LOS SPA HT"] Lemma pop_tail :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB PBS : list blk) (x q pb ty tojs cf : Z) (T : TSet),
HEAPx A ((x, 48) :: PBS ++ LB) m md ->
rw_cells segs m x (jhdr_cells ty 0 tojs pb 0 0 ++ [C8 (Z_to_bv 64 cf)]) ->
opt_pbuf segs m PBS pb ->
stk segs m lo (bv_unsigned sp + -96) -> rw_cells segs m (gTP - 164) [C4 errv] ->
(forall ms' md', next_post q F1 fc1 m md LB ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x64)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 joff_26 joff_28 e_pbfree e_17cb0 e_18a54 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_26 E_26 D_28 E_28 LINK_26 LINK_28 printbuf_free_cps LO LOS SPA HT segs base gTP HIx sp gp s10 s11 lo errv. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until T. intros HP HDR OPB ST ERR K.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
pose proof (wmono_refl segs m) as WM. pose proof (munch_refl [] m) as MU.
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. step.
apply evt_RZ_done.
eapply (printbuf_free_cps HIx) with (BS := PBS) (LB := (x, 48) :: LB) (p := pb) (lo := lo);
[ eapply (heap_perm S4L HIx); [exact HP | perm] | exact OPB | .. ]; try alloc_side.
intros ms2 md2 (m2 & A2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR2 by lia.
clear MU WM MI HDR OPB ST.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. step.
alloc_call (hi_free S4L HIx) S4L HIx HP2 MU WM MI.
{ right. exists 48. left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR3 by lia.
rewrite lb_remove_head in HPR3, HP3.
apply K. unfold next_post.
exists m3, A3, F2, fc2. do 20 eexists.
split; [try g_ret_pc_any; reflexivity |].
split; [exact FS2|]. split; [exact FRM2|]. split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|].
split; [exact HP3|]. split; [exact ST3|]. split; [| exact ERR3].
eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; right; exact Hb] | exact HPR3].
Qed.

Definition zpop (isobj : bool) (m : word -> option byte) (x q : Z) (nz : nat) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs, zobj segs S4F m x q [] nz t tbl size es svs XBS
else exists a arr size, zarr segs S4F m x q [] nz a arr size XBS.

#[using="w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 joff_24 joff_26 joff_28 joff_89 e_pbfree e_alfree e_17cb0 e_lhfree e_18a54 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_24 E_24 D_26 E_26 D_28 E_28 D_89 E_89 LINK_24 LINK_26 LINK_28 LINK_89 printbuf_free_cps lh_table_free_cps array_list_free_cps LO LOS SPA HT"] Lemma pop_ok : forall (isobj : bool)
(x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS : list blk) (x q : Z) (nz : nat) (T : TSet),
HEAPx A (XBS ++ LB) m md ->
zpop isobj m x q nz XBS ->
stk segs m lo (bv_unsigned sp + -96) -> rw_cells segs m (gTP - 164) [C4 errv] ->
(forall ms' md', next_post q F1 fc1 m md LB ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x128)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 joff_24 joff_26 joff_28 joff_89 e_pbfree e_alfree e_17cb0 e_lhfree e_18a54 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_24 E_24 D_26 E_26 D_28 E_28 D_89 E_89 LINK_24 LINK_26 LINK_28 LINK_89 printbuf_free_cps lh_table_free_cps array_list_free_cps LO LOS SPA HT segs base gTP HIx sp gp s10 s11 lo errv. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until T. intros HP ZP ST ERR K.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs m) as WM. pose proof (munch_refl [(x, x + 40)] m) as MU.
destruct isobj.
- destruct ZP as (t & tbl & size & es & svs & Z0).
destruct (zobj_nil_shape segs S4F _ _ _ _ _ _ _ _ _ _ Z0) as (pb & PBS & EX & OPB & HDR & OPEN & VZ & Lz). clear Z0.
subst XBS. rewrite <- app_assoc in HP. cbn [app] in HP.
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. norm_w32. step. step. if_false. step. step. if_true. step. norm_w32. stepz. stepz.
step. if_false. step. if_false. step. if_false. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp + -96) HP MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; in_sub Hb) ltac:(clia))
as (HP2 & AG2 & HPR2).
assert (OPEN2 : lh_open segs S4F m2 t tbl size es svs).
{ eapply lh_open_agree; [exact OPEN | exact AG2 | intros b Hb; in_sub Hb]. }
apply evt_RZ_done.
eapply (lh_table_free_cps HIx) with (LB := (x, 48) :: PBS ++ LB) (lo := lo) (kvs:=[]) (tbl := tbl) (size := size) (es := es) (svs := svs);
[ eapply (heap_perm S4L HIx); [exact HP2 | perm] | exact OPEN2 | exact VZ | .. ]; try alloc_side.
intros ms4 md4 (m4 & A4 & r4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & HP4).
destruct RS4 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F4 & fc4 & -> & FS4 & FRM4).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR4 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
assert (OPB4 : opt_pbuf segs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
- eapply agree_on_incl; [exact AG2 | intros b Hb; in_sub Hb].
- eapply (agree_of_heap_pres segs S4L); [exact HPR4 | reflexivity | intros b Hb; in_sub Hb]. }
clear MU WM MI ST OPEN OPEN2.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
reenter MOK4. step.
apply evt_RZ_done.
eapply pop_tail; [exact HP4 | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB4 | exact ST4 | exact ERR4 |].
intros ms5 md5 (m5 & A5 & F5 & fc5 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & -> & FS5 & FRM5 & VM5 & HP5 & ST5 & HPR5 & ERR5).
apply K. unfold next_post. exists m5, A5, F5, fc5. do 20 eexists.
split; [reflexivity|]. split; [eapply fsaved_trans; [exact FS4 | exact FS5]|]. split; [intros Hf; exact (FRM5 (FRM4 Hf))|].
split; [eapply model_vm_only_trans; [exact VM4 | exact VM5]|]. split; [exact HP5|]. split; [exact ST5|]. split; [| exact ERR5].
eapply heap_pres_trans; [exact HPR2|]. eapply heap_pres_trans; [| exact HPR5].
eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; in_sub Hb].
- destruct ZP as (a & arr & size & Z0).
destruct (zarr_nil_vals segs S4F _ _ _ _ _ _ _ _ Z0) as (pb & PBS & EX & OPB & HDR & AL). clear Z0.
subst XBS. rewrite <- app_assoc in HP. cbn [app] in HP.
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. norm_w32. step. step. if_false. step. step. if_true. step. norm_w32. stepz. stepz.
step. if_false. step. if_true. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp + -96) HP MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; in_sub Hb) ltac:(clia))
as (HP2 & AG2 & HPR2).
assert (AL2 : alist segs S4F m2 [(a, 32); (arr, 8 * size)] a (repeat 0 nz)).
{ eapply alist_agree; [exact AL | exact AG2 | intros b Hb; in_sub Hb]. }
apply evt_RZ_done.
eapply (array_list_free_cps HIx) with (LB := (x, 48) :: PBS ++ LB) (lo := lo) (BS := [(a, 32); (arr, 8 * size)]);
[ eapply (heap_perm S4L HIx); [exact HP2 | perm] | exact AL2 | apply Forall_repeat0 | .. ]; try alloc_side.
intros ms4 md4 (m4 & A4 & r4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & HP4).
destruct RS4 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F4 & fc4 & -> & FS4 & FRM4).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR4 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
assert (OPB4 : opt_pbuf segs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
- eapply agree_on_incl; [exact AG2 | intros b Hb; in_sub Hb].
- eapply (agree_of_heap_pres segs S4L); [exact HPR4 | reflexivity | intros b Hb; in_sub Hb]. }
clear MU WM MI ST AL AL2.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
try g_ret_pc_any.
eapply pop_tail; [exact HP4 | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB4 | exact ST4 | exact ERR4 |].
intros ms5 md5 (m5 & A5 & F5 & fc5 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & -> & FS5 & FRM5 & VM5 & HP5 & ST5 & HPR5 & ERR5).
apply K. unfold next_post. exists m5, A5, F5, fc5. do 20 eexists.
split; [reflexivity|]. split; [eapply fsaved_trans; [exact FS4 | exact FS5]|]. split; [intros Hf; exact (FRM5 (FRM4 Hf))|].
split; [eapply model_vm_only_trans; [exact VM4 | exact VM5]|]. split; [exact HP5|]. split; [exact ST5|]. split; [| exact ERR5].
eapply heap_pres_trans; [exact HPR2|]. eapply heap_pres_trans; [| exact HPR5].
eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; in_sub Hb].
Qed.
End Loop.

End RC__1.

End G.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH.Mq0 Qsw7 QJjn.
Import QPIU.Mqd.
Import QPIU.Mqi.
Import Q9Mh.Mq8.
Import QAyu.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

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
#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma gLAYF0 : ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gTP gIMG_LO gIMG_HI. pose proof LAY_TPLO as X1; pose proof LAY_TPHI as X2; unfold gw_le in X1, X2. split; [split; [exact X1 | exact X2] | exact LAY_gIMG_LO]. Qed.
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

Hypothesis printbuf_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqd.gw_all) (@QPIU.Mqd.printbuf_free_cps) e_pbfree)) in exact T).

Hypothesis lb_remove_zero : ltac:(let T := constr:(ltac:(gw_callee_stmt2 (@Q9Mh.Mq8.gw_all) (@Q9Mh.Mq8.lb_remove_zero) (base + -8)%Z)) in let T := eval cbv beta delta [Q9Mh.Mq8.lb_remove_zero Q9Mh.Mq8.json_tokener_new_entry] in T in let T := gw_fold_pcs T base (-8)%Z [0]%Z in exact T).

Definition put_stmt := ltac:(let t := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stmt))) in let t := eval cbv beta delta [QPIU.Mqi.put_stmt] in t in exact t).
Definition put_stk_P := ltac:(let t := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stk_P))) in let t := eval cbv beta delta [QPIU.Mqi.put_stk_P] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stmt))) in let t := gw_subst t x put_stmt in exact t).
Definition lvblocks := ltac:(let t := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.lvblocks))) in let t := eval cbv beta delta [QAyu.Mq6.lvblocks] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stmt))) in let t := gw_subst t x put_stmt in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stk_P))) in let t := gw_subst t x put_stk_P in exact t).
Definition tokfree_loop_pc : Z := (base + 64)%Z.
Definition tf_frame := ltac:(let t := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.tf_frame))) in let t := eval cbv beta delta [QAyu.Mq6.tf_frame] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stmt))) in let t := gw_subst t x put_stmt in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stk_P))) in let t := gw_subst t x put_stk_P in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.lvblocks))) in let t := gw_subst t x lvblocks in exact t).

Definition lvblocks_S := ltac:(let p := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.lvblocks_S))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stmt))) in let T := gw_subst T x put_stmt in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stk_P))) in let T := gw_subst T x put_stk_P in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.lvblocks))) in let T := gw_subst T x lvblocks in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.tf_frame))) in let T := gw_subst T x tf_frame in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.put_stmt))) in let T := gw_subst T x put_stmt in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.put_stk_P))) in let T := gw_subst T x put_stk_P in exact (p : T)).
Arguments lvblocks_S _%_list_scope _%_nat_scope.
Definition lvblocks_0 := ltac:(let p := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.lvblocks_0))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stmt))) in let T := gw_subst T x put_stmt in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stk_P))) in let T := gw_subst T x put_stk_P in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.lvblocks))) in let T := gw_subst T x lvblocks in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.tf_frame))) in let T := gw_subst T x tf_frame in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.put_stmt))) in let T := gw_subst T x put_stmt in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.put_stk_P))) in let T := gw_subst T x put_stk_P in exact (p : T)).
Definition tokfree_body := ltac:(let p := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.tokfree_body))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stmt))) in let T := gw_subst T x put_stmt in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqi.put_stk_P))) in let T := gw_subst T x put_stk_P in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.lvblocks))) in let T := gw_subst T x lvblocks in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.tf_frame))) in let T := gw_subst T x tf_frame in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.put_stmt))) in let T := gw_subst T x put_stmt in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq6.put_stk_P))) in let T := gw_subst T x put_stk_P in exact (p : T)).
Arguments tokfree_body _ _ _%_nat_scope.

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
#[using="w_19 w_24 w_34 w_36 w_44 joff_19 joff_24 joff_34 joff_36 joff_44 e_pbfree e_blk_16158 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free e_1411c CODE BASE4 BASER D_19 E_19 D_24 E_24 D_34 E_34 D_36 E_36 D_44 E_44 LINK_19 LINK_24 LINK_34 LINK_36 LINK_44 printbuf_free_cps lb_remove_zero S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

#[using="Type"] Lemma firstn_lupd_ge : forall {A} (l : list A) n i x, (n <= i)%nat -> firstn n (lupd l i x) = firstn n l.
Proof. clear - segs.
induction l as [|h t IH]; intros [|n] [|i] x Hni; cbn; auto; try lia. f_equal. apply IH. lia.
Qed.

#[using="Type"] Lemma lvblocks_lupd_ge : forall levels n i x, (n <= i)%nat -> lvblocks (lupd levels i x) n = lvblocks levels n.
Proof. clear - segs. intros. unfold lvblocks. rewrite firstn_lupd_ge by assumption. reflexivity. Qed.

#[using="Type"] Lemma lvl_ok_agree : forall segs_ fn BS m m' l,
lvl_ok segs_ fn m l -> agree_on segs_ BS m m' -> incl (tl_cbs l) BS -> lvl_ok segs_ fn m' l.
Proof. clear - segs.
intros segs_ fn BS m m' l [J N] AG Hi. split; [| exact N]. eapply (jopt_agree segs_ fn); eauto.
Qed.

#[using="Type"] Lemma lvblocks_incl : forall levels n j l, nth_error levels j = Some l -> (j < n)%nat -> incl (lvl_blocks l) (lvblocks levels n).
Proof. clear - segs.
intros levels n. induction n as [|n IH]; intros j l Hj Hjn; [lia|].
destruct (nth_error levels n) as [ln|] eqn:E.
- rewrite (lvblocks_S _ _ _ E). destruct (PeanoNat.Nat.eq_dec j n) as [->|NE].
+ rewrite Hj in E. injection E as ->. apply incl_appl. apply incl_refl.
+ apply incl_appr. eapply IH; [exact Hj | lia].
- apply nth_error_None in E. pose proof (nth_error_Some_length Hj).
unfold lvblocks. rewrite firstn_all2 by lia. unfold lvblocks in IH. rewrite <- (firstn_all2 (n := n) levels) by lia.
eapply IH; [exact Hj | lia].
Qed.

Section TokFree2.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : (put_stmt S4L HIx S4F (e_blk_16158 + 0x0) put_stk_P).

Definition tf_loop_post (x2 gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : Model) (BASE LB0 PBS : list blk) (SP : Z) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (junk : list byte) (s3v s2v s1v s0v rav : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) F' fc' levels' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s1',
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 s0 s1' a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 (base + 0x78)) fc' None m' (seg_rom segs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only md md' /\
HEAPx A' BASE m' md' /\
length levels' = 32%nat /\
(forall j, (j <= i)%nat -> nth_error levels' j = Some lvl_reset) /\
(forall j, (i < j)%nat -> nth_error levels' j = nth_error levels j) /\
tstack segs m' q levels' /\
rw_cells segs m' r (tok_cells pb depth q x) /\
tf_frame m' SP junk s3v s2v s1v s0v rav /\
stk segs m' lo (SP - 48) /\
heap_pres S4L LB0 SP me m' /\
rw_cells segs m' (gTP - 164) [C4 errv] /\
agree_on segs PBS mpre m'.

#[using="w_19 w_24 w_34 w_36 w_44 joff_19 joff_24 e_blk_16158 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_19 E_19 D_24 E_24 LINK_19 LINK_24 lb_remove_zero PUT"] Lemma tokfree_loop :
forall (i : nat) (x1 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (PBS LB0 : list blk) (SP lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (junk : list byte) (s3v s2v s1v s0v rav : word),
(i < 32)%nat -> length levels = 32%nat ->
HEAPx A (lvblocks levels (S i) ++ PBS ++ (r, 72) :: (q, 1024) :: LB0) m md ->
(forall j l, nth_error levels j = Some l -> (j <= i)%nat -> lvl_ok segs S4F m l) ->
tstack segs m q levels ->
rw_cells segs m r (tok_cells pb depth q x) ->
tf_frame m SP junk s3v s2v s1v s0v rav ->
stk segs m lo (SP - 48) -> alloc_ceiling <= lo -> lo <= SP - 48 - put_stk_P ->
SP mod 16 = 0 -> SP <= hi_top S4L HIx -> 0 <= SP < 2^64 ->
heap_pres S4L LB0 SP me m ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP ->
(forall ms' md', tf_loop_post (Z_to_bv 64 (SP - 48)) gp tp (Z_to_bv 64 r) (Z_to_bv 64 (2^32)) (Z_to_bv 64 (-16)) s4 s5 s6 s7 s8 s9 s10 s11
F fc md (PBS ++ (r, 72) :: (q, 1024) :: LB0) LB0 PBS SP me m lo errv q r pb depth x levels i junk s3v s2v s1v s0v rav ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (SP - 48)) gp tp t0 t1 t2 (Z_to_bv 64 r) (Z_to_bv 64 (32 * Z.of_nat i + 16)) (Z_to_bv 64 q)
a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (2^32)) (Z_to_bv 64 (-16)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 tokfree_loop_pc) fc None m (seg_rom segs)) md) T.
Proof. clear - w_19 w_24 w_34 w_36 w_44 joff_19 joff_24 e_blk_16158 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_19 E_19 D_24 E_24 LINK_19 LINK_24 lb_remove_zero PUT segs gTP S4F HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
induction i as [|i IH]; intros until rav; intros Hi LEN HP LOK TS BLK FR ST LO LOS SPA HT SPR HPR ERR TP K.
-
destruct (nth_error levels 0) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP. rewrite <- app_assoc in HP.
eapply (tokfree_body HIx PUT 0) with (P := PBS); [exact Hl | lia | exact LEN | exact HP | rewrite lvblocks_0; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact SPR | exact HPR | exact ERR | exact TP |].
intros ms1 md1 (m1 & A1 & F1 & fc1 & y1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1).
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.
apply rz_evt; [exact MOK1|].
step. if_false.
apply evt_RZ_done. apply K. unfold tf_loop_post.
exists m1, A1, F1, fc1, (lupd levels 0 lvl_reset). do 17 eexists.
split; [reflexivity|]. split; [exact FS1|]. split; [exact FRM1|]. split; [exact VM1|].
split; [rewrite lvblocks_0 in HP1; exact HP1|].
split; [rewrite lupd_length; exact LEN|].
split; [intros j Hj; replace j with 0%nat by lia; apply nth_error_lupd_eq; lia|].
split; [intros j Hj; apply nth_error_lupd_neq; lia|].
split; [exact TS1|]. split; [exact BLK1|]. split; [exact FR1|]. split; [exact ST1|]. split; [exact HPR1 |]. split; [exact ERR1|]. exact AG1.
-
destruct (nth_error levels (S i)) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP. rewrite <- app_assoc in HP.
eapply (tokfree_body HIx PUT (S i)) with (P := lvblocks levels (S i) ++ PBS); [exact Hl | lia | exact LEN | exact HP | rewrite <- app_assoc; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact SPR | exact HPR | exact ERR | exact TP |].
intros ms1 md1 (m1 & A1 & F1 & fc1 & y1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1).
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.
apply rz_evt; [exact MOK1|].
step. if_truex.
replace (32 * Z.of_nat (S i) + 16 - 32) with (32 * Z.of_nat i + 16) by lia.
apply evt_RZ_done.
eapply (IH _ gp tp _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F1 fc1 m1 me md1 T A1 PBS LB0 SP lo errv q r pb depth x (lupd levels (S i) lvl_reset));
[lia | rewrite lupd_length; exact LEN | rewrite lvblocks_lupd_ge by lia; exact HP1 | | exact TS1 | exact BLK1 | exact FR1 | exact ST1 | exact LO | exact LOS | exact SPA | exact HT | exact SPR | exact HPR1 | exact ERR1 | exact TP |].
+ intros j l' Hj Hji. rewrite nth_error_lupd_neq in Hj by lia.
eapply lvl_ok_agree; [eapply LOK; [exact Hj | lia] | exact AG1 | apply incl_appl; eapply incl_tran; [| eapply lvblocks_incl; [exact Hj | lia]]; unfold lvl_blocks; apply incl_appl; apply incl_refl].
+ intros ms2 md2 (m2 & A2 & F2 & fc2 & levels2 & y1' & u0' & u1' & u2' & w0 & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & s1' & -> & FS2 & FRM2 & VM2 & HP2 & LEN2 & RES2 & SAME2 & TS2 & BLK2 & FR2 & ST2 & HPR2 & ERR2 & AG2).
apply K. unfold tf_loop_post.
exists m2, A2, F2, fc2, levels2. do 17 eexists.
split; [reflexivity|]. split; [eapply fsaved_trans; [exact FS1 | exact FS2]|]. split; [intros Hf; apply FRM2, FRM1, Hf|].
split; [eapply model_vm_only_trans; [exact VM1 | exact VM2]|].
split; [exact HP2|]. split; [exact LEN2|].
split. { intros j Hj. destruct (PeanoNat.Nat.eq_dec j (S i)) as [->|NE]; [| apply RES2; lia]. rewrite SAME2 by lia. apply nth_error_lupd_eq. lia. }
split. { intros j Hj. rewrite SAME2 by lia. apply nth_error_lupd_neq. lia. }
split; [exact TS2|]. split; [exact BLK2|]. split; [exact FR2|]. split; [exact ST2|]. split; [exact HPR2 |]. split; [exact ERR2|].
eapply agree_on_trans; [eapply agree_on_incl; [exact AG1 | apply incl_appr; apply incl_refl] | exact AG2].
Qed.

#[using="Type"] Lemma Permutation_concat : forall {A} (L L' : list (list A)), Permutation L L' -> Permutation (concat L) (concat L').
Proof. clear - HIx PUT.
intros A L L' HP. induction HP; cbn.
- apply Permutation_refl.
- apply Permutation_app_head. exact IHHP.
- rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
- eapply Permutation_trans; eauto.
Qed.

#[using="Type"] Lemma lvblocks_all : forall levels, length levels = 32%nat ->
Permutation (concat (map lvl_blocks levels)) (lvblocks levels 32).
Proof. clear - HIx PUT.
intros levels LEN. unfold lvblocks. rewrite firstn_all2 by lia. rewrite map_rev.
apply Permutation_concat. apply Permutation_rev.
Qed.

#[using="Type"] Lemma lvblocks_trunc : forall levels k,
(forall j l, nth_error levels j = Some l -> (k <= j)%nat -> lvl_clean l) ->
forall n, (k <= n)%nat -> lvblocks levels n = lvblocks levels k.
Proof. clear - HIx PUT.
intros levels k H n Hkn. induction n as [|n IH].
- replace k with 0%nat by lia. reflexivity.
- destruct (PeanoNat.Nat.eq_dec k (S n)) as [->|NE]; [reflexivity|].
destruct (nth_error levels n) as [l|] eqn:E.
+ rewrite (lvblocks_S _ _ _ E). rewrite (lvl_clean_blocks l) by (eapply H; [exact E | lia]). cbn. apply IH. lia.
+ apply nth_error_None in E. unfold lvblocks in *. rewrite (firstn_all2 (n := S n)) by lia.
rewrite (firstn_all2 (n := n)) in IH by lia. apply IH. lia.
Qed.

Definition json_tokener_free_entry2 : Z := (base + 0x0).

Definition tokfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (rv : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rv m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv] /\
HEAPx A' LB m' md'.

#[using="w_19 w_24 w_34 w_36 w_44 joff_19 joff_24 joff_34 joff_36 joff_44 e_pbfree e_blk_16158 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_19 E_19 D_24 E_24 D_34 E_34 D_36 E_36 D_44 E_44 LINK_19 LINK_24 LINK_34 LINK_36 LINK_44 printbuf_free_cps lb_remove_zero PUT"] Lemma json_tokener_free_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB BS : list blk) (tk lo : Z) (errv : word),
HEAPx A (BS ++ LB) m md ->
tokrep segs S4F m BS tk -> tk <> 0 ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - put_stk_P ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 tk ->
(forall ms' md', tokfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo errv ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_tokener_free_entry2) fc None m (seg_rom segs)) md) T.
Proof. clear - w_19 w_24 w_34 w_36 w_44 joff_19 joff_24 joff_34 joff_36 joff_44 e_pbfree e_blk_16158 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_19 E_19 D_24 E_24 D_34 E_34 D_36 E_36 D_44 E_44 LINK_19 LINK_24 LINK_34 LINK_36 LINK_44 printbuf_free_cps lb_remove_zero PUT segs gTP S4F HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until errv. intros HP TOKR Htk ST LO LOS SPA HT ERR TP RA A0 K.
destruct TOKR as (q & pb & depth & PBS & levels & x & EBS & LEN & Hd & TOK & PB & Hpb & TS & LOK & CLEAN).
subst BS a0 tp. unfold put_stk_P in LOS. unfold_consts. word_range sp SPR.

set (dn := Z.to_nat depth).
assert (PCV : Permutation (concat (map lvl_blocks levels)) (lvblocks levels (S dn))).
{ rewrite <- (lvblocks_trunc levels (S dn) ltac:(intros jj ll Hj Hkj; eapply CLEAN; [exact Hj | lia]) 32) by lia.
apply lvblocks_all. lia. }
assert (HP0 : HEAPx A (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB) m md).
{ eapply heap_perm; [exact HP|].
replace (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB)
with ((lvblocks levels (S dn) ++ PBS ++ [(tk, 72); (q, 1024)]) ++ LB) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_app_tail.
apply (Permutation_trans (l' := (PBS ++ concat (map lvl_blocks levels)) ++ [(tk, 72); (q, 1024)])).
- apply (Permutation_app_comm [(tk, 72); (q, 1024)] (PBS ++ concat (map lvl_blocks levels))).
- replace (lvblocks levels (S dn) ++ PBS ++ [(tk, 72); (q, 1024)]) with ((lvblocks levels (S dn) ++ PBS) ++ [(tk, 72); (q, 1024)])
by (rewrite <- app_assoc; reflexivity).
apply Permutation_app_tail.
apply (Permutation_trans (l' := concat (map lvl_blocks levels) ++ PBS)); [apply Permutation_app_comm | apply Permutation_app_tail; exact PCV]. }
clear HP.
assert (INtk : In (tk, 72) (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 1024) (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP0 INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP0 INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q 1024 HP0 INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q 1024 HP0 INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (heap_model_ok _ _ _ _ _ _ HP0) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP0) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
unfold tok_cells in TOK.
pose proof PB as PB'. destruct PB' as (buf & bpos & size & pre & post & EPBS & _). stash PB.
apply rz_evt; [exact MOK|]. unfold json_tokener_free_entry2.
step. if_falsex.
carve_frame 48%nat ST.
do 7 step.
step. step. norm_sx32. if_falsex. step. step. step. step. step. step.
rewrite (unsigned_lit depth) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
replace (depth * 32 + 16) with (32 * Z.of_nat dn + 16) by lia.
replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in * by lia.
change 4294967296 with (2 ^ 32).
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mc _) _) _ =>
assert (HPc : HEAPx A (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB) mc md)
by (eapply (heap_frame S4L HIx); [exact HP0 | | exact WM | exact MI]; eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP0 MU); solve_frameW_with HP0);
assert (TSc : tstack segs mc q levels)
by (eapply (tstack_transport segs); [exact TS | exact MU | exact WM | intros j Hj; cbn; split; [lia | exact I]]);
assert (AGc : agree_on segs (lvblocks levels (S dn) ++ PBS ++ (tk, 72) :: (q, 1024) :: LB) m mc)
by (eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [| exact I];
pose proof (heap_blk S4L HIx _ _ _ _ a n HP0 Hin) as (_ & _ & _ & Hhi' & _); unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi'; lia]);
assert (HPRc : heap_pres S4L LB (bv_unsigned sp) m mc)
by (eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outside S4L HIx); [exact HP0 | intros bb Hbb; apply in_or_app; right; apply in_or_app; right; right; right; exact Hbb | clia | ];
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_nil])
end.
eapply (tokfree_loop dn _ gp _ _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc _ m md T A PBS LB (bv_unsigned sp) lo errv q tk pb depth x levels);
[ lia | lia | exact HPc | intros j l Hj Hji; eapply lvl_ok_agree; [eapply LOK; [exact Hj | lia] | exact AGc | apply incl_appl; eapply incl_tran; [| eapply lvblocks_incl; [exact Hj | lia]]; unfold lvl_blocks; apply incl_appl; apply incl_refl]
| exact TSc | exact TOK | exact FR | exact ST | clia | unfold put_stk_P; clia | exact SPA | exact HT | lia
| exact HPRc | exact ERR | reflexivity | ].
intros ms1 md1 (m1 & A1 & F1 & fc1 & levels1 & y1 & u0 & u1 & u2 & w0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & s1' & -> & FS1 & FRM1 & VM1 & HP1 & LEN1 & RES1 & SAME1 & TS1 & TOK1 & FR1 & ST1 & HPR1 & ERR1 & AG1).
clear TSc TOK FR ST MU WM MI HPc.
unfold tok_cells in TOK1. unfold tf_frame in FR1.
assert (INp : In (pb, 16) (PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (rewrite EPBS; left; reflexivity).
assert (INtk1 : In (tk, 72) (PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; left; reflexivity).
assert (INq1 : In (q, 1024) (PBS ++ (tk, 72) :: (q, 1024) :: LB)) by (apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP1 INp) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
assert (Htq : tk <> q).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP1) as ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q 1024 HP1 INtk1 INq1 Htq) as Hdtq.
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.
pose proof (heap_mem_inv _ _ _ _ _ _ HP1) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs m1) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (tk, tk + 72)] m1) as MU.
reenter MOK1.
step. stepz. stepz. step. if_falsex. step.

unstash PB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (PBc : pbuf segs mc PBS pb)
by (eapply pbuf_agree; [exact PB | | apply incl_refl];
eapply agree_on_trans; [eapply agree_on_incl; [exact AGc | rewrite EPBS; intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb] |];
eapply agree_on_trans; [exact AG1 |];
eapply agree_of_munch; [exact MU | exact WM | intros a n Hin; cbn; split; [| split; [| exact I]];
[ pose proof (heap_blk S4L HIx _ _ _ _ a n HP1 ltac:(apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hhi' & _); unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi'; lia
| refine (heap_blk_disjoint S4L HIx _ _ _ _ a n tk 72 HP1 ltac:(apply in_or_app; left; exact Hin) INtk1 _);
intros ->; exact (nodup_prefix_suffix PBS ((tk, 72) :: (q, 1024) :: LB) tk n 72 (heap_blk_nodup S4L HIx _ _ _ _ HP1) Hin ltac:(left; reflexivity)) ]])
end.
apply evt_RZ_done.
eapply (printbuf_free_cps HIx) with (LB := (tk, 72) :: (q, 1024) :: LB) (BS := PBS) (p := pb) (lo := lo);
[ eapply (heap_frame S4L HIx); [exact HP1 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP1 MU);
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_cons; [right; left; exists tk, 72; split; [exact INtk1 | cbn; lia] | apply Forall_nil]]
| right; split; [exact Hpb | apply pbuf_pbufw; exact PBc] | .. ]; try alloc_side.
all: try (unfold put_stk_P in *; clia).
intros ms2 md2 (m2 & A2 & r2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS2 as (w0' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp - 48)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp - 48)) in HPR2 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR1; [| left; cbn; lia]. cbn [hl_segs S4L] in FR1.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK1; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in TOK1.
assert (HPRb : heap_pres S4L LB (bv_unsigned sp) m m2).
{ eapply heap_pres_trans; [exact HPR1|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP1 | intros bb Hbb; apply in_or_app; right; right; right; exact Hbb | clia |].
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_cons; [| apply Forall_nil]]. cbn [fst snd].
right; left. exists tk, 72. split; [exact INtk1|]. split; [| lia].
intros Hin0. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP1) as ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. right. exact (in_map blk_addr _ _ Hin0).
- eapply heap_pres_weaken; [exact HPR2 | lia | intros bb Hbb; right; right; exact Hbb]. }
clear MU WM MI HPR1.

pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs m2) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m2) as MU.
reenter MOK2.
step. step.
alloc_call (hi_free S4L HIx) S4L HIx HP2 MU WM MI.
{ right. exists 1024. right. left. reflexivity. }
all: try (unfold put_stk_P in *; clia).
intros ms3 mx3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp - 48)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp - 48)) in HPR3 by lia.
rewrite (lb_remove_other q (tk, 72)) in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR1; [| left; cbn; lia]. cbn [hl_segs S4L] in FR1.
assert (HPRd : heap_pres S4L LB (bv_unsigned sp) m mx3).
{ eapply heap_pres_trans; [exact HPRb|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb; right; right; exact Hbb | clia |].
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_nil].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; right; exact Hbb]. }
clear MU WM MI HPRb TOK1.

pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs mx3) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] mx3) as MU.
reenter MOK3.
do 8 step.
replace (Z_to_bv 64 (bv_unsigned sp - 48 + 48)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
assert (INtk2 : In (tk, 72) ((tk, 72) :: LB)) by (left; reflexivity).
apply evt_RZ_done. eapply (hi_free S4L HIx) with (p := tk) (lo := lo);
[ eapply (heap_frame S4L HIx); [exact HP3 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU); apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_nil]
| right; exists 72; exact INtk2 | .. ]; try alloc_side.
{ release_frame FR1 ST3 (bv_unsigned sp). exact ST3. }
all: try (unfold put_stk_P in *; clia).
intros ms4 m4 md4 A4 r4 RS4 VM4 ST4 HPR4 ERR4 HP4. open_ret RS4. cbn [hl_segs hl_tp S4L] in *.
rewrite lb_remove_head in HPR4, HP4.
apply K. unfold tokfree_post.
exists m4, A4, r4.
split; [| split; [| split; [exact ST4 | split; [| split; [exact ERR4 | exact HP4]]]]].
- eapply ret_statew_intro; [eapply fsaved_trans; [exact FS1 | exact FS2] | intros Hf; apply FRM2, FRM1, Hf].
- eapply model_vm_only_trans; [exact VM1|]. eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3| exact VM4].
- eapply heap_pres_trans; [exact HPRd|]. eapply heap_pres_trans.
+ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros bb Hbb; right; exact Hbb | clia |].
apply Forall_cons; [left; cbn [fst snd]; clia | apply Forall_nil].
+ eapply heap_pres_weaken; [exact HPR4 | lia | intros bb Hbb; exact Hbb].
Qed.
End TokFree2.

End RC__1.

End G.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Mh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Mh.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAyu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAyu.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwApply2 GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

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

Definition ins_regs := ltac:(let t := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.ins_regs))) in let t := eval cbv beta delta [QAyu.Mq3.ins_regs] in t in exact t).

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
Hypothesis AL_e_fn_lh_char_equal : gw_b4 e_fn_lh_char_equal.
Hypothesis RNG_e_fn_lh_char_equal : gw_br e_fn_lh_char_equal 4.
Hypothesis LAY_POS_e_fn_lh_char_equal : gw_le 1 e_fn_lh_char_equal.
Hypothesis LAY_HI_e_fn_lh_char_equal : gw_le (e_fn_lh_char_equal + 4) 1099511627776.
Hypothesis AL_e_fn_lh_char_hash : gw_b4 e_fn_lh_char_hash.
Hypothesis RNG_e_fn_lh_char_hash : gw_br e_fn_lh_char_hash 4.
Hypothesis LAY_POS_e_fn_lh_char_hash : gw_le 1 e_fn_lh_char_hash.
Hypothesis LAY_HI_e_fn_lh_char_hash : gw_le (e_fn_lh_char_hash + 4) 1099511627776.
#[using="w_10 w_11 hi_10 lo_11 G_10770 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_10 E_10 D_11 E_11 ANCH_11 RNG_G_10770 ROM_G_10770 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal AL_e_fn_lh_char_hash RNG_e_fn_lh_char_hash LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash S4F"] Lemma gw_all : True. Proof. exact I. Qed.
Ltac gj_fn_cbn := try (progress cbn [S4F fn_lh_char_equal fn_lh_char_hash]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Definition new_slot (k v pad pv : Z) : slotv := SV k 0 pad v 0 pv.
Definition ins_svs (svs : list slotv) (g : nat) (sg : slotv) (k v : Z) (hd tl : Z) (ixl : nat) (sl : slotv) (tbl : Z) : list slotv :=
if hd =? 0 then upd svs g (new_slot k v (sv_pad sg) 0)
else upd (upd svs g (new_slot k v (sv_pad sg) tl)) ixl (SV (sv_k sl) (sv_kc sl) (sv_pad sl) (sv_v sl) (ent_addr tbl g) (sv_pv sl)).

Section LhStore.
Variables (sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v : Z) (svs : list slotv) (ffn : Z).
Variables (rac s0c s1c s2c s3c s4c s5c : word).

Definition ins_frame (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells segs m (bv_unsigned sp + -64) [CB 8 junk8; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

Definition hdr_cells (sz cnt hd tl : Z) : list cell :=
[C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 cnt); C8 (Z_to_bv 64 hd); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 ffn); C8 (Z_to_bv 64 (fn_lh_char_hash S4F)); C8 (Z_to_bv 64 (fn_lh_char_equal S4F))].

#[using="w_10 w_11 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash"] Lemma lh_store_block :
forall (g : Z) (sg : slotv) (cnt hd tl : Z) (ixl : nat) (sl : slotv)
(x1 x6 x7 x8 x9 x18 x19 x20 x21 x28 x29 x30 x31 : word) (m : word -> option byte) (junk8 : list byte) (lo : Z),
0 <= g < size -> In size lf_sizes -> Z.of_nat (length svs) = size -> nth_error svs (Z.to_nat g) = Some sg ->
0 <= cnt < size -> 0 <= k < 2^64 -> 0 <= v < 2^64 -> 0 <= ffn < 2^64 ->
(hd = 0 /\ tl = 0) \/ (hd <> 0 /\ tl = ent_addr tbl ixl /\ nth_error svs ixl = Some sl /\ ixl <> Z.to_nat g /\ 0 <= hd < 2^64) ->
0 <= t -> t + 56 <= lo -> 0 <= tbl -> tbl + 40 * size <= lo -> (t + 56 <= tbl \/ tbl + 40 * size <= t) ->
lo <= bv_unsigned sp - 64 ->
mem_inv segs m ->
rw_cells segs m t (hdr_cells size cnt hd tl) ->
lh_slots segs m tbl svs ->
ins_frame m junk8 -> stk segs m lo (bv_unsigned sp + -64) ->
evt segs (fun ms' => exists (x5 x11 x12 : word) m',
ms' = MS (mkR rac sp gp tp x5 x6 x7 s0c s1c (Z_to_bv 64 0)
x11 x12 (Z_to_bv 64 g) (Z_to_bv 64 0) (Z_to_bv 64 tbl) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (tbl + 40 * g))
s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc rac) fc None m' (seg_rom segs)
/\ munch [(t, t + 56); (tbl, tbl + 40 * size)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' t (hdr_cells size (cnt + 1) (if hd =? 0 then ent_addr tbl (Z.to_nat g) else hd) (ent_addr tbl (Z.to_nat g)))
/\ lh_slots segs m' tbl (ins_svs svs (Z.to_nat g) sg k v hd tl ixl sl tbl)
/\ stk segs m' lo (bv_unsigned sp))
(MS (ins_regs sp gp tp s6 s7 s8 s9 s10 s11 t tbl size k v 0 x1 x6 x7 x8 x9 g (Z_to_bv 64 (tbl + g * 40)) x18 x19 x20 x21 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x90)) fc None m (seg_rom segs)).
Proof. clear - w_10 w_11 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash segs base sp gp tp s6 s7 s8 s9 s10 s11 F fc t tbl size k v svs ffn rac s0c s1c s2c s3c s4c s5c. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_hash as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_hash as gL5_; unfold gw_le in gL5_.
intros until lo. intros Hg Hsz Hlen Esg Hcnt Hk Hv Hffn TAIL Ht0 Ht Hb0 Hb SEP LOS MI HDR SL FR ST.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR. unfold ins_frame in FR. unfold hdr_cells in HDR.
pose proof (SL _ _ Esg) as CG. unfold ent_addr, slot_cells in CG. rewrite Z2Nat.id in CG by lia.
pose proof (wmono_refl segs m) as WM.
unfold ins_regs. replace (tbl + g * 40) with (tbl + 40 * g) by lia.
destruct TAIL as [[Hhd Htl] | (Hhd & Htl & Esl & NEl & HhdR)].
-
subst hd tl.
pose proof (munch_refl [(t, t + 56); (tbl + 40 * g, tbl + 40 * g + 40)] m) as MU.
remember (tbl + 40 * g) as B eqn:EB.
step.
step. change (Z.land (bv_unsigned (Z_to_bv 64 0)) (bv_unsigned (Z_to_bv 64 4))) with 0.
step. rewrite (unsigned_lit g) by lia. step. replace (tbl + g * 40) with B by lia.
step. norm_sx32. step.
stepz.
step.
step. norm_w32. step.
step. step. if_true.
step. step. step. step. rewrite (unsigned_lit g) by lia. step. replace (tbl + g * 40) with B by lia.
stepz. stepz.
step. do 8 step.
lazymatch goal with H : rw_cells segs ?mx (bv_unsigned sp + -64) _ |- _ => release_frame H ST (bv_unsigned sp) end.
step. subst B.
apply evt_done. do 3 eexists. eexists. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU]. intros x Hx. cbn in Hx |- *. lia. }
split; [exact WM|]. split; [exact MI|].
split. { unfold hdr_cells. cbn [Z.eqb]. unfold ent_addr. rewrite Z2Nat.id by lia. assumption. }
split; [| exact ST].
unfold ins_svs. cbn [Z.eqb]. eapply (lh_slots_write1 segs m); [exact SL | lia | exact MU | exact WM | | ].
+ intros i NE Hi. unfold ivs_miss_slot. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn; unfold ent_addr.
* destruct SEP; [right; lia | left; nia].
* assert (Z.of_nat i + 1 <= g \/ g + 1 <= Z.of_nat i) as [L|R] by lia; [left; nia | right; nia].
+ unfold ent_addr, slot_cells, new_slot. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Z2Nat.id by lia. assumption.
-
pose proof (SL _ _ Esl) as CL. unfold ent_addr, slot_cells in CL.
pose proof (proj1 (nth_error_Some svs ixl) ltac:(rewrite Esl; discriminate)) as Hixl.
assert (NEg : Z.of_nat ixl <> g) by (intros X; apply NEl; lia).
pose proof (munch_refl [(t, t + 56); (tbl + 40 * g, tbl + 40 * g + 40); (tbl + 40 * Z.of_nat ixl, tbl + 40 * Z.of_nat ixl + 40)] m) as MU.
remember (tbl + 40 * g) as B eqn:EB. remember (tbl + 40 * Z.of_nat ixl) as TL eqn:ETL.
replace tl with TL in * by (subst tl TL; unfold ent_addr; reflexivity).
step.
step. change (Z.land (bv_unsigned (Z_to_bv 64 0)) (bv_unsigned (Z_to_bv 64 4))) with 0.
step. rewrite (unsigned_lit g) by lia. step. replace (tbl + g * 40) with B by lia.
step. norm_sx32. step.
stepz.
step.
step. norm_w32. step.
step. step. if_falsex.
step. step. step. rewrite (unsigned_lit g) by lia. step. replace (tbl + g * 40) with B by lia.
step.
stepz.
step.
step.
step. step. do 8 step.
lazymatch goal with H : rw_cells segs ?mx (bv_unsigned sp + -64) _ |- _ => release_frame H ST (bv_unsigned sp) end.
step. subst B.
apply evt_done. do 3 eexists. eexists. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU]. intros x Hx. cbn in Hx |- *. subst TL. lia. }
split; [exact WM|]. split; [exact MI|].
split. { unfold hdr_cells. destruct (Z.eqb_spec hd 0); [lia|]. unfold ent_addr. rewrite Z2Nat.id by lia. assumption. }
split; [| exact ST].
unfold ins_svs. destruct (Z.eqb_spec hd 0); [lia|].
eapply (lh_slots_write2 segs m); [exact SL | lia | exact Hixl | lia | exact MU | exact WM | | | ].
+ intros i NE1 NE2 Hi. unfold ivs_miss_slot. subst TL.
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn; unfold ent_addr.
* destruct SEP; [right; lia | left; nia].
* assert (Z.of_nat i + 1 <= g \/ g + 1 <= Z.of_nat i) as [L|R] by lia; [left; nia | right; nia].
* assert (i + 1 <= ixl \/ ixl + 1 <= i)%nat as [L|R] by lia; [left; nia | right; nia].
+ unfold ent_addr, slot_cells, new_slot. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Z2Nat.id by lia. subst TL. unfold ent_addr in *. assumption.
+ unfold ent_addr, slot_cells. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Z2Nat.id by lia. subst TL. assumption.
Qed.
End LhStore.

End G.
