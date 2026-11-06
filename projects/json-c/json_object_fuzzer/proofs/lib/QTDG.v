(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo Q8tj QSL3 Q8Q3 Q6WR Q9Mh QPIU QH1t Q7mx QGwP Q6q3 Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply2 Lib.GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3.
Import Q8Q3.
Import Q6WR Q6WR.Mq0.
Import Q9Mh.Mq7.
Import QPIU.Mqh.
Import Q9Mh.Mq5.
Import QH1t.Mq0.
Import Q7mx.Mq1.
Import QH1t.Mq1.
Import QGwP.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition blk_17a68_code : list Z := [0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x01213023; 0x00050413; 0x00853583; 0x02058e63; 0x00000493; 0x00000913; 0x0100006f; 0x00190913; 0x00848493; 0x02b97263; 0x00043503; 0x00950533; 0x00053503; 0xfe0504e3; 0x01843583; 0x000580e7; 0x00843583; 0xfd9ff06f; 0x00043503]%Z.

Definition blk_18a54_code : list Z := [0x00452503; 0x00008067]%Z.

Definition blk_17cb0_code : list Z := [0x00853503; 0x00008067]%Z.

Definition blk_17bbc_code : list Z := [0x00050693; 0x00853503; 0x00a5fe63; 0x00000513; 0x0006b683; 0x00359593; 0x00b685b3; 0x00c5b023; 0x00008067; 0xfff00513; 0x00008067]%Z.

Definition blk_187f8_code : list Z := [0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00050413; 0x02053503; 0x02050063; 0x00843483; 0x00048c63; 0x02043583; 0x00048513; 0x000580e7; 0x0184b483; 0xfe0498e3; 0x01843503]%Z.

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

Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Let e_17a68 : Z := e_alfree.
Let e_187f8 : Z := e_lhfree.
Let e_blk_18934 : Z := e_18934.
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
Hypothesis CODE_e_18934 : code_at segs e_18934 blk_18934_code.
Hypothesis AL_e_18934_b4 : gw_b4 e_18934.
Hypothesis RNG_e_18934_code : gw_br e_18934 288.

Hypothesis AL_e_fn_arr_to_json_string : gw_b4 e_fn_arr_to_json_string.
Hypothesis RNG_e_fn_arr_to_json_string : gw_br e_fn_arr_to_json_string 4.
Hypothesis LAY_POS_e_fn_arr_to_json_string : gw_le 1 e_fn_arr_to_json_string.
Hypothesis LAY_HI_e_fn_arr_to_json_string : gw_le (e_fn_arr_to_json_string + 4) 1099511627776.
Hypothesis AL_e_fn_obj_to_json_string : gw_b4 e_fn_obj_to_json_string.
Hypothesis RNG_e_fn_obj_to_json_string : gw_br e_fn_obj_to_json_string 4.
Hypothesis LAY_POS_e_fn_obj_to_json_string : gw_le 1 e_fn_obj_to_json_string.
Hypothesis LAY_HI_e_fn_obj_to_json_string : gw_le (e_fn_obj_to_json_string + 4) 1099511627776.

Hypothesis nodup_app_l : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QH1t.Mq0.gw_all) (@QH1t.Mq0.nodup_app_l) (base + 488)%Z)) in let T := gw_fold_pcs T base (488)%Z [0; 44; 76; 160]%Z in exact T).
Hypothesis maybe_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QH1t.Mq0.gw_all) (@QH1t.Mq0.maybe_free_cps) (base + 488)%Z)) in let T := gw_fold_pcs T base (488)%Z [0; 44; 76; 160]%Z in exact T).

Hypothesis printbuf_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqd.gw_all) (@QPIU.Mqd.printbuf_free_cps) e_pbfree)) in exact T).
Hypothesis lh_table_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QAyu.Mq2.gw_all) (@QAyu.Mq2.lh_table_free_cps) e_lhfree)) in exact T).
Hypothesis array_list_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mq0.gw_all) (@QPIU.Mq0.array_list_free_cps) e_alfree)) in exact T).

Definition lh_delete_tail_stmt2 := ltac:(let t := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := eval cbv beta delta [QPIU.Mqh.lh_delete_tail_stmt2] in t in let t := eval cbv delta [e_blk_18934] in t in exact t).
Definition next_post := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let t := eval cbv beta delta [Q7mx.Mq1.next_post] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := gw_subst t x lh_delete_tail_stmt2 in exact t).
Definition tyof := ltac:(let t := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.tyof))) in let t := eval cbv beta delta [QH1t.Mq1.tyof] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := gw_subst t x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let t := gw_subst t x next_post in exact t).
Definition head_stmt := ltac:(let t := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.head_stmt))) in let t := eval cbv beta delta [QH1t.Mq1.head_stmt] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := gw_subst t x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let t := gw_subst t x next_post in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.tyof))) in let t := gw_subst t x tyof in exact t).
Definition desc_opt := ltac:(let t := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.desc_opt))) in let t := eval cbv beta delta [QH1t.Mq1.desc_opt] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := gw_subst t x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let t := gw_subst t x next_post in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.tyof))) in let t := gw_subst t x tyof in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.head_stmt))) in let t := gw_subst t x head_stmt in exact t).
Definition cont_stmt := ltac:(let t := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.cont_stmt))) in let t := eval cbv beta delta [QH1t.Mq1.cont_stmt] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := gw_subst t x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let t := gw_subst t x next_post in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.tyof))) in let t := gw_subst t x tyof in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.head_stmt))) in let t := gw_subst t x head_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.desc_opt))) in let t := gw_subst t x desc_opt in exact t).
Definition body_stmt := ltac:(let t := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.body_stmt))) in let t := eval cbv beta delta [QH1t.Mq1.body_stmt] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := gw_subst t x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let t := gw_subst t x next_post in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.tyof))) in let t := gw_subst t x tyof in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.head_stmt))) in let t := gw_subst t x head_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.desc_opt))) in let t := gw_subst t x desc_opt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.cont_stmt))) in let t := gw_subst t x cont_stmt in exact t).

Definition next_post_w := ltac:(let p := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.next_post_w))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let T := gw_subst T x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let T := gw_subst T x next_post in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.tyof))) in let T := gw_subst T x tyof in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.head_stmt))) in let T := gw_subst T x head_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.desc_opt))) in let T := gw_subst T x desc_opt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.cont_stmt))) in let T := gw_subst T x cont_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.body_stmt))) in let T := gw_subst T x body_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.next_post))) in let T := gw_subst T x next_post in let x := constr:(ltac:(gw_ctx2 (@QGwP.Mq1.lh_delete_tail_stmt2))) in let T := gw_subst T x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@QGwP.Mq1.next_post))) in let T := gw_subst T x next_post in let x := constr:(ltac:(gw_ctx2 (@QGwP.Mq1.head_stmt))) in let T := gw_subst T x head_stmt in exact (p : T)).

Definition descend_obj := ltac:(let p := constr:(ltac:(gw_ctx2 (@QGwP.Mq1.descend_obj))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let T := gw_subst T x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let T := gw_subst T x next_post in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.tyof))) in let T := gw_subst T x tyof in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.head_stmt))) in let T := gw_subst T x head_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.desc_opt))) in let T := gw_subst T x desc_opt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.cont_stmt))) in let T := gw_subst T x cont_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.body_stmt))) in let T := gw_subst T x body_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.next_post))) in let T := gw_subst T x next_post in let x := constr:(ltac:(gw_ctx2 (@QGwP.Mq1.lh_delete_tail_stmt2))) in let T := gw_subst T x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@QGwP.Mq1.next_post))) in let T := gw_subst T x next_post in let x := constr:(ltac:(gw_ctx2 (@QGwP.Mq1.head_stmt))) in let T := gw_subst T x head_stmt in exact (p : T)).
Arguments descend_obj _ _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_Z_scope _%_bv_scope _ _ _ _ _ _ _%_list_scope _ _ _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _ _ _%_list_scope _%_list_scope _%_list_scope _%_Z_scope _%_Z_scope _%_Z_scope _ _%_nat_scope.

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
Hypothesis CODE_e_17a68 : code_at segs e_17a68 blk_17a68_code.
Hypothesis CODE_e_18a54 : code_at segs e_18a54 blk_18a54_code.
Hypothesis CODE_e_17cb0 : code_at segs e_17cb0 blk_17cb0_code.
Hypothesis CODE_e_17bbc : code_at segs e_17bbc blk_17bbc_code.
Hypothesis CODE_e_187f8 : code_at segs e_187f8 blk_187f8_code.
Hypothesis CODE_e_17cb8 : code_at segs e_17cb8 blk_17cb8_code.
#[using="w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 joff_24 joff_26 joff_28 joff_34 joff_39 joff_57 joff_63 joff_89 joff_97 joff_101 joff_106 e_pbfree e_alfree e_alread e_17bbc e_17cb0 e_17cb8 e_lhfree e_18934 e_18a54 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_24 E_24 D_26 E_26 D_28 E_28 D_34 E_34 D_39 E_39 D_57 E_57 D_63 E_63 D_89 E_89 D_97 E_97 D_101 E_101 D_106 E_106 LINK_24 LINK_26 LINK_28 LINK_34 LINK_39 LINK_57 LINK_63 LINK_89 LINK_97 LINK_101 LINK_106 CODE_e_18934 AL_e_18934_b4 RNG_e_18934_code AL_e_fn_arr_to_json_string RNG_e_fn_arr_to_json_string LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string AL_e_fn_obj_to_json_string RNG_e_fn_obj_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string nodup_app_l maybe_free_cps printbuf_free_cps lh_table_free_cps array_list_free_cps CODE_e_17a68 CODE_e_18a54 CODE_e_17cb0 CODE_e_17bbc CODE_e_187f8 CODE_e_17cb8 S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

Section BodyO.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (sp gp s10 s11 : word) (lo : Z) (errv : word).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -96 - (32 + 32 + 16 + 8256).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis DEL : lh_delete_tail_stmt2 HIx.

#[using="w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 joff_97 e_alfree e_lhfree e_18934 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_97 E_97 LINK_97 LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string nodup_app_l maybe_free_cps S4F LO LOS SPA HT DEL"] Lemma body_obj_ok : forall kids k,
desc_opt HIx sp gp s10 s11 lo errv k ->
cont_stmt HIx sp gp s10 s11 lo errv true kids ->
head_stmt HIx sp gp s10 s11 lo errv true kids ->
body_stmt HIx sp gp s10 s11 lo errv true kids k.
Proof. clear - w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 joff_97 e_alfree e_lhfree e_18934 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_97 E_97 LINK_97 LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string nodup_app_l maybe_free_cps S4F LO LOS SPA HT DEL HIx sp gp s10 s11 lo errv. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros kids k KD CONT HEADK.
unfold body_stmt. intros until cur. intros HP ZB ST ERR K.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct ZB as (t & tbl & size & es & svs & e0 & Z0 & He0 & Ecur).
destruct (zobj_last segs S4F _ _ _ _ _ _ _ _ _ _ _ _ Z0) as (pb & PBS & KBS1 & bs & esk1 & e & esz & Ees & Lk & Lz & Fz & EX & OPB & HDR & OPEN & OK1 & Hk).
assert (Ee : e0 = e) by (rewrite Ees, <- Lk, nth_error_app_len in He0; injection He0 as He0; symmetry; exact He0). subst e0.
clear Z0.

pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as NDall.
assert (HPl : HEAPx A (lh_blocks t tbl size es ++ ((x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB)) m md).
{ eapply (heap_perm S4L HIx); [exact HP | rewrite EX; perm]. }
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HPl) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & Httb & KEYF).
cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP INx) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP INx) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
assert (INtb : In (tbl, 40 * size) (XBS ++ LB)) by (rewrite EX; unfold lh_blocks; in_elem).
assert (NXT : x <> tbl).
{ intros E. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HPl) as ND. unfold lh_blocks in ND. cbn [map blk_addr fst app] in ND.
inversion ND as [|y l Hn1 ND1]; subst. inversion ND1 as [|y' l' Hn2 ND2]; subst. apply Hn2.
rewrite map_app. apply in_or_app. right. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ x 48 tbl (40 * size) HP INx INtb NXT) as Dxtb.

destruct (lh_open_slot segs S4F _ _ _ _ _ _ _ (length kids) e OPEN ltac:(rewrite Ees, <- Lk; apply nth_error_app_len)) as (sl & Esl & Hix & SLOT).
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
assert (Hixz : 0 <= Z.of_nat (le_ix e) /\ Z.of_nat (le_ix e) + 1 <= size) by lia.
unfold ent_addr in SLOT, Ecur. subst cur.
set (ea := tbl + 40 * Z.of_nat (le_ix e)) in *.
assert (EAR : tbl <= ea /\ ea + 40 <= tbl + 40 * size) by (subst ea; lia).
pose proof (wmono_refl segs m) as WM. pose proof (munch_refl [(ea + 16, ea + 24)] m) as MU.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app] in HDR.
stash Hk. stash KEYF. stash OPB. stash OK1. stash HDR0. cbn [tyof].
apply rz_evt; [exact MOK|].
step. if_false. step. if_false. step. stepz.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
assert (HPtb : HEAPx A ((tbl, 40 * size) :: (t, 56) :: map kblk es ++ (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB) m md).
{ eapply (heap_perm S4L HIx); [exact HPl | unfold lh_blocks; perm]. }
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp + -96) HPtb MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; in_sub Hb) ltac:(clia))
as (HP2 & AG2 & HPR2).
unstash KEYF.
assert (OPEN2 : lh_open segs S4F m2 t tbl size (esk1 ++ with_v e 0 :: esz) (upd svs (le_ix e) (sv_with_v sl 0))).
{ replace (esk1 ++ with_v e 0 :: esz) with (upd es (length kids) (with_v e 0)) by (rewrite Ees, <- Lk; apply upd_app_len').
eapply (lh_open_set_val segs S4F); [exact OPEN | rewrite Ees, <- Lk; apply nth_error_app_len | exact Esl | lia | exact MU | exact WM | | exact Httb | | ].
- apply Forall_cons; [cbn; subst ea; unfold ent_addr; lia | apply Forall_nil].
- intros y Hy. destruct (KEYF y Hy) as (_ & _ & _ & _ & _ & D). exact D.
- unfold ent_addr. fold ea. exact SLOT. }
stash KEYF.

set (es2 := esk1 ++ with_v e 0 :: esz) in OPEN2.
set (svs2 := upd svs (le_ix e) (sv_with_v sl 0)) in OPEN2.
set (XBS1 := ((x, 48) :: lh_blocks t tbl size es ++ concat KBS1) ++ PBS).
assert (ELB : lh_blocks t tbl size es2 = lh_blocks t tbl size es).
{ subst es2. rewrite Ees. unfold lh_blocks. rewrite !map_app. reflexivity. }
assert (Z2 : zobj segs S4F m2 x q kids (S nz) t tbl size es2 svs2 XBS1).
{ unstash HDR0. unstash OPB. unstash OK1. subst XBS1. rewrite <- ELB.
eapply (zobj_last_close segs S4F m m2); [exact Lz | exact Fz | exact OPB | exact HDR0 | exact OK1 | exact OPEN2 | ].
eapply agree_on_incl; [exact AG2 | intros b Hb; in_sub Hb]. }
assert (Hes2 : nth_error es2 (length kids) = Some (with_v e 0)) by (subst es2; rewrite <- Lk; apply nth_error_app_len).
assert (VZ2 : forall j y, (length kids <= j)%nat -> nth_error es2 j = Some y -> le_v y = 0).
{ intros j y Hj Hy. subst es2. rewrite nth_error_app2 in Hy by lia.
destruct (j - length esk1)%nat as [|j'] eqn:Ej; cbn in Hy.
- injection Hy as <-. reflexivity.
- exact (proj1 (Forall_forall _ _) Fz y (nth_error_In _ _ Hy)). }
clear HDR0 OPB OK1 OPEN.
step.
unstash Hk. destruct k as [c|].
-
destruct Hk as [Hv J].
assert (J2 : jval segs S4F c m2 bs (le_v e) 1) by (eapply jval_agree; [exact J | exact AG2 | intros b Hb; in_sub Hb]). clear J.
assert (HPc : HEAPx A (bs ++ XBS1 ++ LB) m2 md) by (eapply (heap_perm S4L HIx); [exact HP2 | subst XBS1; hperm]).
pose proof (nodup_app_l _ _ (heap_blk_nodup S4L HIx _ _ _ _ HPc)) as NDbs.
destruct (jval_hdr segs S4F c m2 bs (le_v e) 1 J2 NDbs) as (cn & tojs_ & pb_ & udel_ & ud_ & rest_ & INc & _ & N48c & _ & _).
pose proof (heap_blk S4L HIx _ _ _ _ (le_v e) cn HPc ltac:(in_sub INc)) as (_ & Hcal & Hclo & Hchi & _). clear tojs_ pb_ udel_ ud_ rest_.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hchi.
if_truex. step. step. step.
apply evt_RZ_done.
eapply (maybe_free_cps HIx) with (s := c) (BS := bs) (LB := XBS1 ++ LB) (x := le_v e) (rc := 1) (lo := lo);
[ exact HPc | lia | lia | exact J2 | .. ]; try alloc_side.
intros ms3 md3 (m3 & A3 & r & RS3 & VM3 & ST3 & HPR3 & ERR3 & OUT3).
destruct RS3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR3 by lia.
match goal with H : rw_cells _ m2 x _ |- _ => rename H into HDR2 end.
match goal with H : rw_cells _ m2 ea _ |- _ => rename H into SLOT2 end.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in HDR2; [| eapply client_range_block; [subst XBS1; in_elem | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in SLOT2; [| eapply (client_range_block S4L _ _ _ _ tbl (40 * size)); [subst XBS1; unfold lh_blocks; in_elem | lia | cbn; lia]]. cbn [hl_segs S4L] in SLOT2.
assert (Z3 : zobj segs S4F m3 x q kids (S nz) t tbl size es2 svs2 XBS1).
{ eapply (zobj_agree segs S4F (XBS1 ++ LB)); [exact Z2 | eapply (agree_of_heap_pres segs S4L); [exact HPR3 | reflexivity | intros b Hb; exact Hb] | intros b Hb; in_sub Hb]. }
assert (HPR23 : heap_pres S4L LB (bv_unsigned sp + -96) m m3).
{ eapply heap_pres_trans; [exact HPR2 | eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; in_sub Hb]]. }
clear MU WM MI HP2 HPtb HPl HP AG2 Z2 ST J2 HPc.
destruct OUT3 as [(_ & Habs & _) | [(-> & _ & HP3) | (-> & _ & ZC & HP3)]]; [lia | |].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m3) as MU. pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. if_falsex. step. norm_w32. step. if_false. step. step. step.
apply evt_RZ_done.
replace (Z.of_nat nz + 1) with (Z.of_nat (S nz)) by lia.
eapply CONT; [exact HP3 | | exact ST3 | exact ERR3 |].
* exists t, tbl, size, es2, svs2. split; [exact Z3|].
intros kids1 kl Ek.
assert (Hj : (length kids1 < length esk1)%nat) by (rewrite Lk, Ek, length_app; cbn; lia).
destruct (nth_error esk1 (length kids1)) as [e'|] eqn:En; [| apply nth_error_None in En; lia].
exists e'. split; [subst es2; rewrite nth_error_app1 by lia; exact En|].
rewrite pv_of_spec, Ek, length_app. cbn [length]. rewrite Nat.add_1_r. cbn [pv_of].
rewrite Ees, nth_error_app1 by lia. rewrite En. reflexivity.
* intros ms' md' NP. apply K. eapply next_post_w; [exact FS3 | exact FRM3 | exact VM3 | exact HPR23 | exact NP].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m3) as MU. pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. if_true.
apply evt_RZ_done.
eapply (descend_obj HIx sp gp s10 s11 lo errv LO LOS SPA HT DEL c kids KD HEADK) with (e2 := with_v e 0); [exact HP3 | exact ZC | exact Z3 | exact Hes2 | exact ST3 | exact ERR3 |].
intros ms' md' NP. apply K. eapply next_post_w; [exact FS3 | exact FRM3 | exact VM3 | exact HPR23 | exact NP].
-
destruct Hk as [Hv Ebs]. rewrite Hv. if_false. step. step. norm_w32. step. if_false. step. step. step.
apply evt_RZ_done.
replace (Z.of_nat nz + 1) with (Z.of_nat (S nz)) by lia.
assert (HPn : HEAPx A (XBS1 ++ LB) m2 md) by (eapply (heap_perm S4L HIx); [exact HP2 | subst XBS1 bs; hperm]).
eapply CONT; [exact HPn | | exact ST | | ].
+ exists t, tbl, size, es2, svs2. split; [exact Z2|].
intros kids1 kl Ek.
assert (Hj : (length kids1 < length esk1)%nat) by (rewrite Lk, Ek, length_app; cbn; lia).
destruct (nth_error esk1 (length kids1)) as [e'|] eqn:En; [| apply nth_error_None in En; lia].
exists e'. split; [subst es2; rewrite nth_error_app1 by lia; exact En|].
rewrite pv_of_spec, Ek, length_app. cbn [length]. rewrite Nat.add_1_r. cbn [pv_of].
rewrite Ees, nth_error_app1 by lia. rewrite En. reflexivity.
+ assumption.
+ intros ms' md' NP. apply K. eapply next_post_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | exact HPR2 | exact NP].
Qed.
End BodyO.

End RC__1.

End G.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Mh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Mh.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Mh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Mh.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAyu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAyu.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7mx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7mx.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QH1t.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH1t.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGwP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGwP.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPIU.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwApply2 GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition blk_18514_code (wb18514_14 wb18514_21 wb18514_53 wb18514_75 wb18514_77 : Z) : list Z :=
[0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x00050913; 0x02853a03; 0x03053a83; 0x00058993; 0x00100513; 0x03800593; wb18514_14; 0x0c050063; 0x00050413; 0x01352023; 0x00052223; 0x02800593; 0x00098513; wb18514_21; 0x00a43c23; 0xfff00493; 0x0c050863; 0x02043023; 0x03443423; 0x03543823; 0x03305063; 0x02800593; 0x02b985b3; 0x00b505b3; 0xfff00613; 0x00c53023; 0x02850513; 0xfeb51ce3; 0x00893a03; 0x020a0e63; 0x000a3503; 0x02843583; 0x000580e7; 0x00050693; 0x000a3583; 0x008a2503; 0x010a3603; 0x00a03733; 0x00271713; 0x00040513; 0x0a0000ef; 0x04051063; 0x018a3a03; 0xfc0a16e3; 0x01893503; wb18514_53; 0x00000493; 0x00843503; 0x01043583; 0x01843603; 0x01392023; 0x00a93423; 0x00b93823; 0x00c93c23; 0x0380006f; 0xfff00493; 0x0380006f; 0x02043503; 0x02050063; 0x00843903; 0x00090c63; 0x02043583; 0x00090513; 0x000580e7; 0x01893903; 0xfe0918e3; 0x01843503; wb18514_75; 0x00040513; wb18514_77; 0x00048513; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x04010113; 0x00008067]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_10 w_11 : Z).
Variables (hi_10 : bv 20).
Variables (lo_11 : bv 12).
Variables (G_10770 GGOT4 GHASH4 GVDSO4 : Z).
Variables (e_blk_18514 : Z).
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

Definition gLAYF0 : Prop := ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Variables (JG_CGT_P gRDATA_LO : Z).
Let vdso_ok4 : Z -> Prop := fun vf => (vf = JG_CGT_P \/ vf = 0)%Z.
Hypothesis CODE : code_at segs base (lhprobe_code w_10 w_11).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 388.
Hypothesis D_10 : decode_any (Z_to_bv 32 w_10) = Some (Auipc 17 hi_10, 4%Z).
Hypothesis E_10 : is_ecall (Z_to_bv 32 w_10) = false.
Hypothesis D_11 : decode_any (Z_to_bv 32 w_11) = Some (FLoad FMT_D 15 17 lo_11, 4%Z).
Hypothesis E_11 : is_ecall (Z_to_bv 32 w_11) = false.
Hypothesis ANCH_11 : gw_anch (Z.shiftl (bv_signed hi_10) 12 + (base + 40) + bv_signed lo_11)%Z G_10770.
Variable wb18514_14 : Z.  Variable joffb18514_14 : bv 21.
Hypothesis D_b18514_14 : decode_any (Z_to_bv 32 wb18514_14) = Some (Jal 1 joffb18514_14, 4%Z).
Hypothesis E_b18514_14 : is_ecall (Z_to_bv 32 wb18514_14) = false.
Hypothesis LINK_b18514_14 : gw_anch (e_blk_18514 + 56 + bv_signed joffb18514_14)%Z e_calloc.
Variable wb18514_21 : Z.  Variable joffb18514_21 : bv 21.
Hypothesis D_b18514_21 : decode_any (Z_to_bv 32 wb18514_21) = Some (Jal 1 joffb18514_21, 4%Z).
Hypothesis E_b18514_21 : is_ecall (Z_to_bv 32 wb18514_21) = false.
Hypothesis LINK_b18514_21 : gw_anch (e_blk_18514 + 84 + bv_signed joffb18514_21)%Z e_calloc.
Variable wb18514_53 : Z.  Variable joffb18514_53 : bv 21.
Hypothesis D_b18514_53 : decode_any (Z_to_bv 32 wb18514_53) = Some (Jal 1 joffb18514_53, 4%Z).
Hypothesis E_b18514_53 : is_ecall (Z_to_bv 32 wb18514_53) = false.
Hypothesis LINK_b18514_53 : gw_anch (e_blk_18514 + 212 + bv_signed joffb18514_53)%Z e_free.
Variable wb18514_75 : Z.  Variable joffb18514_75 : bv 21.
Hypothesis D_b18514_75 : decode_any (Z_to_bv 32 wb18514_75) = Some (Jal 1 joffb18514_75, 4%Z).
Hypothesis E_b18514_75 : is_ecall (Z_to_bv 32 wb18514_75) = false.
Hypothesis LINK_b18514_75 : gw_anch (e_blk_18514 + 300 + bv_signed joffb18514_75)%Z e_free.
Variable wb18514_77 : Z.  Variable joffb18514_77 : bv 21.
Hypothesis D_b18514_77 : decode_any (Z_to_bv 32 wb18514_77) = Some (Jal 1 joffb18514_77, 4%Z).
Hypothesis E_b18514_77 : is_ecall (Z_to_bv 32 wb18514_77) = false.
Hypothesis LINK_b18514_77 : gw_anch (e_blk_18514 + 308 + bv_signed joffb18514_77)%Z e_free.
Hypothesis CODE_e_blk_18514 : code_at segs e_blk_18514 (blk_18514_code wb18514_14 wb18514_21 wb18514_53 wb18514_75 wb18514_77).
Hypothesis AL_e_blk_18514_b4 : gw_b4 e_blk_18514.
Hypothesis RNG_e_blk_18514_code : gw_br e_blk_18514 352.
Hypothesis RNG_GGOT4 : gw_br GGOT4 8.
Hypothesis AL_GGOT4 : gw_al GGOT4 8.
Hypothesis RNG_GHASH4 : gw_br GHASH4 8.
Hypothesis AL_GHASH4 : gw_al GHASH4 8.
Hypothesis RNG_GVDSO4 : gw_br GVDSO4 8.
Hypothesis AL_GVDSO4 : gw_al GVDSO4 8.
Hypothesis LAY_GGOT4_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASH4_GVDSO4 : gw_le (GHASH4 + 8) GVDSO4.
Hypothesis RNG_G_10770 : gw_br G_10770 8.
Hypothesis ROM_G_10770 : ro_bytes segs G_10770 [Z_to_bv 8 31; Z_to_bv 8 133; Z_to_bv 8 235; Z_to_bv 8 81; Z_to_bv 8 184; Z_to_bv 8 30; Z_to_bv 8 229; Z_to_bv 8 63].

Hypothesis AL_e_fn_lh_char_equal : gw_b4 e_fn_lh_char_equal.
Hypothesis RNG_e_fn_lh_char_equal : gw_br e_fn_lh_char_equal 4.
Hypothesis LAY_POS_e_fn_lh_char_equal : gw_le 1 e_fn_lh_char_equal.
Hypothesis LAY_HI_e_fn_lh_char_equal : gw_le (e_fn_lh_char_equal + 4) 1099511627776.
Hypothesis AL_e_fn_lh_char_hash : gw_b4 e_fn_lh_char_hash.
Hypothesis RNG_e_fn_lh_char_hash : gw_br e_fn_lh_char_hash 4.
Hypothesis LAY_POS_e_fn_lh_char_hash : gw_le 1 e_fn_lh_char_hash.
Hypothesis LAY_HI_e_fn_lh_char_hash : gw_le (e_fn_lh_char_hash + 4) 1099511627776.

Definition ins_svs := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q7mx.ins_svs))) in let t := eval cbv beta delta [Q7mx.ins_svs] in t in exact t).
Definition ins_frame := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q7mx.ins_frame))) in let t := eval cbv beta delta [Q7mx.ins_frame] in t in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_svs))) in let t := gw_subst t x ins_svs in exact t).
Definition hdr_cells := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q7mx.hdr_cells))) in let t := eval cbv beta delta [Q7mx.hdr_cells] in t in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_svs))) in let t := gw_subst t x ins_svs in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_frame))) in let t := gw_subst t x ins_frame in exact t).

Definition lh_insert_tail := ltac:(let p := constr:(ltac:(gw_ctx2 (@QGwP.lh_insert_tail))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_svs))) in let T := gw_subst T x ins_svs in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_frame))) in let T := gw_subst T x ins_frame in let x := constr:(ltac:(gw_ctx2 (@Q7mx.hdr_cells))) in let T := gw_subst T x hdr_cells in let x := constr:(ltac:(gw_ctx2 (@QGwP.ins_svs))) in let T := gw_subst T x ins_svs in let x := constr:(ltac:(gw_ctx2 (@QGwP.ins_frame))) in let T := gw_subst T x ins_frame in let x := constr:(ltac:(gw_ctx2 (@QGwP.hdr_cells))) in let T := gw_subst T x hdr_cells in exact (p : T)).

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
Hypothesis VOL_GVDSO4 : forall a, (GVDSO4 <= a < GVDSO4 + 8)%Z -> gVOL a.
Hypothesis LAY_RDATA_GGOT4 : gw_le gRDATA_LO GGOT4.
Hypothesis LAY_GHASH4x12_GVDSO4 : gw_le (GHASH4 + 12) GVDSO4.
Hypothesis LAY_IMG_GGOT4 : gw_le gIMG_LO GGOT4.
Hypothesis LAY_GVDSO4_IMG : gw_le (GVDSO4 + 8) gIMG_HI.
Hypothesis AL_e_fn_lh_entry_free : gw_b4 e_fn_lh_entry_free.
Hypothesis RNG_e_fn_lh_entry_free : gw_br e_fn_lh_entry_free 4.
Hypothesis LAY_POS_e_fn_lh_entry_free : gw_le 1 e_fn_lh_entry_free.
Hypothesis LAY_HI_e_fn_lh_entry_free : gw_le (e_fn_lh_entry_free + 4) 1099511627776.
#[using="w_10 w_11 hi_10 lo_11 G_10770 GGOT4 GHASH4 GVDSO4 e_blk_18514 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free JG_CGT_P gRDATA_LO CODE BASE4 BASER D_10 E_10 D_11 E_11 ANCH_11 wb18514_14 joffb18514_14 D_b18514_14 E_b18514_14 LINK_b18514_14 wb18514_21 joffb18514_21 D_b18514_21 E_b18514_21 LINK_b18514_21 wb18514_53 joffb18514_53 D_b18514_53 E_b18514_53 LINK_b18514_53 wb18514_75 joffb18514_75 D_b18514_75 E_b18514_75 LINK_b18514_75 wb18514_77 joffb18514_77 D_b18514_77 E_b18514_77 LINK_b18514_77 CODE_e_blk_18514 AL_e_blk_18514_b4 RNG_e_blk_18514_code RNG_GGOT4 AL_GGOT4 RNG_GHASH4 AL_GHASH4 RNG_GVDSO4 AL_GVDSO4 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 RNG_G_10770 ROM_G_10770 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal AL_e_fn_lh_char_hash RNG_e_fn_lh_char_hash LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash CS_GHASH4 CS_GGOT4 CS_GVDSO4 VOL_GVDSO4 LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG AL_e_fn_lh_entry_free RNG_e_fn_lh_entry_free LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.
Local Tactic Notation "gj_rv" ident(h) := try revert h.

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
Ltac gj_fn_cbn := try (progress cbn [S4F fn_lh_entry_free]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section RC__1.

Definition lh_insert_entry : Z := (base + 0x0).
Definition lh_resize_entry : Z := (e_blk_18514 + 0x0).

Definition strip (e : lent) : Z * Z * list byte * Z := (le_k e, le_kn e, le_ks e, le_v e).

Definition fsaved_caller_saved3 : Prop := forall F a b c,
QCcH.fsaved F (bvmap_set 13 a (bvmap_set 14 b (bvmap_set 15 c F))).

Section LhInsert2.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation lh_glob4 := (lh_glob segs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).
Hypothesis LF : lf_test_spec.

Variable MREL : Model -> Model -> Prop.
Hypothesis MREL_refl : forall md, MREL md md.
Hypothesis MREL_trans : forall a b c, MREL a b -> MREL b c -> MREL a c.
Hypothesis MREL_vm : forall a b, model_vm_only a b -> MREL a b.

Definition lh_resize_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo t tbl size ns : Z) (es : list lent) (svs : list slotv)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
MREL md md' /\ stk segs m' lo (bv_unsigned sp) /\ heap_presx S4L gVOL LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\ lh_glob4 m' /\
( (r = 2^64 - 1 /\ lh_open segs S4F m' t tbl size es svs /\ HEAPx A' (lh_blocks t tbl size es ++ LB) m' md')
\/ (r = 0 /\ exists tbl' es' svs', map strip es' = map strip es /\
lh_open segs S4F m' t tbl' ns es' svs' /\ HEAPx A' (lh_blocks t tbl' ns es' ++ LB) m' md') ).

Definition lh_resize_stmt (RD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (t tbl size ns : Z) (es : list lent) (svs : list slotv),
HEAPx A (lh_blocks t tbl size es ++ LB) m md ->
lh_open segs S4F m t tbl size es svs -> lh_glob4 m ->
In ns lf_sizes -> lf_thr size + 1 <= lf_thr ns ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 ns ->
(forall ms' md', lh_resize_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo t tbl size ns es svs ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_resize_entry) fc None m (seg_rom segs)) md) T.

Definition lh_insert_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo t tbl size : Z) (es : list lent) (svs : list slotv)
(k kn : Z) (ks : list byte) (v : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
MREL md md' /\ stk segs m' lo (bv_unsigned sp) /\ heap_presx S4L gVOL LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\ lh_glob4 m' /\
( (r = 2^64 - 1 /\ lh_open segs S4F m' t tbl size es svs /\ cstr segs m' k kn ks /\
HEAPx A' (lh_blocks t tbl size es ++ (k, kn) :: LB) m' md')
\/ (r = 0 /\ exists tbl' size' es' svs' (g : nat), map strip es' = map strip es /\
lh_open segs S4F m' t tbl' size' (es' ++ [LE g k kn ks v]) svs' /\
HEAPx A' (lh_blocks t tbl' size' (es' ++ [LE g k kn ks v]) ++ LB) m' md') ).

Definition lh_insert_fix_post (ffn : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo t tbl size : Z) (es : list lent)
(k kn : Z) (ks : list byte) (v : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (errv' : word) svs' (g : nat),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' /\
MREL md md' /\ stk segs m' lo (bv_unsigned sp) /\ heap_presx S4L gVOL LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\ lh_glob4 m' /\
lh_openf segs S4F ffn m' t tbl size (es ++ [LE g k kn ks v]) svs' /\
HEAPx A' (lh_blocks t tbl size (es ++ [LE g k kn ks v]) ++ LB) m' md'.

Definition lf_size_cases : Prop := forall S, In S lf_sizes -> S <= 2^29 \/ S = 1073741824 \/ S = 2147483647.

Section Finish.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo t : Z).
Variables (k kn : Z) (ks : list byte) (v : Z) (T : TSet) (ffn : Z).
Hypothesis Hffn : 0 <= ffn < 2^64.
Hypothesis Hkn : kn <= 2^31.

Definition lh_insert_finish : Prop := gw_uses Hffn (gw_uses Hkn (forall (tbl size : Z) (es : list lent) (svs : list slotv) (h : Z)
(x1 x5 x6 x7 x8 x9 x15 x17 x18 x19 x20 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (errv : word) (junk8 : list byte),
HEAPx A (lh_blocks t tbl size es ++ (k, kn) :: LB) m md ->
lh_openf segs S4F ffn m t tbl size es svs ->
Z.of_nat (length es) + 1 <= lf_thr size ->
cstr segs m k kn ks -> 0 <= v < 2^64 -> 0 <= h < 2^64 ->
lh_glob4 m ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
ins_frame sp ra s0 s1 s2 s3 s4 s5 m junk8 ->
rw_cells segs m (gTP - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
QCcH.fsaved F F1 -> (QCcH.frm0 fc -> QCcH.frm0 fc1) ->
MREL md0 md -> heap_presx S4L gVOL LB (bv_unsigned sp) m0 m ->
(forall ms' md', lh_insert_fix_post ffn ra sp gp (Z_to_bv 64 gTP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo t tbl size es k kn ks v ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) x5 x6 x7 x8 x9
(Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 h) (Z_to_bv 64 0) x15 (Z_to_bv 64 size) x17
x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x44)) fc1 None m (seg_rom segs)) md) T)).
End Finish.

Definition lh_insert_prologue : Prop := gw_uses LF (forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (t tbl size : Z) (es : list lent) (svs : list slotv) (lo ffn : Z),
mem_inv segs m -> frm0 fc ->
lh_openf segs S4F ffn m t tbl size es svs -> lh_below lo t tbl size es ->
stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
evt segs (fun ms' => exists fc' m' junk8,
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1 a2 a3 a4
(bword (lf_thr size <=? Z.of_nat (length es))) (Z_to_bv 64 size) (Z_to_bv 64 (Z.shiftl (bv_signed hi_10) 12 + (base + 40)))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 13 (fcvt_d_w RNE (Z_to_bv 64 size)) (bvmap_set 14 (fcvt_d_w RNE (Z_to_bv 64 (Z.of_nat (length es))))
(bvmap_set 15 (fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 size)) (Z_to_bv 64 K066)) F)))
(Z_to_bv 64 (base + 0x40)) fc' None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ frm0 fc'
/\ ins_frame sp ra s0 s1 s2 s3 s4 s5 m' junk8 /\ stk segs m' lo (bv_unsigned sp + -64)
/\ lh_openf segs S4F ffn m' t tbl size es svs)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_insert_entry) fc None m (seg_rom segs))).

Definition lh_insert_cps : Prop := gw_uses LF (gw_uses MREL_refl (forall (RD : Z), lh_resize_stmt RD -> 0 <= RD ->
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (svs : list slotv)
(k kn : Z) (ks : list byte) (v h : Z),
HEAPx A (lh_blocks t tbl size es ++ (k, kn) :: LB) m md ->
lh_open segs S4F m t tbl size es svs -> lh_glob4 m -> cstr segs m k kn ks -> kn <= 2^31 ->
0 <= v < 2^64 -> 0 <= h < 2^64 ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - RD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v -> a3 = Z_to_bv 64 h -> a4 = Z_to_bv 64 0 ->
(forall ms' md', lh_insert_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo t tbl size es svs k kn ks v ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_insert_entry) fc None m (seg_rom segs)) md) T)).

Definition lh_insert_small_cps : Prop := gw_uses LF (gw_uses MREL_refl (forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (svs : list slotv)
(k kn : Z) (ks : list byte) (v h ffn : Z),
HEAPx A (lh_blocks t tbl size es ++ (k, kn) :: LB) m md ->
lh_openf segs S4F ffn m t tbl size es svs -> lh_glob4 m -> cstr segs m k kn ks -> kn <= 2^31 -> 0 <= ffn < 2^64 ->
Z.of_nat (length es) + 1 <= lf_thr size -> 0 <= v < 2^64 -> 0 <= h < 2^64 ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v -> a3 = Z_to_bv 64 h -> a4 = Z_to_bv 64 0 ->
(forall ms' md', lh_insert_fix_post ffn ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo t tbl size es k kn ks v ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_insert_entry) fc None m (seg_rom segs)) md) T)).
End LhInsert2.

End RC__1.

End G.
