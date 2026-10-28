(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Mh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Mh.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Mh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Mh.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QAyu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAyu.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7mx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7mx.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH1t.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH1t.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGwP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGwP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QTDG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTDG.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPIU.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwApply2 GwApplyJ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition lhresize_code (w_14 w_21 w_53 w_75 w_77 : Z) : list Z :=
[0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x14050063; 0x00050913; 0x00757513; 0x12051a63; 0x00058993; 0x02893a03; 0x03093a83; 0x00100513; 0x03800593; w_14; 0x0e050263; 0x00050413; 0x00757513; 0x10051663; 0x01342023; 0x00042223; 0x02800593; 0x00098513; w_21; 0x00a43c23; 0xfff00493; 0x0e050c63; 0x02043023; 0x03443423; 0x03543823; 0x03305a63; 0x00000593; 0xfff54613; 0x00757693; 0x02800713; 0x02e98733; 0xfff00793; 0x0cb66063; 0x0a069e63; 0x00b50833; 0x02858593; 0x00f83023; 0xfeb716e3; 0x00893a03; 0x040a0263; 0x007a7513; 0x08051e63; 0x000a3503; 0x02843583; 0x000580e7; 0x00050693; 0x000a3583; 0x008a2503; 0x010a3603; 0x00a03733; 0x00271713; 0x00040513; 0x0ac000ef; 0x04051063; 0x018a3a03; 0xfc0a12e3; 0x01893503; w_53; 0x00000493; 0x00843503; 0x01043583; 0x01843603; 0x01392023; 0x00a93423; 0x00b93823; 0x00c93c23; 0x0440006f; 0xfff00493; 0x0440006f; 0x02043503; 0x02050663; 0x00840913; 0x00093903; 0x02090063; 0x02043583; 0x00090513; 0x000580e7; 0x00797513; 0x01890913; 0xfe0502e3; 0xc0001073; 0x01843503; w_75; 0x00040513; w_77; 0x00048513; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x04010113; 0x00008067]%Z.


Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_14 w_21 w_53 w_75 w_77 : Z).
Variables (joff_14 joff_21 joff_53 joff_75 joff_77 : bv 21).
Variables (GGOT4 GHASH4 GVDSO4 : Z).
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
Let e_blk_18514 : Z := base.
Variables (JG_CGT_P gRDATA_LO : Z).
Let vdso_ok4 : Z -> Prop := fun vf => (vf = JG_CGT_P \/ vf = 0)%Z.
Hypothesis CODE : code_at segs base (lhresize_code w_14 w_21 w_53 w_75 w_77).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 412.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Jal 1 joff_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Jal 1 joff_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis D_53 : decode_any (Z_to_bv 32 w_53) = Some (Jal 1 joff_53, 4%Z).
Hypothesis E_53 : is_ecall (Z_to_bv 32 w_53) = false.
Hypothesis D_75 : decode_any (Z_to_bv 32 w_75) = Some (Jal 1 joff_75, 4%Z).
Hypothesis E_75 : is_ecall (Z_to_bv 32 w_75) = false.
Hypothesis D_77 : decode_any (Z_to_bv 32 w_77) = Some (Jal 1 joff_77, 4%Z).
Hypothesis E_77 : is_ecall (Z_to_bv 32 w_77) = false.
Hypothesis LINK_14 : gw_anch (base + 68 + bv_signed joff_14)%Z e_calloc.
Hypothesis LINK_21 : gw_anch (base + 104 + bv_signed joff_21)%Z e_calloc.
Hypothesis LINK_53 : gw_anch (base + 260 + bv_signed joff_53)%Z e_free.
Hypothesis LINK_75 : gw_anch (base + 360 + bv_signed joff_75)%Z e_free.
Hypothesis LINK_77 : gw_anch (base + 368 + bv_signed joff_77)%Z e_free.
Hypothesis AL_e_blk_17d8c_b4 : gw_b4 e_fn_lh_char_hash.
Hypothesis RNG_e_blk_17d8c_code : gw_br e_fn_lh_char_hash 1712.
Hypothesis RNG_GGOT4 : gw_br GGOT4 8.
Hypothesis AL_GGOT4 : gw_al GGOT4 8.
Hypothesis RNG_GHASH4 : gw_br GHASH4 8.
Hypothesis AL_GHASH4 : gw_al GHASH4 8.
Hypothesis RNG_GVDSO4 : gw_br GVDSO4 8.
Hypothesis AL_GVDSO4 : gw_al GVDSO4 8.
Hypothesis LAY_GGOT4_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASH4_GVDSO4 : gw_le (GHASH4 + 8) GVDSO4.

Definition hdr_cells := ltac:(let t := constr:(ltac:(gw_callee_stmt (@Q7mx.gw_all) (@Q7mx.hdr_cells) 0%Z)) in let t := eval cbv beta delta [Q7mx.hdr_cells] in t in exact t).

Definition lh_resize_entry : Z := (base + 0)%Z.
Definition strip := ltac:(let t := constr:(ltac:(gw_callee_stmt (@QTDG.gw_all) (@QTDG.strip) (base + 412)%Z)) in let t := eval cbv beta delta [QTDG.strip] in t in let t := eval cbv beta delta [e_blk_18514 QTDG.lh_insert_entry QTDG.lh_resize_entry] in t in let x := constr:(ltac:(gw_callee_stmt (@Q7mx.gw_all) (@Q7mx.hdr_cells) 0%Z)) in let t := gw_subst t x hdr_cells in exact t).
Definition lh_resize_post := ltac:(let t := constr:(ltac:(gw_callee_stmt (@QTDG.gw_all) (@QTDG.lh_resize_post) (base + 412)%Z)) in let t := eval cbv beta delta [QTDG.lh_resize_post] in t in let t := eval cbv beta delta [e_blk_18514 QTDG.lh_insert_entry QTDG.lh_resize_entry] in t in let x := constr:(ltac:(gw_callee_stmt (@Q7mx.gw_all) (@Q7mx.hdr_cells) 0%Z)) in let t := gw_subst t x hdr_cells in let x := constr:(ltac:(gw_callee_stmt (@QTDG.gw_all) (@QTDG.strip) (base + 412)%Z)) in let t := gw_subst t x strip in exact t).
Definition lh_resize_stmt := ltac:(let t := constr:(ltac:(gw_callee_stmt (@QTDG.gw_all) (@QTDG.lh_resize_stmt) (base + 412)%Z)) in let t := eval cbv beta delta [QTDG.lh_resize_stmt] in t in let t := eval cbv beta delta [e_blk_18514 QTDG.lh_insert_entry QTDG.lh_resize_entry] in t in let x := constr:(ltac:(gw_callee_stmt (@Q7mx.gw_all) (@Q7mx.hdr_cells) 0%Z)) in let t := gw_subst t x hdr_cells in let x := constr:(ltac:(gw_callee_stmt (@QTDG.gw_all) (@QTDG.strip) (base + 412)%Z)) in let t := gw_subst t x strip in let x := constr:(ltac:(gw_callee_stmt (@QTDG.gw_all) (@QTDG.lh_resize_post) (base + 412)%Z)) in let t := gw_subst t x lh_resize_post in exact t).

Hypothesis lh_glob_client : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@Q9Mh.Mq4.gw_all) (@Q9Mh.Mq4.lh_glob_client) (base + -220)%Z)) in let T := eval cbv beta delta [Q9Mh.Mq4.lh_kchar_table_new_entry] in T in let T := gw_fold_pcs T base (-220)%Z [0; 136; 148]%Z in let x := constr:(ltac:(gw_callee_stmt (@Q7mx.gw_all) (@Q7mx.hdr_cells) 0%Z)) in let T := gw_subst T x hdr_cells in let x := constr:(ltac:(gw_callee_stmt (@QTDG.gw_all) (@QTDG.strip) (base + 412)%Z)) in let T := gw_subst T x strip in let x := constr:(ltac:(gw_callee_stmt (@QTDG.gw_all) (@QTDG.lh_resize_post) (base + 412)%Z)) in let T := gw_subst T x lh_resize_post in let x := constr:(ltac:(gw_callee_stmt (@QTDG.gw_all) (@QTDG.lh_resize_stmt) (base + 412)%Z)) in let T := gw_subst T x lh_resize_stmt in exact T).

Hypothesis lh_insert_small_cps : ltac:(let T := constr:(ltac:(gw_callee_stmt2 (@QTDG.gw_all) (@QTDG.lh_insert_small_cps) (base + 412)%Z)) in let T := eval cbv beta delta [QTDG.lh_insert_small_cps QTDG.lh_insert_entry QTDG.lh_resize_entry] in T in let T := gw_fold_pcs T base (412)%Z [0; 64; 68; 104; 128; 144; 276]%Z in exact T).

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
Hypothesis LAY_POS_e_fn_lh_char_hash : gw_le 1 e_fn_lh_char_hash.
Hypothesis LAY_HI_e_fn_lh_char_hash : gw_le (e_fn_lh_char_hash + 4) 1099511627776.
Hypothesis LAY_RDATA_GGOT4 : gw_le gRDATA_LO GGOT4.
Hypothesis LAY_GHASH4x12_GVDSO4 : gw_le (GHASH4 + 12) GVDSO4.
Hypothesis LAY_IMG_GGOT4 : gw_le gIMG_LO GGOT4.
Hypothesis LAY_GVDSO4_IMG : gw_le (GVDSO4 + 8) gIMG_HI.
Hypothesis AL_e_fn_lh_char_equal : gw_b4 e_fn_lh_char_equal.
Hypothesis RNG_e_fn_lh_char_equal : gw_br e_fn_lh_char_equal 4.
Hypothesis LAY_POS_e_fn_lh_char_equal : gw_le 1 e_fn_lh_char_equal.
Hypothesis LAY_HI_e_fn_lh_char_equal : gw_le (e_fn_lh_char_equal + 4) 1099511627776.
Hypothesis AL_e_fn_lh_entry_free : gw_b4 e_fn_lh_entry_free.
Hypothesis RNG_e_fn_lh_entry_free : gw_br e_fn_lh_entry_free 4.
Hypothesis LAY_POS_e_fn_lh_entry_free : gw_le 1 e_fn_lh_entry_free.
Hypothesis LAY_HI_e_fn_lh_entry_free : gw_le (e_fn_lh_entry_free + 4) 1099511627776.
#[using="w_14 w_21 w_53 w_75 w_77 joff_14 joff_21 joff_53 joff_75 joff_77 GGOT4 GHASH4 GVDSO4 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free JG_CGT_P gRDATA_LO CODE BASE4 BASER D_14 E_14 D_21 E_21 D_53 E_53 D_75 E_75 D_77 E_77 LINK_14 LINK_21 LINK_53 LINK_75 LINK_77 AL_e_blk_17d8c_b4 RNG_e_blk_17d8c_code RNG_GGOT4 AL_GGOT4 RNG_GHASH4 AL_GHASH4 RNG_GVDSO4 AL_GVDSO4 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_glob_client lh_insert_small_cps CS_GHASH4 CS_GGOT4 CS_GVDSO4 VOL_GVDSO4 LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal AL_e_fn_lh_entry_free RNG_e_fn_lh_entry_free LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

Definition lh_char_hash_entry : Z := (e_fn_lh_char_hash + 0x0).

#[using="Type"] Lemma firstn_S_nth : forall (A : Type) (l : list A) j x, nth_error l j = Some x -> firstn (S j) l = firstn j l ++ [x].
Proof. clear - segs.
intros A l; induction l as [|y l IH]; intros [|j] x H; cbn in *; try discriminate.
- injection H as ->. reflexivity.
- rewrite (IH j x H). reflexivity.
Qed.

#[using="Type"] Lemma strip_snoc : forall esn es j e g,
map strip esn = map strip (firstn j es) -> nth_error es j = Some e ->
map strip (esn ++ [LE g (le_k e) (le_kn e) (le_ks e) (le_v e)]) = map strip (firstn (S j) es).
Proof. clear - segs. intros esn es j e g H Hj. rewrite map_app, H, (firstn_S_nth _ _ _ _ Hj), map_app. reflexivity. Qed.

#[using="Type"] Lemma perm_mid2 : forall (l1 : list blk) a b l2, Permutation (l1 ++ a :: b :: l2) (b :: l1 ++ a :: l2).
Proof. clear - segs.
intros l1 a b l2. replace (l1 ++ a :: b :: l2) with ((l1 ++ [a]) ++ b :: l2) by (rewrite <- app_assoc; reflexivity).
replace (l1 ++ a :: l2) with ((l1 ++ [a]) ++ l2) by (rewrite <- app_assoc; reflexivity).
apply Permutation_sym. apply Permutation_middle.
Qed.

Section LhResize.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation lh_glob4 := (lh_glob segs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).
Hypothesis LF : lf_test_spec.
Variable MREL : Model -> Model -> Prop.
Hypothesis MREL_refl : forall md, MREL md md.
Hypothesis MREL_trans : forall a b c, MREL a b -> MREL b c -> MREL a c.
Hypothesis MREL_vm : forall a b, model_vm_only a b -> MREL a b.

Definition lh_hash_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (h : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 h) m' ms' /\ 0 <= h < 2^64 /\
MREL md md' /\ stk segs m' lo (bv_unsigned sp) /\ heap_presx S4L gVOL LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\ lh_glob4 m' /\ HEAPx A' LB m' md'.

Definition lh_char_hash_stmt (HD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (kp kn : Z) (ks : list byte),
HEAPx A LB m md -> In (kp, kn) LB -> cstr segs m kp kn ks -> lh_glob4 m ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - HD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 kp ->
(forall ms' md', lh_hash_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_char_hash_entry) fc None m (seg_rom segs)) md) T.

Variable HD : Z.
Hypothesis HD_ge : 8256 + 64 <= HD.
Hypothesis HASH : lh_char_hash_stmt HD.

#[using="w_14 w_21 w_53 w_75 w_77 GGOT4 GHASH4 GVDSO4 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal gRDATA_LO CODE LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma lh_init_loop2 :
forall (k i n : nat) (x1 x2 gp tp t0 t1 t2 x8 x9 a1 a2 a3 a4 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tbl : Z),
(k = n - 1 - i)%nat -> (i < n)%nat -> 0 <= tbl -> tbl + 40 * Z.of_nat n < 2^64 - 1 ->
a1 = Z_to_bv 64 (40 * Z.of_nat i) -> a2 = Z_to_bv 64 (2^64 - 1 - tbl) -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 (40 * Z.of_nat n) ->
mem_inv segs m ->
lh_slots segs m tbl (init_svs i n) ->
evt segs (fun ms' => exists m',
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 tbl) (Z_to_bv 64 (40 * Z.of_nat n)) (Z_to_bv 64 (2^64 - 1 - tbl)) (Z_to_bv 64 0) (Z_to_bv 64 (40 * Z.of_nat n)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (tbl + 40 * Z.of_nat (n - 1))) a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xb8)) fc None m' (seg_rom segs)
/\ munch [(tbl, tbl + 40 * Z.of_nat n)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ lh_slots segs m' tbl (init_svs n n))
(MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 tbl) a1 a2 a3 a4 (Z_to_bv 64 (-1)) a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xa0)) fc None m (seg_rom segs)).
Proof. clear - w_14 w_21 w_53 w_75 w_77 GGOT4 GHASH4 GVDSO4 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal gRDATA_LO CODE LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free segs base HIx LF MREL MREL_refl MREL_trans MREL_vm HD HD_ge HASH. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_hash as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_hash as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GHASH4x12_GVDSO4 as gL7_; unfold gw_le in gL7_. pose proof LAY_IMG_GGOT4 as gL8_; unfold gw_le in gL8_. pose proof LAY_GVDSO4_IMG as gL9_; unfold gw_le in gL9_. pose proof LAY_POS_e_fn_lh_char_equal as gL10_; unfold gw_le in gL10_. pose proof LAY_HI_e_fn_lh_char_equal as gL11_; unfold gw_le in gL11_. pose proof LAY_POS_e_fn_lh_entry_free as gL12_; unfold gw_le in gL12_. pose proof LAY_HI_e_fn_lh_entry_free as gL13_; unfold gw_le in gL13_.
induction k as [|k IH]; intros until tbl; intros Hk Hi Ht0 Htn E1 E2 E3 E4 MI SL; subst a1 a2 a3 a4.
- pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C. unfold ent_addr, slot_cells, ZSLOT in C. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
step. if_falsex. step. first [if_falsex | idtac].
step. step.
remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots segs mx tbl (init_svs (S i) n)) end.
{ rewrite <- init_svs_step by lia. eapply (lh_slots_write_slot segs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |].
unfold ent_addr, slot_cells, ESLOT. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite <- EB.
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity. exact C. }
clear C MU2 SL. step. subst B. if_falsex.
apply evt_done. eexists. split; [|split; [exact MU | split; [exact WM | split; [exact MI | ]]]].
+ replace (40 * Z.of_nat i + 40) with (40 * Z.of_nat n) by lia. replace (Z.of_nat (n - 1)) with (Z.of_nat i) by lia. reflexivity.
+ replace n with (S i) at 1 by lia. exact SL'.
- pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C. unfold ent_addr, slot_cells, ZSLOT in C. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
step. if_falsex. step. first [if_falsex | idtac].
step. step.
remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots segs mx tbl (init_svs (S i) n)) end.
{ rewrite <- init_svs_step by lia. eapply (lh_slots_write_slot segs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |].
unfold ent_addr, slot_cells, ESLOT. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite <- EB.
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity. exact C. }
clear C MU2 SL. step. subst B. if_truex.
eapply evt_cut.
{ eapply (IH (S i) n); [lia | lia | exact Ht0 | exact Htn | f_equal; lia | reflexivity | reflexivity | reflexivity | exact MI | exact SL']. }
cbv beta. intros ms' (m' & -> & MU' & WM' & MI' & SLn).
apply evt_done. exists m'. split; [reflexivity|]. split; [|split; [|split; [exact MI' | exact SLn]]].
+ eapply munch_trans; [exact MU | exact MU'].
+ eapply wmono_trans; [exact WM | exact WM'].
Qed.

Section Loop.
Variables (sp gp : word) (s7 s8 s9 s10 s11 : word) (F0 : bvmap 5 word) (fc0 : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo t tbl SZ NS nt ntbl : Z) (es : list lent) (svs : list slotv) (T : TSet).
Variables (rac s0c s1c s2c s3c s4c s5c s6c : word).
Variable j8 : list byte.

Definition rs_frame (m : word -> option byte) : Prop :=
rw_cells segs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].
Definition old_hdr (m : word -> option byte) : Prop :=
rw_cells segs m t (hdr_cells tbl (fn_lh_entry_free S4F) SZ (Z.of_nat (length es)) (hd_of tbl es) (tl_of tbl es)).

Definition rs_exit : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (errv : word) (esn : list lent) (svsn : list slotv),
HEAPx A (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB) m md ->
lh_openf segs S4F 0 m nt ntbl NS esn svsn -> map strip esn = map strip es ->
old_hdr m -> lh_glob4 m ->
stk segs m lo (bv_unsigned sp + -64) -> rs_frame m ->
rw_cells segs m (gTP - 164) [C4 errv] -> frm0 fc -> QCcH.fsaved F0 F -> (QCcH.frm0 fc0 -> QCcH.frm0 fc) ->
MREL md0 md -> heap_presx S4L gVOL LB (bv_unsigned sp) m0 m ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 nt) (Z_to_bv 64 (-1))
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 t) (Z_to_bv 64 NS) (Z_to_bv 64 0) (Z_to_bv 64 (fn_lh_char_equal S4F)) s6c s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x100)) fc None m (seg_rom segs)) md) T.

#[using="w_14 w_21 w_53 w_75 w_77 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER AL_e_blk_17d8c_b4 RNG_e_blk_17d8c_code LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_insert_small_cps LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LF MREL_refl MREL_trans HD_ge HASH"] Lemma lh_resize_loop :
forall (k j : nat) (e : lent) (esn : list lent) (svsn : list slotv)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (errv : word),
(k = length es - S j)%nat -> nth_error es j = Some e ->
HEAPx A (lh_blocks nt ntbl NS esn ++ map kblk (skipn j es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB) m md ->
lh_openf segs S4F 0 m nt ntbl NS esn svsn -> map strip esn = map strip (firstn j es) ->
In SZ lf_sizes -> In NS lf_sizes -> lf_thr SZ + 1 <= lf_thr NS -> Z.of_nat (length es) <= lf_thr SZ ->
lh_slots segs m tbl svs -> lh_link tbl es svs -> Z.of_nat (length svs) = SZ -> lh_keys segs m (skipn j es) ->
old_hdr m -> lh_glob4 m ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - HD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rs_frame m -> rw_cells segs m (gTP - 164) [C4 errv] -> frm0 fc ->
QCcH.fsaved F0 F -> (QCcH.frm0 fc0 -> QCcH.frm0 fc) ->
MREL md0 md -> heap_presx S4L gVOL LB (bv_unsigned sp) m0 m ->
rs_exit ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 nt) (Z_to_bv 64 (-1))
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 t) (Z_to_bv 64 NS) (Z_to_bv 64 (ent_addr tbl (le_ix e))) (Z_to_bv 64 (fn_lh_char_equal S4F)) s6c s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xc0)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_14 w_21 w_53 w_75 w_77 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER AL_e_blk_17d8c_b4 RNG_e_blk_17d8c_code LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_insert_small_cps LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LF MREL_refl MREL_trans HD_ge HASH segs base gTP gVOL S4F HIx MREL MREL_vm HD sp gp s7 s8 s9 s10 s11 F0 fc0 m0 md0 LB lo t tbl SZ NS nt ntbl es svs T rac s0c s1c s2c s3c s4c s5c s6c j8. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_hash as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_hash as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GHASH4x12_GVDSO4 as gL7_; unfold gw_le in gL7_. pose proof LAY_IMG_GGOT4 as gL8_; unfold gw_le in gL8_. pose proof LAY_GVDSO4_IMG as gL9_; unfold gw_le in gL9_. pose proof LAY_POS_e_fn_lh_char_equal as gL10_; unfold gw_le in gL10_. pose proof LAY_HI_e_fn_lh_char_equal as gL11_; unfold gw_le in gL11_. pose proof LAY_POS_e_fn_lh_entry_free as gL12_; unfold gw_le in gL12_. pose proof LAY_HI_e_fn_lh_entry_free as gL13_; unfold gw_le in gL13_.
induction k as [|k IH]; intros until errv; intros Hk Hj HP NOPEN STRIP Hsz Hsz2 Hthr2 Hcnt SL LINK Hlen KEYS OHDR G ST LO LOS SPA HT FR ERR FRM FS FRM0 VM0 HPR KX.
all: pose proof (proj1 (nth_error_Some es j) ltac:(rewrite Hj; discriminate)) as Hjlt.
all: pose proof LINK as (LK1 & LK2 & LK3 & LK4).
all: destruct (LK1 j e Hj) as (sv & Esv & Ek & Ekc & Ev & Enx & Epv).
all: pose proof (SL (le_ix e) sv Esv) as C; unfold slot_cells in C; rewrite Ek, Ekc, Ev, Enx, Epv in C.
all: pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Esv; discriminate)) as Hix.
all: pose proof NOPEN as (NHDR & NSL & NLINK & NKEYS & _ & Ncnt & Nlen); unfold lh_hdrf in NHDR.
all: assert (SK : skipn j es = e :: skipn (S j) es) by
(rewrite <- (firstn_skipn j es) in Hj; rewrite nth_error_app2 in Hj by (rewrite length_firstn; lia);
rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hj by lia;
remember (skipn j es) as sk eqn:ES; destruct sk as [|e0 tl']; [discriminate|]; cbn in Hj; injection Hj as ->;
f_equal; change tl' with (skipn 1 (e :: tl')); rewrite ES, skipn_skipn; reflexivity).
all: rewrite SK in HP, KEYS; cbn [map app] in HP.
all: assert (KEYSe : lh_keys segs m [e]) by (unfold lh_keys in *; constructor; [exact (Forall_inv KEYS) | constructor]).
all: pose proof (Forall_inv KEYS) as CSe; cbn in CSe.
all: unfold rs_frame in FR; unfold old_hdr, hdr_cells in OHDR; unfold_consts; word_range sp SPR.
all: pose proof (lf_thr_lt SZ Hsz) as Hlt; pose proof (lf_size_range SZ Hsz) as HSR; pose proof (lf_size_range NS Hsz2) as HSR2.
all: pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK; pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI; cbn [hl_segs S4L] in MI.

all: assert (HinB : In (tbl, 40 * SZ) (lh_blocks nt ntbl NS esn ++ kblk e :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB))
by (apply in_or_app; right; right; apply in_or_app; right; right; left; reflexivity).
all: assert (HinT : In (t, 56) (lh_blocks nt ntbl NS esn ++ kblk e :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB))
by (apply in_or_app; right; right; apply in_or_app; right; left; reflexivity).
all: assert (HinK : In (le_k e, le_kn e) (lh_blocks nt ntbl NS esn ++ kblk e :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB))
by (apply in_or_app; right; left; reflexivity).
all: pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP HinB) as (_ & Hbal & Hblo & Hbhi & _); pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP HinK) as (Hkn0 & _ & Hklo & Hkhi & _).
all: unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi, Hkhi.
all: destruct (lh_key_bytes segs m [e] e KEYSe ltac:(left; reflexivity)) as (KB & KNZ & KL).
all: pose proof (wmono_refl segs m) as WM; pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU.
all: remember (ent_addr tbl (le_ix e)) as B eqn:EB.
all: assert (EB8 : B mod 8 = 0) by (rewrite EB; unfold ent_addr; clear -Hbal; Z.div_mod_to_equations; lia).
all: assert (EBr : 0 <= B < 2^64) by (rewrite EB; unfold ent_addr; lia).
all: apply rz_evt; [exact MOK|].
all: step; step; ub_align_auto; step; step; step.
all: cbn [fn_lh_char_hash S4F]; gw_ret_pc_var_tac.

all: apply evt_RZ_done; eapply (HASH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md T A _ lo errv (le_k e) (le_kn e) (le_ks e));
[ heap_now S4L HIx HP MU WM MI | exact HinK | exact CSe | exact G | ..]; try alloc_side; try exact FRM.
all: intros ms2 md2 (m2 & A2 & h & errv2 & RS & Hh & VM2 & ST2 & HPR2 & ERR2 & G2 & HP2).
all: destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2); cbn [hl_segs S4L] in *.
all: rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST2, HPR2 by lia.
all: apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]; cbn [hl_segs S4L] in FR.
all: apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in OHDR; [| eapply client_rangex_block; [exact HinT | lia | cbn; lia]]; cbn [hl_segs S4L] in OHDR.
all: apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in C; [| eapply client_rangex_block; [exact HinB | rewrite EB; unfold ent_addr; lia | cbn; rewrite EB; unfold ent_addr; nia]]; cbn [hl_segs S4L] in C.
all: pose proof (lh_slots_presx S4L _ _ _ _ _ tbl svs SZ HPR2 HinB Hlen SL) as SL2; cbn [hl_segs S4L] in SL2.
all: pose proof (lh_keys_presx S4L _ _ _ _ _ (e :: skipn (S j) es) HPR2 ltac:(intros e' He'; apply in_or_app; right; change (In (kblk e') (map kblk (e :: skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB)); apply in_or_app; left; apply in_map_iff; exists e'; split; [reflexivity | exact He']) KEYS) as KEYS2; cbn [hl_segs S4L] in KEYS2.
all: pose proof (lh_open_presx S4L S4F _ 0 _ _ _ _ nt ntbl NS esn svsn HPR2 ltac:(intros b Hb; apply in_or_app; left; exact Hb) NOPEN) as NOPEN2; cbn [hl_segs S4L] in NOPEN2.
all: assert (HPR' : heap_presx S4L gVOL LB (bv_unsigned sp) m0 m2) by
(eapply heap_presx_trans; [exact HPR|]; eapply heap_presx_weaken; [exact HPR2 | lia | intros b Hb; apply in_or_app; right; right; apply in_or_app; right; right; right; exact Hb | intros a' Ha'; exact Ha']).
all: clear MU WM MI ST.
all: pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2; pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI; cbn [hl_segs S4L] in MI.
all: pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m2) as MU; pose proof (wmono_refl segs m2) as WM.
all: reenter MOK2.
all: step; step; step; norm_sx32; step; step; step; step; step.
all: assert (LEN : length esn = j) by
(apply (f_equal (@length _)) in STRIP; rewrite !length_map, length_firstn in STRIP; lia).
all: destruct (LK4 e (nth_error_In _ _ Hj)) as (Hk0 & HkF & Hkn31 & Hv).
all: apply evt_RZ_done;
eapply (lh_insert_small_cps HIx LF MREL MREL_refl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2 md2 T A2
(map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB) lo errv2 nt ntbl NS esn svsn
(le_k e) (le_kn e) (le_ks e) (le_v e) h 0);
[ exact HP2 | exact NOPEN2 | exact G2 | exact (Forall_inv KEYS2) | exact Hkn31 | lia | rewrite LEN; lia | lia | exact Hh | ..]; try alloc_side;
try exact (FRM2 FRM).
all: intros ms3 md3 (m3 & A3 & errv3 & svs3 & g & RS3 & VM3 & ST3 & HPR3 & ERR3 & G3 & NOPEN3 & HP3).
all: destruct RS3 as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & F3 & fc3 & -> & FS3 & FRM3); cbn [hl_segs S4L] in *.
all: rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST3, HPR3 by lia.
all: apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]; cbn [hl_segs S4L] in FR.
all: apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR3) in OHDR; [| eapply client_rangex_block; [apply in_or_app; right; left; reflexivity | lia | cbn; lia]]; cbn [hl_segs S4L] in OHDR.
all: apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR3) in C; [| eapply client_rangex_block; [apply in_or_app; right; right; left; reflexivity | rewrite EB; unfold ent_addr; lia | cbn; rewrite EB; unfold ent_addr; nia]]; cbn [hl_segs S4L] in C.
all: pose proof (lh_slots_presx S4L _ _ _ _ _ tbl svs SZ HPR3 ltac:(apply in_or_app; right; right; left; reflexivity) Hlen SL2) as SL3; cbn [hl_segs S4L] in SL3.
all: pose proof (lh_keys_presx S4L _ _ _ _ _ (skipn (S j) es) HPR3 ltac:(intros e' He'; apply in_or_app; left; apply in_map_iff; exists e'; split; [reflexivity | exact He']) (Forall_inv_tail KEYS2)) as KEYS3; cbn [hl_segs S4L] in KEYS3.
all: assert (HPR'' : heap_presx S4L gVOL LB (bv_unsigned sp) m0 m3) by
(eapply heap_presx_trans; [exact HPR'|]; eapply heap_presx_weaken; [exact HPR3 | lia | intros b Hb; apply in_or_app; right; right; right; exact Hb | intros a' Ha'; exact Ha']).
all: clear MU WM MI.
all: pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3; pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI; cbn [hl_segs S4L] in MI.
all: pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m3) as MU; pose proof (wmono_refl segs m3) as WM.
all: reenter MOK3.
all: step; if_false.
-
assert (NX : nx_of tbl es j = 0) by (unfold nx_of; rewrite (proj2 (nth_error_None es (S j))) by lia; reflexivity).
rewrite NX in C.
step. step. if_false.
rewrite (skipn_all2 es) in HP3 by lia. cbn [map app] in HP3.
apply evt_RZ_done.
eapply (KX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 md3 A3 errv3 (esn ++ [LE g (le_k e) (le_kn e) (le_ks e) (le_v e)]) svs3);
first [exact HP3 | exact NOPEN3 | exact OHDR | exact G3 | exact ST3 | exact FR | exact ERR3 | exact (FRM3 (FRM2 FRM)) | exact HPR'' | idtac].
+ rewrite (strip_snoc esn es j e g STRIP Hj), firstn_all2 by lia. reflexivity.
+ eapply fsaved_trans; [exact FS | eapply fsaved_trans; [exact FS2 | exact FS3]].
+ intros _. exact (FRM3 (FRM2 FRM)).
+ eapply MREL_trans; [exact VM0 | eapply MREL_trans; [exact VM2 | exact VM3]].
-
destruct (nth_error es (S j)) as [e'|] eqn:E2; [| exfalso; apply nth_error_None in E2; lia].
assert (NX : nx_of tbl es j = ent_addr tbl (le_ix e')) by (unfold nx_of; rewrite E2; reflexivity).
rewrite NX in C.
destruct (LK1 (S j) e' E2) as (sv' & Esv' & _). pose proof (proj1 (nth_error_Some svs (le_ix e')) ltac:(rewrite Esv'; discriminate)) as Hix'.
step. step. unfold ent_addr. if_truex.
change (tbl + 40 * Z.of_nat (le_ix e')) with (ent_addr tbl (le_ix e')).
apply evt_RZ_done.
eapply (IH (S j) e' (esn ++ [LE g (le_k e) (le_kn e) (le_ks e) (le_v e)]) svs3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 md3 A3 errv3);
first [exact E2 | exact HP3 | exact NOPEN3 | exact OHDR | exact G3 | exact ST3 | exact FR | exact ERR3 | exact (FRM3 (FRM2 FRM)) | exact HPR'' | exact KX
| exact SL3 | exact LINK | exact KEYS3 | exact Hthr2 | idtac].
+ lia.
+ exact (strip_snoc esn es j e g STRIP Hj).
+ exact Hsz.
+ exact Hsz2.
+ exact Hcnt.
+ exact Hlen.
+ exact LO.
+ exact LOS.
+ exact SPA.
+ exact HT.
+ eapply fsaved_trans; [exact FS | eapply fsaved_trans; [exact FS2 | exact FS3]].
+ intros _. exact (FRM3 (FRM2 FRM)).
+ eapply MREL_trans; [exact VM0 | eapply MREL_trans; [exact VM2 | exact VM3]].
Qed.

Definition rs_K : Prop :=
forall ms' md', lh_resize_post HIx MREL rac sp gp (Z_to_bv 64 gTP) s0c s1c s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 F0 fc0 m0 md0 LB lo t tbl SZ NS es svs ms' md' ->
realizes segs (mkCfg ms' md') T.

#[using="w_14 w_21 w_53 w_75 w_77 joff_53 joff_77 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER D_53 E_53 D_77 E_77 LINK_53 LINK_77 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_glob_client LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free MREL_trans MREL_vm HD_ge"] Lemma lh_resize_tail :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (errv : word) (esn : list lent) (svsn : list slotv),
rs_K -> bv_unsigned rac mod 2 = 0 ->
HEAPx A (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB) m md ->
lh_openf segs S4F 0 m nt ntbl NS esn svsn -> map strip esn = map strip es ->
old_hdr m -> lh_glob4 m ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - HD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rs_frame m -> rw_cells segs m (gTP - 164) [C4 errv] -> frm0 fc -> QCcH.fsaved F0 F -> (QCcH.frm0 fc0 -> QCcH.frm0 fc) ->
MREL md0 md -> heap_presx S4L gVOL LB (bv_unsigned sp) m0 m ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 nt) (Z_to_bv 64 (-1))
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 t) (Z_to_bv 64 NS) x20
(Z_to_bv 64 (fn_lh_char_equal S4F)) s6c s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x100)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_14 w_21 w_53 w_75 w_77 joff_53 joff_77 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER D_53 E_53 D_77 E_77 LINK_53 LINK_77 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_glob_client LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free MREL_trans MREL_vm HD_ge segs base gTP gVOL S4F HIx LF MREL MREL_refl HD HASH sp gp s7 s8 s9 s10 s11 F0 fc0 m0 md0 LB lo t tbl SZ NS nt ntbl es svs T rac s0c s1c s2c s3c s4c s5c s6c j8. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_hash as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_hash as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GHASH4x12_GVDSO4 as gL7_; unfold gw_le in gL7_. pose proof LAY_IMG_GGOT4 as gL8_; unfold gw_le in gL8_. pose proof LAY_GVDSO4_IMG as gL9_; unfold gw_le in gL9_. pose proof LAY_POS_e_fn_lh_char_equal as gL10_; unfold gw_le in gL10_. pose proof LAY_HI_e_fn_lh_char_equal as gL11_; unfold gw_le in gL11_. pose proof LAY_POS_e_fn_lh_entry_free as gL12_; unfold gw_le in gL12_. pose proof LAY_HI_e_fn_lh_entry_free as gL13_; unfold gw_le in gL13_.
intros until svsn; intros K RAC HP NOPEN STRIP OHDR G ST LO LOS SPA HT FR ERR FRM FS FRM0 VM0 HPR.
pose proof NOPEN as (NHDR & NSL & NLINK & NKEYS & Hsz2 & Ncnt & Nlen); unfold lh_hdrf in NHDR.
assert (LEN : length esn = length es) by (apply (f_equal (@length _)) in STRIP; rewrite !length_map in STRIP; exact STRIP).
unfold rs_frame in FR; unfold old_hdr, hdr_cells in OHDR; unfold_consts; word_range sp SPR.
pose proof (lf_size_range NS Hsz2) as HSR2.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK; pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI; cbn [hl_segs S4L] in MI.
assert (HPp : HEAPx A ((tbl, 40 * SZ) :: lh_blocks nt ntbl NS esn ++ (t, 56) :: LB) m md) by
(eapply heap_perm; [exact HP | apply perm_mid2]).
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HP) as (_ & (Hnbal & Hnblo & Hnbhi & Hnbimg) & _ & NKF).
cbn [hl_img_lo hl_img_hi S4L] in Hnbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hnbhi, NKF.
pose proof (blocks2 S4L HIx _ _ _ _ _ _ _ _ ltac:(eapply heap_perm; [exact HP | apply Permutation_sym; apply (Permutation_middle (lh_blocks nt ntbl NS esn) ((tbl, 40 * SZ) :: LB) (t, 56))]))
as ((Htal & Htlo & Hthi & Htimg) & _ & _).
cbn [hl_img_lo hl_img_hi S4L] in Htimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HP) as ((Hntal & Hntlo & Hnthi & Hntimg) & _).
cbn [hl_img_lo hl_img_hi S4L] in Hntimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hnthi.
pose proof (wmono_refl segs m) as WM; pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|].
step. step.

alloc_call (hi_free S4L HIx) S4L HIx HPp MU WM MI.
{ right. exists (40 * SZ). left. reflexivity. }
intros ms5 m5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR5, HP5.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in OHDR; [| eapply client_range_block; [apply in_or_app; right; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in OHDR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in NHDR; [| eapply client_range_block; [apply in_or_app; left; unfold lh_blocks; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in NHDR.
pose proof (lh_slots_pres S4L _ _ _ _ ntbl svsn NS HPR5 ltac:(apply in_or_app; left; unfold lh_blocks; right; left; reflexivity) Nlen NSL) as NSL5; cbn [hl_segs S4L] in NSL5.
pose proof (lh_keys_pres S4L _ _ _ _ esn HPR5 ltac:(intros e' He'; apply in_or_app; left; unfold lh_blocks; right; right; apply in_map_iff; exists e'; split; [reflexivity | exact He']) NKEYS) as NKEYS5; cbn [hl_segs S4L] in NKEYS5.
pose proof (lh_glob_client _ _ _ _ HPR5 G) as G5.
assert (HPR' : heap_presx S4L gVOL LB (bv_unsigned sp) m0 m5) by
(eapply heap_presx_trans; [exact HPR|]; apply heap_pres_presx; eapply heap_pres_weaken; [exact HPR5 | lia | intros b Hb; apply in_or_app; right; right; exact Hb]).
assert (HP5' : HEAPx A5 ((t, 56) :: (nt, 56) :: (ntbl, 40 * NS) :: map kblk esn ++ LB) m5 md5) by
(eapply heap_perm; [exact HP5 | apply Permutation_sym; apply (Permutation_middle (lh_blocks nt ntbl NS esn) LB (t, 56))]).
destruct (blocks2 S4L HIx _ _ _ _ _ _ _ _ HP5') as (_ & _ & Htnt).
clear MU WM MI ST HP5 HPp.
pose proof (heap_model_ok _ _ _ _ _ _ HP5') as MOK5; pose proof (heap_mem_inv _ _ _ _ _ _ HP5') as MI; cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (t, t + 56)] m5) as MU; pose proof (wmono_refl segs m5) as WM.
reenter MOK5.
step. step. step. step.
step. step. step. step. step. step. step.

alloc_call (hi_free S4L HIx) S4L HIx HP5' MU WM MI.
{ right. exists 56. right. left. reflexivity. }
intros ms6 m6 md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6. open_ret RS6. cbn [hl_segs S4L] in *.
rewrite lb_remove_other in HPR6, HP6 by (cbn; lia). rewrite lb_remove_head in HPR6, HP6.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
match goal with H : rw_cells segs ?mx t _ , MUx : munch _ m5 ?mx |- _ => rename H into HDR6 end.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR6) in HDR6; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR6.

lazymatch type of HPR6 with heap_pres _ _ _ ?mid _ =>
match goal with MUx : munch _ m5 mid, WMx : wmono segs m5 mid |- _ =>
assert (HPRs : heap_pres S4L ((ntbl, 40 * NS) :: map kblk esn ++ LB) (bv_unsigned sp) m5 mid);
[ eapply (heap_pres_of_munch S4L _ (bv_unsigned sp)); [exact MUx | exact WMx |];
eapply (client_outside S4L HIx); [exact HP5' | intros b Hb; right; right; exact Hb | clia |];
solve_clientW S4L HIx HP5' |] end end.
pose proof (lh_slots_pres S4L _ _ _ _ ntbl svsn NS HPRs ltac:(left; reflexivity) Nlen NSL5) as NSLs; cbn [hl_segs S4L] in NSLs.
pose proof (lh_keys_pres S4L _ _ _ _ esn HPRs ltac:(intros e' He'; right; apply in_or_app; left; apply in_map_iff; exists e'; split; [reflexivity | exact He']) NKEYS5) as NKEYSs; cbn [hl_segs S4L] in NKEYSs.
pose proof (lh_glob_client _ _ _ _ HPRs G5) as Gs.
pose proof (lh_slots_pres S4L _ _ _ _ ntbl svsn NS HPR6 ltac:(right; left; reflexivity) Nlen NSLs) as NSL6; cbn [hl_segs S4L] in NSL6.
pose proof (lh_keys_pres S4L _ _ _ _ esn HPR6 ltac:(intros e' He'; right; right; apply in_or_app; left; apply in_map_iff; exists e'; split; [reflexivity | exact He']) NKEYSs) as NKEYS6; cbn [hl_segs S4L] in NKEYS6.
pose proof (lh_glob_client _ _ _ _ HPR6 Gs) as G6.
assert (HPR'' : heap_presx S4L gVOL LB (bv_unsigned sp) m0 m6).
{ eapply heap_presx_trans; [exact HPR'|]. apply heap_pres_presx. eapply heap_pres_trans.
- eapply heap_pres_weaken; [exact HPRs | lia | intros b Hb; right; apply in_or_app; right; exact Hb].
- eapply heap_pres_weaken; [exact HPR6 | lia | intros b Hb; right; right; apply in_or_app; right; exact Hb]. }
rewrite <- LEN in HDR6.
clear MU WM MI HPRs NSLs NKEYSs Gs NSL5 NKEYS5 G5.
pose proof (heap_model_ok _ _ _ _ _ _ HP6) as MOK6; pose proof (heap_mem_inv _ _ _ _ _ _ HP6) as MI; cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m6) as MU; pose proof (wmono_refl segs m6) as WM.
reenter MOK6.
do 10 step.
apply evt_RZ_done. apply K. unfold lh_resize_post.
exists m6, A6, 0, errv.
split; [| split; [| split; [| split; [exact HPR'' | split; [exact ERR6 | split; [exact G6 | right]]]]]].
+ unfold ret_statew. do 16 eexists. split; [reflexivity|]. split; [exact FS | exact FRM0].
+ eapply MREL_trans; [exact VM0 | apply MREL_vm; eapply model_vm_only_trans; [exact VM5 | exact VM6]].
+ release_frame FR ST6 (bv_unsigned sp). exact ST6.
+ split; [reflexivity|]. exists ntbl, esn, svsn. split; [exact STRIP|]. split; [| exact HP6].
unfold lh_open. split; [exact HDR6 | split; [exact NSL6 | split; [exact NLINK | split; [exact NKEYS6 | split; [exact Hsz2 | split; [exact Ncnt | exact Nlen]]]]]].
Qed.

#[using="w_14 w_21 w_53 w_75 w_77 joff_53 joff_77 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER D_53 E_53 D_77 E_77 LINK_53 LINK_77 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_glob_client LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free MREL_trans MREL_vm HD_ge"] Lemma rs_exit_ok : rs_K -> bv_unsigned rac mod 2 = 0 ->
alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - HD -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rs_exit.
Proof. clear - w_14 w_21 w_53 w_75 w_77 joff_53 joff_77 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER D_53 E_53 D_77 E_77 LINK_53 LINK_77 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_glob_client LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free MREL_trans MREL_vm HD_ge HIx LF MREL MREL_refl HD HASH sp gp s7 s8 s9 s10 s11 F0 fc0 m0 md0 LB lo t tbl SZ NS nt ntbl es svs T rac s0c s1c s2c s3c s4c s5c s6c j8. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_hash as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_hash as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GHASH4x12_GVDSO4 as gL7_; unfold gw_le in gL7_. pose proof LAY_IMG_GGOT4 as gL8_; unfold gw_le in gL8_. pose proof LAY_GVDSO4_IMG as gL9_; unfold gw_le in gL9_. pose proof LAY_POS_e_fn_lh_char_equal as gL10_; unfold gw_le in gL10_. pose proof LAY_HI_e_fn_lh_char_equal as gL11_; unfold gw_le in gL11_. pose proof LAY_POS_e_fn_lh_entry_free as gL12_; unfold gw_le in gL12_. pose proof LAY_HI_e_fn_lh_entry_free as gL13_; unfold gw_le in gL13_.
intros K RAC LO LOS SPA HT. unfold rs_exit. intros until svsn; intros HP NOPEN STRIP OHDR G ST FR ERR FRM FS FRM0 VM0 HPR.

eapply (lh_resize_tail x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) t3 t4 t5 t6 F fc m md A errv esn svsn);
first [exact K | exact RAC | exact HP | exact NOPEN | exact STRIP | exact OHDR | exact G | exact ST | exact LO | exact LOS | exact SPA | exact HT
| exact FR | exact ERR | exact FRM | exact FS | exact FRM0 | exact VM0 | exact HPR].
Qed.
End Loop.

#[using="Type"] Lemma perm_resize : forall (q nt t tbl : Z) (a b c d : Z) (M LB : list blk),
Permutation ((q, a) :: (nt, b) :: (t, c) :: (tbl, d) :: M ++ LB) ((nt, b) :: (q, a) :: M ++ (t, c) :: (tbl, d) :: LB).
Proof. clear - HIx LF MREL MREL_refl MREL_trans MREL_vm HD HD_ge HASH.
intros. transitivity ((nt, b) :: (q, a) :: (t, c) :: (tbl, d) :: M ++ LB); [apply perm_swap|]. apply perm_skip. apply perm_skip.
change (Permutation (([(t, c); (tbl, d)] ++ M) ++ LB) (M ++ ([(t, c); (tbl, d)] ++ LB))). rewrite (app_assoc M).
apply Permutation_app_tail. apply Permutation_app_comm.
Qed.

Ltac weq := first [ reflexivity
| apply bv_eq; rewrite ?unsigned_lit by lia; first [ lia | reflexivity ]
| match goal with |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] => rewrite (unsigned_lit x) by lia; rewrite (ub_land7 x) by ub_mod_solve; reflexivity end
| match goal with |- context [Z.lxor (bv_unsigned (Z_to_bv 64 ?x)) 18446744073709551615] => rewrite (unsigned_lit x) by lia; rewrite (lxor_ones64 x) by lia; f_equal; lia end
| match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] => is_var x; rewrite (unsigned_lit x) by lia; f_equal; lia end
| lazymatch goal with |- ?g => idtac "weq-open:" g; fail end ].

Ltac lhb_in Hb :=
unfold lh_blocks in Hb; cbn [In] in Hb; destruct Hb as [Hb | [Hb | Hb]];
[left; exact Hb | right; left; exact Hb | right; right; apply in_or_app; left; exact Hb].

#[using="w_14 w_21 w_53 w_75 w_77 joff_14 joff_21 joff_53 joff_77 LAY_gIMG_LO LAY_TPLO LAY_TPHI JG_CGT_P gRDATA_LO CODE BASE4 BASER D_14 E_14 D_21 E_21 D_53 E_53 D_77 E_77 LINK_14 LINK_21 LINK_53 LINK_77 AL_e_blk_17d8c_b4 RNG_e_blk_17d8c_code RNG_GGOT4 RNG_GHASH4 RNG_GVDSO4 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_glob_client lh_insert_small_cps LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free S4F LF MREL_refl MREL_trans MREL_vm HD_ge HASH"] Lemma lh_resize_cps : lh_resize_stmt HIx MREL (64 + HD).
Proof. clear - w_14 w_21 w_53 w_75 w_77 joff_14 joff_21 joff_53 joff_77 LAY_gIMG_LO LAY_TPLO LAY_TPHI JG_CGT_P gRDATA_LO CODE BASE4 BASER D_14 E_14 D_21 E_21 D_53 E_53 D_77 E_77 LINK_14 LINK_21 LINK_53 LINK_77 AL_e_blk_17d8c_b4 RNG_e_blk_17d8c_code RNG_GGOT4 RNG_GHASH4 RNG_GVDSO4 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_glob_client lh_insert_small_cps LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free S4F LF MREL_refl MREL_trans MREL_vm HD_ge HASH HIx MREL HD. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_hash as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_hash as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GHASH4x12_GVDSO4 as gL7_; unfold gw_le in gL7_. pose proof LAY_IMG_GGOT4 as gL8_; unfold gw_le in gL8_. pose proof LAY_GVDSO4_IMG as gL9_; unfold gw_le in gL9_. pose proof LAY_POS_e_fn_lh_char_equal as gL10_; unfold gw_le in gL10_. pose proof LAY_HI_e_fn_lh_char_equal as gL11_; unfold gw_le in gL11_. pose proof LAY_POS_e_fn_lh_entry_free as gL12_; unfold gw_le in gL12_. pose proof LAY_HI_e_fn_lh_entry_free as gL13_; unfold gw_le in gL13_.
unfold lh_resize_stmt. intros until svs. intros HP OPEN G Hsz2 Hthr2 ST LO LOS SPA HT ERR TP RA FRM A0 A1 K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen). unfold lh_hdr, lh_hdrf in HDR.
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR. pose proof (lf_size_range ns Hsz2) as HSR2.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.

change (lh_blocks t tbl size es ++ LB) with ((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) in HP.
pose proof (heap_pres_refl S4L (map kblk es ++ LB) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He). lia. }
apply rz_evt; [exact MOK|]. unfold lh_resize_entry. subst a0 a1 tp.
carve_frame 64%nat ST.
do 8 step.
step. if_falsex. step. step. step. ub_align_auto. do 6 step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (OPEN1 : lh_open segs S4F mx t tbl size es svs) by
(eapply (lh_open_frame segs S4F _ m mx t tbl size es svs _ lo); [exact OPEN | exact BELOW | exact MU | exact WM | constructor; [cbn; lia | constructor]]);
assert (G1 : lh_glob4 mx) by
(eapply (lh_glob_frame segs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4 m mx); [exact G | exact MU | exact WM | constructor; [cbn; gw_expose GHASH4; gw_expose GGOT4; gw_expose GVDSO4; lia | constructor]])
end.

alloc_call (hi_calloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 nt e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
pose proof (lh_open_pres S4L S4F _ _ _ _ _ t tbl size es svs HPR2 ltac:(intros b Hb; lhb_in Hb) OPEN1) as OPEN2; cbn [hl_segs S4L] in OPEN2.
pose proof (lh_glob_client _ _ _ _ HPR2 G1) as G2.
clear MU WM MI ST OPEN G OPEN1 G1.
destruct OUT2 as [(-> & HerrHP2 & HP2) | (Hnt & BLK & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_truex. step. step. do 10 step.
apply evt_RZ_done. apply K. unfold lh_resize_post.
exists m2, A2, (2^64 - 1), e2.
split; [| split; [apply MREL_vm; exact VM2 | split; [| split; [| split; [exact ERR2 | split; [exact G2 | left]]]]]].
+ unfold ret_statew. do 16 eexists.
split; [replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity); reflexivity|].
split; [apply QCcH.fsaved_refl | intros H0; exact H0].
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR | lia | intros b Hb; apply in_or_app; right; exact Hb].
+ split; [reflexivity|]. split; [exact OPEN2 | exact HP2].
-
change (1 * 56) with 56 in HP2. change (Z.to_nat (1 * 56)) with 56%nat in BLK.
apply (rw_cells_recast segs m2 nt _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in BLK;
[| cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
destruct (blocks2 S4L HIx _ _ _ _ _ _ _ _ HP2) as ((Hnal & Hnlo & Hnhi & Hnimg) & _ & Hnt_t).
cbn [hl_img_lo hl_img_hi S4L] in Hnimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hnhi.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (nt, nt + 56)] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_falsex. step. step. step. ub_align_auto. step. stepz. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mz4 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HPRw : heap_pres S4L ((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) (bv_unsigned sp) m2 mx) by
(eapply (heap_pres_of_munch S4L _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outside S4L HIx); [exact HP2 | intros b Hb; right; exact Hb | clia |]; solve_clientW S4L HIx HP2)
end.
pose proof (lh_open_pres S4L S4F _ _ _ _ _ t tbl size es svs HPRw ltac:(intros b Hb; lhb_in Hb) OPEN2) as OPEN2'; cbn [hl_segs S4L] in OPEN2'.
pose proof (lh_glob_client _ _ _ _ HPRw G2) as G2'. clear HPRw.

alloc_call (hi_calloc S4L HIx) S4L HIx HP2 MU WM MI.
intros ms3 m3 md3 A3 q e3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
match goal with H : rw_cells segs _ nt _ |- _ => rename H into NBLK end.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in NBLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in NBLK.
pose proof (lh_open_pres S4L S4F _ _ _ _ _ t tbl size es svs HPR3 ltac:(intros b Hb; right; lhb_in Hb) OPEN2') as OPEN3; cbn [hl_segs S4L] in OPEN3.
pose proof (lh_glob_client _ _ _ _ HPR3 G2') as G3.
clear MU WM MI ST2 OPEN2 G2 OPEN2' G2'.
destruct OUT3 as [(-> & HerrHP3 & HP3) | (Hq & BLK2 & HP3)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (nt, nt + 56)] m3) as MU. pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
stepz. step. step. if_true. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HPRw : heap_pres S4L ((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) (bv_unsigned sp) m3 mx) by
(eapply (heap_pres_of_munch S4L _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outside S4L HIx); [exact HP3 | intros b Hb; right; exact Hb | clia |]; solve_clientW S4L HIx HP3)
end.
pose proof (lh_open_pres S4L S4F _ _ _ _ _ t tbl size es svs HPRw ltac:(intros b Hb; lhb_in Hb) OPEN3) as OPEN3'; cbn [hl_segs S4L] in OPEN3'.
pose proof (lh_glob_client _ _ _ _ HPRw G3) as G3'. clear HPRw.

alloc_call (hi_free S4L HIx) S4L HIx HP3 MU WM MI.
{ right. exists 56. left. reflexivity. }
intros ms5 m5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR5, HP5.
extend_pres S4L HIx HPR MU WM HP3 HPR5.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
pose proof (lh_open_pres S4L S4F _ _ _ _ _ t tbl size es svs HPR5 ltac:(intros b Hb; lhb_in Hb) OPEN3') as OPEN5; cbn [hl_segs S4L] in OPEN5.
pose proof (lh_glob_client _ _ _ _ HPR5 G3') as G5.
clear MU WM MI ST3 OPEN3 G3 OPEN3' G3'.
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m5) as MU. pose proof (wmono_refl segs m5) as WM.
reenter MOK5.
do 10 step.
apply evt_RZ_done. apply K. unfold lh_resize_post.
exists m5, A5, (2^64 - 1), e3.
split; [| split; [apply MREL_vm; eapply model_vm_only_trans; [| exact VM5]; eapply model_vm_only_trans; [exact VM2 | exact VM3]
| split; [| split; [| split; [exact ERR5 | split; [exact G5 | left]]]]]].
* unfold ret_statew. do 16 eexists.
split; [replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity); reflexivity|].
split; [apply QCcH.fsaved_refl | intros H0; exact H0].
* release_frame FR ST5 (bv_unsigned sp). exact ST5.
* apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR | lia | intros b Hb; apply in_or_app; right; exact Hb].
* split; [reflexivity|]. split; [exact OPEN5 | exact HP5].
+
replace (ns * 40) with (40 * ns) in HP3 by lia.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
destruct (blocks2 S4L HIx _ _ _ _ _ _ _ _ HP3) as ((Hqal & Hqlo & Hqhi & Hqimg) & _ & Hq_nt).
cbn [hl_img_lo hl_img_hi S4L] in Hqimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
destruct (blocks2 S4L HIx _ _ _ _ _ _ _ _ ltac:(eapply heap_perm; [exact HP3 | apply perm_skip; apply perm_swap])) as (_ & _ & Hq_t).
destruct (blocks2 S4L HIx _ _ _ _ _ _ _ _ ltac:(eapply heap_perm; [exact HP3 | apply perm_skip; transitivity ((nt, 56) :: (tbl, 40 * size) :: (t, 56) :: (map kblk es ++ LB)); [apply perm_skip; apply perm_swap | apply perm_swap]])) as (_ & _ & Hq_tbl).
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (nt, nt + 56); (q, q + 40 * ns)] m3) as MU. pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. step. step. if_falsex.
stepz. step. step.
step. if_falsex.
step. step. step. step. step. step.
replace (Z.to_nat (ns * 40)) with (Z.to_nat (40 * Z.of_nat (Z.to_nat ns))) in BLK2 by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (zeros_slots segs (Z.to_nat ns) mx q BLK2) as SL0 end.
rewrite <- init_svs_0 in SL0. clear BLK2.
assert (Hq8 : q mod 8 = 0) by (clear -Hqal; Z.div_mod_to_equations; lia).
call (lh_init_loop2 (Z.to_nat ns - 1) 0 (Z.to_nat ns)); [lia | lia | lia | lia | weq | weq | weq | weq | | exact SL0 |]; [assumption|].
match goal with H : lh_slots segs _ q (init_svs _ _) |- _ => rename H into NSL end.
match goal with H : mem_inv segs ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI5 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HPRw : heap_pres S4L ((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) (bv_unsigned sp) m3 mx) by
(eapply (heap_pres_of_munch S4L _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outside S4L HIx); [exact HP3 | intros b Hb; right; right; exact Hb | clia |]; solve_clientW S4L HIx HP3);
assert (HP5 : HEAPx A3 ((q, 40 * ns) :: (nt, 56) :: (t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) mx md3) by
(heap_now S4L HIx HP3 MU WM MI5);
rename mx into m5
end.
pose proof (lh_open_pres S4L S4F _ _ _ _ _ t tbl size es svs HPRw ltac:(intros b Hb; lhb_in Hb) OPEN3) as OPEN5; cbn [hl_segs S4L] in OPEN5.
pose proof (lh_glob_client _ _ _ _ HPRw G3) as G5.
assert (HPR' : heap_pres S4L (map kblk es ++ LB) (bv_unsigned sp) m m5) by
(eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPRw | lia | intros b Hb; right; right; exact Hb]]).
assert (HPL : HEAPx A3 (lh_blocks nt q ns [] ++ map kblk (skipn 0 es) ++ (t, 56) :: (tbl, 40 * size) :: LB) m5 md3) by
(eapply heap_perm; [exact HP5 | apply perm_resize]).
pose proof (lf_thr_lt ns Hsz2) as Hlt2.
assert (NOPEN : lh_openf segs S4F 0 m5 nt q ns [] (init_svs (Z.to_nat ns) (Z.to_nat ns))).
{ split; [exact NBLK|]. split; [exact NSL|]. split; [| split; [constructor | split; [exact Hsz2 | split; [cbn; lia | rewrite init_svs_length; lia]]]].
split; [| split; [| split; [constructor | intros e He; destruct He]]].
- intros j e E. destruct j; discriminate.
- intros i sv E _. rewrite init_svs_all in E. apply nth_error_In in E. apply repeat_spec in E. subst sv. left. reflexivity. }
pose proof OPEN5 as (_ & SL5 & _ & KEYS5 & _).
clear HPRw HP3 OPEN3 G3 MU WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m5) as MU. pose proof (wmono_refl segs m5) as WM.
destruct es as [|e0 es'].
*
cbn [hd_of tl_of] in HDR.
step. step. if_true.
apply evt_RZ_done.
eapply (lh_resize_tail sp gp s7 s8 s9 s10 s11 F fc m md LB lo t tbl size ns nt q [] svs T ra s0 s1 s2 s3 s4 s5 s6 _
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 md3 A3 e3 [] (init_svs (Z.to_nat ns) (Z.to_nat ns)));
first [exact K | exact RA | exact HPL | exact NOPEN | reflexivity | exact HDR | exact G5 | exact ST3 | exact SPA | exact HT | exact FR | exact ERR3 | exact FRM
| apply QCcH.fsaved_refl | idtac].
-- clia.
-- lia.
-- intros H0; exact H0.
-- apply MREL_vm. eapply model_vm_only_trans; [exact VM2 | exact VM3].
-- apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR' | lia | intros b Hb; apply in_or_app; right; exact Hb].
*
cbn [hd_of] in HDR.
pose proof LINK as (LK1 & _). destruct (LK1 0%nat e0 eq_refl) as (sv0 & Esv0 & _).
pose proof (proj1 (nth_error_Some svs (le_ix e0)) ltac:(rewrite Esv0; discriminate)) as Hix0.
step. step. unfold ent_addr. if_falsex.
change (tbl + 40 * Z.of_nat (le_ix e0)) with (ent_addr tbl (le_ix e0)).
apply evt_RZ_done.
eapply (lh_resize_loop sp gp s7 s8 s9 s10 s11 F fc m md LB lo t tbl size ns nt q (e0 :: es') svs T ra s0 s1 s2 s3 s4 s5 s6 _
(length es') 0 e0 [] (init_svs (Z.to_nat ns) (Z.to_nat ns))
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 md3 A3 e3);
first [exact HPL | exact NOPEN | exact Hsz | exact Hsz2 | exact Hthr2 | exact Hcnt | exact SL5 | exact LINK | exact Hlen | exact KEYS5 | exact HDR | exact G5
| exact ST3 | exact SPA | exact HT | exact FR | exact ERR3 | exact FRM | apply QCcH.fsaved_refl | idtac].
-- cbn [length]. lia.
-- reflexivity.
-- reflexivity.
-- clia.
-- lia.
-- intros H0; exact H0.
-- apply MREL_vm. eapply model_vm_only_trans; [exact VM2 | exact VM3].
-- apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR' | lia | intros b Hb; apply in_or_app; right; exact Hb].
-- apply (rs_exit_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ svs); [exact K | exact RA | clia | lia | exact SPA | exact HT].
Qed.
End LhResize.

End RC__1.

End G.
