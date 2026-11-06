(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QCcH Q0Ek Qsw7 QJjn QRUw Q8tj QgoP QVbl QSL3 QPIU QnCn Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply Lib.GwApply2 Lib.GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QCcH Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QgoP.
Import QVbl.Mq5.
Import QSL3.
Import QPIU.Mqb.
Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q0Hd.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm; gwj_align_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm; gwj_align_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition ulhsmall_code (w_2 : Z) : list Z :=
[0xff010113; 0x00113423; w_2; 0x00153513; 0x00813083; 0x01010113; 0x00008067]%Z.

Definition blk_1a328_code : list Z :=
[0x00050a63; 0x00757593; 0x00059663; 0x00452503; 0x00008067; 0xc0001073]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_2 : Z).
Variables (joff_2 : bv 21).
Variables (e_blk_1a328 e_strcmp : Z).
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
Hypothesis AL_gTP : gw_al gTP 4.
Hypothesis RNG_gTP : gw_br gTP 8.
#[using="gH2 gH3 LAY_gIMG_LO"] Lemma gLAYF : ((0 <= gIMG_LO /\ gIMG_HI <= alloc_ceiling) /\ (gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - gH2 gH3 LAY_gIMG_LO gTP gIMG_LO gIMG_HI. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.
#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma gLAYF0 : ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gTP gIMG_LO gIMG_HI. pose proof LAY_TPLO as X1; pose proof LAY_TPHI as X2; unfold gw_le in X1, X2. split; [split; [exact X1 | exact X2] | exact LAY_gIMG_LO]. Qed.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Hypothesis CODE : code_at segs base (ulhsmall_code w_2).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 28.
Hypothesis D_2 : decode_any (Z_to_bv 32 w_2) = Some (Jal 1 joff_2, 4%Z).
Hypothesis E_2 : is_ecall (Z_to_bv 32 w_2) = false.
Hypothesis LINK_2 : gw_anch (base + 8 + bv_signed joff_2)%Z (e_strcmp + 0)%Z.
Hypothesis CODE_e_blk_1a328 : code_at segs e_blk_1a328 blk_1a328_code.
Hypothesis AL_e_blk_1a328_b4 : gw_b4 e_blk_1a328.
Hypothesis RNG_e_blk_1a328_code : gw_br e_blk_1a328 24.

Definition strcmp_post := Eval cbv beta delta [QVbl.Mq5.strcmp_post] in (@QVbl.Mq5.strcmp_post segs).
Definition strcmp_stmt := ltac:(let t := eval cbv beta delta [QVbl.Mq5.strcmp_stmt] in (@QVbl.Mq5.strcmp_stmt segs e_strcmp) in let t := gw_subst t (@QVbl.Mq5.strcmp_post segs) strcmp_post in exact t).

Hypothesis strcmp_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq5.strcmp_spec segs e_strcmp) 3%nat in let T := gw_subst T (@QVbl.Mq5.strcmp_post segs) strcmp_post in let T := gw_subst T (@QVbl.Mq5.strcmp_stmt segs e_strcmp) strcmp_stmt in exact T).

Let U4L : heap_layout :=
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
Let U4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
#[using="w_2 joff_2 e_blk_1a328 e_strcmp RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI AL_gTP RNG_gTP e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_2 E_2 LINK_2 CODE_e_blk_1a328 AL_e_blk_1a328_b4 RNG_e_blk_1a328_code strcmp_spec U4F"] Lemma gw_all : True. Proof. exact I. Qed.

Definition u_lh_table_length_entry : Z := (e_blk_1a328 + 0x0).
Definition u_lh_char_equal_entry : Z := (base + 0x0).

Definition u_lh_table_length_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (kvs : list (Z * Z)) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length kvs))) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE_e_blk_1a328"] Lemma u_lh_table_length_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (BS : list blk) (t : Z) (kvs : list (Z * Z)),
mem_inv segs m ->
lhtab2 segs U4F m BS t kvs -> 0 < t -> t mod 16 = 0 ->
a0 = Z_to_bv 64 t ->
evt segs (u_lh_table_length_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc kvs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 u_lh_table_length_entry) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE_e_blk_1a328 segs U4F. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until kvs. intros MI LH TNZ TAL A0.
destruct LH as (tbl & size & es & svs & -> & _ & HDR & _ & _ & _ & Hsz & Hcnt & _).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
unfold u_lh_table_length_entry, u_lh_table_length_post. rewrite length_map. subst a0.
pose proof (rw_cells_bound segs m t _ HDR) as TB. cbn [cells_size csize Nat.add] in TB.
step. if_falsex. step. step. ubsan_align8 t.
step. norm_sx32. step. finish.
Qed.

Definition u_lh_char_equal_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 : word) (ls rs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if strcmp_model ls rs =? 0 then 1 else 0)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ bytes_at segs m' (bv_unsigned a0) (ls ++ [b0]) /\ bytes_at segs m' (bv_unsigned a1) (rs ++ [b0]).

#[using="w_2 joff_2 e_strcmp gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_2 E_2 LINK_2 strcmp_spec"] Lemma u_lh_char_equal_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (lo : Z),
mem_inv segs m ->
bytes_at segs m (bv_unsigned a0) (ls ++ [b0]) -> bytes_at segs m (bv_unsigned a1) (rs ++ [b0]) ->
~ In b0 ls -> ~ In b0 rs ->
stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 ->
(bv_unsigned a0 + Z.of_nat (length ls) + 1 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0) ->
(bv_unsigned a1 + Z.of_nat (length rs) + 1 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1) ->
evt segs (u_lh_char_equal_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 u_lh_char_equal_entry) fc None m (seg_rom segs)).
Proof. clear - w_2 joff_2 e_strcmp gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_2 E_2 LINK_2 strcmp_spec segs. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until lo. intros MI SL SR NL NR ST LOS SEPL SEPR.
word_range sp SPR. word_range a0 A0R. word_range a1 A1R.
pose proof (bytes_at_bound _ _ _ _ SL) as BL. pose proof (bytes_at_bound _ _ _ _ SR) as BR.
rewrite length_app in BL, BR. cbn [length] in BL, BR.
pose proof (strcmp_walk_range (ls ++ [b0]) (rs ++ [b0])) as MR. change (strcmp_walk (ls ++ [b0]) (rs ++ [b0])) with (strcmp_model ls rs) in MR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl segs m) as WM.
unfold u_lh_char_equal_entry, u_lh_char_equal_post.
carve_frame 16%nat ST.
step. step. step.
call strcmp_spec; [exact SL | exact SR | exact NL | exact NR | exact MI |].
match goal with H : ?v = Z_to_bv 64 (strcmp_model ls rs) |- _ => subst v end.
step. rewrite seqz_of_model by lia.
step. step.
lazymatch goal with H : rw_cells segs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame H ST (bv_unsigned sp) end.
step. finish.
Qed.

End G.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qrtz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwApply2 GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm; gwj_align_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm; gwj_align_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition ulhnew_code (w_7 w_8 w_12 w_21 w_26 w_27 w_45 : Z) : list Z :=
[0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x00058493; w_7; w_8; 0x00050413; 0x00100513; 0x03800593; w_12; 0x08050463; 0x00757593; 0x08059e63; 0x00852023; 0x00052223; 0x02800593; 0x00050993; 0x00040513; w_21; 0x00050593; 0x00098513; 0x00b9bc23; 0x04058863; w_26; w_27; 0x02953023; 0x03253423; 0x02c53823; 0x04805063; 0x00000613; 0xfff5c693; 0x0075f713; 0x02800793; 0x02f407b3; 0xfff00813; 0x04c6e063; 0x02071e63; 0x00c588b3; 0x02860613; 0x0108b023; 0xfec796e3; 0x00c0006f; w_45; 0x00000513; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x03010113; 0x00008067; 0xc0001073]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_7 w_8 w_12 w_21 w_26 w_27 w_45 : Z).
Variables (hi_7 hi_26 : bv 20).
Variables (lo_8 lo_27 : bv 12).
Variables (joff_12 joff_21 joff_45 : bv 21).
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
Hypothesis AL_gTP : gw_al gTP 4.
Hypothesis RNG_gTP : gw_br gTP 8.
#[using="gH2 gH3 LAY_gIMG_LO"] Lemma gLAYF : ((0 <= gIMG_LO /\ gIMG_HI <= alloc_ceiling) /\ (gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - gH2 gH3 LAY_gIMG_LO gTP gIMG_LO gIMG_HI. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.
#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma gLAYF0 : ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gTP gIMG_LO gIMG_HI. pose proof LAY_TPLO as X1; pose proof LAY_TPHI as X2; unfold gw_le in X1, X2. split; [split; [exact X1 | exact X2] | exact LAY_gIMG_LO]. Qed.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Variable vdso_ok4 : Z -> Prop.
Variables (JG_CGT_P gRDATA_LO : Z).
Hypothesis CODE : code_at segs base (ulhnew_code w_7 w_8 w_12 w_21 w_26 w_27 w_45).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 220.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 11 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Load SZ8 true 18 11 lo_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (Jal 1 joff_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Jal 1 joff_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 12 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (Load SZ8 true 12 12 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_45 : decode_any (Z_to_bv 32 w_45) = Some (Jal 1 joff_45, 4%Z).
Hypothesis E_45 : is_ecall (Z_to_bv 32 w_45) = false.
Hypothesis ANCH_8 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_8)%Z GHASH4.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z GGOT4.
Hypothesis LINK_12 : gw_anch (base + 48 + bv_signed joff_12)%Z e_calloc.
Hypothesis LINK_21 : gw_anch (base + 84 + bv_signed joff_21)%Z e_calloc.
Hypothesis LINK_45 : gw_anch (base + 180 + bv_signed joff_45)%Z e_free.
Hypothesis RNG_GGOT4 : gw_br GGOT4 8.
Hypothesis AL_GGOT4 : gw_al GGOT4 8.
Hypothesis RNG_GHASH4 : gw_br GHASH4 8.
Hypothesis AL_GHASH4 : gw_al GHASH4 8.
Hypothesis RNG_GVDSO4 : gw_br GVDSO4 8.
Hypothesis AL_GVDSO4 : gw_al GVDSO4 8.
Hypothesis LAY_GGOTU_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASHU_GVDSO4 : gw_le (GHASH4 + 8) GVDSO4.

Hypothesis CS_GHASH4 : forall a, (GHASH4 <= a < GHASH4 + 12)%Z -> gCS a.
Hypothesis CS_GGOT4 : forall a, (GGOT4 <= a < GGOT4 + 8)%Z -> gCS a.
Hypothesis CS_GVDSO4 : forall a, (GVDSO4 <= a < GVDSO4 + 8)%Z -> gCS a.

Hypothesis LAY_IMG_GGOT4 : gw_le gIMG_LO GGOT4.
Hypothesis LAY_GVDSO4_IMG : gw_le (GVDSO4 + 8) gIMG_HI.

Let U4L : heap_layout :=
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
Let U4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
Hypothesis LAY_RDATA_GGOT4 : gw_le gRDATA_LO GGOT4.
Hypothesis LAY_GGOT4_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASH4x12_GVDSO4 : gw_le (GHASH4 + 12) GVDSO4.
Hypothesis AL_e_fn_lh_entry_free : gw_b4 e_fn_lh_entry_free.
Hypothesis RNG_e_fn_lh_entry_free : gw_br e_fn_lh_entry_free 4.
Hypothesis LAY_POS_e_fn_lh_entry_free : gw_le 1 e_fn_lh_entry_free.
Hypothesis LAY_HI_e_fn_lh_entry_free : gw_le (e_fn_lh_entry_free + 4) 1099511627776.
#[using="w_7 w_8 w_12 w_21 w_26 w_27 w_45 hi_7 hi_26 lo_8 lo_27 joff_12 joff_21 joff_45 GGOT4 GHASH4 GVDSO4 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI AL_gTP RNG_gTP e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free vdso_ok4 JG_CGT_P gRDATA_LO CODE BASE4 BASER D_7 E_7 D_8 E_8 D_12 E_12 D_21 E_21 D_26 E_26 D_27 E_27 D_45 E_45 ANCH_8 ANCH_27 LINK_12 LINK_21 LINK_45 RNG_GGOT4 AL_GGOT4 RNG_GHASH4 AL_GHASH4 RNG_GVDSO4 AL_GVDSO4 LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 AL_e_fn_lh_entry_free RNG_e_fn_lh_entry_free LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free U4F"] Lemma gw_all : True. Proof. exact I. Qed.

Ltac g_ra_even := lazymatch goal with |- (bv_unsigned (Z_to_bv 64 (?b + ?k)) mod 2 = 0)%Z =>
let X := fresh in let Y := fresh in pose proof BASE4 as X; pose proof BASER as Y; unfold gw_b4, gw_br in X, Y; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia end.
Ltac alloc_side ::=
try (progress fold U4L); try (progress fold U4F);
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
Ltac gj_fold := try (progress fold U4L); repeat match goal with H : _ |- _ => progress fold U4L in H end; try (progress fold U4F); repeat match goal with H : _ |- _ => progress fold U4F in H end.
Ltac unfold_consts ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
Ltac clia ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
Ltac unfold_consts_goal ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size.
Ltac gj_fn_cbn := try (progress cbn [U4F fn_lh_entry_free]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section RC__1.

Section ULhNew.
Variable HIx : heap_iface U4L.
Notation HEAPx := (HEAP U4L HIx).

Definition u_lh_kchar_table_new_entry : Z := (base + 0x0).

#[using="w_7 w_8 w_12 w_21 w_26 w_27 w_45 GGOT4 GHASH4 GVDSO4 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_entry_free gRDATA_LO CODE LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma u_lh_init_loop :
forall (k i n : nat) (x1 x2 gp tp t0 t1 t2 x8 x9 a0 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tbl : Z),
(k = n - 1 - i)%nat -> (i < n)%nat -> 0 <= tbl -> tbl + 40 * Z.of_nat n < 2^64 ->
mem_inv segs m ->
lh_slots segs m tbl (init_svs i n) ->
evt segs (fun ms' => exists m' a7',
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 a0 (Z_to_bv 64 tbl) (Z_to_bv 64 (40 * Z.of_nat n)) (Z_to_bv 64 (18446744073709551615 - tbl)) (Z_to_bv 64 0) (Z_to_bv 64 (40 * Z.of_nat n)) (Z_to_bv 64 (-1)) a7' x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xb0)) fc None m' (seg_rom segs)
/\ munch [(tbl, tbl + 40 * Z.of_nat n)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ lh_slots segs m' tbl (init_svs n n))
(MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 a0 (Z_to_bv 64 tbl) (Z_to_bv 64 (40 * Z.of_nat i)) (Z_to_bv 64 (18446744073709551615 - tbl)) (Z_to_bv 64 0) (Z_to_bv 64 (40 * Z.of_nat n)) (Z_to_bv 64 (-1)) a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x98)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_8 w_12 w_21 w_26 w_27 w_45 GGOT4 GHASH4 GVDSO4 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_entry_free gRDATA_LO CODE LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free segs base HIx. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOTU_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASHU_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_IMG_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GVDSO4_IMG as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GGOT4_GHASH4 as gL7_; unfold gw_le in gL7_. pose proof LAY_GHASH4x12_GVDSO4 as gL8_; unfold gw_le in gL8_. pose proof LAY_POS_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_. pose proof LAY_HI_e_fn_lh_entry_free as gL10_; unfold gw_le in gL10_.
induction k as [|k IH]; intros until tbl; intros Hk Hi Ht0 Htn MI SL.
all: pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C; unfold ent_addr, slot_cells, ZSLOT in C; cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
all: pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU; pose proof (wmono_refl segs m) as WM.
all: pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
all: remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
all: step; if_falsex. all: step; if_false.
all: step; rewrite <- EB. all: step.
all: stepz.
all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots segs mx tbl (init_svs (S i) n));
[ rewrite <- init_svs_step by lia; eapply (lh_slots_write_slot segs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |];
unfold ent_addr, slot_cells, ESLOT; cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]; rewrite <- EB;
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity; exact C |] end.
all: clear C MU2 SL; step.
- if_falsex. apply evt_done. do 2 eexists. split; [|split; [exact MU | split; [exact WM | split; [exact MI | ]]]].
+ replace (40 * Z.of_nat i + 40) with (40 * Z.of_nat n) by lia. reflexivity.
+ replace n with (S i) at 1 by lia. exact SL'.
- if_truex. replace (40 * Z.of_nat i + 40) with (40 * Z.of_nat (S i)) by lia.
eapply evt_cut.
{ eapply (IH (S i) n); [lia | lia | exact Ht0 | exact Htn | exact MI | exact SL']. }
cbv beta. intros ms' (m' & a7' & -> & MU' & WM' & MI' & SLn).
apply evt_done. exists m', a7'. split; [reflexivity|]. split; [|split; [|split; [exact MI' | exact SLn]]].
+ eapply munch_trans; [exact MU | exact MU'].
+ eapply wmono_trans; [exact WM | exact WM'].
Qed.

Notation lh_globU := (lh_glob segs U4F GHASH4 GGOT4 GVDSO4 vdso_ok4).

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma u_lh_glob_client : forall LB SP m m', heap_pres U4L LB SP m m' -> lh_globU m -> lh_globU m'.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOTU_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASHU_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_IMG_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GVDSO4_IMG as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GGOT4_GHASH4 as gL7_; unfold gw_le in gL7_. pose proof LAY_GHASH4x12_GVDSO4 as gL8_; unfold gw_le in gL8_. pose proof LAY_POS_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_. pose proof LAY_HI_e_fn_lh_entry_free as gL10_; unfold gw_le in gL10_.
intros LB SP m m' HPR ([seed G1] & G2 & (vf & G3 & VF)). split; [| split].
- exists seed. eapply (heap_pres_rw_cells U4L); [exact HPR | exact G1 |]. right; left. intros a Ha. cbn in Ha. gw_expose GHASH4.
cbn. gw_cs.
- eapply (heap_pres_rw_cells U4L); [exact HPR | exact G2 |]. right; left. intros a Ha. cbn in Ha. gw_expose GGOT4.
cbn. gw_cs.
- exists vf. split; [| exact VF]. eapply (heap_pres_rw_cells U4L); [exact HPR | exact G3 |]. right; left. intros a Ha. cbn in Ha. gw_expose GVDSO4.
cbn. gw_cs.
Qed.

Definition u_lh_table_new_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS U4L HIx) (r : Z) (errv' : word),
ret_statew U4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres U4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
lh_globU m' /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, lhtab2 segs U4F m' BS r [] /\ HEAPx A' (BS ++ LB) m' md') ).

#[using="w_7 w_8 w_12 w_21 w_26 w_27 w_45 hi_7 hi_26 lo_8 lo_27 joff_12 joff_21 joff_45 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER D_7 E_7 D_8 E_8 D_12 E_12 D_21 E_21 D_26 E_26 D_27 E_27 D_45 E_45 ANCH_8 ANCH_27 LINK_12 LINK_21 LINK_45 RNG_GGOT4 RNG_GHASH4 RNG_GVDSO4 LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma u_lh_kchar_table_new_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS U4L HIx) (LB : list blk) (lo : Z) (errv : word),
HEAPx A LB m md ->
lh_globU m ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top U4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 (fn_lh_entry_free U4F) ->
(forall ms' md', u_lh_table_new_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 u_lh_kchar_table_new_entry) fc None m (seg_rom segs)) md) T.
Proof. clear - w_7 w_8 w_12 w_21 w_26 w_27 w_45 hi_7 hi_26 lo_8 lo_27 joff_12 joff_21 joff_45 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER D_7 E_7 D_8 E_8 D_12 E_12 D_21 E_21 D_26 E_26 D_27 E_27 D_45 E_45 ANCH_8 ANCH_27 LINK_12 LINK_21 LINK_45 RNG_GGOT4 RNG_GHASH4 RNG_GVDSO4 LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free segs gTP U4F HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOTU_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASHU_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_IMG_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GVDSO4_IMG as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GGOT4_GHASH4 as gL7_; unfold gw_le in gL7_. pose proof LAY_GHASH4x12_GVDSO4 as gL8_; unfold gw_le in gL8_. pose proof LAY_POS_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_. pose proof LAY_HI_e_fn_lh_entry_free as gL10_; unfold gw_le in gL10_.
intros until errv. intros HP G ST LO LOS SPA HT ERR TP RA A0 A1 K.
unfold_consts. word_range sp SPR.
destruct G as ([seed G1] & G2 & (vf & G3 & VF)). gw_expose GHASH4. gw_expose GGOT4. gw_expose GVDSO4.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs U4L] in MI.
pose proof (heap_pres_refl U4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. unfold u_lh_kchar_table_new_entry. subst a0 a1.
carve_frame 48%nat ST.
do 6 step.
step. step. step. step. step. step. step.

alloc_call (hi_calloc U4L HIx) U4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs U4L] in *.
extend_pres U4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs U4L] in FR.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR2) in G1; [| right; left; intros q Hq; cbn in Hq; cbn; gw_cs]. cbn [hl_segs U4L] in G1.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR2) in G2; [| right; left; intros q Hq; cbn in Hq; cbn; gw_cs]. cbn [hl_segs U4L] in G2.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR2) in G3; [| right; left; intros q Hq; cbn in Hq; cbn; gw_cs]. cbn [hl_segs U4L] in G3.
clear MU WM MI ST.
destruct OUT2 as [(-> & HerrHP2 & HP2) | (Hr & BLK & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs U4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_truex. do 7 step.
apply evt_RZ_done. apply K. unfold u_lh_table_new_post.
exists m2, A2, 0, e2.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| left; auto]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ split; [exists seed; exact G1 | split; [exact G2 | exists vf; split; [exact G3 | exact VF]]].
-
change (Z.to_nat (1 * 56)) with 56%nat in BLK. change (1 * 56) with 56 in HP2. cbn [repeat] in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs U4L] in MI.
pose proof (heap_blk U4L HIx _ _ _ _ r 56 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img U4L HIx _ _ _ _ r 56 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi U4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 56)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_falsex. step. step. ubsan_align8 r.
stepz.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mcnt end.
step. step. step. step.

alloc_call (hi_calloc U4L HIx) U4L HIx HP2 MU WM MI.
intros ms3 m3 md3 A3 q e3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. cbn [hl_segs U4L] in *.
extend_pres U4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs U4L] in FR.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs U4L] in BLK.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR3) in G1; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs U4L] in G1.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR3) in G2; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs U4L] in G2.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR3) in G3; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs U4L] in G3.
clear MU WM MI ST2.
destruct OUT3 as [(-> & HerrHP3 & HP3) | (Hq & BLK2 & HP3)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs U4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 56)] m3) as MU.
pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. step. stepz. step. if_true. step.

alloc_call (hi_free U4L HIx) U4L HIx HP3 MU WM MI.
{ right. exists 56. left. reflexivity. }
intros ms5 m5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. cbn [hl_segs U4L] in *.
rewrite lb_remove_head in HPR5, HP5.
extend_pres U4L HIx HPR MU WM HP3 HPR5.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs U4L] in FR.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR5) in G1; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs U4L] in G1.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR5) in G2; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs U4L] in G2.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR5) in G3; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs U4L] in G3.
clear MU WM MI ST3 BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs U4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m5) as MU.
pose proof (wmono_refl segs m5) as WM.
reenter MOK5.
do 8 step.
apply evt_RZ_done. apply K. unfold u_lh_table_new_post.
exists m5, A5, 0, e3.
split; [| split; [| split; [| split; [exact HPR | split; [exact ERR5 | split; [| left; auto]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; [| exact VM5]. eapply model_vm_only_trans; eassumption.
* release_frame FR ST5 (bv_unsigned sp). exact ST5.
* split; [exists seed; exact G1 | split; [exact G2 | exists vf; split; [exact G3 | exact VF]]].
+
change (16 * 40) with (40 * 16) in HP3. change (16 * 40) with (40 * Z.of_nat 16) in BLK2.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs U4L] in MI.
destruct (blocks2 U4L HIx _ _ _ _ _ _ _ _ HP3) as ((Hqal & Hqlo & Hqhi & Hqimg) & _ & Hdj).
cbn [hl_img_lo hl_img_hi U4L] in Hqimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 56); (q, q + 640)] m3) as MU.
pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. step. step. step. if_falsex.
step. step. step. stepz. step.
step. if_false. step. step. ub_notltu q 0. step. rewrite (unsigned_lit q), (land7_of_mod8 q) by (first [lia | mod8_tac]). step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (zeros_slots segs 16 mx q BLK2) as SL0 end.
rewrite <- init_svs_0 in SL0. clear BLK2.
replace (Z_to_bv 64 0) with (Z_to_bv 64 (40 * Z.of_nat 0)) at 2 by (f_equal; lia).
replace 640 with (40 * Z.of_nat 16) by reflexivity.
call (u_lh_init_loop 15 0 16); [reflexivity | lia | lia | lia | | exact SL0 |]. { assumption. }
match goal with H : lh_slots segs _ q (init_svs 16 16) |- _ => rename H into SL16 end.
do 8 step.
apply evt_RZ_done. apply K. unfold u_lh_table_new_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A3, r, e3 end.
assert (HP3' : HEAPx A3 ((r, 56) :: (q, 40 * 16) :: LB) m3 md3) by (eapply heap_perm; [exact HP3 | apply perm_swap]).
split; [| split; [| split; [| split; [ | split; [ eassumption | split; [| right]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; eassumption.
* release_frame FR ST3 (bv_unsigned sp). exact ST3.
* eapply heap_pres_trans; [exact HPR|].
lazymatch goal with |- heap_pres _ _ _ _ ?mf =>
match goal with MUx : munch _ m3 mf, WMx : wmono segs m3 mf |- _ =>
eapply (heap_pres_of_munch U4L LB (bv_unsigned sp)); [exact MUx | exact WMx |];
eapply (client_outside U4L HIx); [exact HP3' | intros b Hb; right; right; exact Hb | clia |];
solve_clientW U4L HIx HP3' end end.
* split; [eexists; eassumption | split; [eassumption | exists vf; split; [eassumption | exact VF]]].
* split; [exact Hr|]. exists [(r, 56); (q, 40 * 16)]. split.
-- exists q, 16, [], (init_svs 16 16). split; [reflexivity|]. split; [reflexivity|].
split; [| split; [exact SL16 | split; [| split; [constructor | split; [cbn; tauto | split; [cbn; lia | rewrite init_svs_length; lia]]]]]].
++ unfold lh_hdr, lh_hdrf. cbn [length Z.of_nat hd_of tl_of].
match goal with H : rw_cells segs _ r (?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
apply (rw_cells_recast_prefix segs _ r [c1; c2; c3] [C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] rest) in H;
[ cbn [app] in H; exact H | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity ] end.
++ split; [| split; [| split; [constructor | intros e He; destruct He]]].
** intros j e E. destruct j; discriminate.
** intros i sv E _. rewrite init_svs_all in E. apply nth_error_In in E. apply repeat_spec in E. subst sv. left. reflexivity.
-- cbn [app]. lazymatch goal with |- HEAP _ _ _ _ ?mf _ =>
match goal with MUx : munch _ m3 mf, WMx : wmono segs m3 mf, MIx : mem_inv segs mf |- _ =>
eapply (heap_frame U4L HIx); [exact HP3' | | exact WMx | exact MIx];
eapply (frame_writes_ok U4L HIx _ _ _ _ _ _ HP3' MUx); solve_frameW_with HP3' end end.
Qed.
End ULhNew.

End RC__1.

End G.
