(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo QPIU Q8tj QSL3 QAyu QnCn Q6WR Q9Mh Q6q3 Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply2 Lib.GwApplyJ Q7mx Q5Rg QQLG QRGY QXOI.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPIU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
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
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition maybefree1_code (w_30 w_34 w_39 w_41 w_43 w_51 w_55 : Z) : list Z :=
[0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00050413; 0x00757513; 0x0c051e63; 0x00442503; 0xfff5051b; 0x00a42223; 0x00050663; 0x00000513; 0x08c0006f; 0x01843683; 0x00068e63; 0x02043603; 0x00040513; 0x00058493; 0x00060593; 0x000680e7; 0x00048593; 0x00042503; 0x00600613; 0x00043c23; 0x02043023; 0x02c50a63; 0x00500613; 0x00c50e63; 0x00400613; 0x02c51a63; 0x06058463; 0x02843503; w_30; 0x0240006f; 0x04058463; 0x02843503; w_34; 0x0140006f; 0x02843503; 0x00055663; 0x03043503; w_39; 0x01043503; w_41; 0x00040513; w_43; 0x00100513; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0x00008067; 0x02843503; w_51; 0x00051a63; 0xfb1ff06f; 0x02843503; w_55; 0xf8050ae3; 0x00200513; 0xfcdff06f; 0xc0001073]%Z.

Definition blk_17544_code (wb17544_1 : Z) : list Z :=
[0x00058513; wb17544_1]%Z.

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_3 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

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
Let e_blk_1a328 : Z := e_18a54.
Let e_blk_17cb0 : Z := e_17cb0.
Hypothesis CODE : code_at segs base (maybefree1_code w_30 w_34 w_39 w_41 w_43 w_51 w_55).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 248.
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
Hypothesis LINK_30 : gw_anch (base + 128 + bv_signed joff_30)%Z (e_187f8 + 0)%Z.
Hypothesis LINK_34 : gw_anch (base + 144 + bv_signed joff_34)%Z (e_17a68 + 0)%Z.
Hypothesis LINK_39 : gw_anch (base + 164 + bv_signed joff_39)%Z e_free.
Hypothesis LINK_41 : gw_anch (base + 172 + bv_signed joff_41)%Z (e_pbfree + 0)%Z.
Hypothesis LINK_43 : gw_anch (base + 180 + bv_signed joff_43)%Z e_free.
Hypothesis LINK_51 : gw_anch (base + 212 + bv_signed joff_51)%Z (e_17cb0 + 0)%Z.
Hypothesis LINK_55 : gw_anch (base + 228 + bv_signed joff_55)%Z (e_18a54 + 0)%Z.

Hypothesis printbuf_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@UPIU.Mqd.gw_all) (@UPIU.Mqd.printbuf_free_cps) e_pbfree)) in exact T).
Hypothesis lh_table_length_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QRGY.Mq0.gw_all) (@QRGY.Mq0.u_lh_table_length_spec) (base + 15008)%Z)) in let T := eval cbv beta delta [QRGY.Mq0.u_lh_table_length_entry QRGY.Mq0.u_lh_char_equal_entry] in T in let T := gw_fold_pcs T base (15008)%Z [0]%Z in exact T).
Hypothesis lh_table_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QXOI.gw_all) (@QXOI.u_lh_table_free_cps) e_187f8)) in exact T).
Hypothesis array_list_length_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@UPIU.Mq2.gw_all) (@UPIU.Mq2.array_list_length_spec) (base + 11180)%Z)) in let T := eval cbv beta delta [UPIU.Mq2.array_list_length_entry UPIU.Mq2.array_list_get_idx_entry] in T in let T := gw_fold_pcs T base (11180)%Z [0]%Z in exact T).
Hypothesis array_list_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@UPIU.Mq0.gw_all) (@UPIU.Mq0.array_list_free_cps) e_17a68)) in exact T).
Variable wb17544_1 : Z.  Variable joffb17544_1 : bv 21.
Hypothesis D_b17544_1 : decode_any (Z_to_bv 32 wb17544_1) = Some (Jal 0 joffb17544_1, 4%Z).
Hypothesis E_b17544_1 : is_ecall (Z_to_bv 32 wb17544_1) = false.
Hypothesis LINK_b17544_1 : gw_anch (e_fn_free_userdata + 4 + bv_signed joffb17544_1)%Z e_free.
Hypothesis CODE_e_blk_17544 : code_at segs e_fn_free_userdata (blk_17544_code wb17544_1).
Hypothesis AL_e_blk_17544_b4 : gw_b4 e_fn_free_userdata.
Hypothesis RNG_e_blk_17544_code : gw_br e_fn_free_userdata 8.
Hypothesis LAY_POS_e_fn_free_userdata : gw_le 1 e_fn_free_userdata.
Hypothesis LAY_HI_e_fn_free_userdata : gw_le (e_fn_free_userdata + 4) 1099511627776.
Hypothesis LAY_POS_e_fn_ud_to_json_string : gw_le 1 e_fn_ud_to_json_string.
Hypothesis LAY_HI_e_fn_ud_to_json_string : gw_le (e_fn_ud_to_json_string + 4) 1099511627776.

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
#[using="w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_30 joff_34 joff_39 joff_41 joff_43 joff_51 joff_55 e_pbfree e_17a68 e_17cb0 e_187f8 e_18a54 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_30 E_30 D_34 E_34 D_39 E_39 D_41 E_41 D_43 E_43 D_51 E_51 D_55 E_55 LINK_30 LINK_34 LINK_39 LINK_41 LINK_43 LINK_51 LINK_55 printbuf_free_cps lh_table_length_spec lh_table_free_cps array_list_length_spec array_list_free_cps wb17544_1 joffb17544_1 D_b17544_1 E_b17544_1 LINK_b17544_1 CODE_e_blk_17544 AL_e_blk_17544_b4 RNG_e_blk_17544_code LAY_POS_e_fn_free_userdata LAY_HI_e_fn_free_userdata LAY_POS_e_fn_ud_to_json_string LAY_HI_e_fn_ud_to_json_string S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

Section MF.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition mf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word)
(s : jshape) (BS : list blk) (x rc : Z)
(ms1 : machine_state) (md1 : Model) : Prop :=
exists m1 (A1 : AS S4L HIx) (r : Z),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m1 ms1 /\
model_vm_only md md1 /\
stk segs m1 lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m1 /\
rw_cells segs m1 (gTP - 164) [C4 errv] /\
( (r = 0 /\ 2 <= rc /\ jval segs S4F s m1 BS x (rc - 1) /\ HEAPx A1 (BS ++ LB) m1 md1)
\/ (r = 1 /\ rc = 1 /\ HEAPx A1 LB m1 md1)
\/ (r = 2 /\ rc = 1 /\ zomb segs S4F s m1 x BS /\ HEAPx A1 (BS ++ LB) m1 md1) ).

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo : Z) (errv : word) (s : jshape) (BS : list blk) (x rc : Z) (T : TSet).

Definition mf_frame (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells segs m (bv_unsigned sp + -32) [CB 8 junk8; C8 s1; C8 s0; C8 ra].

Definition KPOST : Prop :=
forall ms1 md1, mf_post ra sp gp (Z_to_bv 64 gTP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo errv s BS x rc ms1 md1 ->
realizes segs (mkCfg ms1 md1) T.

#[using="w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_41 joff_43 e_pbfree LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_41 E_41 D_43 E_43 LINK_41 LINK_43 printbuf_free_cps"] Lemma mf_gen :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(n ty tojs pb : Z) (rest : list cell) (PBS : list blk) (junk8 : list byte),
HEAPx A ((x, n) :: PBS ++ LB) m md ->
rw_cells segs m x (jhdr_cells ty 0 tojs pb 0 0 ++ rest) ->
opt_pbuf segs m PBS pb ->
mf_frame m junk8 ->
stk segs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
KPOST ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0xa8)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_41 joff_43 e_pbfree LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_41 E_41 D_43 E_43 LINK_41 LINK_43 printbuf_free_cps segs base gTP HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo errv s BS x rc T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until junk8. intros HP HDR OPB FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc K.
unfold mf_frame in FR. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ x n HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x n HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU.
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. step.

apply evt_RZ_done.
eapply (printbuf_free_cps HIx) with (BS := PBS) (LB := (x, n) :: LB) (p := pb) (lo := lo);
[ eapply (heap_perm S4L HIx); [exact HP | perm] | .. ]; try alloc_side.
{ exact OPB. }
intros ms2 md2 (m2 & A2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR2 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (HPRa : heap_pres S4L LB (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; right; exact Hb]. }
clear MU WM MI HPR HDR OPB ST.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. step.

alloc_call (hi_free S4L HIx) S4L HIx HP2 MU WM MI.
{ right. exists n. left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR3 by lia.
rewrite lb_remove_head in HPR3, HP3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (HPRb : heap_pres S4L LB (bv_unsigned sp) m0 m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; exact Hb]. }
clear MU WM MI HPRa.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m3) as MU.
pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. step. step. step. step.
release_frame FR ST3 (bv_unsigned sp).
step.
apply evt_RZ_done. apply K. unfold mf_post.
exists m3, A3, 1.
split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS | exact FS2] | intros Hf; exact (FRM2 (FRM Hf))] |].
split; [eapply model_vm_only_trans; [exact VM0 | eapply model_vm_only_trans; [exact VM2 | exact VM3]] |].
split; [exact ST3|]. split; [exact HPRb|]. split; [exact ERR3|].
right; left. split; [reflexivity|]. split; [exact Hrc | exact HP3].
Qed.

#[using="w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_41 joff_43 e_pbfree LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_41 E_41 D_43 E_43 LINK_41 LINK_43 printbuf_free_cps"] Lemma mf_scalar :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(n ty tojs pb u1 u2 : Z) (rest : list cell) (PBS : list blk) (junk8 : list byte),
HEAPx A ((x, n) :: PBS ++ LB) m md ->
rw_cells segs m x (jhdr_cells ty 0 tojs pb u1 u2 ++ rest) -> Z.of_nat (cells_size (jhdr_cells ty 0 tojs pb u1 u2 ++ rest)) = n ->
(ty = 1 \/ ty = 2 \/ ty = 3) ->
opt_pbuf segs m PBS pb ->
mf_frame m junk8 ->
stk segs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
KPOST ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x54)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_41 joff_43 e_pbfree LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_41 E_41 D_43 E_43 LINK_41 LINK_43 printbuf_free_cps segs base gTP HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo errv s BS x rc T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until junk8. intros HP HDR Hn Hty OPB FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc K.
unfold mf_frame in FR. unfold_consts. word_range sp SPR.
rewrite cells_size_app in Hn. cbn [cells_size csize jhdr_cells Nat.add] in Hn.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ x n HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x n HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(x, x + 40)] m) as MU.
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. norm_w32. step. stepz. stepz.
step. if_falsex. step. step. if_falsex. step. step. if_truex.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
assert (HP2 : HEAPx A ((x, n) :: PBS ++ LB) m2 md).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
right; left. exists x, n. split; [left; reflexivity | lia]. }
assert (HPR2 : heap_pres S4L LB (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; right; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists x, n. split; [left; reflexivity|]. split; [| lia].
exact (nodup_prefix_suffix ((x, n) :: PBS) LB x n n (heap_blk_nodup S4L HIx _ _ _ _ HP) ltac:(left; reflexivity)). }
assert (OPB2 : opt_pbuf segs m2 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | eapply agree_of_munch; [exact MU | exact WM |] | apply incl_refl].
intros a k Hin. cbn. split; [| exact I].
assert (Hne : x <> a).
{ intros <-. exact (nodup_prefix_suffix [(x, n)] (PBS ++ LB) x n k (heap_blk_nodup S4L HIx _ _ _ _ HP) ltac:(left; reflexivity) ltac:(apply in_or_app; left; exact Hin)). }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ x n a k HP ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hin) Hne).
pose proof (heap_blk S4L HIx _ _ _ _ a k HP ltac:(right; apply in_or_app; left; exact Hin)) as (Hk & _). lia. }
apply evt_RZ_done.
eapply mf_gen; [exact HP2 | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB2 | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | exact VM0 | exact HPR2 | exact FS | exact FRM | exact Hrc | exact K].
Qed.
End MF.

Section MF2.
Ltac gj_fn_cbn := try (progress cbn [S4F fn_free_userdata fn_ud_to_json_string]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo : Z) (errv : word) (s : jshape) (BS : list blk) (x rc : Z) (T : TSet).

#[using="w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_39 joff_41 joff_43 e_pbfree LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_39 E_39 D_41 E_41 D_43 E_43 LINK_39 LINK_41 LINK_43 printbuf_free_cps LAY_POS_e_fn_free_userdata LAY_HI_e_fn_free_userdata LAY_POS_e_fn_ud_to_json_string LAY_HI_e_fn_ud_to_json_string"] Lemma mf_str : forall (h : bool)
(x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (junk8 : list byte),
s = Sstr h ->
HEAPx A (BS ++ LB) m md ->
jval segs S4F s m BS x 0 ->
mf_frame ra sp s0 s1 m junk8 ->
stk segs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
KPOST HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo errv s BS x rc T ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x54)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_39 joff_41 joff_43 e_pbfree LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_39 E_39 D_41 E_41 D_43 E_43 LINK_39 LINK_41 LINK_43 printbuf_free_cps LAY_POS_e_fn_free_userdata LAY_HI_e_fn_free_userdata LAY_POS_e_fn_ud_to_json_string LAY_HI_e_fn_ud_to_json_string segs base gTP S4F HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo errv s BS x rc T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_free_userdata as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_free_userdata as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_ud_to_json_string as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_ud_to_json_string as gL5_; unfold gw_le in gL5_.
intros until junk8. intros Hs HP J FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc K.
unfold mf_frame in FR. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(x, x + 40)] m) as MU.
subst s. destruct h.
-
destruct J as (pb & PBS & REST & EBS & OPB & len & pd & pdn & str & junk2 & ER & HL & HS & HPD & HDR & HD). subst REST BS.
cbn [app] in HP.
pose proof (heap_blk S4L HIx _ _ _ _ x 56 HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 56 HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
pose proof (heap_blk S4L HIx _ _ _ _ pd pdn HP ltac:(right; left; reflexivity)) as (Hpdn & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi, Hphi.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hxpd.
clear HD.
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. norm_w32. step. stepz. stepz. step. if_truex.
step. step. if_falsex. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp) HP MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; right; apply in_or_app; right; exact Hb) ltac:(clia))
as (HP2 & AG2 & HPR2).

alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ right. exists pdn. right; left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR3 by lia.
rewrite lb_remove_other in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
assert (OPB3 : opt_pbuf segs m3 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
- eapply agree_on_incl; [exact AG2 | intros b Hb; right; apply in_or_app; left; exact Hb].
- eapply (agree_of_heap_pres segs S4L); [exact HPR3 | reflexivity | intros b Hb; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres S4L LB (bv_unsigned sp) m0 m3).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans; [exact HPR2|].
eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; right; apply in_or_app; right; exact Hb]. }
try g_ret_pc_any.
eapply mf_gen; [exact HP3 | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB3 | exact FR | exact ST3 | clia | clia | exact SPA | exact HT
| exact ERR3 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM3] | exact HPRb | exact FS | exact FRM | exact Hrc | exact K].
-
destruct J as (pb & PBS & REST & EBS & OPB & len & str & junk & ER & HL & HS & HDR). subst REST BS.
cbn [app] in HP.
pose proof (heap_blk S4L HIx _ _ _ _ x (str_objsize len) HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x (str_objsize len) HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi. unfold str_objsize in *.
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. norm_w32. step. stepz. stepz. step. if_truex.
step. step. if_truex.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp) HP MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; apply in_or_app; right; exact Hb) ltac:(clia))
as (HP2 & AG2 & HPR2).
apply evt_RZ_done.
eapply mf_gen; [exact HP2 | unfold jhdr_cells; cbn [app]; exact HDR | | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | exact VM0 | eapply heap_pres_trans; [exact HPR | exact HPR2] | exact FS | exact FRM | exact Hrc | exact K].
eapply opt_pbuf_agree; [exact OPB | eapply agree_on_incl; [exact AG2 | intros b Hb; apply in_or_app; left; exact Hb] | apply incl_refl].
Qed.

#[using="w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_41 joff_43 e_pbfree LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_41 E_41 D_43 E_43 LINK_41 LINK_43 wb17544_1 D_b17544_1 E_b17544_1 LINK_b17544_1 CODE_e_blk_17544 AL_e_blk_17544_b4 RNG_e_blk_17544_code printbuf_free_cps LAY_POS_e_fn_free_userdata LAY_HI_e_fn_free_userdata LAY_POS_e_fn_ud_to_json_string LAY_HI_e_fn_ud_to_json_string joffb17544_1"] Lemma mf_dblu :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (junk8 : list byte)
(pb : Z) (PBS : list blk) (bits : word) (ud udn : Z) (uds : list byte),
s = Sdouble true -> BS = [(x, 48); (ud, udn)] ++ PBS ->
HEAPx A (BS ++ LB) m md ->
opt_pbuf segs m PBS pb ->
rw_cells segs m x (jhdr_cells JT_DOUBLE 0 (fn_ud_to_json_string S4F) pb (fn_free_userdata S4F) ud ++ [C8 bits]) ->
cstr segs m ud udn uds ->
mf_frame ra sp s0 s1 m junk8 ->
stk segs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
KPOST HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo errv s BS x rc T ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x34)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_41 joff_43 e_pbfree LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_41 E_41 D_43 E_43 LINK_41 LINK_43 wb17544_1 D_b17544_1 E_b17544_1 LINK_b17544_1 CODE_e_blk_17544 AL_e_blk_17544_b4 RNG_e_blk_17544_code printbuf_free_cps LAY_POS_e_fn_free_userdata LAY_HI_e_fn_free_userdata LAY_POS_e_fn_ud_to_json_string LAY_HI_e_fn_ud_to_json_string joffb17544_1 segs base gTP S4F HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo errv s BS x rc T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_free_userdata as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_free_userdata as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_ud_to_json_string as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_ud_to_json_string as gL5_; unfold gw_le in gL5_.
intros until uds. intros Hs HBS HP OPB HDR UD FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc K.
unfold mf_frame in FR. unfold_consts. word_range sp SPR. subst BS. cbn [app] in HP.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
pose proof (heap_blk S4L HIx _ _ _ _ ud udn HP ltac:(right; left; reflexivity)) as (Hudn & Hual & Hulo & Huhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi, Huhi.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hxud.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [] m) as MU.
clear UD.
unfold jhdr_cells in HDR. cbn [app fn_ud_to_json_string fn_free_userdata S4F] in HDR.
apply rz_evt; [exact MOK|].
step. step. if_falsex. step. step. step. step. step.

step. step.
alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ right. exists udn. right; left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR3 by lia.
rewrite lb_remove_other in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
assert (OPB3 : opt_pbuf segs m3 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_heap_pres segs S4L); [exact HPR3 | reflexivity | intros b Hb; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres S4L LB (bv_unsigned sp) m0 m3).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; right; apply in_or_app; right; exact Hb]. }
clear MU WM MI ST HPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
reenter MOK3. step.
apply evt_RZ_done.
eapply mf_scalar; [exact HP3 | unfold jhdr_cells; cbn [app]; exact HDR | reflexivity | right; left; reflexivity | exact OPB3 | exact FR | exact ST3 | clia | clia | exact SPA | exact HT
| exact ERR3 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM3] | exact HPRb | exact FS | exact FRM | exact Hrc | exact K].
Qed.
End MF2.

Section MF3.
Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].
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
F1 (Z_to_bv 64 (base + 0x54)) fc1 None m (seg_rom segs)) md) T.
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
assert (Ht16 : 0 < t /\ t mod 16 = 0).
{ destruct LT as (tbl_ & size_ & es_ & svs_ & _ & ETBS_ & _).
assert (INt : In (t, 56) TBS) by (rewrite ETBS_; unfold lh_blocks; left; reflexivity).
destruct (heap_blk S4L HIx _ _ _ _ t 56 HP ltac:(in_sub INt)) as (_ & Ht16a & Ht0 & _). split; assumption. }
call lh_table_length_spec; [exact MI | exact LT2 | exact (proj1 Ht16) | exact (proj2 Ht16) | reflexivity |].
clear HP2 AG2 HPR2 LT2. match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end. rename MI0 into MI.
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
F1 (Z_to_bv 64 (base + 0x54)) fc1 None m (seg_rom segs)) md) T.
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
call array_list_length_spec; [exact MI | exact AL2 | intros b n Hb; destruct (heap_blk S4L HIx _ _ _ _ b n HP ltac:(in_sub Hb)) as (_ & Hb16 & Hb0 & Hbhi & _); unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | reflexivity |].
clear HP2 AG2 HPR2 AL2. match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end. rename MI0 into MI.
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

Section MF4.
Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].
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
step. step. step. step. step. step. step. ubsan_align Hxal. step. norm_w32. step. norm_w32. stepz.
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
