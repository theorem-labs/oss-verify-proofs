(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVbl.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPIU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPIU.Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Mh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Mh.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRGY.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXOI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXOI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwApply2 GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm; gwj_align_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm; gwj_align_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition ulhlookup_code : list Z :=
[0xfb010113; 0x04113423; 0x04813023; 0x02913c23; 0x03213823; 0x03313423; 0x03413023; 0x01513c23; 0x01613823; 0x01713423; 0x10050863; 0x00050413; 0x00757513; 0x10051263; 0x00058493; 0x00042583; 0x0e058c63; 0x0cb05263; 0x00000993; 0x02b67933; 0x02800a13; 0xffe00a93; 0xfff00b13; 0x0280006f; 0x00042583; 0x0019899b; 0x00190513; 0x0019091b; 0x0125c633; 0x00163613; 0xfff60613; 0x00a67933; 0x08b9d463; 0x01843603; 0x03490bb3; 0x00cb8533; 0x00c036b3; 0x00153713; 0x0ae68063; 0x08c56e63; 0x034916b3; 0x43fbd713; 0x00e6c6b3; 0x00d036b3; 0x08069463; 0x08060263; 0x00757613; 0x06061e63; 0x00053503; 0xfb5500e3; 0x05650063; 0x03043603; 0x00048593; 0x000600e7; 0xf80504e3; 0x01843503; 0x00ab8bb3; 0x04abea63; 0x00a035b3; 0x001bb613; 0x00c5c5b3; 0x04058263; 0x02800593; 0x02b905b3; 0x00b50533; 0x0080006f; 0x00000513; 0x04813083; 0x04013403; 0x03813483; 0x03013903; 0x02813983; 0x02013a03; 0x01813a83; 0x01013b03; 0x00813b83; 0x05010113; 0x00008067; 0xc0001073]%Z.

Lemma mul40_chk : forall n, 0 <= n -> n * 40 < 2^63 ->
v_sltu (Z_to_bv 64 0)
(Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 n) * 40) 64)))
(bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (n * 40))) 63))))) = Z_to_bv 64 0.
Proof.
intros n H0 H1. rewrite !signed_lit by lia. rewrite !Z.shiftr_div_pow2 by lia. rewrite !Z.div_small by lia.
rewrite (unsigned_lit 0) by lia. change (Z.lxor 0 0) with 0. apply v_sltu_0'. rewrite !unsigned_lit; lia.
Qed.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section G.
Variables (segs : list Segment) (base : Z).
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

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma gLAYF0 : ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gTP gIMG_LO gIMG_HI. pose proof LAY_TPLO as X1; pose proof LAY_TPHI as X2; unfold gw_le in X1, X2. split; [split; [exact X1 | exact X2] | exact LAY_gIMG_LO]. Qed.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Variables (e_blk_1a328 e_strcmp : Z).
Hypothesis CODE : code_at segs base ulhlookup_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 316.

Definition u_lh_char_equal_post := ltac:(let t := constr:(ltac:(gw_callee_stmt (@QRGY.Mq0.gw_all) (@QRGY.Mq0.u_lh_char_equal_post) e_fn_lh_char_equal)) in let t := eval cbv beta delta [QRGY.Mq0.u_lh_char_equal_post] in t in exact t).

Hypothesis u_lh_char_equal_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QRGY.Mq0.gw_all) (@QRGY.Mq0.u_lh_char_equal_spec) e_fn_lh_char_equal)) in let x := constr:(ltac:(gw_callee_stmt (@QRGY.Mq0.gw_all) (@QRGY.Mq0.u_lh_char_equal_post) e_fn_lh_char_equal)) in let T := gw_subst T x u_lh_char_equal_post in exact T).

Hypothesis ent_addr_mod8 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QXOI.gw_all) (@QXOI.ent_addr_mod8) (base + -112)%Z)) in let T := eval cbv beta delta [QXOI.u_lh_entry_free_entry QXOI.u_lh_table_free_entry] in T in let T := gw_fold_pcs T base (-112)%Z [0; 48; 80]%Z in let x := constr:(ltac:(gw_callee_stmt (@QRGY.Mq0.gw_all) (@QRGY.Mq0.u_lh_char_equal_post) e_fn_lh_char_equal)) in let T := gw_subst T x u_lh_char_equal_post in exact T).
Arguments ent_addr_mod8 _%_Z_scope _%_nat_scope.

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
Hypothesis AL_e_fn_lh_char_equal : gw_b4 e_fn_lh_char_equal.
Hypothesis RNG_e_fn_lh_char_equal : gw_br e_fn_lh_char_equal 4.
Hypothesis LAY_POS_e_fn_lh_char_equal : gw_le 1 e_fn_lh_char_equal.
Hypothesis LAY_HI_e_fn_lh_char_equal : gw_le (e_fn_lh_char_equal + 4) 1099511627776.
#[using="RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI AL_gTP RNG_gTP e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free e_blk_1a328 e_strcmp CODE BASE4 BASER u_lh_char_equal_spec ent_addr_mod8 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal U4F"] Lemma gw_all : True. Proof. exact I. Qed.

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
Ltac gj_fn_cbn := try (progress cbn [U4F fn_lh_char_equal]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Definition u_lh_lookup_entry : Z := (base + 0x0).

Section ULhLookup.
Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size kp lo : Z) (es : list lent) (svs : list slotv) (ps : list byte).

Definition u_lookup_res (r : Z) : Prop :=
r = 0 \/ exists j e, nth_error es j = Some e /\ r = ent_addr tbl (le_ix e) /\ le_ks e = ps.

Definition u_lh_lookup_post (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (r : Z) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ lh_open segs U4F m' t tbl size es svs
/\ bytes_at segs m' kp (ps ++ [b0])
/\ u_lookup_res r.

Definition ulk_frame (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells segs m (bv_unsigned sp + -80) [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_char_equal CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma u_lh_lookup_next :
forall (n cnt : Z) (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word) (m : word -> option byte),
0 <= cnt < size -> 0 <= n < size -> In size lf_sizes -> mem_inv segs m ->
evt segs (fun ms' =>
(cnt + 1 < size /\
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp)
(Z_to_bv 64 (n + 1)) (Z_to_bv 64 size) (Z_to_bv 64 (if n + 1 =? size then 0 else -1)) a3 a4 a5 a6 a7
(Z_to_bv 64 (next_ix size n)) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 40) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1)) x22 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x84)) fc None m (seg_rom segs))
\/ (cnt + 1 = size /\
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp)
(Z_to_bv 64 (n + 1)) (Z_to_bv 64 size) (Z_to_bv 64 (if n + 1 =? size then 0 else -1)) a3 a4 a5 a6 a7
(Z_to_bv 64 (next_ix size n)) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 40) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1)) x22 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x108)) fc None m (seg_rom segs)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 n) (Z_to_bv 64 cnt) (Z_to_bv 64 40) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1)) x22 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x64)) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_char_equal CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs base ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
intros until m. intros Hcnt Hn Hsz MI.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
step. norm_w32. step. step. norm_w32. step. rewrite (unsigned_lit size), (unsigned_lit (n + 1)) by lia.
unfold next_ix. destruct (Z.eqb_spec (n + 1) size) as [EQ|NE].
- rewrite EQ, Z.lxor_nilpotent. step. rewrite (v_sltiu_1 (Z_to_bv 64 0) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. rewrite (unsigned_lit size) by lia. change (bv_unsigned (Z_to_bv 64 (1 + -1))) with 0. rewrite Z.land_0_l.
replace (1 + -1) with 0 by lia.
step.
destruct (Z.lt_ge_cases (cnt + 1) size).
+ if_falsex. apply evt_done. left. split; [lia | reflexivity].
+ if_truex. apply evt_done. right. split; [lia | reflexivity].
- pose proof (lxor_bound size (n + 1) 31 ltac:(lia) ltac:(lia) ltac:(lia)) as LB.
assert (LNZ : Z.lxor size (n + 1) <> 0) by (intros X; apply Z.lxor_eq in X; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (Z.lxor size (n + 1))) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615.
rewrite (unsigned_lit (n + 1)) by lia. rewrite land_ones64_l by lia.
replace (0 + -1) with (-1) by lia.
step.
destruct (Z.lt_ge_cases (cnt + 1) size).
+ if_falsex. apply evt_done. left. split; [lia | reflexivity].
+ if_truex. apply evt_done. right. split; [lia | reflexivity].
Qed.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma u_lh_lookup_exit0 :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word) (m0 m : word -> option byte) (junk8 : list byte),
mem_inv segs m -> lh_open segs U4F m t tbl size es svs -> bytes_at segs m kp (ps ++ [b0]) ->
stk segs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp - 96 -> ulk_frame m junk8 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m0 m -> wmono segs m0 m ->
evt segs (u_lh_lookup_post m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x108)) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs base U4F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
intros until junk8. intros MI OPEN PS ST LOS FR MU WM. unfold ulk_frame in FR. word_range sp SPR.
step. do 10 step. release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold u_lh_lookup_post. do 14 eexists. exists 0. eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact OPEN|]. split; [exact PS|].
left. reflexivity.
Qed.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma u_lh_lookup_exit1 :
forall (n : Z) (e : lent) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 t3 t4 t5 t6 : word) (m0 m : word -> option byte) (junk8 : list byte),
0 <= n < size -> In size lf_sizes -> In e es -> le_ix e = Z.to_nat n -> le_ks e = ps ->
mem_inv segs m -> lh_open segs U4F m t tbl size es svs -> lh_below lo t tbl size es -> 0 < tbl -> bytes_at segs m kp (ps ++ [b0]) ->
stk segs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp - 96 -> ulk_frame m junk8 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m0 m -> wmono segs m0 m ->
evt segs (u_lh_lookup_post m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 n) x19 x20 x21 x22 (Z_to_bv 64 (n * 40)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xdc)) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs base U4F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
intros until junk8. intros Hn Hsz He Hix Hks MI OPEN BELOW Hblo PS ST LOS FR MU WM. unfold ulk_frame in FR. word_range sp SPR.
pose proof OPEN as (HDR & _). unfold lh_hdr, lh_hdrf in HDR. pose proof BELOW as (Ht0 & Ht & Hb0 & Hb & _).
pose proof (lf_size_range size Hsz) as HSR. unfold_consts.
step. step. step. if_falsex.
step. step. step.
rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 tbl)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_sltiu_0 (Z_to_bv 64 (n * 40 + tbl)) 1) by (rewrite ?unsigned_lit by lia; lia).
rewrite !unsigned_lit by lia. change (Z.lxor 1 0) with 1.
step. if_false.
step. step. rewrite (unsigned_lit n) by lia. step.
do 11 step. release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold u_lh_lookup_post. do 14 eexists. exists (tbl + n * 40). eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact OPEN|]. split; [exact PS|].
right. destruct (In_nth_error _ _ He) as [j Hj]. exists j, e. split; [exact Hj|]. split; [unfold ent_addr; rewrite Hix; lia | exact Hks].
Qed.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER u_lh_char_equal_spec ent_addr_mod8 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma u_lh_lookup_loop :
forall (k : nat) (n cnt : Z) (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (m0 m : word -> option byte) (junk8 : list byte),
Z.of_nat k = size - cnt -> 0 <= cnt < size -> 0 <= n < size ->
mem_inv segs m ->
lh_open segs U4F m t tbl size es svs -> lh_below lo t tbl size es -> tbl mod 16 = 0 -> 0 < tbl ->
bytes_at segs m kp (ps ++ [b0]) -> ~ In b0 ps -> (kp + Z.of_nat (length ps) + 1 <= lo \/ bv_unsigned sp <= kp) ->
stk segs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp - 96 ->
ulk_frame m junk8 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m0 m -> wmono segs m0 m ->
evt segs (u_lh_lookup_post m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 n) (Z_to_bv 64 cnt) (Z_to_bv 64 40) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1)) x23 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x84)) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER u_lh_char_equal_spec ent_addr_mod8 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs base U4F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
induction k as [|k IH]; intros until junk8; intros Hk Hcnt Hn MI OPEN BELOW Hbal Hblo PS NP SEPk ST LOS FR MU WM; [lia|].
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hc & Hlen). pose proof BELOW as (Ht0 & Ht & Hb0 & Hb & Hkb).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. pose proof FR as FR0. unfold ulk_frame in FR. word_range sp SPR. unfold_consts.
pose proof (bytes_at_bound _ _ _ _ PS) as PSB. rewrite length_app in PSB. cbn [length] in PSB.
destruct (nth_error svs (Z.to_nat n)) as [sv|] eqn:Esv.
2:{ exfalso. apply nth_error_None in Esv. lia. }
pose proof (SL (Z.to_nat n) sv Esv) as C. unfold ent_addr, slot_cells in C. rewrite Z2Nat.id in C by lia.
pose proof (rw_cells_bound segs m _ _ C) as CB0. cbn [cells_size csize Nat.add] in CB0.

step. step. step. rewrite (unsigned_lit n) by lia.
step. step. ub_nzpair tbl (n * 40 + tbl). step. if_false.
step. if_falsex.
step. step. step. step. rewrite (mul40_chk n) by lia. step. if_false.
step. if_falsex.
step. rewrite (unsigned_lit (n * 40 + tbl)) by lia. rewrite (land7_of_mod8 (n * 40 + tbl)) by (replace (n * 40 + tbl) with (tbl + 40 * Z.of_nat (Z.to_nat n)) by lia; apply ent_addr_mod8; exact Hbal).
step. if_false.
replace (n * 40 + tbl) with (tbl + 40 * n) by lia.
remember (tbl + 40 * n) as B eqn:EB.
step. subst B.
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (in_dec Nat.eq_dec (Z.to_nat n) (map le_ix es)) as [LIVE|DEAD].
-
apply in_map_iff in LIVE. destruct LIVE as (e & Hix & He).
destruct (In_nth_error _ _ He) as [j Hj].
destruct (LK1 j e Hj) as (sv' & Esv' & Ek & Ekc & Ev & Enx & Epv). rewrite Hix, Esv in Esv'. injection Esv' as <-.
destruct (LK4 e He) as (Hk0 & HkF & Hkn31 & Hv). unfold LH_FREEDv in HkF.
destruct (lh_key_bytes segs m es e KEYS He) as (KB & KNZ & KL).
rewrite Ek.
step. unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 (-2))) with 18446744073709551614. rewrite (unsigned_lit (le_k e)) by lia. if_false.
step. unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615. rewrite (unsigned_lit (le_k e)) by lia. if_false.
step. step. step.

cbn [fn_lh_char_equal U4F]. gw_ret_pc_var_tac.
pose proof (Hkb e He) as Hke.
pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp + -80)] m) as MUk. pose proof (wmono_refl segs m) as WMk.
eapply evt_cut.
{ eapply u_lh_char_equal_spec with (ls := le_ks e) (rs := ps) (lo := lo);
rewrite ?(unsigned_lit (le_k e)), ?(unsigned_lit kp), ?(unsigned_lit (bv_unsigned sp + -80)) by lia;
first [exact KB | exact PS | exact KNZ | exact NP | exact ST | exact MI | lia]. }
unfold u_lh_char_equal_post. cbv beta.
rewrite ?(unsigned_lit (le_k e)), ?(unsigned_lit kp), ?(unsigned_lit (bv_unsigned sp + -80)) by lia.
post_call segs m.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (OPEN' : lh_open segs U4F mx t tbl size es svs)
by (eapply (lh_open_frame segs U4F _ m mx); [exact OPEN | exact BELOW | exact MUk | exact WMk | apply Forall_cons; [cbn; lia | apply Forall_nil]]);
rename mx into m2 end.
match goal with H : stk segs m2 lo _ |- _ => rename H into ST2 end.
match goal with H : bytes_at segs m2 kp _ |- _ => rename H into PS2 end.
clear MUk WMk OPEN. try clear C. try clear PS. try clear ST.
destruct (Z.eqb_spec (strcmp_model (le_ks e) ps) 0) as [EQ0|NE0].
+
step. if_false.
eapply (u_lh_lookup_exit1 n e); first [exact OPEN' | exact BELOW | exact Hblo | exact PS2 | exact ST2 | exact MU | exact WM | exact He | exact Hix | exact Hsz | eassumption | idtac].
apply (proj1 (strcmp_model_zero _ _ KNZ NP)). exact EQ0.
+
step. if_true. step. norm_sx32.
match goal with H : mem_inv segs m2 |- _ => rename H into MI end.
eapply evt_cut; [eapply (u_lh_lookup_next n cnt); [lia | lia | exact Hsz | exact MI] |].
cbv beta. intros ms' [[Hlt' ->] | [Heq ->]].
* eapply (IH (next_ix size n) (cnt + 1));
first [exact OPEN' | exact BELOW | exact PS2 | exact NP | exact SEPk | exact ST2 | exact FR | exact MU | exact WM | exact MI | exact Hbal | exact Hblo | idtac];
unfold next_ix; try (destruct (Z.eqb_spec (n + 1) size)); lia.
* eapply u_lh_lookup_exit0; first [exact OPEN' | exact PS2 | exact ST2 | exact FR | exact MU | exact WM | exact MI | lia].
-
destruct (LK2 (Z.to_nat n) sv Esv DEAD) as [EK | FK]; rewrite EK || rewrite FK; unfold LH_EMPTYv, LH_FREEDv.
+ step. if_false. step. if_true.
eapply u_lh_lookup_exit0; first [exact OPEN | exact PS | exact ST | exact FR0 | exact MU | exact WM | exact MI | lia].
+ step. if_true.
eapply evt_cut; [eapply (u_lh_lookup_next n cnt); [lia | lia | exact Hsz | exact MI] |].
cbv beta. intros ms' [[Hlt' ->] | [Heq ->]].
* eapply (IH (next_ix size n) (cnt + 1));
first [exact OPEN | exact BELOW | exact PS | exact NP | exact SEPk | exact ST | exact FR0 | exact MU | exact WM | exact MI | exact Hbal | exact Hblo | idtac];
unfold next_ix; try (destruct (Z.eqb_spec (n + 1) size)); lia.
* eapply u_lh_lookup_exit0; first [exact OPEN | exact PS | exact ST | exact FR0 | exact MU | exact WM | exact MI | lia].
Qed.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER u_lh_char_equal_spec ent_addr_mod8 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma u_lh_lookup_spec :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (h : Z),
mem_inv segs m ->
lh_open segs U4F m t tbl size es svs -> lh_below lo t tbl size es -> t mod 16 = 0 -> tbl mod 16 = 0 -> 0 < t -> 0 < tbl ->
bytes_at segs m kp (ps ++ [b0]) -> ~ In b0 ps -> (kp + Z.of_nat (length ps) + 1 <= lo \/ bv_unsigned sp <= kp) ->
stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 kp -> a2 = Z_to_bv 64 h -> 0 <= h < 2^64 ->
evt segs (u_lh_lookup_post m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 u_lh_lookup_entry) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER u_lh_char_equal_spec ent_addr_mod8 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs U4F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
intros until h. intros MI OPEN BELOW Htal Hbal Htlo Hblo PS NP SEPk ST LOS A0 A1 A2 Hh.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hc & Hlen). pose proof BELOW as (Ht0 & Ht & Hb0 & Hb & Hkb).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. word_range sp SPR. unfold_consts.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl segs m) as WM.
unfold u_lh_lookup_entry. subst a0 a1 a2.
carve_frame 80%nat ST.
do 10 step.
step. if_falsex. step. step. step. ubsan_align Htal.
step. step. norm_sx32. step. if_falsex. step. if_falsex.
step. step. rewrite remu_lit by lia. step. step. step. step.
pose proof (Z.mod_pos_bound h size ltac:(lia)) as HM.
eapply (u_lh_lookup_loop (Z.to_nat size) (h mod size) 0);
first [exact BELOW | exact PS | exact NP | exact SEPk | exact ST | exact MU | exact WM | exact MI | exact FR | exact Hbal | exact Hblo | lia | idtac].
eapply (lh_open_frame segs U4F _ m); [exact OPEN | exact BELOW | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]].
Qed.
End ULhLookup.

End G.
