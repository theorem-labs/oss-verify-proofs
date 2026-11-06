(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QCcH Q0Ek Qsw7 QJjn QPIU QQLG QnCn Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply Lib.GwApply2 Lib.GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QCcH Q0Ek Qsw7 QJjn.
Import QPIU.Mqe.
Import QQLG.Mq9.
Import QnCn.Mq0.
Import QPIU.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q0Hd.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition aldel_code (w_39 : Z) : list Z :=
[0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x00060413; 0x00050493; 0xfff64613; 0xfff00513; 0x08b66063; 0x0084b603; 0x06c5fc63; 0x00b40933; 0x07266863; 0x00359993; 0x0325fe63; 0x00098a13; 0x00040a93; 0x0100006f; 0xfffa8a93; 0x008a0a13; 0x020a8063; 0x0004b503; 0x01450533; 0x00053503; 0xfe0504e3; 0x0184b583; 0x000580e7; 0xfddff06f; 0x0084b603; 0x0004b583; 0x00391693; 0x41260633; 0x01358533; 0x00d585b3; 0x00361613; w_39; 0x00000513; 0x0084b583; 0x408585b3; 0x00b4b423; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x04010113; 0x00008067]%Z.

Lemma lxor_ones64 : forall c, 0 <= c < 2^64 -> Z.lxor c 18446744073709551615 = 18446744073709551615 - c.
Proof.
intros c Hc. pose proof (Z.add_lxor_2land c 18446744073709551615) as H.
change 18446744073709551615 with (Z.ones 64) in H at 2. rewrite Z.land_ones in H by lia.
rewrite Z.mod_small in H by lia. lia.
Qed.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_39 : Z).
Variables (joff_39 : bv 21).
Variables (e_memmove : Z).
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
Hypothesis CODE : code_at segs base (aldel_code w_39).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 212.
Hypothesis D_39 : decode_any (Z_to_bv 32 w_39) = Some (Jal 1 joff_39, 4%Z).
Hypothesis E_39 : is_ecall (Z_to_bv 32 w_39) = false.
Hypothesis LINK_39 : gw_anch (base + 156 + bv_signed joff_39)%Z (e_memmove + 0)%Z.

Definition memmove_post := Eval cbv beta delta [QQLG.Mq9.memmove_post] in (@QQLG.Mq9.memmove_post segs).
Definition memmove_stmt := ltac:(let t := eval cbv beta delta [QQLG.Mq9.memmove_stmt] in (@QQLG.Mq9.memmove_stmt segs e_memmove) in let t := gw_subst t (@QQLG.Mq9.memmove_post segs) memmove_post in exact t).

Hypothesis memmove_specZ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqe.gw_all) (@QPIU.Mqe.memmove_specZ) (base + -7816)%Z)) in let T := eval cbv beta delta [QPIU.Mqe.printbuf_memappend_entry] in T in let T := gw_subst T (@QQLG.Mq9.memmove_post segs) memmove_post in let T := gw_subst T (@QQLG.Mq9.memmove_stmt segs e_memmove) memmove_stmt in let T := gw_subst T (@QPIU.Mqe.memmove_post segs) memmove_post in let T := gw_subst T (@QPIU.Mqe.memmove_stmt segs (base + -7816)%Z) memmove_stmt in let T := gw_fold_pcs T base (-7816)%Z [0; 260]%Z in exact T).

Hypothesis al_nth_null : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mq0.gw_all) (@QPIU.Mq0.al_nth_null) (base + -592)%Z)) in let T := eval cbv beta delta [QPIU.Mq0.array_list_free_entry] in T in let T := gw_subst T (@QQLG.Mq9.memmove_post segs) memmove_post in let T := gw_subst T (@QQLG.Mq9.memmove_stmt segs e_memmove) memmove_stmt in let T := gw_fold_pcs T base (-592)%Z [0; 56; 88]%Z in exact T).

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
Hypothesis AL_e_fn_arr_entry_free : gw_b4 e_fn_arr_entry_free.
Hypothesis RNG_e_fn_arr_entry_free : gw_br e_fn_arr_entry_free 4.
Hypothesis LAY_POS_e_fn_arr_entry_free : gw_le 1 e_fn_arr_entry_free.
Hypothesis LAY_HI_e_fn_arr_entry_free : gw_le (e_fn_arr_entry_free + 4) 1099511627776.
#[using="w_39 joff_39 e_memmove RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_39 E_39 LINK_39 memmove_specZ al_nth_null AL_e_fn_arr_entry_free RNG_e_fn_arr_entry_free LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.
Ltac gj_fn_cbn := try (progress cbn [S4F fn_arr_entry_free]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

#[using="al_nth_null"] Lemma al_nth_app_r : forall ps zs i, Z.of_nat (length ps) <= i -> Forall (fun p => p = 0) zs -> al_nth (ps ++ zs) i = 0.
Proof. clear - al_nth_null.
intros ps zs i Hi NUL. unfold al_nth. rewrite app_nth2 by lia.
pose proof (al_nth_null zs (i - Z.of_nat (length ps)) NUL) as X. unfold al_nth in X.
replace (Z.to_nat i - length ps)%nat with (Z.to_nat (i - Z.of_nat (length ps))) by lia. exact X.
Qed.

Section AlDel.
Hypothesis MEMMOVE : memmove_stmt.

Definition array_list_del_idx_entry : Z := (base + 0x0).

#[using="w_39 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free"] Lemma al_del_loop :
forall (k : nat) (i S4v S5v : Z) (x1 x2 gp tp t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a arr len size stop : Z) (qs : list Z) (idx : Z),
Z.of_nat k = stop - 1 - i -> idx <= i < stop -> S4v = 8 * i -> S5v = stop - i -> stop = Z.of_nat (length qs) -> stop <= len -> 8 * len < 2^64 ->
0 <= idx -> (forall j, idx <= j < stop -> al_nth qs j = 0) ->
mem_inv segs m ->
rw_cells segs m a [C8 (Z_to_bv 64 arr); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (fn_arr_entry_free S4F))] ->
u64arr segs m arr (wl qs) ->
evt segs (eq (MS (mkR x1 x2 gp tp t0 t1 t2 x8 (Z_to_bv 64 a) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 (8 * stop)) (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x80)) fc None m (seg_rom segs)))
(MS (mkR x1 x2 gp tp t0 t1 t2 x8 (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 S4v) (Z_to_bv 64 S5v) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x64)) fc None m (seg_rom segs)).
Proof. clear - w_39 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free segs base S4F MEMMOVE. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_arr_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_arr_entry_free as gL3_; unfold gw_le in gL3_.
induction k as [|k IH]; intros until idx; intros Hk Hi HS4 HS5 Hstop Hsl H64 Hidx NUL MI HDR ARR; subst S4v S5v.
- pose proof (u64arr_bound segs m arr (wl qs) ARR) as AB. rewrite wl_length in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
step. step.
pose proof (al_slot_read segs m arr qs i (wa (arr + 8 * i)) ARR ltac:(lia) eq_refl) as RD.
rewrite (NUL i) in RD by lia.
step. step. if_true. step. step. step. if_truex.
apply evt_done. replace (stop - i + -1) with 0 by lia. replace (8 * i + 8) with (8 * stop) by lia. reflexivity.
- pose proof (u64arr_bound segs m arr (wl qs) ARR) as AB. rewrite wl_length in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
step. step.
pose proof (al_slot_read segs m arr qs i (wa (arr + 8 * i)) ARR ltac:(lia) eq_refl) as RD.
rewrite (NUL i) in RD by lia.
step. step. if_true. step. step. step. if_falsex.
eapply (IH (i + 1)); [ | | | | exact Hstop | exact Hsl | exact H64 | exact Hidx | exact NUL | exact MI | exact HDR | exact ARR]; lia.
Qed.

Definition array_list_del_idx_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a arr size : Z) (ps zs : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (match zs with [] => 2^64 - 1 | _ => 0 end)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (a, a + AL_SZ); (arr, arr + 8 * size)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ alist segs S4F m' [(a, AL_SZ); (arr, 8 * size)] a ps.

#[using="w_39 joff_39 e_memmove gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_39 E_39 LINK_39 memmove_specZ al_nth_null LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free MEMMOVE"] Lemma array_list_del_idx_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a arr size : Z) (ps zs : list Z) (lo : Z),
mem_inv segs m ->
alist segs S4F m [(a, AL_SZ); (arr, 8 * size)] a (ps ++ zs) ->
Forall (fun p => p = 0) zs ->
(a + AL_SZ <= arr \/ arr + 8 * size <= a) ->
stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
a + AL_SZ <= lo -> arr + 8 * size <= lo ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 (Z.of_nat (length ps)) -> a2 = Z_to_bv 64 (Z.of_nat (length zs)) ->
evt segs (array_list_del_idx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a arr size ps zs lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_del_idx_entry) fc None m (seg_rom segs)).
Proof. clear - w_39 joff_39 e_memmove gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_39 E_39 LINK_39 memmove_specZ al_nth_null LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free MEMMOVE segs S4F. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_arr_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_arr_entry_free as gL3_; unfold gw_le in gL3_.
intros until lo. intros MI AL NUL SEP ST LOS ALO ARRLO A0 A1 A2.
destruct (alist_openx segs S4F m a arr size (ps ++ zs) AL) as (junk & HDR & ARR & JK & Hlen & Hsz).
unfold al_hdr in HDR. unfold al_tail in JK.
pose proof (length_app ps zs) as LA. apply (f_equal Z.of_nat) in LA. rewrite Nat2Z.inj_add in LA. rewrite LA in HDR.
pose proof (u64arr_bound segs m arr (wl (ps ++ zs)) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length (ps ++ zs)) as WL.
pose proof (rw_cells_bound segs m a _ HDR) as HB. cbn [cells_size csize Nat.add] in HB.
word_range sp SPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (a, a + AL_SZ); (arr, arr + 8 * size)] m) as MU.
unfold array_list_del_idx_entry, array_list_del_idx_post. subst a0 a1 a2.
carve_frame 64%nat ST.
do 8 step.
step. step. step.
unfold v_xori. rewrite (unsigned_lit (Z.of_nat (length zs))) by lia. change (bv_wrap 64 (-1)) with 18446744073709551615.
rewrite lxor_ones64 by lia.
step. step. if_falsex.
step.
destruct zs as [|z zs'].
-
change (Z.of_nat (@length Z [])) with 0 in *. rewrite app_nil_r in *. rewrite Z.add_0_r in *. clear LA.
step. if_truex.
do 9 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
eapply alist_close. split; [exact HDR | split; [exact ARR | split; [exact JK | lia]]].
- assert (LZ : 1 <= Z.of_nat (length (z :: zs'))) by (cbn [length]; lia).
step. if_falsex. step. step. if_falsex.
step. rewrite (unsigned_lit (Z.of_nat (length ps))) by lia. rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length ps)) 3) by lia. change (2^3) with 8.
step. if_falsex. step. step. step.
eapply evt_cut.
{ eapply al_del_loop with (k := Z.to_nat (Z.of_nat (length (z :: zs')) - 1)) (i := Z.of_nat (length ps))
(a := a) (arr := arr) (len := Z.of_nat (length ps) + Z.of_nat (length (z :: zs'))) (size := size)
(stop := Z.of_nat (length (z :: zs')) + Z.of_nat (length ps)) (qs := ps ++ z :: zs') (idx := Z.of_nat (length ps));
[ | | | | lia | lia | lia | lia | | exact MI | exact HDR | exact ARR].
- lia.
- lia.
- lia.
- lia.
- intros j Hj. apply al_nth_app_r; [lia | exact NUL]. }
intros ms' <-.

destruct (al_tail_absorb segs m0 arr size ps (z :: zs') junk ARR JK ltac:(lia)) as [ARR1 TL]. clear ARR JK.
unfold al_tail in TL.
pose proof (wl_length ps) as WL1.
step. step.
step. rewrite (unsigned_lit (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps))) by lia.
rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps)) 3) by lia. change (2^3) with 8.
step. rewrite !unsigned_lit by lia.
replace (Z.of_nat (length ps) + Z.of_nat (length (z :: zs')) - (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps))) with 0 by lia.
step. step.
step. step.

assert (DST : rw_cells segs m0 (arr + Z.of_nat (length ps) * 8) [CB 0%nat []]).
{ split; [split; [cbn; auto | cbn; apply bytes_at_nil; lia] | cbn; split; [lia | split; [lia | intros i Hi; lia]]]. }
call (memmove_specZ MEMMOVE); [lia | lia | lia | apply bytes_at_nil; lia | reflexivity | exact DST | exact MI |].
step. step.
step. rewrite !unsigned_lit by lia.
replace (Z.of_nat (length ps) + Z.of_nat (length (z :: zs')) - Z.of_nat (length (z :: zs'))) with (Z.of_nat (length ps)) by lia.
step.
do 9 step.
apply evt_done. do 15 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split. { lazymatch goal with |- stk _ ?mf _ _ => match goal with FRx : rw_cells segs mf (bv_unsigned sp + -64) _, STx : stk segs mf _ _ |- _ =>
release_frame FRx STx (bv_unsigned sp); exact STx end end. }
eapply alist_close. split; [| split; [eassumption | split; [eassumption | lia]]]. unfold al_hdr. eassumption.
Qed.
End AlDel.

End G.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH QHnV QfLs QRUw QgoP Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QPIU.Mqd.
Import QRUw.Mq2.
Import QgoP.
Import QPIU.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition jonewdoubles_code (w_8 w_12 w_14 w_23 w_31 w_32 w_42 w_44 w_45 : Z) : list Z :=
[0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00813027; 0x00050493; 0x22a50453; 0x03000513; w_8; 0x06050c63; 0x00050413; 0x00100513; w_12; 0x02051513; w_14; 0x00250513; 0x00a43023; 0x00b43423; 0x00043823; 0x00043c23; 0x02043023; 0x02843427; 0x00048513; w_23; 0x04050263; 0x00050493; 0x01843603; 0x00060863; 0x02043583; 0x00040513; 0x000600e7; w_31; w_32; 0x00000597; 0x05c58593; 0x00b43423; 0x00a43c23; 0x02943023; 0x02c0006f; 0x00000413; 0x0240006f; 0x01043503; w_42; 0x00040513; w_44; w_45; 0x00000413; 0x00c00593; 0x00b52023; 0x00040513; 0x01813083; 0x01013403; 0x00813483; 0x00013407; 0x02010113; 0x00008067]%Z.

Definition blk_194bc_code : list Z := [0x00020513; 0xf5c50513; 0x00008067]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_8 w_12 w_14 w_23 w_31 w_32 w_42 w_44 w_45 : Z).
Variables (hi_12 hi_31 : bv 20).
Variables (lo_14 lo_32 : bv 12).
Variables (joff_8 joff_23 joff_42 joff_44 joff_45 : bv 21).
Variables (GOT_free_userdata : Z).
Variables (e_pbfree e_194bc e_f_strdup : Z).
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
Hypothesis CODE : code_at segs base (jonewdoubles_code w_8 w_12 w_14 w_23 w_31 w_32 w_42 w_44 w_45).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 224.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Jal 1 joff_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (Auipc 11 hi_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (OpImm ALU_ADD 11 11 lo_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_23 : decode_any (Z_to_bv 32 w_23) = Some (Jal 1 joff_23, 4%Z).
Hypothesis E_23 : is_ecall (Z_to_bv 32 w_23) = false.
Hypothesis D_31 : decode_any (Z_to_bv 32 w_31) = Some (Auipc 10 hi_31, 4%Z).
Hypothesis E_31 : is_ecall (Z_to_bv 32 w_31) = false.
Hypothesis D_32 : decode_any (Z_to_bv 32 w_32) = Some (Load SZ8 true 10 10 lo_32, 4%Z).
Hypothesis E_32 : is_ecall (Z_to_bv 32 w_32) = false.
Hypothesis D_42 : decode_any (Z_to_bv 32 w_42) = Some (Jal 1 joff_42, 4%Z).
Hypothesis E_42 : is_ecall (Z_to_bv 32 w_42) = false.
Hypothesis D_44 : decode_any (Z_to_bv 32 w_44) = Some (Jal 1 joff_44, 4%Z).
Hypothesis E_44 : is_ecall (Z_to_bv 32 w_44) = false.
Hypothesis D_45 : decode_any (Z_to_bv 32 w_45) = Some (Jal 1 joff_45, 4%Z).
Hypothesis E_45 : is_ecall (Z_to_bv 32 w_45) = false.
Hypothesis ANCH_14 : gw_anch (Z.shiftl (bv_signed hi_12) 12 + (base + 48) + bv_signed lo_14)%Z e_fn_dbl_to_json_string.
Hypothesis ANCH_32 : gw_anch (Z.shiftl (bv_signed hi_31) 12 + (base + 124) + bv_signed lo_32)%Z GOT_free_userdata.
Hypothesis LINK_8 : gw_anch (base + 32 + bv_signed joff_8)%Z e_malloc.
Hypothesis LINK_23 : gw_anch (base + 92 + bv_signed joff_23)%Z (e_f_strdup + 0)%Z.
Hypothesis LINK_42 : gw_anch (base + 168 + bv_signed joff_42)%Z (e_pbfree + 0)%Z.
Hypothesis LINK_44 : gw_anch (base + 176 + bv_signed joff_44)%Z e_free.
Hypothesis LINK_45 : gw_anch (base + 180 + bv_signed joff_45)%Z (e_194bc + 0)%Z.

Definition strdup_stmt := ltac:(let t := constr:(ltac:(gw_callee_stmt (@QPIU.Mq5.gw_all) (@QPIU.Mq5.strdup_stmt) e_f_strdup)) in let t := eval cbv beta delta [QPIU.Mq5.strdup_stmt] in t in exact t).

Hypothesis printbuf_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqd.gw_all) (@QPIU.Mqd.printbuf_free_cps) e_pbfree)) in let x := constr:(ltac:(gw_callee_stmt (@QPIU.Mq5.gw_all) (@QPIU.Mq5.strdup_stmt) e_f_strdup)) in let T := gw_subst T x strdup_stmt in exact T).

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
Hypothesis CS_GOT_free_userdata : forall a, (GOT_free_userdata <= a < GOT_free_userdata + 8)%Z -> gCS a.
Hypothesis ANCH_R34 : gw_anch (0 + (base + 132) + 92)%Z e_fn_ud_to_json_string.
Hypothesis CODE_e_194bc : code_at segs e_194bc blk_194bc_code.
Hypothesis AL_e_fn_free_userdata : gw_b4 e_fn_free_userdata.
Hypothesis RNG_e_fn_free_userdata : gw_br e_fn_free_userdata 4.
Hypothesis LAY_POS_e_fn_free_userdata : gw_le 1 e_fn_free_userdata.
Hypothesis LAY_HI_e_fn_free_userdata : gw_le (e_fn_free_userdata + 4) 1099511627776.
Hypothesis AL_e_fn_ud_to_json_string : gw_b4 e_fn_ud_to_json_string.
Hypothesis RNG_e_fn_ud_to_json_string : gw_br e_fn_ud_to_json_string 4.
Hypothesis LAY_POS_e_fn_ud_to_json_string : gw_le 1 e_fn_ud_to_json_string.
Hypothesis LAY_HI_e_fn_ud_to_json_string : gw_le (e_fn_ud_to_json_string + 4) 1099511627776.
#[using="w_8 w_12 w_14 w_23 w_31 w_32 w_42 w_44 w_45 hi_12 hi_31 lo_14 lo_32 joff_8 joff_23 joff_42 joff_44 joff_45 GOT_free_userdata e_pbfree e_194bc e_f_strdup RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_8 E_8 D_12 E_12 D_14 E_14 D_23 E_23 D_31 E_31 D_32 E_32 D_42 E_42 D_44 E_44 D_45 E_45 ANCH_14 ANCH_32 LINK_8 LINK_23 LINK_42 LINK_44 LINK_45 printbuf_free_cps CS_GOT_free_userdata ANCH_R34 CODE_e_194bc AL_e_fn_free_userdata RNG_e_fn_free_userdata LAY_POS_e_fn_free_userdata LAY_HI_e_fn_free_userdata AL_e_fn_ud_to_json_string RNG_e_fn_ud_to_json_string LAY_POS_e_fn_ud_to_json_string LAY_HI_e_fn_ud_to_json_string S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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
Ltac gj_fn_cbn := try (progress cbn [S4F fn_free_userdata fn_ud_to_json_string]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section RC__1.

Section JoNewDoubleS.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis STRDUP : strdup_stmt HIx.

#[using="Type"] Lemma fsaved_restore : forall (F F' : bvmap 5 word) (k1 k2 k3 : bv 5) (v : word),
bv_unsigned k1 = bv_unsigned k2 -> bv_unsigned k1 = bv_unsigned k3 ->
fsaved (bvmap_set k1 v F) F' -> fsaved F (bvmap_set k2 (Sem.reg_get F k3) F').
Proof. clear - HIx STRDUP.
intros F F' k1 k2 k3 v E12 E13 FS j Hj.
replace k2 with k1 by (apply bv_eq; exact E12). replace k3 with k1 by (apply bv_eq; exact E13).
destruct (Z.eq_dec (bv_unsigned k1) (bv_unsigned (Z_to_bv 5 j))) as [E|NE].
- replace (Z_to_bv 5 j) with k1 by (apply bv_eq; exact E). apply QEpW.reg_get_set_same.
- rewrite QEpW.reg_get_set_other by (intros E; apply NE; rewrite E; reflexivity).
rewrite (FS j Hj). apply QEpW.reg_get_set_other. intros E; apply NE; rewrite E; reflexivity.
Qed.

#[using="Type"] Lemma le8_read : forall segs_ m a v, bytes_at segs_ m a (le8 v) -> ov_read_bytes segs_ m (Z_to_bv 64 a) 8 = Some (le8 v).
Proof. clear - HIx STRDUP.
intros segs_ m a v H.
pose proof (bytes_at_read segs_ m a (le8 v) 0 8 H ltac:(lia) ltac:(pose proof (length_le8 v); cbn; lia)) as R.
rewrite Z.add_0_r in R. cbn [skipn Z.to_nat] in R.
replace (firstn 8 (le8 v)) with (le8 v) in R. 2:{ symmetry. apply firstn_all2. rewrite length_le8. lia. }
pose proof (bytes_at_bound _ _ _ _ H) as B. unfold wa in R. exact R.
Qed.

Definition json_object_new_double_s_entry : Z := (base + 0x0).

Definition new_dbls_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (ds lo : Z) (str : list byte)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
bytes_at segs m' ds (str ++ [b0]) /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, jval segs S4F (Sdouble true) m' BS r 1 /\ HEAPx A' (BS ++ LB) m' md') ).

#[using="w_8 w_12 w_14 w_23 w_31 w_32 w_42 w_44 w_45 hi_12 hi_31 lo_14 lo_32 joff_8 joff_23 joff_42 joff_44 joff_45 e_pbfree e_194bc e_f_strdup LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_8 E_8 D_12 E_12 D_14 E_14 D_23 E_23 D_31 E_31 D_32 E_32 D_42 E_42 D_44 E_44 D_45 E_45 ANCH_14 ANCH_32 LINK_8 LINK_23 LINK_42 LINK_44 LINK_45 printbuf_free_cps CS_GOT_free_userdata ANCH_R34 CODE_e_194bc LAY_POS_e_fn_free_userdata LAY_HI_e_fn_free_userdata LAY_POS_e_fn_ud_to_json_string LAY_HI_e_fn_ud_to_json_string STRDUP"] Lemma json_object_new_double_s_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (ds lo b n : Z) (str bytes : list byte) (errv : word),
HEAPx A LB m md ->
In (b, n) LB -> str_in_block S4L m b n bytes ds str ->
Z.of_nat (length str) + 1 <= 2^31 ->
bytes_at segs m GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 32 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 ds ->
(forall ms' md', new_dbls_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB ds lo str ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_double_s_entry) fc None m (seg_rom segs)) md) T.
Proof. clear - w_8 w_12 w_14 w_23 w_31 w_32 w_42 w_44 w_45 hi_12 hi_31 lo_14 lo_32 joff_8 joff_23 joff_42 joff_44 joff_45 e_pbfree e_194bc e_f_strdup LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_8 E_8 D_12 E_12 D_14 E_14 D_23 E_23 D_31 E_31 D_32 E_32 D_42 E_42 D_44 E_44 D_45 E_45 ANCH_14 ANCH_32 LINK_8 LINK_23 LINK_42 LINK_44 LINK_45 printbuf_free_cps CS_GOT_free_userdata ANCH_R34 CODE_e_194bc LAY_POS_e_fn_free_userdata LAY_HI_e_fn_free_userdata LAY_POS_e_fn_ud_to_json_string LAY_HI_e_fn_ud_to_json_string STRDUP segs GOT_free_userdata gTP S4F HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_free_userdata as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_free_userdata as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_ud_to_json_string as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_ud_to_json_string as gL5_; unfold gw_le in gL5_.
intros until errv. intros HP Hin SIB LEN32 GOT ST LO LOS SPA HT ERR TP RA A0 K.
destruct SIB as (BLKB & Hbds & Hdse & Hfst & NONUL). cbn [hl_segs S4L] in BLKB.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
pose proof (heap_blk S4L HIx _ _ _ _ b n HP Hin) as (Hn0 & Hbal & Hb0 & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ b n HP Hin) as Hbimg. cbn [hl_img_lo hl_img_hi S4L] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
assert (LENB : length bytes = Z.to_nat n) by (destruct BLKB as [[[Hwf _] _] _]; exact Hwf).
subst a0 tp.
assert (SRC1 : bytes_at segs m ds (str ++ [b0])).
{ pose proof (bytes_at_sub S4L m b bytes (Z.to_nat (ds - b)) (length str + 1) (rw_cells_bytes_at S4L _ _ _ _ BLKB) ltac:(lia)) as X.
rewrite Hfst in X. replace (b + Z.of_nat (Z.to_nat (ds - b))) with ds in X by lia. exact X. }
assert (CR : client_range S4L LB (bv_unsigned sp) ds (Z.of_nat (length str) + 1)).
{ eapply client_range_block; [exact Hin | lia | lia]. }
assert (SRCm : forall mx, heap_pres S4L LB (bv_unsigned sp) m mx -> bytes_at segs mx ds (str ++ [b0])).
{ intros mx HPRx. eapply (heap_pres_bytes_at S4L); [exact HPRx | exact SRC1 |]. rewrite length_app. cbn [length].
replace (Z.of_nat (length str + 1)) with (Z.of_nat (length str) + 1) by lia. exact CR. }
assert (GOTm : forall mx, heap_pres S4L LB (bv_unsigned sp) m mx -> bytes_at segs mx GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F)))).
{ intros mx HPRx. eapply (heap_pres_bytes_at S4L); [exact HPRx | exact GOT |]. right; left. intros a Ha.
rewrite length_le8 in Ha. cbn. gw_cs. }
clear SRC1.
assert (GOTk : True -> bytes_at segs m GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F)))) by (intros _; exact GOT). clear GOT.
apply rz_evt; [exact MOK|]. unfold json_object_new_double_s_entry.
carve_frame 32%nat ST.
do 9 step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_truex. do 9 step.
apply evt_RZ_done. apply K. unfold new_dbls_post.
exists m2, A2, 0, e2.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [|left; auto]]]]]].
+ apply ret_statew_intro; [apply fsaved_set_self'; reflexivity | intros Hf; exact Hf].
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ exact (SRCm _ HPR).
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
assert (Hrb : r <> b) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ n HP2 Hin)).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ r 48 b n HP2 ltac:(left; reflexivity) ltac:(right; exact Hin) Hrb) as Hdisjrb.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in BLKB; [| eapply client_range_block; [exact Hin | lia | cbn [cells_size csize]; lia]]. cbn [hl_segs S4L] in BLKB.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_falsex.
step. do 5 step. stepz. stepz. stepz. stepz. stepz. stepz. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
assert (HP3 : HEAPx A2 ((r, 48) :: LB) mcur md2) by
(eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU); solve_frameW_with HP2)
end.
destruct (str_slack S4L HIx _ _ _ _ b n bytes ds str HP3 ltac:(right; exact Hin) (conj BLKB (conj Hbds (conj Hdse (conj Hfst NONUL))))) as [slack [SRC3 [PAD3 SLK3]]]. cbn [hl_segs S4L] in SRC3.
pose proof (bytes_at_bound _ _ _ _ SRC3) as Hbb3. rewrite length_app in Hbb3. cbn [length] in Hbb3.
apply evt_RZ_done. eapply STRDUP; [exact HP3 | rewrite unsigned_lit by lia; exact SRC3 | exact NONUL | rewrite unsigned_lit by lia; exact PAD3
| rewrite !unsigned_lit by lia; eapply client_range_block; [right; exact Hin | lia | lia]
| rewrite !unsigned_lit by lia; left; unfold_consts; lia | lia | .. ]; try alloc_side.
intros ms4 md4 POST4. destruct POST4 as (m4 & A4 & r2 & e4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & STR4 & OUT4). open_ret RS4. cbn [hl_segs S4L] in *.
rewrite (unsigned_lit ds) in STR4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR4 by lia.

assert (HPRa : heap_pres S4L LB (bv_unsigned sp) m m4).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb; right; exact Hbb | clia |]. solve_clientW S4L HIx HP2.
- eapply heap_pres_weaken; [exact HPR4 | lia | intros bb Hbb; right; exact Hbb]. }
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
clear MU WM MI ST2 SRC3 PAD3 SLK3 Hbb3 BLKB HP3.
destruct OUT4 as [(-> & HP4) | (Hr2 & SBLK & HP4)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m4) as MU. pose proof (wmono_refl segs m4) as WM.
reenter MOK4.
step. if_truex. step. step.

apply evt_RZ_done.
eapply (printbuf_free_cps HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 md4 T A4 ((r, 48) :: LB) [] 0 lo e4);
[ cbn [app]; eapply (heap_frame S4L HIx); [exact HP4 | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP4 MU); solve_frameW_with HP4
| left; split; reflexivity | .. ]; try alloc_side.
intros ms5 md5 (m5 & A5 & r5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & HP5).
destruct RS5 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F5 & fc5 & -> & FS5 & FRM5).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR5 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (HPRb : heap_pres S4L LB (bv_unsigned sp) m m5).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_weaken; [exact HPR5 | lia | intros bb Hbb; right; exact Hbb]. }
clear MU WM MI.
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m5) as MU. pose proof (wmono_refl segs m5) as WM.
apply rz_evt; [exact MOK5|].
try g_ret_pc_any.
step. step.

alloc_call (hi_free S4L HIx) S4L HIx HP5 MU WM MI.
{ right. exists 48. left. reflexivity. }
intros ms6 m6 md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6. open_ret RS6. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR6, HP6.
extend_pres S4L HIx HPRb MU WM HP5 HPR6.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI.
pose proof (heap_model_ok _ _ _ _ _ _ HP6) as MOK6.
pose proof (heap_mem_inv _ _ _ _ _ _ HP6) as MI. cbn [hl_segs S4L] in MI.
change (gTP - 164) with (gTP + -164) in ERR6.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); ((gTP + -164), (gTP + -160))] m6) as MU. pose proof (wmono_refl segs m6) as WM.
reenter MOK6.
do 4 step. step. step. stepz. step.
do 6 step.
apply evt_RZ_done. apply K. unfold new_dbls_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A6, 0 end. eexists.
split; [| split; [| split; [| split; [ | split; [eassumption | split; [| left; split; [reflexivity|]]]]]]].
* apply ret_statew_intro; [| intros Hf; apply FRM5; exact Hf].
eapply fsaved_restore; [reflexivity | reflexivity | exact FS5].
* eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM4|]. eapply model_vm_only_trans; [exact VM5| exact VM6].
* release_frame FR ST6 (bv_unsigned sp). exact ST6.
* eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP6 | intros bb Hbb; exact Hbb | clia |]. solve_clientW S4L HIx HP6.
* apply SRCm. eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP6 | intros bb Hbb; exact Hbb | clia |]. solve_clientW S4L HIx HP6.
* eapply (heap_frame S4L HIx); [exact HP6 | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP6 MU). solve_frameW_with HP6.
+
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r2 _ HP4 ltac:(left; reflexivity)) as (_ & Hr2al & Hr2lo & Hr2hi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r2 _ HP4 ltac:(left; reflexivity)) as Himg_r2. cbn [hl_img_lo hl_img_hi S4L] in Himg_r2.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hr2hi.
assert (Hr2r : r2 <> r) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ 48 HP4 ltac:(left; reflexivity))).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ r2 _ r 48 HP4 ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hr2r) as Hdisj2.
pose proof (GOTm _ HPRa) as GOT4. cbn [fn_free_userdata S4F] in GOT4.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48)] m4) as MU. pose proof (wmono_refl segs m4) as WM.
reenter MOK4.
step. if_falsex. step. step. step. if_true.
step. pose proof (le8_read segs _ _ _ GOT4) as RD1. step. clear RD1. step. step. stepz. stepz. stepz. step. step.
do 6 step.
apply evt_RZ_done. apply K. unfold new_dbls_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A4, r, e4 end.
split; [| split; [| split; [| split; [ | split; [exact ERR4 | split; [| right]]]]]].
* apply ret_statew_intro; [apply fsaved_set_self'; reflexivity | intros Hf; exact Hf].
* eapply model_vm_only_trans; [exact VM2| exact VM4].
* release_frame FR ST4 (bv_unsigned sp). exact ST4.
* eapply heap_pres_trans; [exact HPRa|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP4 | intros bb Hbb; right; right; exact Hbb | clia |]. solve_clientW S4L HIx HP4.
* first [exact STR4 | eapply (bytes_at_transport segs); [exact STR4 | exact MU |]; cbn; rewrite length_app; cbn [length]; unfold_consts; lia].
* split; [exact Hr|]. exists [(r, 48); (r2, Z.of_nat (length str) + 1)]. split.
-- jhdr_split BLK.
cbn [jval]. exists 0, [], [(r, 48); (r2, Z.of_nat (length str) + 1)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Sem.reg_get F (Z_to_bv 5 10)), r2, (Z.of_nat (length str) + 1), str. split; [reflexivity|]. split; [lia|]. split.
++ unfold jhdr_cells. cbn [fn_ud_to_json_string fn_free_userdata S4F app]. exact BLK.
++ unfold cstr. split; [lia|]. split.
** apply Forall_forall. intros x Hx E0. apply NONUL. apply bv8_zero_iff in E0. subst x. exact Hx.
** exists []. rewrite app_nil_r. unfold b0 in SBLK. exact SBLK.
-- eapply (heap_frame S4L HIx); [ eapply heap_perm; [exact HP4 | apply perm_swap] | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ (heap_perm _ _ _ _ _ _ _ HP4 (perm_swap _ _ _)) MU). solve_frameW_with HP4.
Qed.
End JoNewDoubleS.

End RC__1.

End G.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import QPIU.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.

Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Section G.
Variables (segs : list Segment).
Variables (e_blk_16e24 e_blk_16f30 e_blk_17684 e_blk_17710 e_blk_17718 : Z).

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
Variables (GGOT4 GHASH4 GVDSO4 JG_CGT_P gRDATA_LO : Z).
Hypothesis CS_GHASH4 : forall a, (GHASH4 <= a < GHASH4 + 12)%Z -> gCS a.
Hypothesis CS_GGOT4 : forall a, (GGOT4 <= a < GGOT4 + 8)%Z -> gCS a.
Hypothesis CS_GVDSO4 : forall a, (GVDSO4 <= a < GVDSO4 + 8)%Z -> gCS a.
Hypothesis LAY_RDATA_GGOT4 : gw_le gRDATA_LO GGOT4.
Hypothesis LAY_GGOT4_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASH4x12_GVDSO4 : gw_le (GHASH4 + 12) GVDSO4.
Hypothesis LAY_IMG_GGOT4 : gw_le gIMG_LO GGOT4.
Hypothesis LAY_GVDSO4_IMG : gw_le (GVDSO4 + 8) gIMG_HI.
#[using="e_blk_16e24 e_blk_16f30 e_blk_17684 e_blk_17710 e_blk_17718 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free GGOT4 GHASH4 GVDSO4 JG_CGT_P gRDATA_LO CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG S4F"] Lemma gw_all : True. Proof. exact I. Qed.
Definition jc_glob_P := ltac:(gw_ctx2 (@QPIU.Mq6.jc_glob_P)).

Section RC__1.

Fixpoint okmax (l : list (option jshape)) : Z :=
match l with [] => 0 | None :: l' => okmax l' | Some s :: l' => Z.max (sdepth s) (okmax l') end.
Definition odep (o : option jshape) : Z := match o with None => 0 | Some s => sdepth s end.
#[using="Type"] Lemma kmax_nonneg : forall l, 0 <= (fix kmax (l0 : list (option jshape)) : Z := match l0 with [] => 0 | None :: l' => kmax l' | Some s' :: l' => Z.max (sdepth s') (kmax l') end) l.
Proof. clear - segs. induction l as [|[x|] l IHl]; cbn; lia. Qed.
#[using="Type"] Lemma sdepth_nonneg : forall s, 0 <= sdepth s.
Proof. clear - segs. intros [| | | |kids|kids]; cbn -[Z.add Z.max]; try lia; pose proof (kmax_nonneg kids); lia. Qed.

#[using="Type"] Lemma odep_nonneg : forall o, 0 <= odep o.
Proof. clear - segs. intros [s|]; cbn; [apply sdepth_nonneg | lia]. Qed.

Section JoStmts.
Variable L : heap_layout.
Variable HIx : heap_iface L.
Variable fn : fnaddrs.
Variable G : (word -> option byte) -> Prop.
Notation segs_ := (hl_segs L).

Definition jo_pre (A : AS L HIx) (LBall : list blk) (m : word -> option byte) (md : Model)
(sp tp ra : word) (lo stkb : Z) (errv : word) : Prop :=
HEAP L HIx A LBall m md /\
stk segs_ m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - stkb /\
bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= hi_top L HIx /\
rw_cells segs_ m (hl_tp L - 164) [C4 errv] /\
tp = Z_to_bv 64 (hl_tp L) /\ bv_unsigned ra mod 2 = 0.

Definition jo_post_frame (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : Model) : Prop :=
ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs_ m' lo (bv_unsigned sp) /\
heap_pres L LB (bv_unsigned sp) m m' /\
(exists errv', rw_cells segs_ m' (hl_tp L - 164) [C4 errv']).

Definition jo_post_framex (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : Model) : Prop :=
ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs_ m' lo (bv_unsigned sp) /\
heap_presx L (hl_volatile L) LB (bv_unsigned sp) m m' /\
(exists errv', rw_cells segs_ m' (hl_tp L - 164) [C4 errv']).

Definition jo_new_container_stmt (entry stkb : Z) (s : jshape) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB : list blk) (lo : Z) (errv : word),
jo_pre A LB m md sp tp ra lo stkb errv -> G m ->
(forall ms' md' m' r, jo_post_frame ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
((r = 0 /\ exists A', HEAP L HIx A' LB m' md') \/
(r <> 0 /\ exists A' BS, jval segs_ fn s m' BS r 1 /\ HEAP L HIx A' (BS ++ LB) m' md')) ->
realizes segs_ (mkCfg ms' md') T) ->
realizes segs_ (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs_)) md) T.

Definition jo_array_add_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB ABS VBS : list blk) (lo p v : Z) (kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_pre A (ABS ++ VBS ++ LB) m md sp tp ra lo stkb errv ->
jval segs_ fn (Sarr kids) m ABS p 1 -> jopt segs_ fn vs m VBS v ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 v ->
(forall ms' md' m' r, jo_post_frame ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
((r = 0 /\ exists A' ABS', jval segs_ fn (Sarr (kids ++ [vs])) m' ABS' p 1 /\ HEAP L HIx A' (ABS' ++ LB) m' md') \/
(r = 2^64 - 1 /\ exists A', jval segs_ fn (Sarr kids) m' ABS p 1 /\ jopt segs_ fn vs m' VBS v /\ HEAP L HIx A' (ABS ++ VBS ++ LB) m' md')) ->
realizes segs_ (mkCfg ms' md') T) ->
realizes segs_ (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs_)) md) T.

Definition jo_array_shrink_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB ABS : list blk) (lo p : Z) (kids : list (option jshape)) (errv : word),
jo_pre A (ABS ++ LB) m md sp tp ra lo stkb errv ->
jval segs_ fn (Sarr kids) m ABS p 1 -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 0 ->
(forall ms' md' m' r, jo_post_frame ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
(exists A' ABS', jval segs_ fn (Sarr kids) m' ABS' p 1 /\ HEAP L HIx A' (ABS' ++ LB) m' md') ->
realizes segs_ (mkCfg ms' md') T) ->
realizes segs_ (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs_)) md) T.

Definition jo_object_add_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB OBS VBS : list blk) (lo p v k kn : Z) (ks : list byte) (kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_pre A (OBS ++ VBS ++ LB) m md sp tp ra lo stkb errv -> G m ->
jval segs_ fn (Sobj kids) m OBS p 1 -> jopt segs_ fn vs m VBS v ->
In (k, kn) LB -> cstr segs_ m k kn ks -> kn <= 2^31 ->
frm0 fc ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v ->
(forall ms' md' m' r, jo_post_framex ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' -> G m' ->
((r = 0 /\ exists A' OBS' kids', jval segs_ fn (Sobj kids') m' OBS' p 1 /\ HEAP L HIx A' (OBS' ++ LB) m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)) \/
(r = 2^64 - 1 /\ exists A' REM, jval segs_ fn (Sobj kids) m' OBS p 1 /\ jopt segs_ fn vs m' VBS v /\ HEAP L HIx A' (OBS ++ VBS ++ REM ++ LB) m' md')) ->
realizes segs_ (mkCfg ms' md') T) ->
realizes segs_ (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs_)) md) T.

End JoStmts.

Definition jo_new_object_P (HIx : heap_iface S4L) := jo_new_container_stmt S4L HIx S4F jc_glob_P (e_blk_16e24 + 0x0) (48 + 48 + 8256) (Sobj []).
Definition jo_new_array_P (HIx : heap_iface S4L) := jo_new_container_stmt S4L HIx S4F (fun _ => True) (e_blk_17684 + 0x0) (32 + 32 + 8256) (Sarr []).
Definition jo_array_add_P (HIx : heap_iface S4L) := jo_array_add_stmt S4L HIx S4F (e_blk_17710 + 0x0) (64 + 8256).
Definition jo_array_shrink_P (HIx : heap_iface S4L) := jo_array_shrink_stmt S4L HIx S4F (e_blk_17718 + 0x0) (64 + 8256).
Definition jo_object_add_P (HIx : heap_iface S4L) := jo_object_add_stmt S4L HIx S4F jc_glob_P (e_blk_16f30 + 0x0) (96 + 64 + 64 + 8256 + 2048).

End RC__1.

End G.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj QVbl QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QCcH Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QgoP.
Import QVbl.Mq5.
Import QSL3.
Import QPIU.Mqb.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q0Hd.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition lhlookup_code : list Z :=
[0x00052683; 0x0ad05063; 0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x01613023; 0x00050413; 0x00058493; 0x00000913; 0x02d679b3; 0x02800a13; 0xffe00a93; 0xfff00b13; 0x0240006f; 0x00198513; 0x0019899b; 0x0136c5b3; 0x0015b593; 0xfff58593; 0x0019091b; 0x00a5f9b3; 0x02d95a63; 0x01843503; 0x034985b3; 0x00b50533; 0x00053503; 0xfd5508e3; 0x01650e63; 0x03043603; 0x00048593; 0x000600e7; 0x00051e63; 0x00042683; 0xfb5ff06f; 0x00000513; 0x01c0006f; 0x00000513; 0x00008067; 0x01843503; 0x02800593; 0x02b985b3; 0x00b50533; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x00013b03; 0x04010113; 0x00008067]%Z.

Definition next_ix (size n : Z) : Z := if n + 1 =? size then 0 else n + 1.

Lemma land_ones64_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma remu_lit : forall a b, 0 <= a < 2^64 -> 0 < b < 2^64 ->
mul_div M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
destruct (Z.eqb_spec b 0); [lia|]. apply bv_eq. rewrite bv_modu_unsigned, !unsigned_lit; try lia.
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
#[using="gH2 gH3 LAY_gIMG_LO"] Lemma gLAYF : ((0 <= gIMG_LO /\ gIMG_HI <= alloc_ceiling) /\ (gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - gH2 gH3 LAY_gIMG_LO gTP gIMG_LO gIMG_HI. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.
#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma gLAYF0 : ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gTP gIMG_LO gIMG_HI. pose proof LAY_TPLO as X1; pose proof LAY_TPHI as X2; unfold gw_le in X1, X2. split; [split; [exact X1 | exact X2] | exact LAY_gIMG_LO]. Qed.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Variables (e_blk_18a54 e_strcmp : Z).
Hypothesis CODE : code_at segs base lhlookup_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 228.

Definition lh_char_equal_post := ltac:(let t := constr:(ltac:(gw_callee_stmt (@QPIU.Mqb.gw_all) (@QPIU.Mqb.lh_char_equal_post) e_fn_lh_char_equal)) in let t := eval cbv beta delta [QPIU.Mqb.lh_char_equal_post] in t in exact t).

Hypothesis lh_char_equal_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqb.gw_all) (@QPIU.Mqb.lh_char_equal_spec) e_fn_lh_char_equal)) in let x := constr:(ltac:(gw_callee_stmt (@QPIU.Mqb.gw_all) (@QPIU.Mqb.lh_char_equal_post) e_fn_lh_char_equal)) in let T := gw_subst T x lh_char_equal_post in exact T).

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
#[using="RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free e_blk_18a54 e_strcmp CODE BASE4 BASER lh_char_equal_spec AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal S4F"] Lemma gw_all : True. Proof. exact I. Qed.
Ltac gj_fn_cbn := try (progress cbn [S4F fn_lh_char_equal]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Definition lh_lookup_entry := (base + 0x0).

Section LhLookup.
Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size kp lo : Z) (es : list lent) (svs : list slotv) (ps : list byte).

Definition lookup_res (r : Z) : Prop :=
r = 0 \/ exists j e, nth_error es j = Some e /\ r = ent_addr tbl (le_ix e) /\ le_ks e = ps.

Definition lh_lookup_post (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (r : Z) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ lh_open segs S4F m' t tbl size es svs
/\ bytes_at segs m' kp (ps ++ [b0])
/\ lookup_res r.

Definition lk_frame (m : word -> option byte) : Prop :=
rw_cells segs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_char_equal CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma lh_lookup_next :
forall (n cnt : Z) (x1 t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte),
0 <= cnt < size -> 0 <= n < size -> In size lf_sizes -> mem_inv segs m ->
evt segs (fun ms' =>
(cnt + 1 < size /\
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp)
(Z_to_bv 64 (n + 1)) (Z_to_bv 64 (if n + 1 =? size then 0 else -1)) a2 (Z_to_bv 64 size) a4 a5 a6 a7
(Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (next_ix size n)) (Z_to_bv 64 40) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x6c)) fc None m (seg_rom segs))
\/ (cnt + 1 = size /\
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp)
(Z_to_bv 64 (n + 1)) (Z_to_bv 64 (if n + 1 =? size then 0 else -1)) a2 (Z_to_bv 64 size) a4 a5 a6 a7
(Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (next_ix size n)) (Z_to_bv 64 40) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x9c)) fc None m (seg_rom segs)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 a1 a2 (Z_to_bv 64 size) a4 a5 a6 a7
(Z_to_bv 64 cnt) (Z_to_bv 64 n) (Z_to_bv 64 40) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x4c)) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_char_equal CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs base ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
intros until m. intros Hcnt Hn Hsz MI.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
step. step. norm_w32. step. rewrite (unsigned_lit size), (unsigned_lit (n + 1)) by lia.
unfold next_ix. destruct (Z.eqb_spec (n + 1) size) as [EQ|NE].
- rewrite EQ, Z.lxor_nilpotent. step. rewrite (v_sltiu_1 (Z_to_bv 64 0) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. norm_w32. step. rewrite (unsigned_lit size) by lia. rewrite Z.land_0_l.
step.
destruct (Z.lt_ge_cases (cnt + 1) size).
+ if_falsex. apply evt_done. left. split; [lia | reflexivity].
+ if_truex. apply evt_done. right. split; [lia | reflexivity].
- pose proof (lxor_bound size (n + 1) 31 ltac:(lia) ltac:(lia) ltac:(lia)) as LB.
assert (LNZ : Z.lxor size (n + 1) <> 0) by (intros X; apply Z.lxor_eq in X; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (Z.lxor size (n + 1))) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. norm_w32. step. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615.
rewrite (unsigned_lit (n + 1)) by lia. rewrite land_ones64_l by lia.
replace (0 + -1) with (-1) by lia. change (-1) with (-1).
step.
destruct (Z.lt_ge_cases (cnt + 1) size).
+ if_falsex. apply evt_done. left. split; [lia | reflexivity].
+ if_truex. apply evt_done. right. split; [lia | reflexivity].
Qed.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma lh_lookup_exit0 :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 : word) (m0 m : word -> option byte),
mem_inv segs m -> lh_open segs S4F m t tbl size es svs -> bytes_at segs m kp (ps ++ [b0]) ->
stk segs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 -> lk_frame m ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m0 m -> wmono segs m0 m ->
evt segs (lh_lookup_post m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x9c)) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs base S4F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
intros until m. intros MI OPEN PS ST LOS FR MU WM. unfold lk_frame in FR. word_range sp SPR.
step. step. do 9 step. release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold lh_lookup_post. do 14 eexists. exists 0. eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact OPEN|]. split; [exact PS|].
left. reflexivity.
Qed.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma lh_lookup_exit1 :
forall (n : Z) (e : lent) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 x22 t3 t4 t5 t6 : word) (m0 m : word -> option byte),
0 <= n < size -> In size lf_sizes -> In e es -> le_ix e = Z.to_nat n -> le_ks e = ps ->
mem_inv segs m -> lh_open segs S4F m t tbl size es svs -> lh_below lo t tbl size es -> bytes_at segs m kp (ps ++ [b0]) ->
stk segs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 -> lk_frame m ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m0 m -> wmono segs m0 m ->
evt segs (lh_lookup_post m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 a1 a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 n) x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xac)) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs base S4F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
intros until m. intros Hn Hsz He Hix Hks MI OPEN BELOW PS ST LOS FR MU WM. unfold lk_frame in FR. word_range sp SPR.
pose proof OPEN as (HDR & _). unfold lh_hdr, lh_hdrf in HDR. pose proof BELOW as (Ht0 & Ht & Hb0 & Hb & _).
pose proof (lf_size_range size Hsz) as HSR.
step. step. step. rewrite (unsigned_lit n) by lia. step.
do 9 step. release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold lh_lookup_post. do 14 eexists. exists (tbl + n * 40). eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact OPEN|]. split; [exact PS|].
right. destruct (In_nth_error _ _ He) as [j Hj]. exists j, e. split; [exact Hj|]. split; [unfold ent_addr; rewrite Hix; lia | exact Hks].
Qed.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER lh_char_equal_spec AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma lh_lookup_loop :
forall (k : nat) (n cnt : Z) (x1 t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m0 m : word -> option byte),
Z.of_nat k = size - cnt -> 0 <= cnt < size -> 0 <= n < size ->
mem_inv segs m ->
lh_open segs S4F m t tbl size es svs -> lh_below lo t tbl size es ->
bytes_at segs m kp (ps ++ [b0]) -> ~ In b0 ps -> (kp + Z.of_nat (length ps) + 1 <= lo \/ bv_unsigned sp <= kp) ->
stk segs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 ->
lk_frame m ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m0 m -> wmono segs m0 m ->
evt segs (lh_lookup_post m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 a1 a2 (Z_to_bv 64 size) a4 a5 a6 a7
(Z_to_bv 64 cnt) (Z_to_bv 64 n) (Z_to_bv 64 40) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x6c)) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER lh_char_equal_spec AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs base S4F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
induction k as [|k IH]; intros until m; intros Hk Hcnt Hn MI OPEN BELOW PS NP SEPk ST LOS FR MU WM; [lia|].
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hc & Hlen). pose proof BELOW as (Ht0 & Ht & Hb0 & Hb & Hkb).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. pose proof FR as FR0. unfold lk_frame in FR. word_range sp SPR.
pose proof (bytes_at_bound _ _ _ _ PS) as PSB. rewrite length_app in PSB. cbn [length] in PSB.
destruct (nth_error svs (Z.to_nat n)) as [sv|] eqn:Esv.
2:{ exfalso. apply nth_error_None in Esv. lia. }
pose proof (SL (Z.to_nat n) sv Esv) as C. unfold ent_addr, slot_cells in C. rewrite Z2Nat.id in C by lia.
pose proof (rw_cells_bound segs m _ _ C) as CB0. cbn [cells_size csize Nat.add] in CB0.
step. step. rewrite (unsigned_lit n) by lia. step.
replace (tbl + n * 40) with (tbl + 40 * n) by lia.
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

cbn [fn_lh_char_equal S4F]. gw_ret_pc_var_tac.
pose proof (Hkb e He) as Hke.
pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp + -64)] m) as MUk. pose proof (wmono_refl segs m) as WMk.
eapply evt_cut.
{ eapply lh_char_equal_spec with (ls := le_ks e) (rs := ps) (lo := lo);
rewrite ?(unsigned_lit (le_k e)), ?(unsigned_lit kp), ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
first [exact KB | exact PS | exact KNZ | exact NP | exact ST | exact MI | lia]. }
unfold lh_char_equal_post. cbv beta.
rewrite ?(unsigned_lit (le_k e)), ?(unsigned_lit kp), ?(unsigned_lit (bv_unsigned sp + -64)) by lia.
post_call segs m.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (OPEN' : lh_open segs S4F mx t tbl size es svs)
by (eapply (lh_open_frame segs S4F _ m mx); [exact OPEN | exact BELOW | exact MUk | exact WMk | apply Forall_cons; [cbn; lia | apply Forall_nil]]);
rename mx into m2 end.
match goal with H : stk segs m2 lo _ |- _ => rename H into ST2 end.
match goal with H : bytes_at segs m2 kp _ |- _ => rename H into PS2 end.
clear MUk WMk OPEN. try clear C. try clear PS. try clear ST.
destruct (Z.eqb_spec (strcmp_model (le_ks e) ps) 0) as [EQ0|NE0].
+
step. if_true.
eapply (lh_lookup_exit1 n e); first [exact OPEN' | exact BELOW | exact PS2 | exact ST2 | exact MU | exact WM | exact He | exact Hix | exact Hsz | eassumption | idtac].
apply (proj1 (strcmp_model_zero _ _ KNZ NP)). exact EQ0.
+
step. if_false. step. norm_sx32. step.
match goal with H : mem_inv segs m2 |- _ => rename H into MI end.
eapply evt_cut; [eapply (lh_lookup_next n cnt); [lia | lia | exact Hsz | exact MI] |].
cbv beta. intros ms' [[Hlt' ->] | [Heq ->]].
* eapply (IH (next_ix size n) (cnt + 1));
first [exact OPEN' | exact BELOW | exact PS2 | exact NP | exact SEPk | exact ST2 | exact FR | exact MU | exact WM | exact MI | idtac];
unfold next_ix; try (destruct (Z.eqb_spec (n + 1) size)); lia.
* eapply lh_lookup_exit0; first [exact OPEN' | exact PS2 | exact ST2 | exact FR | exact MU | exact WM | exact MI | lia].
-
destruct (LK2 (Z.to_nat n) sv Esv DEAD) as [EK | FK]; rewrite EK || rewrite FK; unfold LH_EMPTYv, LH_FREEDv.
+ step. if_false. step. if_true.
eapply lh_lookup_exit0; first [exact OPEN | exact PS | exact ST | exact FR0 | exact MU | exact WM | exact MI | lia].
+ step. if_true.
eapply evt_cut; [eapply (lh_lookup_next n cnt); [lia | lia | exact Hsz | exact MI] |].
cbv beta. intros ms' [[Hlt' ->] | [Heq ->]].
* eapply (IH (next_ix size n) (cnt + 1));
first [exact OPEN | exact BELOW | exact PS | exact NP | exact SEPk | exact ST | exact FR0 | exact MU | exact WM | exact MI | idtac];
unfold next_ix; try (destruct (Z.eqb_spec (n + 1) size)); lia.
* eapply lh_lookup_exit0; first [exact OPEN | exact PS | exact ST | exact FR0 | exact MU | exact WM | exact MI | lia].
Qed.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER lh_char_equal_spec AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma lh_lookup_spec :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (h : Z),
mem_inv segs m ->
lh_open segs S4F m t tbl size es svs -> lh_below lo t tbl size es ->
bytes_at segs m kp (ps ++ [b0]) -> ~ In b0 ps -> (kp + Z.of_nat (length ps) + 1 <= lo \/ bv_unsigned sp <= kp) ->
stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 kp -> a2 = Z_to_bv 64 h -> 0 <= h < 2^64 ->
evt segs (lh_lookup_post m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_lookup_entry) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER lh_char_equal_spec AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs S4F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
intros until h. intros MI OPEN BELOW PS NP SEPk ST LOS A0 A1 A2 Hh.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hc & Hlen). pose proof BELOW as (Ht0 & Ht & Hb0 & Hb & Hkb).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl segs m) as WM.
unfold lh_lookup_entry. subst a0 a1 a2.
step. norm_sx32. step. if_falsex.
carve_frame 64%nat ST.
do 9 step.
step. step. step. step. rewrite remu_lit by lia. step. step. step. step.
pose proof (Z.mod_pos_bound h size ltac:(lia)) as HM.
eapply (lh_lookup_loop (Z.to_nat size) (h mod size) 0);
first [exact BELOW | exact PS | exact NP | exact SEPk | exact ST | exact MU | exact WM | exact MI | exact FR | lia | idtac].
eapply (lh_open_frame segs S4F _ m); [exact OPEN | exact BELOW | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]].
Qed.
End LhLookup.

End G.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn Q8tj.
Import QSL3.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.

Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition lhnew_code (w_7 w_8 w_12 w_19 w_24 w_25 w_38 : Z) : list Z :=
[0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x00058493; w_7; w_8; 0x00050413; 0x00100513; 0x03800593; w_12; 0x06050663; 0x00852023; 0x00052223; 0x02800593; 0x00050993; 0x00040513; w_19; 0x00050593; 0x00098513; 0x00b9bc23; 0x02058e63; w_24; w_25; 0x02953023; 0x03253423; 0x02c53823; 0x02805663; 0x02800613; 0x02c40633; 0x00c58633; 0xfff00693; 0x00d5b023; 0x02858593; 0xfec59ce3; 0x00c0006f; w_38; 0x00000513; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x03010113; 0x00008067]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_7 w_8 w_12 w_19 w_24 w_25 w_38 : Z).
Variables (hi_7 hi_24 : bv 20).
Variables (lo_8 lo_25 : bv 12).
Variables (joff_12 joff_19 joff_38 : bv 21).
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
Variable vdso_ok4 : Z -> Prop.
Variables (JG_CGT_P gRDATA_LO : Z).
Hypothesis CODE : code_at segs base (lhnew_code w_7 w_8 w_12 w_19 w_24 w_25 w_38).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 188.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 11 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Load SZ8 true 18 11 lo_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (Jal 1 joff_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (Jal 1 joff_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_24 : decode_any (Z_to_bv 32 w_24) = Some (Auipc 12 hi_24, 4%Z).
Hypothesis E_24 : is_ecall (Z_to_bv 32 w_24) = false.
Hypothesis D_25 : decode_any (Z_to_bv 32 w_25) = Some (Load SZ8 true 12 12 lo_25, 4%Z).
Hypothesis E_25 : is_ecall (Z_to_bv 32 w_25) = false.
Hypothesis D_38 : decode_any (Z_to_bv 32 w_38) = Some (Jal 1 joff_38, 4%Z).
Hypothesis E_38 : is_ecall (Z_to_bv 32 w_38) = false.
Hypothesis ANCH_8 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_8)%Z GHASH4.
Hypothesis ANCH_25 : gw_anch (Z.shiftl (bv_signed hi_24) 12 + (base + 96) + bv_signed lo_25)%Z GGOT4.
Hypothesis LINK_12 : gw_anch (base + 48 + bv_signed joff_12)%Z e_calloc.
Hypothesis LINK_19 : gw_anch (base + 76 + bv_signed joff_19)%Z e_calloc.
Hypothesis LINK_38 : gw_anch (base + 152 + bv_signed joff_38)%Z e_free.
Hypothesis RNG_GGOT4 : gw_br GGOT4 8.
Hypothesis AL_GGOT4 : gw_al GGOT4 8.
Hypothesis RNG_GHASH4 : gw_br GHASH4 8.
Hypothesis AL_GHASH4 : gw_al GHASH4 8.
Hypothesis RNG_GVDSO4 : gw_br GVDSO4 8.
Hypothesis AL_GVDSO4 : gw_al GVDSO4 8.
Hypothesis LAY_GGOT4_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASH4_GVDSO4 : gw_le (GHASH4 + 8) GVDSO4.

Hypothesis CS_GHASH4 : forall a, (GHASH4 <= a < GHASH4 + 12)%Z -> gCS a.
Hypothesis CS_GGOT4 : forall a, (GGOT4 <= a < GGOT4 + 8)%Z -> gCS a.
Hypothesis CS_GVDSO4 : forall a, (GVDSO4 <= a < GVDSO4 + 8)%Z -> gCS a.

Hypothesis LAY_IMG_GGOT4 : gw_le gIMG_LO GGOT4.
Hypothesis LAY_GVDSO4_IMG : gw_le (GVDSO4 + 8) gIMG_HI.

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
Hypothesis LAY_RDATA_GGOT4 : gw_le gRDATA_LO GGOT4.
Hypothesis LAY_GHASH4x12_GVDSO4 : gw_le (GHASH4 + 12) GVDSO4.
Hypothesis AL_e_fn_lh_entry_free : gw_b4 e_fn_lh_entry_free.
Hypothesis RNG_e_fn_lh_entry_free : gw_br e_fn_lh_entry_free 4.
Hypothesis LAY_POS_e_fn_lh_entry_free : gw_le 1 e_fn_lh_entry_free.
Hypothesis LAY_HI_e_fn_lh_entry_free : gw_le (e_fn_lh_entry_free + 4) 1099511627776.
#[using="w_7 w_8 w_12 w_19 w_24 w_25 w_38 hi_7 hi_24 lo_8 lo_25 joff_12 joff_19 joff_38 GGOT4 GHASH4 GVDSO4 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free vdso_ok4 JG_CGT_P gRDATA_LO CODE BASE4 BASER D_7 E_7 D_8 E_8 D_12 E_12 D_19 E_19 D_24 E_24 D_25 E_25 D_38 E_38 ANCH_8 ANCH_25 LINK_12 LINK_19 LINK_38 RNG_GGOT4 AL_GGOT4 RNG_GHASH4 AL_GHASH4 RNG_GVDSO4 AL_GVDSO4 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 AL_e_fn_lh_entry_free RNG_e_fn_lh_entry_free LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

Section LhNew.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition lh_kchar_table_new_entry : Z := (base + 0x0).

#[using="w_7 w_8 w_12 w_19 w_24 w_25 w_38 GGOT4 GHASH4 GVDSO4 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_entry_free gRDATA_LO CODE LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma lh_init_loop :
forall (k i n : nat) (x1 x2 gp tp t0 t1 t2 x8 x9 a0 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tbl : Z),
(k = n - 1 - i)%nat -> (i < n)%nat -> 0 <= tbl -> tbl + 40 * Z.of_nat n < 2^64 ->
mem_inv segs m ->
lh_slots segs m tbl (init_svs i n) ->
evt segs (fun ms' => exists m',
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 a0 (Z_to_bv 64 (tbl + 40 * Z.of_nat n)) (Z_to_bv 64 (tbl + 40 * Z.of_nat n)) (Z_to_bv 64 (-1)) a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x94)) fc None m' (seg_rom segs)
/\ munch [(tbl, tbl + 40 * Z.of_nat n)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ lh_slots segs m' tbl (init_svs n n))
(MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 a0 (Z_to_bv 64 (tbl + 40 * Z.of_nat i)) (Z_to_bv 64 (tbl + 40 * Z.of_nat n)) (Z_to_bv 64 (-1)) a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x88)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_8 w_12 w_19 w_24 w_25 w_38 GGOT4 GHASH4 GVDSO4 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_entry_free gRDATA_LO CODE LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free segs base HIx. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_IMG_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GVDSO4_IMG as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GHASH4x12_GVDSO4 as gL7_; unfold gw_le in gL7_. pose proof LAY_POS_e_fn_lh_entry_free as gL8_; unfold gw_le in gL8_. pose proof LAY_HI_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_.
induction k as [|k IH]; intros until tbl; intros Hk Hi Ht0 Htn MI SL.
- pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C. unfold ent_addr, slot_cells, ZSLOT in C. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots segs mx tbl (init_svs (S i) n)) end.
{ rewrite <- init_svs_step by lia. eapply (lh_slots_write_slot segs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |].
unfold ent_addr, slot_cells, ESLOT. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite <- EB.
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity. exact C. }
clear C MU2 SL. step. step. subst B. if_falsex.
apply evt_done. eexists. split; [|split; [exact MU | split; [exact WM | split; [exact MI | ]]]].
+ replace (tbl + 40 * Z.of_nat i + 40) with (tbl + 40 * Z.of_nat n) by lia. reflexivity.
+ replace n with (S i) at 1 by lia. exact SL'.
- pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C. unfold ent_addr, slot_cells, ZSLOT in C. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots segs mx tbl (init_svs (S i) n)) end.
{ rewrite <- init_svs_step by lia. eapply (lh_slots_write_slot segs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |].
unfold ent_addr, slot_cells, ESLOT. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite <- EB.
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity. exact C. }
clear C MU2 SL. step. step. subst B. if_truex.
replace (tbl + 40 * Z.of_nat i + 40) with (tbl + 40 * Z.of_nat (S i)) by lia.
eapply evt_cut.
{ eapply (IH (S i) n); [lia | lia | exact Ht0 | exact Htn | exact MI | exact SL']. }
cbv beta. intros ms' (m' & -> & MU' & WM' & MI' & SLn).
apply evt_done. exists m'. split; [reflexivity|]. split; [|split; [|split; [exact MI' | exact SLn]]].
+ eapply munch_trans; [exact MU | exact MU'].
+ eapply wmono_trans; [exact WM | exact WM'].
Qed.

Notation lh_glob4 := (lh_glob segs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma lh_glob_client : forall LB SP m m', heap_pres S4L LB SP m m' -> lh_glob4 m -> lh_glob4 m'.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_IMG_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GVDSO4_IMG as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GHASH4x12_GVDSO4 as gL7_; unfold gw_le in gL7_. pose proof LAY_POS_e_fn_lh_entry_free as gL8_; unfold gw_le in gL8_. pose proof LAY_HI_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_.
intros LB SP m m' HPR ([seed G1] & G2 & (vf & G3 & VF)). split; [| split].
- exists seed. eapply (heap_pres_rw_cells S4L); [exact HPR | exact G1 |]. right; left. intros a Ha. cbn in Ha. gw_expose GHASH4.
cbn. gw_cs.
- eapply (heap_pres_rw_cells S4L); [exact HPR | exact G2 |]. right; left. intros a Ha. cbn in Ha. gw_expose GGOT4.
cbn. gw_cs.
- exists vf. split; [| exact VF]. eapply (heap_pres_rw_cells S4L); [exact HPR | exact G3 |]. right; left. intros a Ha. cbn in Ha. gw_expose GVDSO4.
cbn. gw_cs.
Qed.

Definition lh_table_new_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
lh_glob4 m' /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, lhtab2 segs S4F m' BS r [] /\ HEAPx A' (BS ++ LB) m' md') ).

#[using="w_7 w_8 w_12 w_19 w_24 w_25 w_38 hi_7 hi_24 lo_8 lo_25 joff_12 joff_19 joff_38 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER D_7 E_7 D_8 E_8 D_12 E_12 D_19 E_19 D_24 E_24 D_25 E_25 D_38 E_38 ANCH_8 ANCH_25 LINK_12 LINK_19 LINK_38 RNG_GGOT4 RNG_GHASH4 RNG_GVDSO4 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma lh_kchar_table_new_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word),
HEAPx A LB m md ->
lh_glob4 m ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 (fn_lh_entry_free S4F) ->
(forall ms' md', lh_table_new_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_kchar_table_new_entry) fc None m (seg_rom segs)) md) T.
Proof. clear - w_7 w_8 w_12 w_19 w_24 w_25 w_38 hi_7 hi_24 lo_8 lo_25 joff_12 joff_19 joff_38 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER D_7 E_7 D_8 E_8 D_12 E_12 D_19 E_19 D_24 E_24 D_25 E_25 D_38 E_38 ANCH_8 ANCH_25 LINK_12 LINK_19 LINK_38 RNG_GGOT4 RNG_GHASH4 RNG_GVDSO4 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free segs gTP S4F HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_IMG_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GVDSO4_IMG as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GHASH4x12_GVDSO4 as gL7_; unfold gw_le in gL7_. pose proof LAY_POS_e_fn_lh_entry_free as gL8_; unfold gw_le in gL8_. pose proof LAY_HI_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_.
intros until errv. intros HP G ST LO LOS SPA HT ERR TP RA A0 A1 K.
unfold_consts. word_range sp SPR.
destruct G as ([seed G1] & G2 & (vf & G3 & VF)). gw_expose GHASH4. gw_expose GGOT4. gw_expose GVDSO4.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. unfold lh_kchar_table_new_entry. subst a0 a1.
carve_frame 48%nat ST.
do 6 step.
step. step. step. step. step. step. step.

alloc_call (hi_calloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in G1; [| right; left; intros q Hq; cbn in Hq; cbn; gw_cs]. cbn [hl_segs S4L] in G1.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in G2; [| right; left; intros q Hq; cbn in Hq; cbn; gw_cs]. cbn [hl_segs S4L] in G2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in G3; [| right; left; intros q Hq; cbn in Hq; cbn; gw_cs]. cbn [hl_segs S4L] in G3.
clear MU WM MI ST.
destruct OUT2 as [(-> & HerrHP2 & HP2) | (Hr & BLK & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_truex. do 7 step.
apply evt_RZ_done. apply K. unfold lh_table_new_post.
exists m2, A2, 0, e2.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| left; auto]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ split; [exists seed; exact G1 | split; [exact G2 | exists vf; split; [exact G3 | exact VF]]].
-
change (Z.to_nat (1 * 56)) with 56%nat in BLK. change (1 * 56) with 56 in HP2. cbn [repeat] in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r 56 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 56 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 56)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_falsex.
stepz.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mz4 end.
step. step. step. step.

alloc_call (hi_calloc S4L HIx) S4L HIx HP2 MU WM MI.
intros ms3 m3 md3 A3 q e3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in G1; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs S4L] in G1.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in G2; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs S4L] in G2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in G3; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs S4L] in G3.
clear MU WM MI ST2.
destruct OUT3 as [(-> & HerrHP3 & HP3) | (Hq & BLK2 & HP3)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 56)] m3) as MU.
pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. step. stepz. step. if_true. step.

alloc_call (hi_free S4L HIx) S4L HIx HP3 MU WM MI.
{ right. exists 56. left. reflexivity. }
intros ms5 m5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR5, HP5.
extend_pres S4L HIx HPR MU WM HP3 HPR5.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in G1; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs S4L] in G1.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in G2; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs S4L] in G2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in G3; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs S4L] in G3.
clear MU WM MI ST3 BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m5) as MU.
pose proof (wmono_refl segs m5) as WM.
reenter MOK5.
do 8 step.
apply evt_RZ_done. apply K. unfold lh_table_new_post.
exists m5, A5, 0, e3.
split; [| split; [| split; [| split; [exact HPR | split; [exact ERR5 | split; [| left; auto]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; [| exact VM5]. eapply model_vm_only_trans; eassumption.
* release_frame FR ST5 (bv_unsigned sp). exact ST5.
* split; [exists seed; exact G1 | split; [exact G2 | exists vf; split; [exact G3 | exact VF]]].
+
change (16 * 40) with (40 * 16) in HP3. change (16 * 40) with (40 * Z.of_nat 16) in BLK2.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
destruct (blocks2 S4L HIx _ _ _ _ _ _ _ _ HP3) as ((Hqal & Hqlo & Hqhi & Hqimg) & _ & Hdj).
cbn [hl_img_lo hl_img_hi S4L] in Hqimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 56); (q, q + 640)] m3) as MU.
pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. step. step. step. if_falsex.
step. step. step. stepz. step.
step. if_false. step. step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (zeros_slots segs 16 mx q BLK2) as SL0 end.
rewrite <- init_svs_0 in SL0. clear BLK2.
replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 40 * Z.of_nat 0)) by (f_equal; lia).
replace (q + 640) with (q + 40 * Z.of_nat 16) by reflexivity.
call (lh_init_loop 15 0 16); [reflexivity | lia | lia | lia | | exact SL0 |]. { assumption. }
match goal with H : lh_slots segs _ q (init_svs 16 16) |- _ => rename H into SL16 end.
do 8 step.
apply evt_RZ_done. apply K. unfold lh_table_new_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A3, r, e3 end.
assert (HP3' : HEAPx A3 ((r, 56) :: (q, 40 * 16) :: LB) m3 md3) by (eapply heap_perm; [exact HP3 | apply perm_swap]).
split; [| split; [| split; [| split; [ | split; [ eassumption | split; [| right]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; eassumption.
* release_frame FR ST3 (bv_unsigned sp). exact ST3.
* eapply heap_pres_trans; [exact HPR|].
lazymatch goal with |- heap_pres _ _ _ _ ?mf =>
match goal with MUx : munch _ m3 mf, WMx : wmono segs m3 mf |- _ =>
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MUx | exact WMx |];
eapply (client_outside S4L HIx); [exact HP3' | intros b Hb; right; right; exact Hb | clia |];
solve_clientW S4L HIx HP3' end end.
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
eapply (heap_frame S4L HIx); [exact HP3' | | exact WMx | exact MIx];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3' MUx); solve_frameW_with HP3' end end.
Qed.
End LhNew.

End RC__1.

End G.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH QmZZ QKQo Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo.
Import QPIU.Mqd.
Import Q6WR.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition maybefree1_code (w_30 w_34 w_39 w_41 w_43 w_51 w_55 : Z) : list Z :=
[0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00050413; 0x00452503; 0xfff5051b; 0x00a42223; 0x00050663; 0x00000513; 0x08c0006f; 0x01843683; 0x00068e63; 0x02043603; 0x00040513; 0x00058493; 0x00060593; 0x000680e7; 0x00048593; 0x00042503; 0x00600613; 0x00043c23; 0x02043023; 0x02c50a63; 0x00500613; 0x00c50e63; 0x00400613; 0x02c51a63; 0x06058463; 0x02843503; w_30; 0x0240006f; 0x04058463; 0x02843503; w_34; 0x0140006f; 0x02843503; 0x00055663; 0x03043503; w_39; 0x01043503; w_41; 0x00040513; w_43; 0x00100513; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0x00008067; 0x02843503; w_51; 0x00051a63; 0xfb1ff06f; 0x02843503; w_55; 0xf8050ae3; 0x00200513; 0xfcdff06f]%Z.

Definition blk_187f8_code : list Z := [0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00050413; 0x02053503; 0x02050063; 0x00843483; 0x00048c63; 0x02043583; 0x00048513; 0x000580e7; 0x0184b483; 0xfe0498e3; 0x01843503]%Z.

Definition blk_17a68_code : list Z := [0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x01213023; 0x00050413; 0x00853583; 0x02058e63; 0x00000493; 0x00000913; 0x0100006f; 0x00190913; 0x00848493; 0x02b97263; 0x00043503; 0x00950533; 0x00053503; 0xfe0504e3; 0x01843583; 0x000580e7; 0x00843583; 0xfd9ff06f; 0x00043503]%Z.

Definition blk_17cb0_code : list Z := [0x00853503; 0x00008067]%Z.

Definition blk_18a54_code : list Z := [0x00452503; 0x00008067]%Z.

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

Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
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
#[using="w_30 w_34 w_39 w_41 w_43 w_51 w_55 joff_30 joff_34 joff_39 joff_41 joff_43 joff_51 joff_55 e_pbfree e_17a68 e_17cb0 e_187f8 e_18a54 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_30 E_30 D_34 E_34 D_39 E_39 D_41 E_41 D_43 E_43 D_51 E_51 D_55 E_55 LINK_30 LINK_34 LINK_39 LINK_41 LINK_43 LINK_51 LINK_55 printbuf_free_cps CODE_e_187f8 CODE_e_17a68 CODE_e_17cb0 CODE_e_18a54 S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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
F1 (Z_to_bv 64 (base + 0xa0)) fc1 None m (seg_rom segs)) md) T.
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
F1 (Z_to_bv 64 (base + 0x4c)) fc1 None m (seg_rom segs)) md) T.
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

End RC__1.

End G.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.Mq0.
Import QPIU.Mqe.
Import QQLG.Mq9.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition blk_194bc_code : list Z := [0x00020513; 0xf5c50513; 0x00008067]%Z.

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_3 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_14 w_47 w_70 : Z).
Variables (joff_14 joff_47 joff_70 : bv 21).
Variables (e_194bc e_memmove : Z).
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
Hypothesis CODE : code_at segs base (pbmemappend_code w_14 w_47 w_70).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 356.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Jal 1 joff_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_47 : decode_any (Z_to_bv 32 w_47) = Some (Jal 1 joff_47, 4%Z).
Hypothesis E_47 : is_ecall (Z_to_bv 32 w_47) = false.
Hypothesis D_70 : decode_any (Z_to_bv 32 w_70) = Some (Jal 1 joff_70, 4%Z).
Hypothesis E_70 : is_ecall (Z_to_bv 32 w_70) = false.
Hypothesis LINK_14 : gw_anch (base + 56 + bv_signed joff_14)%Z (e_194bc + 0)%Z.
Hypothesis LINK_47 : gw_anch (base + 188 + bv_signed joff_47)%Z e_realloc.
Hypothesis LINK_70 : gw_anch (base + 280 + bv_signed joff_70)%Z (e_memmove + 0)%Z.

Definition memmove_post := Eval cbv beta delta [QQLG.Mq9.memmove_post] in (@QQLG.Mq9.memmove_post segs).
Definition memmove_stmt := ltac:(let t := eval cbv beta delta [QQLG.Mq9.memmove_stmt] in (@QQLG.Mq9.memmove_stmt segs e_memmove) in let t := gw_subst t (@QQLG.Mq9.memmove_post segs) memmove_post in exact t).

Definition pbufx := ltac:(let t := constr:(ltac:(gw_ctx2 (@QPIU.Mqe.pbufx))) in let t := eval cbv beta delta [QPIU.Mqe.pbufx] in t in exact t).
Definition memappend_post_c := ltac:(let t := constr:(ltac:(gw_ctx2 (@QPIU.Mqe.memappend_post_c))) in let t := eval cbv beta delta [QPIU.Mqe.memappend_post_c] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqe.pbufx))) in let t := gw_subst t x pbufx in exact t).
Definition memappend_tail := ltac:(let p := constr:(ltac:(gw_ctx2 (@QPIU.Mqe.memappend_tail))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqe.pbufx))) in let T := gw_subst T x pbufx in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqe.memappend_post_c))) in let T := gw_subst T x memappend_post_c in exact (p : T)).

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
Hypothesis CODE_e_194bc : code_at segs e_194bc blk_194bc_code.
#[using="w_14 w_47 w_70 joff_14 joff_47 joff_70 e_194bc e_memmove RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_14 E_14 D_47 E_47 D_70 E_70 LINK_14 LINK_47 LINK_70 CODE_e_194bc S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

#[using="Type"] Lemma lor_ones64_r : forall x, 0 <= x < 2^64 -> Z.lor x 18446744073709551615 = 18446744073709551615.
Proof. clear - segs. intros x Hx. change 18446744073709551615 with (Z.ones 64). apply Z.lor_ones_low; [lia|].
destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. Qed.
#[using="Type"] Lemma lor_ones64_l : forall x, 0 <= x < 2^64 -> Z.lor 18446744073709551615 x = 18446744073709551615.
Proof. clear - segs. intros. rewrite Z.lor_comm. apply lor_ones64_r. assumption. Qed.
#[using="Type"] Lemma v_sltu_1 : forall x y : word, bv_unsigned x < bv_unsigned y -> v_sltu x y = Z_to_bv 64 1.
Proof. clear - segs. intros x y H. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y)); [reflexivity|lia]. Qed.
#[using="Type"] Lemma v_sltu_0 : forall x y : word, bv_unsigned y <= bv_unsigned x -> v_sltu x y = Z_to_bv 64 0.
Proof. clear - segs. intros x y H. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y)); [lia|reflexivity]. Qed.
#[using="Type"] Lemma unsigned_m1 : bv_unsigned (Z_to_bv 64 (-1)) = 18446744073709551615.
Proof. clear - segs. reflexivity. Qed.

Section PbMemappendMain.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo : Z) (pb n : Z) (T : TSet).

Definition src_cls (SP b : Z) (src : list byte) : Prop :=
client_range S4L LB SP b n \/ ro_bytes segs b src.

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma src_cls_transport : forall SP SP' LB' b src m m',
src_cls SP b src -> Z.of_nat (length src) = n -> bytes_at segs m b src ->
heap_pres S4L LB' SP' m m' -> SP' <= SP -> (forall x, In x LB -> In x LB') -> mem_inv segs m' ->
0 <= b -> b + n <= 2^64 ->
bytes_at segs m' b src.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI segs HIx MEMMOVE ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo pb n T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros SP SP' LB' b src m m' [CR|RO] L SRC HPR HS HL MI Hb0 Hbn.
- eapply (heap_pres_bytes_at S4L); [| exact SRC | rewrite L].
eapply heap_pres_weaken; [exact HPR | exact HS | exact HL]. exact CR.
- apply ro_bytes_at; [exact MI | lia | lia | exact RO].
Qed.

#[using="w_14 w_47 w_70 joff_70 e_memmove LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_70 E_70 LINK_70 MEMMOVE"] Lemma memappend_rebase :
forall (buf0 bpos0 cap0 : Z) (content0 : list byte) (x1 t0 t1 t2 x9 a0 a2 a4 a5 a6 a7 x19 x20 x21 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(obuf ocap buf bpos cap b : Z) (content src : list byte) (errv : word) (framejunk : list byte),
HEAP S4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbufx m pb buf bpos cap content ->
bpos + n + 1 <= cap -> 0 <= n < 2^31 ->
bytes_at segs m b src -> Z.of_nat (length src) = n ->
0 <= b < 2^64 -> b + n <= 2^64 ->
(b + n <= obuf \/ obuf + ocap <= b) -> 0 <= obuf -> obuf + ocap <= 2^64 -> 0 < ocap < 2^31 ->
a0 = Z_to_bv 64 pb -> a2 = Z_to_bv 64 n ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (bv_unsigned sp + -64) [CB 8 framejunk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells segs m (gTP - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
bpos = bpos0 -> firstn (Z.to_nat bpos) content = firstn (Z.to_nat bpos0) content0 ->
(forall ms' md', memappend_post_c HIx ra sp gp (Z_to_bv 64 gTP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB pb buf0 bpos0 cap0 content0 src n lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 obuf) x9 a0 (Z_to_bv 64 b) a2 (Z_to_bv 64 buf) a4 a5 a6 a7 (Z_to_bv 64 ocap) x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xdc)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_14 w_47 w_70 joff_70 e_memmove LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_70 E_70 LINK_70 MEMMOVE segs base gTP HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo pb n T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros buf0 bpos0 cap0 content0. intros until framejunk. intros HP PBX ROOM Hn SRC SRCL Hb0 Hbn OSEP Ob0 Obn Ocap A0 A2 ST LO LOS SPA HT FR ERR RA VM0 HPR Ebpos Epre K.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
unfold_consts. word_range sp SPR.
subst a0 a2.
apply rz_evt; [exact MOK|].
step. step. step. step. step. step. step. step.
rewrite (unsigned_lit b) by lia. rewrite (unsigned_lit obuf) by lia.
destruct (Z.eq_dec b obuf) as [Eb|Nb].
-
assert (n = 0) by lia. subst b.
rewrite (v_sltu_0 (Z_to_bv 64 obuf) (Z_to_bv 64 obuf)) by lia.
replace (obuf - obuf) with 0 by lia.
rewrite (v_sltu_1 (Z_to_bv 64 0) (Z_to_bv 64 ocap)) by (rewrite !unsigned_lit by lia; lia).
match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => let v := eval vm_compute in (bv_swrap 32 e) in change (bv_swrap 32 e) with v end.
step. if_falsex. step.
assert (src = []) as -> by (destruct src; [reflexivity | cbn in SRCL; lia]).
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
apply evt_RZ_done.
eapply (memappend_tail HIx MEMMOVE ra sp gp (Z_to_bv 64 gTP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo pb buf0 bpos0 cap0 n content0 T
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A buf bpos cap buf content [] errv framejunk);
first [ reflexivity | eassumption | lia | idtac ].

1: unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption.
1: apply bytes_at_nil; unfold_consts; lia.
all: try (unfold_consts; lia).
-
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
match goal with |- context [Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?v) + 0))] =>
replace (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0))) with (Z_to_bv 64 (-1)) end.
2:{ assert (Hv : forall v, v = 18446744073709551615 -> Z_to_bv 64 (-1) = Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0))).
{ intros v ->. rewrite (unsigned_lit 18446744073709551615) by lia.
replace (18446744073709551615 + 0) with (-1 + 4294967296 * 4294967296) by lia.
rewrite swrap32_shift, swrap32_id by lia. reflexivity. }
apply Hv. clear Hv.
pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (b - obuf))) as R1. unfold bv_modulus in R1. cbn in R1.
destruct (Z.lt_ge_cases b obuf) as [Hlt|Hge].
- rewrite (v_sltu_1 (Z_to_bv 64 b) (Z_to_bv 64 obuf)) by (rewrite (unsigned_lit b) by lia; rewrite (unsigned_lit obuf) by lia; lia).
rewrite (unsigned_lit 1) by lia. rewrite (swrap32_id (0 - 1)) by lia. change (0 - 1) with (-1). rewrite unsigned_m1.
rewrite lor_ones64_l by lia. rewrite (unsigned_lit 18446744073709551615) by lia.
rewrite lor_ones64_l; [reflexivity|].
match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as R2; unfold bv_modulus in R2; cbn in R2; lia end.
- assert (obuf + ocap <= b) by lia.
rewrite (v_sltu_0 (Z_to_bv 64 b) (Z_to_bv 64 obuf)) by (rewrite (unsigned_lit b) by lia; rewrite (unsigned_lit obuf) by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite (swrap32_id (0 - 0)) by lia. change (0 - 0) with 0. rewrite (unsigned_lit 0) by lia.
rewrite (unsigned_lit (b - obuf)) by lia. rewrite Z.lor_0_l.
rewrite (v_sltu_0 (Z_to_bv 64 (b - obuf)) (Z_to_bv 64 ocap)) by (rewrite (unsigned_lit (b - obuf)) by lia; rewrite (unsigned_lit ocap) by lia; lia).
rewrite (unsigned_lit 0) by lia. change (0 + -1) with (-1). rewrite unsigned_m1.
rewrite (unsigned_lit (b - obuf)) by lia. rewrite lor_ones64_r by lia. reflexivity. }
step. if_truex.
apply evt_RZ_done.
eapply (memappend_tail HIx MEMMOVE ra sp gp (Z_to_bv 64 gTP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo pb buf0 bpos0 cap0 n content0 T
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A buf bpos cap b content src errv framejunk);
first [ reflexivity | eassumption | lia | idtac ].
all: first [unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption | unfold_consts; lia].
Qed.

#[using="w_14 w_47 w_70 joff_47 joff_70 e_memmove LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_47 E_47 D_70 E_70 LINK_47 LINK_70 MEMMOVE"] Lemma memappend_grow :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(buf bpos cap ns b : Z) (content src : list byte) (errv : word) (framejunk : list byte),
HEAP S4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbufx m pb buf bpos cap content ->
bpos + n + 1 <= ns -> cap <= ns < 2^31 -> 0 <= n < 2^31 ->
bytes_at segs m b src -> Z.of_nat (length src) = n -> src_cls (bv_unsigned sp) b src ->
0 <= b < 2^64 -> b + n <= 2^64 ->
(b + n <= buf \/ buf + cap <= b) ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (bv_unsigned sp + -64) [CB 8 framejunk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells segs m (gTP - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
(forall ms' md', memappend_post_c HIx ra sp gp (Z_to_bv 64 gTP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB pb buf bpos cap content src n lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 buf) (Z_to_bv 64 ns) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 cap) (Z_to_bv 64 b) (Z_to_bv 64 n) (Z_to_bv 64 pb) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xb4)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_14 w_47 w_70 joff_47 joff_70 e_memmove LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_47 E_47 D_70 E_70 LINK_47 LINK_70 MEMMOVE segs base gTP HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo pb n T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until framejunk. intros HP PBX ROOM Hns Hn SRC SRCL SCL Hb0 Hbn SEP ST LO LOS SPA HT FR ERR RA VM0 HPR K.
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
assert (LEN : length content = Z.to_nat cap) by (destruct PBUF as [[[Hwf _] _] _]; exact Hwf).
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as Hbimg. cbn [hl_img_lo hl_img_hi S4L] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hbhi.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hpbbuf.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ pb PB_SZ buf cap HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hpbbuf) as Hdisj.
pose proof (wmono_refl segs m) as WM.
change (gTP - 164) with (gTP + -164) in ERR.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (pb, pb + 16); ((gTP + -164), (gTP + -160))] m) as MU.
rewrite <- (app_nil_r content) in PBUF.
apply rz_evt; [exact MOK|].
step. step. step.

alloc_call (hi_realloc S4L HIx) S4L HIx HP MU WM MI.
{ right; left. reflexivity. }
intros ms2 m2 md2 A2 r errv2 RS VM2 ST2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite lb_remove_other in OUT2 by (cbn; lia). rewrite lb_remove_head in OUT2.
destruct OUT2 as [(-> & _ & HPR2 & HP2) | (Hr & HPR2 & [junk BLK] & HP2)].
-
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in PBS; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in PBS.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in PBUF; [| eapply client_range_block; [right; left; reflexivity | lia | cbn [cells_size csize]; lia]]. cbn [hl_segs S4L] in PBUF.
clear MU WM MI ST.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.

step. if_truex. step. step. do 9 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
apply evt_RZ_done. apply K. unfold memappend_post_c.
exists m2, A2, (2^64 - 1), errv2, buf, cap.
split; [| split; [eapply model_vm_only_trans; [exact VM0 | exact VM2] | split; [| split; [exact HPR | split; [exact ERR2 | split; [exact HP2| right]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ rewrite app_nil_r in PBUF. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
unfold pbuf_core. repeat (split; [first [lia | eassumption] |]). eassumption.
-
pose proof (heap_blk S4L HIx _ _ _ _ r ns HP2 ltac:(left; reflexivity)) as (_ & Hral & Hrlo & Hrhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r ns HP2 ltac:(left; reflexivity)) as Hrimg. cbn [hl_img_lo hl_img_hi S4L] in Hrimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP2) as Hrpb.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ r ns pb PB_SZ HP2 ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hrpb) as Hrdisj.
cbn in Hrdisj.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in PBS; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in PBS.
clear MU WM MI ST PBUF.
rewrite LEN, Z.min_r, Z2Nat.id, firstn_all2 in BLK by lia.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(pb, pb + 16)] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_falsex. step. step. stepz. stepz. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end || idtac.
assert (HPR3 : heap_pres S4L LB (bv_unsigned sp + -64) m m3).
{ eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPR2 | lia | intros x Hx; cbn; right; exact Hx] |].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp + -64)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb0; right; right; exact Hbb0 | clia |]. solve_clientW S4L HIx HP2. }
assert (SRC3 : bytes_at segs m3 b src).
{ eapply (src_cls_transport (bv_unsigned sp) (bv_unsigned sp + -64) LB);
[exact SCL | exact SRCL | exact SRC | exact HPR3 | lia | intros x Hx; exact Hx | exact MI | lia | lia]. }
apply evt_RZ_done.
eapply (memappend_rebase buf bpos cap content _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 md2 A2 buf cap r bpos ns b (content ++ junk) src errv2 framejunk);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- HEAP _ _ _ _ _ _ =>
eapply (heap_frame S4L HIx); [ eapply heap_perm; [exact HP2 | apply perm_swap] | | exact WM | exact MI ];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ (heap_perm _ _ _ _ _ _ _ HP2 (perm_swap _ _ _)) MU); solve_frameW_with HP2
| |- pbufx _ _ _ _ _ _ =>
unfold pbufx, pbuf_core; split; [lia|]; split; [lia|]; split; [destruct BLK as [[[Hwf _] _] _]; rewrite Hwf; lia|]; split; [eassumption|];
exact BLK
| |- model_vm_only _ _ => eapply model_vm_only_trans; eassumption
| |- heap_pres _ _ _ _ _ =>
eapply heap_pres_trans; [exact HPR|];
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb0; right; right; exact Hbb0 | clia |];
solve_clientW S4L HIx HP2
| |- firstn _ _ = firstn _ _ =>
rewrite firstn_app; replace (Z.to_nat bpos - length content)%nat with 0%nat by lia; cbn [firstn]; apply app_nil_r
| |- _ => unfold_consts; lia
end.
Qed.
End PbMemappendMain.

End RC__1.

End G.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbVh QlEo_c1 QWxq_c1 Q8Q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsjA QEpW QZDE QbVh QlEo_c1 QWxq_c1 QXup Q5Rg.
Import QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Q8tj QKQo.
Import QSL3.
Import Q8Q3.
Import QnCn.Mq0.
Import Q6WR.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma upd_app_len' : forall {X} (a b : list X) x y, upd (a ++ x :: b) (length a) y = a ++ y :: b.
Proof. intros X a. induction a as [|z a IH]; intros b x y; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma nth_error_app_len : forall {X} (a b : list X) x, nth_error (a ++ x :: b) (length a) = Some x.
Proof. intros. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma firstn_app_len : forall {X} (a b : list X), firstn (length a) (a ++ b) = a.
Proof. intros. rewrite firstn_app, Nat.sub_diag, firstn_all. cbn. apply app_nil_r. Qed.

Lemma Forall_repeat0 : forall n, Forall (fun p : Z => p = 0) (repeat 0 n).
Proof. induction n; cbn; constructor; auto. Qed.

Ltac hperm := unfold lh_blocks, kblk, blk; perm.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation wz := (Z_to_bv 64) (only parsing).

#[using="Type"] Lemma zobjc_hdr : forall m x q kids XBS,
zobjc segs fn m x q kids XBS -> List.NoDup (map blk_addr XBS) ->
exists pb cf, In (x, 48) XBS /\
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz cf)]) /\
(forall m' q', rw_cells segs m' x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q' ++ [C8 (wz cf)]) ->
agree_on segs (others x XBS) m m' -> zobjc segs fn m' x q' kids XBS).
Proof.
intros m x q kids XBS (t & tbl & size & es & svs & pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK) ND.
exists pb, t. split; [rewrite EX; left; reflexivity|]. split; [exact HDR|].
intros m' q' HDR' AG. exists t, tbl, size, es, svs, pb, PBS, KBS, esk, esz.
split; [exact Ees|]. split; [exact Lz|]. split; [exact Fz|]. split; [exact EX|]. rewrite EX in ND, AG.
split; [| split; [exact HDR' | split]].
- eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; right; exact Hb]].
- eapply lh_open_agree; [exact OPEN | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]].
- eapply okids_agree; [exact OK | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb]].
Qed.

#[using="Type"] Lemma zarrc_hdr : forall m x q kids XBS,
zarrc segs fn m x q kids XBS -> List.NoDup (map blk_addr XBS) ->
exists pb cf, In (x, 48) XBS /\
rw_cells segs m x (jhdr_cells JT_ARRAY 0 (fn_arr_to_json_string fn) pb 0 q ++ [C8 (wz cf)]) /\
(forall m' q', rw_cells segs m' x (jhdr_cells JT_ARRAY 0 (fn_arr_to_json_string fn) pb 0 q' ++ [C8 (wz cf)]) ->
agree_on segs (others x XBS) m m' -> zarrc segs fn m' x q' kids XBS).
Proof.
intros m x q kids XBS (a & arr & size & pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK) ND.
exists pb, a. split; [rewrite EX; left; reflexivity|]. split; [exact HDR|].
intros m' q' HDR' AG. exists a, arr, size, pb, PBS, KBS, ps.
split; [exact EX|]. rewrite EX in ND, AG.
split; [| split; [exact HDR' | split]].
- eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; right; exact Hb]].
- eapply alist_agree; [exact AL | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]].
- eapply okids_agree; [exact OK | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb]].
Qed.

#[using="Type"] Lemma zobj_last : forall m x q kids k nz t tbl size es svs XBS,
zobj segs fn m x q (kids ++ [k]) nz t tbl size es svs XBS ->
exists pb PBS KBS1 bs esk1 e esz,
es = esk1 ++ e :: esz /\ length esk1 = length kids /\ length esz = nz /\ Forall (fun e => le_v e = 0) esz /\
XBS = ((x, 48) :: lh_blocks t tbl size es ++ (concat KBS1 ++ bs)) ++ PBS /\
opt_pbuf segs m PBS pb /\
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz t)]) /\
lh_open segs fn m t tbl size es svs /\
okids segs fn m kids (map le_v esk1) KBS1 /\
match k with None => le_v e = 0 /\ bs = [] | Some c => le_v e <> 0 /\ jval segs fn c m bs (le_v e) 1 end.
Proof.
intros m x q kids k nz t tbl size es svs XBS (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 L2]. rewrite length_map, length_app in L1. cbn in L1.
destruct (snoc_inv_gen esk) as [-> | (esk1 & e & ->)]; [cbn in L1; lia|].
rewrite map_app in OK. cbn [map] in OK.
destruct (okids_snoc_inv _ _ _ _ _ _ _ OK) as (vs1 & v & KBS1 & bs & Evs & -> & OK1 & Hk).
apply app_inj_last in Evs as [<- <-].
exists pb, PBS, KBS1, bs, esk1, e, esz.
rewrite length_app in L1. cbn in L1.
split; [rewrite Ees, <- app_assoc; reflexivity|]. split; [lia|]. split; [exact Lz|]. split; [exact Fz|].
split; [rewrite EX, concat_snoc; reflexivity|].
split; [exact OPB|]. split; [exact HDR|]. split; [exact OPEN|]. split; [exact OK1 | exact Hk].
Qed.

#[using="Type"] Lemma zobj_last_close : forall m m' x q kids nz t tbl size esk1 e esz svs' pb PBS KBS1,
length esz = nz -> Forall (fun e => le_v e = 0) esz ->
opt_pbuf segs m PBS pb ->
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz t)]) ->
okids segs fn m kids (map le_v esk1) KBS1 ->
lh_open segs fn m' t tbl size (esk1 ++ with_v e 0 :: esz) svs' ->
agree_on segs ((x, 48) :: concat KBS1 ++ PBS) m m' ->
zobj segs fn m' x q kids (S nz) t tbl size (esk1 ++ with_v e 0 :: esz) svs'
(((x, 48) :: lh_blocks t tbl size (esk1 ++ with_v e 0 :: esz) ++ concat KBS1) ++ PBS).
Proof.
intros m m' x q kids nz t tbl size esk1 e esz svs' pb PBS KBS1 Lz Fz OPB HDR OK OPEN AG.
exists pb, PBS, KBS1, esk1, (with_v e 0 :: esz).
split; [reflexivity|]. split; [cbn; lia|]. split; [apply Forall_cons; [reflexivity | exact Fz]|]. split; [reflexivity|].
split; [| split; [| split; [exact OPEN|]]].
- eapply opt_pbuf_agree; [exact OPB | exact AG | intros b Hb; right; apply in_or_app; right; exact Hb].
- eapply rw_cells_agree; [exact HDR | exact AG | exists x, 48; split; [left; reflexivity | cbn; lia]].
- eapply okids_agree; [exact OK | exact AG | intros b Hb; right; apply in_or_app; left; exact Hb].
Qed.

#[using="Type"] Lemma zobj_nil_vals : forall m x q nz t tbl size es svs XBS,
zobj segs fn m x q [] nz t tbl size es svs XBS -> forall e, In e es -> le_v e = 0.
Proof.
intros m x q nz t tbl size es svs XBS (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK) e He.
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _]. rewrite length_map in L1. destruct esk; [| cbn in L1; discriminate].
subst es. cbn in He. exact (proj1 (Forall_forall _ _) Fz e He).
Qed.

#[using="Type"] Lemma zarr_nil_vals : forall m x q nz a arr size XBS,
zarr segs fn m x q [] nz a arr size XBS ->
exists pb PBS, XBS = [(x, 48); (a, 32); (arr, 8 * size)] ++ PBS /\ opt_pbuf segs m PBS pb /\
rw_cells segs m x (jhdr_cells JT_ARRAY 0 (fn_arr_to_json_string fn) pb 0 q ++ [C8 (wz a)]) /\
alist segs fn m [(a, 32); (arr, 8 * size)] a (repeat 0 nz).
Proof.
intros m x q nz a arr size XBS (pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK).
destruct (okids_nil_inv _ _ _ _ _ OK) as [-> ->]. exists pb, PBS. cbn [concat app] in EX.
split; [exact EX|]. split; [exact OPB|]. split; [exact HDR | exact AL].
Qed.

#[using="Type"] Lemma zobj_nil_shape : forall m x q nz t tbl size es svs XBS,
zobj segs fn m x q [] nz t tbl size es svs XBS ->
exists pb PBS, XBS = ((x, 48) :: lh_blocks t tbl size es) ++ PBS /\ opt_pbuf segs m PBS pb /\
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz t)]) /\
lh_open segs fn m t tbl size es svs /\ (forall e, In e es -> le_v e = 0) /\ length es = nz.
Proof.
intros m x q nz t tbl size es svs XBS Z0. pose proof (zobj_nil_vals _ _ _ _ _ _ _ _ _ _ Z0) as VZ.
destruct Z0 as (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK).
destruct (okids_nil_inv _ _ _ _ _ OK) as [E1 ->]. destruct esk; [| cbn in E1; discriminate]. subst es.
exists pb, PBS. cbn [concat app] in EX. rewrite app_nil_r in EX.
split; [exact EX|]. split; [exact OPB|]. split; [exact HDR|]. split; [exact OPEN|]. split; [exact VZ | cbn; exact Lz].
Qed.

End WithSegs.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi Qsw7 QJjn.
Import QPIU.Mqg.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition toknew_code (w_0 w_1 : Z) : list Z :=
[w_0; w_1]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_0 w_1 : Z).
Variables (joff_1 : bv 21).
Variables (e_1411c : Z).
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
Proof. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.
Definition gLAYF0 : Prop := ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Hypothesis CODE : code_at segs base (toknew_code w_0 w_1).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 8.
Hypothesis D_1 : decode_any (Z_to_bv 32 w_1) = Some (Jal 0 joff_1, 4%Z).
Hypothesis E_1 : is_ecall (Z_to_bv 32 w_1) = false.
Hypothesis LINK_1 : gw_anch (base + 4 + bv_signed joff_1)%Z (e_1411c + 0)%Z.

Hypothesis rw_cells_recast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqg.gw_all) (@QPIU.Mqg.rw_cells_recast) (base + 7104)%Z)) in let T := eval cbv beta delta [QPIU.Mqg.printbuf_new_entry] in T in let T := gw_fold_pcs T base (7104)%Z [0; 28; 52; 80]%Z in exact T).
Hypothesis printbuf_new_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqg.gw_all) (@QPIU.Mqg.printbuf_new_cps) (base + 7104)%Z)) in let T := eval cbv beta delta [QPIU.Mqg.printbuf_new_entry] in T in let T := gw_fold_pcs T base (7104)%Z [0; 28; 52; 80]%Z in exact T).

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
#[using="w_0 w_1 joff_1 e_1411c RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_1 E_1 LINK_1 rw_cells_recast printbuf_new_cps S4F"] Lemma gw_all : True. Proof. exact I. Qed.
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

Section RC__1.

Section TokNew.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition json_tokener_new_entry : Z := (base + 0x0).

Definition tstack_of_zeros : Prop := forall m k A,
rw_cells segs m A [CB (32 * k)%nat (repeat (Z_to_bv 8 0) (32 * k))] ->
tstack segs m A (repeat lvl_zero k).

Definition lb_remove_notin : Prop := forall p LB, (forall n, ~ In (p, n) LB) -> lb_remove p LB = LB.
Definition lb_remove_zero : Prop := forall A LB m md, HEAPx A LB m md -> lb_remove 0 LB = LB.

Definition tok_cells0 : list cell :=
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7);
C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Definition lvl_cells0 : list cell := [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition toknew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, tok_fresh segs m' BS r /\ HEAPx A' (BS ++ LB) m' md') ).

Definition json_tokener_new_cps : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word),
HEAPx A LB m md ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
(forall ms' md', toknew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_tokener_new_entry) fc None m (seg_rom segs)) md) T.
End TokNew.

End RC__1.

End G.
End Mq8.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPIU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPIU.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwApply2 GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_27 : Z).
Variables (joff_27 : bv 21).
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
Hypothesis CODE : code_at segs base (aladd_code w_27).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 200.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (Jal 1 joff_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis LINK_27 : gw_anch (base + 108 + bv_signed joff_27)%Z e_realloc.

Definition array_list_add_entry : Z := (base + 0)%Z.
Definition array_list_add_post := ltac:(let t := constr:(ltac:(gw_ctx2 (@QPIU.array_list_add_post))) in let t := eval cbv beta delta [QPIU.array_list_add_post] in t in exact t).
Definition add_frame := ltac:(let t := constr:(ltac:(gw_ctx2 (@QPIU.add_frame))) in let t := eval cbv beta delta [QPIU.add_frame] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.array_list_add_post))) in let t := gw_subst t x array_list_add_post in exact t).
Definition al_add_store := ltac:(let p := constr:(ltac:(gw_ctx2 (@QPIU.al_add_store))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QPIU.array_list_add_post))) in let T := gw_subst T x array_list_add_post in let x := constr:(ltac:(gw_ctx2 (@QPIU.add_frame))) in let T := gw_subst T x add_frame in exact (p : T)).
Definition al_add_grow := ltac:(let p := constr:(ltac:(gw_ctx2 (@QPIU.al_add_grow))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QPIU.array_list_add_post))) in let T := gw_subst T x array_list_add_post in let x := constr:(ltac:(gw_ctx2 (@QPIU.add_frame))) in let T := gw_subst T x add_frame in exact (p : T)).

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
#[using="w_27 joff_27 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_27 E_27 LINK_27 S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

Section AlAdd2.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo a arr size d : Z) (ps : list Z) (T : TSet).

#[using="w_27 joff_27 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_27 E_27 LINK_27"] Lemma array_list_add_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : AS S4L HIx) (errv : word),
HEAPx A ((a, AL_SZ) :: (arr, 8 * size) :: LB) m0 md0 ->
alist segs S4F m0 [(a, AL_SZ); (arr, 8 * size)] a ps ->
0 <= d < 2^64 ->
stk segs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m0 (gTP - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 d ->
(forall ms' md', array_list_add_post HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo a arr size d ps ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp (Z_to_bv 64 gTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_add_entry) fc None m0 (seg_rom segs)) md0) T.
Proof. clear - w_27 joff_27 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_27 E_27 LINK_27 segs gTP S4F HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo a arr size d ps T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until errv. intros HP AL Hd ST LO LOS SPA HT ERR RA A0 A1 K.
destruct (alist_openx segs S4F m0 a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz).
unfold al_hdr in HDR. unfold al_tail in JK.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (al_blocks S4L HIx _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
cbn [hl_img_lo hl_img_hi S4L] in Himg, Himg2. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (u64arr_bound segs m0 arr (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length ps) as WL.
pose proof (wmono_refl segs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m0) as MU.
apply rz_evt; [exact MOK|]. unfold array_list_add_entry. subst a0 a1.
carve_frame 48%nat ST.
do 6 step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPx A ((a, 32) :: (arr, 8 * size) :: LB) m1 md0).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP. }
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m0 m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia |].
solve_clientW S4L HIx HP. }
step. step. step. step. if_falsex. step. step.
destruct (Z.lt_ge_cases (Z.of_nat (length ps) + 1) size) as [LT|GE].
-
if_falsex. step. step.
apply evt_RZ_done.
eapply (al_add_store HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo a arr size d ps T
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A arr size junk errv);
first [exact HP1 | exact ARR | exact JK | exact ST | exact SPA | exact HT | exact RA | exact K | exact HPR1
| apply model_vm_only_refl | idtac].
all: lazymatch goal with
| |- al_hdr _ _ _ _ _ _ _ => unfold al_hdr; exact HDR
| |- add_frame _ _ _ _ _ _ _ _ => unfold add_frame; eassumption
| |- rw_cells _ _ _ _ => exact ERR
| |- _ \/ _ => left; split; [reflexivity | split; [reflexivity | lia]]
| |- _ => clia
end.
-
if_truex.
apply evt_RZ_done.
eapply (al_add_grow HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo a arr size d ps T
_ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A junk errv);
first [exact HP1 | exact ARR | exact JK | exact ST | exact SPA | exact HT | exact RA | exact K | exact HPR1
| apply model_vm_only_refl | idtac].
all: lazymatch goal with
| |- al_hdr _ _ _ _ _ _ _ => unfold al_hdr; exact HDR
| |- add_frame _ _ _ _ _ _ _ _ => unfold add_frame; eassumption
| |- rw_cells _ _ _ _ => exact ERR
| |- _ => clia
end.
Qed.
End AlAdd2.

End RC__1.

End G.
