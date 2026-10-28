(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QCcH Q0Ek Qsw7 QJjn QQLG QnCn Q0Hd QRBl Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply Lib.GwApply2 Lib.GwApplyJ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPIU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QCcH Q0Ek Qsw7 QJjn.
Import UPIU.Mqe.
Import QQLG.Mq9.
Import QnCn.Mq0.
Import UPIU.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition aldel_code (w_39 : Z) : list Z :=
[0xfb010113; 0x04113423; 0x04813023; 0x02913c23; 0x03213823; 0x03313423; 0x03413023; 0x01513c23;
0x01613823; 0x01713423; 0x01813023; 0x00060413; 0x00050493; 0xfff64613; 0xfff00513; 0x10b66263;
0x12048863; 0x0074f613; 0x12061463; 0x0084b603; 0x0ec5f863; 0x00b40933; 0x0f266463; 0x00100993;
0x03c99993; 0x00359a93; 0x01358a33; 0x0725f463; 0x000a0b13; 0x000a8b93; 0x00040c13; 0x0140006f;
0xfffc0c13; 0x008b8b93; 0x001b0b13; 0x040c0463; 0x0004b583; 0x01758533; 0x00b03633; 0x00153693;
0x0cd60863; 0x03db5613; 0x0c061463; 0x0cb56263; 0x0c058063; 0x00bb85b3; 0x0075f593; 0x0a059a63;
0x00053503; 0xfa050ee3; 0x0184b583; 0x000580e7; 0xfb1ff06f; 0x0004b603; 0x01560533; 0x00c036b3;
0x00153593; 0x08b68663; 0x03da5593; 0x08059263; 0x08c56063; 0x00391593; 0x00b605b3; 0x0015b713;
0x06e68863; 0x013909b3; 0x03d9d693; 0x06069263; 0x06c5e063; 0x00b56633; 0x00767613; 0x04061a63;
0x0084b603; 0x41260633; 0x00361613; w_39; 0x00000513; 0x0084b583; 0x408585b3; 0x00b4b423;
0x04813083; 0x04013403; 0x03813483; 0x03013903; 0x02813983; 0x02013a03; 0x01813a83; 0x01013b03;
0x00813b83; 0x00013c03; 0x05010113; 0x00008067; 0xc0001073]%Z.

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
Hypothesis BASER : gw_br base 372.
Hypothesis D_39 : decode_any (Z_to_bv 32 w_39) = Some (Jal 1 joff_39, 4%Z).
Hypothesis E_39 : is_ecall (Z_to_bv 32 w_39) = false.
Hypothesis LINK_39 : gw_anch (base + 300 + bv_signed joff_39)%Z (e_memmove + 0)%Z.

Definition memmove_post := Eval cbv beta delta [QQLG.Mq9.memmove_post] in (@QQLG.Mq9.memmove_post segs).
Definition memmove_stmt := ltac:(let t := eval cbv beta delta [QQLG.Mq9.memmove_stmt] in (@QQLG.Mq9.memmove_stmt segs e_memmove) in let t := gw_subst t (@QQLG.Mq9.memmove_post segs) memmove_post in exact t).

Hypothesis memmove_specZ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@UPIU.Mqe.gw_all) (@UPIU.Mqe.memmove_specZ) (base + -13612)%Z)) in let T := eval cbv beta delta [UPIU.Mqe.printbuf_memappend_entry] in T in let T := gw_subst T (@QQLG.Mq9.memmove_post segs) memmove_post in let T := gw_subst T (@QQLG.Mq9.memmove_stmt segs e_memmove) memmove_stmt in let T := gw_subst T (@UPIU.Mqe.memmove_post segs) memmove_post in let T := gw_subst T (@UPIU.Mqe.memmove_stmt segs (base + -13612)%Z) memmove_stmt in let T := gw_fold_pcs T base (-13612)%Z [0; 352]%Z in exact T).

Hypothesis al_nth_null : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@UPIU.Mq0.gw_all) (@UPIU.Mq0.al_nth_null) (base + -868)%Z)) in let T := eval cbv beta delta [UPIU.Mq0.array_list_free_entry] in T in let T := gw_subst T (@QQLG.Mq9.memmove_post segs) memmove_post in let T := gw_subst T (@QQLG.Mq9.memmove_stmt segs e_memmove) memmove_stmt in let T := gw_fold_pcs T base (-868)%Z [0; 80; 144]%Z in exact T).

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
forall (k : nat) (i S6v S7v S8v : Z) (x1 x2 gp tp t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a arr len size stop : Z) (qs : list Z) (idx : Z),
Z.of_nat k = stop - 1 - i -> idx <= i < stop -> S6v = i + 2^60 -> S7v = 8 * i -> S8v = stop - i -> stop = Z.of_nat (length qs) -> stop <= len -> 8 * len < 2^64 ->
0 < arr -> arr mod 16 = 0 -> arr + 8 * len <= alloc_ceiling ->
0 <= idx -> (forall j, idx <= j < stop -> al_nth qs j = 0) ->
mem_inv segs m ->
rw_cells segs m a [C8 (Z_to_bv 64 arr); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (fn_arr_entry_free S4F))] ->
u64arr segs m arr (wl qs) ->
evt segs (fun ms => exists a1' a2' a3', ms = MS (mkR x1 x2 gp tp t0 t1 t2 x8 (Z_to_bv 64 a) (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7 x18 x19 x20 x21 (Z_to_bv 64 (stop + 2^60)) (Z_to_bv 64 (8 * stop)) (Z_to_bv 64 0) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xd4)) fc None m (seg_rom segs))
(MS (mkR x1 x2 gp tp t0 t1 t2 x8 (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 (Z_to_bv 64 S6v) (Z_to_bv 64 S7v) (Z_to_bv 64 S8v) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x90)) fc None m (seg_rom segs)).
Proof. clear - w_39 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free segs base S4F MEMMOVE. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_arr_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_arr_entry_free as gL3_; unfold gw_le in gL3_.
induction k as [|k IH]; intros until idx; intros Hk Hi HS6 HS7 HS8 Hstop Hsl H64 Harr0 Harr16 Harrhi Hidx NUL MI HDR ARR; subst S6v S7v S8v.
- pose proof (u64arr_bound segs m arr (wl qs) ARR) as AB. rewrite wl_length in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (al_slot_read segs m arr qs i (wa (arr + 8 * i)) ARR ltac:(lia) eq_refl) as RD.
rewrite (NUL i) in RD by lia.
step. step. step. step. step. QRBl.ub_cmp_auto.
step. step. QRBl.ub_cmp_auto.
step. if_falsex.
step. if_falsex.
step. step. rewrite (unsigned_lit (8 * i + arr)) by lia. rewrite (QRBl.ub_land7 (8 * i + arr)) by (Z.div_mod_to_equations; lia).
step. if_false.
step. step. if_true. step. step. step. step. if_truex.
apply evt_done. do 3 eexists. replace (stop - i + -1) with 0 by lia. replace (8 * i + 8) with (8 * stop) by lia. replace (i + 2^60 + 1) with (stop + 2^60) by lia. reflexivity.
- pose proof (u64arr_bound segs m arr (wl qs) ARR) as AB. rewrite wl_length in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (al_slot_read segs m arr qs i (wa (arr + 8 * i)) ARR ltac:(lia) eq_refl) as RD.
rewrite (NUL i) in RD by lia.
step. step. step. step. step. QRBl.ub_cmp_auto.
step. step. QRBl.ub_cmp_auto.
step. if_falsex.
step. if_falsex.
step. step. rewrite (unsigned_lit (8 * i + arr)) by lia. rewrite (QRBl.ub_land7 (8 * i + arr)) by (Z.div_mod_to_equations; lia).
step. if_false.
step. step. if_true. step. step. step. step. if_falsex.
eapply (IH (i + 1)); [ | | | | | exact Hstop | exact Hsl | exact H64 | exact Harr0 | exact Harr16 | exact Harrhi | exact Hidx | exact NUL | exact MI | exact HDR | exact ARR]; lia.
Qed.

Definition array_list_del_idx_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a arr size : Z) (ps zs : list Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (match zs with [] => 2^64 - 1 | _ => 0 end)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (a, a + AL_SZ); (arr, arr + 8 * size)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ alist segs S4F m' [(a, AL_SZ); (arr, 8 * size)] a ps.

#[using="w_39 joff_39 e_memmove gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_39 E_39 LINK_39 memmove_specZ al_nth_null LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free MEMMOVE"] Lemma array_list_del_idx_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a arr size : Z) (ps zs : list Z) (lo : Z),
mem_inv segs m ->
alist segs S4F m [(a, AL_SZ); (arr, 8 * size)] a (ps ++ zs) ->
(forall b n, In (b, n) [(a, AL_SZ); (arr, 8 * size)] -> 0 < b /\ b mod 16 = 0 /\ b + n <= alloc_ceiling) ->
Forall (fun p => p = 0) zs ->
(a + AL_SZ <= arr \/ arr + 8 * size <= a) ->
stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 ->
a + AL_SZ <= lo -> arr + 8 * size <= lo ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 (Z.of_nat (length ps)) -> a2 = Z_to_bv 64 (Z.of_nat (length zs)) ->
evt segs (array_list_del_idx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a arr size ps zs lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_del_idx_entry) fc None m (seg_rom segs)).
Proof. clear - w_39 joff_39 e_memmove gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_39 E_39 LINK_39 memmove_specZ al_nth_null LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free MEMMOVE segs S4F. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_arr_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_arr_entry_free as gL3_; unfold gw_le in gL3_.
intros until lo. intros MI AL HBS NUL SEP ST LOS ALO ARRLO A0 A1 A2.
destruct (alist_openx segs S4F m a arr size (ps ++ zs) AL) as (junk & HDR & ARR & JK & Hlen & Hsz).
destruct (HBS a AL_SZ ltac:(left; reflexivity)) as (Ha0 & Ha16 & Hahi).
destruct (HBS arr (8 * size) ltac:(right; left; reflexivity)) as (Harr0 & Harr16 & Harrhi). clear HBS.
unfold al_hdr in HDR. unfold al_tail in JK.
pose proof (length_app ps zs) as LA. apply (f_equal Z.of_nat) in LA. rewrite Nat2Z.inj_add in LA. rewrite LA in HDR.
pose proof (u64arr_bound segs m arr (wl (ps ++ zs)) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length (ps ++ zs)) as WL.
pose proof (rw_cells_bound segs m a _ HDR) as HB. cbn [cells_size csize Nat.add] in HB.
word_range sp SPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (a, a + AL_SZ); (arr, arr + 8 * size)] m) as MU.
unfold array_list_del_idx_entry, array_list_del_idx_post. subst a0 a1 a2.
carve_frame 80%nat ST.
do 11 step.
step. step. step.
unfold v_xori. rewrite (unsigned_lit (Z.of_nat (length zs))) by lia. change (bv_wrap 64 (-1)) with 18446744073709551615.
rewrite lxor_ones64 by lia.
step. step. if_falsex.
step. if_falsex. step. step. ubsan_align Ha16.
step.
destruct zs as [|z zs'].
-
change (Z.of_nat (@length Z [])) with 0 in *. rewrite app_nil_r in *. rewrite Z.add_0_r in *. clear LA.
step. if_truex.
do 12 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
eapply alist_close. split; [exact HDR | split; [exact ARR | split; [exact JK | lia]]].
- assert (LZ : 1 <= Z.of_nat (length (z :: zs'))) by (cbn [length]; lia).
step. if_falsex. step. step. if_falsex.
step. step. step. step. rewrite (unsigned_lit (Z.of_nat (length ps))) by lia. rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length ps)) 3) by lia. change (2^3) with 8.
step. if_falsex. step. step. step. step.
eapply evt_cut.
{ eapply al_del_loop with (k := Z.to_nat (Z.of_nat (length (z :: zs')) - 1)) (i := Z.of_nat (length ps))
(a := a) (arr := arr) (len := Z.of_nat (length ps) + Z.of_nat (length (z :: zs'))) (size := size)
(stop := Z.of_nat (length (z :: zs')) + Z.of_nat (length ps)) (qs := ps ++ z :: zs') (idx := Z.of_nat (length ps));
[ | | | | | lia | lia | lia | exact Harr0 | exact Harr16 | lia | lia | | exact MI | exact HDR | exact ARR].
- lia.
- lia.
- lia.
- lia.
- lia.
- intros j Hj. apply al_nth_app_r; [lia | exact NUL]. }
intros ms' (a1' & a2' & a3' & ->).

destruct (al_tail_absorb segs m1 arr size ps (z :: zs') junk ARR JK ltac:(lia)) as [ARR1 TL]. clear ARR JK.
unfold al_tail in TL.
pose proof (wl_length ps) as WL1.
step. step. step. step. step. QRBl.ub_cmp_auto.
step. step. QRBl.ub_cmp_auto.
step. if_falsex.
step. step. step. step. rewrite (unsigned_lit (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps))) by lia.
rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps)) 3) by lia. change (2^3) with 8.
QRBl.ub_cmp_auto.
step. step. step. QRBl.ub_cmp_auto.
step. if_falsex.
step. step. step.
assert (AL71 : Z.land (Z.lor (arr + Z.of_nat (length ps) * 8) (arr + (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps)) * 8)) 7 = 0).
{ rewrite zb_land_lor_distr_l, !QRBl.ub_land7 by (Z.div_mod_to_equations; lia). reflexivity. }
rewrite (unsigned_lit (arr + Z.of_nat (length ps) * 8)) by lia.
rewrite (unsigned_lit (arr + (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps)) * 8)) by lia.
rewrite (unsigned_lit (Z.lor (arr + Z.of_nat (length ps) * 8) (arr + (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps)) * 8))) by (apply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; lia).
rewrite AL71. if_false.
step. step. step. step.
rewrite (unsigned_lit (Z.of_nat (length ps) + Z.of_nat (length (z :: zs')))) by lia.
rewrite (unsigned_lit (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps))) by lia.
replace (Z.of_nat (length ps) + Z.of_nat (length (z :: zs')) - (Z.of_nat (length (z :: zs')) + Z.of_nat (length ps))) with 0 by lia.
change (Z.shiftl (bv_unsigned (Z_to_bv 64 0)) 3) with 0.

assert (DST : rw_cells segs m1 (arr + Z.of_nat (length ps) * 8) [CB 0%nat []]).
{ split; [split; [cbn; auto | cbn; apply bytes_at_nil; lia] | cbn; split; [lia | split; [lia | intros i Hi; lia]]]. }
call (memmove_specZ MEMMOVE); [lia | lia | lia | apply bytes_at_nil; lia | reflexivity | exact DST | exact MI |].
step. step.
step. rewrite !unsigned_lit by lia.
replace (Z.of_nat (length ps) + Z.of_nat (length (z :: zs')) - Z.of_nat (length (z :: zs'))) with (Z.of_nat (length ps)) by lia.
step.
do 12 step.
apply evt_done. do 15 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split. { lazymatch goal with |- stk _ ?mf _ _ => match goal with FRx : rw_cells segs mf (bv_unsigned sp + -80) _, STx : stk segs mf _ _ |- _ =>
release_frame FRx STx (bv_unsigned sp); exact STx end end. }
eapply alist_close. split; [| split; [eassumption | split; [eassumption | lia]]]. unfold al_hdr. eassumption.
Qed.
End AlDel.

End G.
End Mq0.
