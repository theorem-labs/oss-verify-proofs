(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg Qc3B QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj QSL3 Q9Mh QAyu Q7mx QH1t QPIU Q6q3 Q3CA Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply Lib.GwApply2 Lib.GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QSL3.
Import Q9Mh.Mq4.
Import QAyu.Mq2.
Import Q7mx.
Import QH1t.
Import QPIU.Mqh.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q3CA.
Import Q0Hd.

Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition lhdelete_code : list Z :=
[0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x01613023; 0x00058413; 0x00050493; 0x01053903; 0xffd00993; 0xffe00a13; 0x0184b583; 0x40b90b33; 0xfff00513; 0x0a0b4a63; 0x01658633; 0x00063603; 0x0ac9e463; 0x0044a503; 0x0204b603; 0x02093a83; 0xfff50513; 0x00a4a223; 0x00060863; 0x00090513; 0x000600e7; 0x0184b583; 0x0104b683; 0x0084b603; 0x01658533; 0x01453023; 0x00053823; 0x00a68e63; 0x02a60663; 0x01853583; 0x02053603; 0x00b63c23; 0x02c5b023; 0x0300006f; 0x02a60263; 0x0206b583; 0x0005bc23; 0x00b4b823; 0x01c0006f; 0x01863583; 0x0205b023; 0x00b4b423; 0x00c0006f; 0x0004b423; 0x0004b823; 0x00053c23; 0x02053023; 0x00090593; 0x00890463; 0x000a8593; 0x00000513; 0x00890663; 0x00058913; 0xf40592e3; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x00013b03; 0x04010113; 0x00008067]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
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
Variables (JG_CGT_P gRDATA_LO : Z).
Let vdso_ok4 : Z -> Prop := fun vf => (vf = JG_CGT_P \/ vf = 0)%Z.
Hypothesis CODE : code_at segs base lhdelete_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 288.
Hypothesis RNG_GGOT4 : gw_br GGOT4 8.
Hypothesis AL_GGOT4 : gw_al GGOT4 8.
Hypothesis RNG_GHASH4 : gw_br GHASH4 8.
Hypothesis AL_GHASH4 : gw_al GHASH4 8.
Hypothesis RNG_GVDSO4 : gw_br GVDSO4 8.
Hypothesis AL_GVDSO4 : gw_al GVDSO4 8.
Hypothesis LAY_GGOT4_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASH4_GVDSO4 : gw_le (GHASH4 + 8) GVDSO4.

Hypothesis lh_glob_client : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@Q9Mh.Mq4.gw_all) (@Q9Mh.Mq4.lh_glob_client) (base + -1244)%Z)) in let T := eval cbv beta delta [Q9Mh.Mq4.lh_kchar_table_new_entry] in T in let T := gw_fold_pcs T base (-1244)%Z [0; 136; 148]%Z in exact T).

Hypothesis lh_entry_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QAyu.Mq2.gw_all) (@QAyu.Mq2.lh_entry_free_cps) (base + -316)%Z)) in let T := eval cbv beta delta [QAyu.Mq2.lh_entry_free_entry QAyu.Mq2.lh_table_free_entry] in T in let T := gw_fold_pcs T base (-316)%Z [0; 36; 56]%Z in exact T).

Let e_blk_18934 : Z := base.
Definition lh_delete_tail_post2 := ltac:(let t := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_post2))) in let t := eval cbv beta delta [QPIU.Mqh.lh_delete_tail_post2] in t in let t := eval cbv delta [e_blk_18934] in t in exact t).
Definition lh_delete_tail_stmt2 := ltac:(let t := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := eval cbv beta delta [QPIU.Mqh.lh_delete_tail_stmt2] in t in let t := eval cbv delta [e_blk_18934] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_post2))) in let t := gw_subst t x lh_delete_tail_post2 in exact t).

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
Hypothesis AL_e_fn_lh_entry_free : gw_b4 e_fn_lh_entry_free.
Hypothesis RNG_e_fn_lh_entry_free : gw_br e_fn_lh_entry_free 4.
Hypothesis CS_GHASH4 : forall a, (GHASH4 <= a < GHASH4 + 12)%Z -> gCS a.
Hypothesis CS_GGOT4 : forall a, (GGOT4 <= a < GGOT4 + 8)%Z -> gCS a.
Hypothesis CS_GVDSO4 : forall a, (GVDSO4 <= a < GVDSO4 + 8)%Z -> gCS a.
Hypothesis LAY_RDATA_GGOT4 : gw_le gRDATA_LO GGOT4.
Hypothesis LAY_GHASH4x12_GVDSO4 : gw_le (GHASH4 + 12) GVDSO4.
Hypothesis LAY_IMG_GGOT4 : gw_le gIMG_LO GGOT4.
Hypothesis LAY_GVDSO4_IMG : gw_le (GVDSO4 + 8) gIMG_HI.
Hypothesis LAY_POS_e_fn_lh_entry_free : gw_le 1 e_fn_lh_entry_free.
Hypothesis LAY_HI_e_fn_lh_entry_free : gw_le (e_fn_lh_entry_free + 4) 1099511627776.
#[using="GGOT4 GHASH4 GVDSO4 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free JG_CGT_P gRDATA_LO CODE BASE4 BASER RNG_GGOT4 AL_GGOT4 RNG_GHASH4 AL_GHASH4 RNG_GVDSO4 AL_GVDSO4 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_glob_client lh_entry_free_cps AL_e_fn_lh_entry_free RNG_e_fn_lh_entry_free CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.
Local Tactic Notation "gj_rv" ident(h) := try revert h.
Ltac gj_keep_lay := gj_rv gLAYF_; gj_rv gL0_; gj_rv gL1_; gj_rv gL2_; gj_rv gL3_; gj_rv gL4_; gj_rv gL5_; gj_rv gL6_; gj_rv gL7_; gj_rv gL8_; gj_rv gL9_.
Ltac gj_intro_lay := repeat lazymatch goal with |- ((_ <= _)%Z -> _) => intro | |- ((_ /\ _) -> _) => intro end.

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

Definition lh_delete_tail_entry : Z := (base + 0x0).

Definition del_slot (s : slotv) : slotv := SV LH_FREEDv (sv_kc s) (sv_pad s) 0 0 0.
Definition clr_nx (s : slotv) : slotv := SV (sv_k s) (sv_kc s) (sv_pad s) (sv_v s) 0 (sv_pv s).

#[using="Type"] Lemma snoc_inv : forall (l : list lent), l = [] \/ exists l' x, l = l' ++ [x].
Proof. clear - segs.
intros l. destruct l as [|y l']; [left; reflexivity|]. right.
exists (removelast (y :: l')), (last (y :: l') y). apply app_removelast_last. discriminate.
Qed.

#[using="base"] Lemma firstn_snoc_le : forall (A : Type) (l : list A) x n, (n <= length l)%nat -> firstn n (l ++ [x]) = firstn n l.
Proof. clear - base. intros A l x n H. rewrite firstn_app. replace (n - length l)%nat with 0%nat by klia. cbn. apply app_nil_r. Qed.

#[using="base"] Lemma pv_of_snoc2 : forall tbl es1 el e, pv_of tbl ((es1 ++ [el]) ++ [e]) (length (es1 ++ [el])) = ent_addr tbl (le_ix el).
Proof. clear - base.
intros. rewrite pv_of_app_le by klia. unfold pv_of. rewrite length_app. cbn [length]. rewrite Nat.add_1_r.
rewrite nth_error_app2, Nat.sub_diag by klia. reflexivity.
Qed.
#[using="Type"] Lemma perm_key_front : forall t tbl size es0 e LB,
Permutation (lh_blocks t tbl size (es0 ++ [e]) ++ LB) (kblk e :: lh_blocks t tbl size es0 ++ LB).
Proof. clear - segs.
intros. unfold lh_blocks, kblk. rewrite map_app.
apply (Permutation_trans (l' := ((le_k e, le_kn e) :: (t, 56) :: (tbl, 40 * size) :: map (fun e0 => (le_k e0, le_kn e0)) es0) ++ LB)); [| apply Permutation_refl].
apply Permutation_app_tail. apply Permutation_sym. apply (Permutation_cons_append ((t, 56) :: (tbl, 40 * size) :: map _ es0)).
Qed.

Section Unsnoc.
Variables (tbl : Z) (es0 : list lent) (e : lent) (svs : list slotv) (se : slotv).
Hypothesis LINK : lh_link tbl (es0 ++ [e]) svs.
Hypothesis Ese : nth_error svs (le_ix e) = Some se.

#[using="LINK Ese"] Lemma lh_link_unsnoc_nil : es0 = [] -> lh_link tbl [] (upd svs (le_ix e) (del_slot se)).
Proof. clear - LINK Ese tbl es0 e svs se.
intros E0. rewrite E0 in LINK. destruct LINK as (LK1 & LK2 & LK3 & LK4).
pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Ese; discriminate)) as Hix.
split; [intros j x E; destruct j; discriminate|]. split; [| split; [constructor | intros x []]].
intros i s E _. destruct (Nat.eq_dec i (le_ix e)) as [->|NE].
- rewrite nth_error_upd_same in E by exact Hix. injection E as <-. right. reflexivity.
- rewrite nth_error_upd_other in E by (intros X; apply NE; symmetry; exact X). apply (LK2 i s E).
cbn. intros [X|[]]. apply NE. symmetry; exact X.
Qed.

#[using="base LINK Ese"] Lemma lh_link_unsnoc_cons : forall es1 el sl,
es0 = es1 ++ [el] -> nth_error svs (le_ix el) = Some sl ->
lh_link tbl es0 (upd (upd svs (le_ix e) (del_slot se)) (le_ix el) (clr_nx sl)).
Proof. clear - base LINK Ese tbl es0 e svs se.
intros es1 el sl E0 Esl. destruct LINK as (LK1 & LK2 & LK3 & LK4).
pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Ese; discriminate)) as Hix.
pose proof (proj1 (nth_error_Some svs (le_ix el)) ltac:(rewrite Esl; discriminate)) as Hixl.
assert (L0 : length es0 = S (length es1)) by (rewrite E0, length_app; cbn; klia).
assert (Eel : nth_error (es0 ++ [e]) (length es1) = Some el) by (rewrite E0, <- app_assoc; cbn; rewrite nth_error_app2, Nat.sub_diag by klia; reflexivity).
assert (Ee : nth_error (es0 ++ [e]) (length es0) = Some e) by (rewrite nth_error_app2, Nat.sub_diag by klia; reflexivity).
assert (IXNE : forall j1 j2 x1 x2, nth_error (es0 ++ [e]) j1 = Some x1 -> nth_error (es0 ++ [e]) j2 = Some x2 -> j1 <> j2 -> le_ix x1 <> le_ix x2).
{ intros j1 j2 x1 x2 H1 H2 NE X. apply NE. eapply (proj1 (NoDup_nth_error _) LK3 j1 j2).
- rewrite length_map. apply (proj1 (nth_error_Some _ j1)). rewrite H1; discriminate.
- erewrite nth_error_map, H1, nth_error_map, H2. cbn. rewrite X. reflexivity. }
pose proof (IXNE _ _ _ _ Eel Ee ltac:(klia)) as NEle.
split; [| split; [| split]].
- intros j x E.
pose proof (proj1 (nth_error_Some es0 j) ltac:(rewrite E; discriminate)) as Hj.
assert (E' : nth_error (es0 ++ [e]) j = Some x) by (rewrite nth_error_app1 by klia; exact E).
destruct (LK1 j x E') as (s & Es & A1 & A2 & A3 & A4 & A5).
pose proof (IXNE _ _ _ _ E' Ee ltac:(klia)) as NExe.
destruct (Nat.eq_dec j (length es1)) as [-> | NEj].
+
rewrite Eel in E'. injection E' as <-. rewrite Esl in Es. injection Es as <-.
exists (clr_nx sl). rewrite nth_error_upd_same by (rewrite upd_length; exact Hixl). split; [reflexivity|].
cbn [clr_nx sv_k sv_kc sv_v sv_nx sv_pv]. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split.
* symmetry. apply nx_of_last. klia.
* rewrite A5. apply pv_of_app_le. klia.
+
pose proof (IXNE _ _ _ _ E' Eel NEj) as NExl.
exists s. rewrite nth_error_upd_other by (intros X; apply NExl; symmetry; exact X).
rewrite nth_error_upd_other by (intros X; apply NExe; symmetry; exact X).
split; [exact Es|]. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split.
* rewrite A4. apply nx_of_app_lt. klia.
* rewrite A5. apply pv_of_app_le. klia.
- intros i s E NI.
assert (NE1 : i <> le_ix el) by (intros ->; apply NI; rewrite E0, map_app; apply in_or_app; right; left; reflexivity).
rewrite nth_error_upd_other in E by (intros X; apply NE1; symmetry; exact X).
destruct (Nat.eq_dec i (le_ix e)) as [->|NE2].
+ rewrite nth_error_upd_same in E by exact Hix. injection E as <-. right. reflexivity.
+ rewrite nth_error_upd_other in E by (intros X; apply NE2; symmetry; exact X). apply (LK2 i s E).
rewrite map_app. intros X. apply in_app_iff in X as [X | [X | []]]; [exact (NI X) | exact (NE2 (eq_sym X))].
- rewrite map_app in LK3. exact (NoDup_app_remove_r _ _ LK3).
- intros x Hx. apply LK4. apply in_or_app. left. exact Hx.
Qed.
End Unsnoc.

Section LhDelete.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation lh_glob4 := (lh_glob segs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).

#[using="GGOT4 GHASH4 GVDSO4 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_entry_free gRDATA_LO LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma lh_writes_pres : forall A t tbl size es LB m md m' W SP,
HEAPx A (lh_blocks t tbl size es ++ LB) m md -> munch W m m' -> wmono segs m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP) \/ (t <= fst iv /\ snd iv <= t + 56) \/ (tbl <= fst iv /\ snd iv <= tbl + 40 * size)) W ->
alloc_ceiling <= SP ->
heap_pres S4L LB SP m m'.
Proof. clear - GGOT4 GHASH4 GVDSO4 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_entry_free gRDATA_LO LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free segs HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_RDATA_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GHASH4x12_GVDSO4 as gL5_; unfold gw_le in gL5_. pose proof LAY_IMG_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GVDSO4_IMG as gL7_; unfold gw_le in gL7_. pose proof LAY_POS_e_fn_lh_entry_free as gL8_; unfold gw_le in gL8_. pose proof LAY_HI_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_.
intros A t tbl size es LB m md m' W SP HP MU WM HW HSP.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
eapply (heap_pres_of_munch S4L LB SP); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; exact Hb | exact HSP |].
(gj_keep_lay; clear - HW ND; gj_intro_lay). induction W as [|[a b] W IH]; [apply Forall_nil|].
apply Forall_cons_iff in HW as [H1 HW]. apply Forall_cons; [| apply IH; exact HW]. cbn [fst snd] in *.
destruct H1 as [H1 | [H1 | H1]].
- left. exact H1.
- right; left. exists t, 56. split; [left; reflexivity|]. split; [| klia].
intros IN. eapply (nodup_prefix_suffix (lh_blocks t tbl size es) LB t 56 56); [exact ND | left; reflexivity | exact IN].
- right; left. exists tbl, (40 * size). split; [right; left; reflexivity|]. split; [| klia].
intros IN. eapply (nodup_prefix_suffix (lh_blocks t tbl size es) LB tbl (40 * size) (40 * size)); [exact ND | right; left; reflexivity | exact IN].
Qed.

Section DelLoop.
Variables (sp gp : word) (s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo t tbl size : Z) (jf : nat) (ef : lent) (T : TSet).
Variables (rac s0c s1c s2c s3c s4c s5c s6c : word).
Variable errv : word.

Variable GI : (word -> option byte) -> Prop.
Hypothesis GI_munch : forall m m' W, GI m -> munch W m m' -> wmono segs m m' -> Forall (fun iv => gIMG_HI <= fst iv \/ snd iv <= 0x10000) W -> GI m'.
Hypothesis GI_pres : forall m m' LB' SP, heap_pres S4L LB' SP m m' -> GI m -> GI m'.

Definition del_frame (m : word -> option byte) : Prop :=
rw_cells segs m (bv_unsigned sp + -64) [C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

Definition del_exit (esf : list lent) : Prop :=
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x21 x22 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (svsf : list slotv),
HEAPx A (lh_blocks t tbl size esf ++ LB) m md ->
lh_open segs S4F m t tbl size esf svsf -> GI m ->
stk segs m lo (bv_unsigned sp + -64) -> del_frame m ->
rw_cells segs m (gTP - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 (ent_addr tbl (le_ix ef))) (Z_to_bv 64 t)
(Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 (-3)) (Z_to_bv 64 (-2)) x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xf8)) fc None m (seg_rom segs)) md) T.

#[using="GGOT4 GHASH4 GVDSO4 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_entry_free_cps AL_e_fn_lh_entry_free RNG_e_fn_lh_entry_free LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free GI_munch GI_pres"] Lemma lh_del_loop :
forall (d : nat) (es0 : list lent) (e : lent) (svs : list slotv)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx),
(d = length es0 - jf)%nat -> (jf <= length es0)%nat -> nth_error (es0 ++ [e]) jf = Some ef ->
HEAPx A (lh_blocks t tbl size (es0 ++ [e]) ++ LB) m md ->
lh_open segs S4F m t tbl size (es0 ++ [e]) svs ->
(forall j x, (jf <= j)%nat -> nth_error (es0 ++ [e]) j = Some x -> le_v x = 0) ->
GI m ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
del_frame m -> rw_cells segs m (gTP - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
del_exit (firstn jf es0) ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 (ent_addr tbl (le_ix ef))) (Z_to_bv 64 t)
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ent_addr tbl (le_ix e))) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-2)) x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x38)) fc None m (seg_rom segs)) md) T.
Proof. clear - GGOT4 GHASH4 GVDSO4 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_entry_free_cps AL_e_fn_lh_entry_free RNG_e_fn_lh_entry_free LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free GI_munch GI_pres segs base gTP S4F HIx sp gp s7 s8 s9 s10 s11 F fc m0 md0 LB lo t tbl size jf ef T rac s0c s1c s2c s3c s4c s5c s6c errv GI. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_RDATA_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GHASH4x12_GVDSO4 as gL5_; unfold gw_le in gL5_. pose proof LAY_IMG_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GVDSO4_IMG as gL7_; unfold gw_le in gL7_. pose proof LAY_POS_e_fn_lh_entry_free as gL8_; unfold gw_le in gL8_. pose proof LAY_HI_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_.
induction d as [|d IH]; intros until A; intros Hd Hjf Hef HP OPEN VZ G ST LO LOS SPA HT FR ERR VM0 HPR KX.
all: pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen); unfold lh_hdr, lh_hdrf in HDR.
all: rewrite tl_of_app in HDR.
all: pose proof LINK as (LK1 & LK2 & LK3 & LK4).
all: assert (Ee : nth_error (es0 ++ [e]) (length es0) = Some e) by (rewrite nth_error_app2, Nat.sub_diag by klia; reflexivity).
all: destruct (LK1 (length es0) e Ee) as (se & Ese & Ek & Ekc & Ev & Enx & Epv).
all: pose proof (SL (le_ix e) se Ese) as C; unfold slot_cells in C; rewrite Ek, Ekc, Ev, Enx, Epv in C.
all: rewrite (VZ (length es0) e ltac:(klia) Ee) in C; rewrite (nx_of_app_new tbl es0 e (length es0) eq_refl) in C.
all: pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Ese; discriminate)) as Hix.
all: destruct (LK1 jf ef Hef) as (sf & Esf & _); pose proof (proj1 (nth_error_Some svs (le_ix ef)) ltac:(rewrite Esf; discriminate)) as Hixf; clear sf Esf.
all: destruct (LK4 e ltac:(apply in_or_app; right; left; reflexivity)) as (Hk0 & HkF & Hkn31 & Hv).
all: unfold del_frame in FR; unfold_consts; word_range sp SPR.
all: pose proof (lf_thr_lt size Hsz) as Hlt; pose proof (lf_size_range size Hsz) as HSR.
all: assert (LEN : Z.of_nat (length (es0 ++ [e])) = Z.of_nat (length es0) + 1) by (rewrite length_app; cbn; klia); rewrite LEN in HDR, Hcnt.
all: pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK; pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI; cbn [hl_segs S4L] in MI.
all: destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
all: cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg; unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
all: destruct (KF e ltac:(apply in_or_app; right; left; reflexivity)) as (Hkn0 & _ & Hkhi & Hkimg & DKt & DKb); cbn [hl_img_lo hl_img_hi S4L] in Hkimg.
all: stash Hkimg; stash DKt; stash DKb.
all: assert (IXNE : forall j1 j2 y1 y2, nth_error (es0 ++ [e]) j1 = Some y1 -> nth_error (es0 ++ [e]) j2 = Some y2 -> j1 <> j2 -> le_ix y1 <> le_ix y2) by
(intros j1 j2 y1 y2 H1 H2 NE X; apply NE; eapply (proj1 (NoDup_nth_error _) LK3 j1 j2);
[ rewrite length_map; apply (proj1 (nth_error_Some _ j1)); rewrite H1; discriminate
| erewrite nth_error_map, H1, nth_error_map, H2; cbn; rewrite X; reflexivity ]).
all: assert (HPk : HEAPx A ((le_k e, le_kn e) :: (t, 56) :: (tbl, 40 * size) :: (map kblk es0 ++ LB)) m md) by (eapply heap_perm; [exact HP | apply perm_key_front]).

all: destruct (snoc_inv es0) as [E0 | (es1 & el & E0)]; [| destruct (LK1 (length es1) el ltac:(rewrite E0, <- app_assoc; cbn; rewrite nth_error_app2, Nat.sub_diag by klia; reflexivity)) as (sl & Esl & Elk & Elkc & Elv & Elnx & Elpv)].
3:{ exfalso. subst es0. cbn in Hd. klia. }

all: try (pose proof (SL (le_ix el) sl Esl) as Cl; unfold slot_cells in Cl; rewrite Elk, Elkc, Elv, Elnx, Elpv in Cl;
pose proof (proj1 (nth_error_Some svs (le_ix el)) ltac:(rewrite Esl; discriminate)) as Hixl;
assert (L0 : length es0 = S (length es1)) by (rewrite E0, length_app; cbn; (clear; lia));
assert (NXl : nx_of tbl (es0 ++ [e]) (length es1) = ent_addr tbl (le_ix e)) by (unfold nx_of; rewrite <- L0, Ee; reflexivity); rewrite NXl in Cl;
assert (PV : pv_of tbl (es0 ++ [e]) (length es0) = ent_addr tbl (le_ix el)) by (rewrite E0; apply pv_of_snoc2); rewrite PV in C;
assert (NEl : le_ix el <> le_ix e) by
(eapply (IXNE (length es1) (length es0)); [rewrite E0, <- app_assoc; cbn; rewrite nth_error_app2, Nat.sub_diag by (clear; lia); reflexivity | exact Ee | ((gj_keep_lay; clear - L0; gj_intro_lay); lia)]);
destruct (nth_error es0 0) as [x0|] eqn:Ex0; [| exfalso; apply nth_error_None in Ex0; ((gj_keep_lay; clear - L0 Ex0 Hd; gj_intro_lay); lia)];
assert (HD0 : hd_of tbl (es0 ++ [e]) = ent_addr tbl (le_ix x0)) by (rewrite hd_of_nth, nth_error_app1, Ex0 by ((gj_keep_lay; clear - L0 Hd; gj_intro_lay); lia); reflexivity);
assert (NE0 : le_ix x0 <> le_ix e) by (eapply (IXNE 0%nat (length es0)); [rewrite nth_error_app1 by ((gj_keep_lay; clear - L0 Hd; gj_intro_lay); lia); exact Ex0 | exact Ee | ((gj_keep_lay; clear - L0 Hd; gj_intro_lay); lia)]);
destruct (LK1 0%nat x0 ltac:(rewrite nth_error_app1 by ((gj_keep_lay; clear - L0 Hd; gj_intro_lay); lia); exact Ex0)) as (sx0 & Esx0 & _);
pose proof (proj1 (nth_error_Some svs (le_ix x0)) ltac:(rewrite Esx0; discriminate)) as Hix0;
rewrite HD0 in HDR;
destruct (KF el ltac:(rewrite E0; apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as (_ & Hlklo & Hlkhi & _ & DKlt & DKlb);
stash DKlt; stash DKlb).
1: replace (pv_of tbl (es0 ++ [e]) (length es0)) with 0 in C by (rewrite E0; reflexivity);
replace (hd_of tbl (es0 ++ [e])) with (ent_addr tbl (le_ix e)) in HDR by (rewrite E0; reflexivity);
rewrite E0 in Hef, Hjf; cbn [app] in Hef; cbn in Hjf; assert (Hjf0 : jf = 0%nat) by klia;
rewrite Hjf0 in Hef; cbn in Hef; injection Hef as Eef.
2,3: remember (pv_of tbl (es0 ++ [e]) (length es1)) as PVl eqn:EPVl.
all: remember (ent_addr tbl (le_ix e)) as B eqn:EB.
all: assert (HB : B = tbl + 40 * Z.of_nat (le_ix e)) by (rewrite EB; reflexivity).
all: try (remember (ent_addr tbl (le_ix el)) as Bl eqn:EBl; assert (HBl : Bl = tbl + 40 * Z.of_nat (le_ix el)) by (rewrite EBl; reflexivity)).
all: pose proof (wmono_refl segs m) as WM; pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (t, t + 56)] m) as MU.
all: apply rz_evt; [exact MOK|].
all: step; step; step.
all: rewrite (unsigned_lit B), (unsigned_lit tbl) by klia.
all: step; if_falsex.
all: step. all: replace (tbl + (B - tbl)) with B by klia.
all: step. all: step.
all: replace (bv_ltu (Z_to_bv 64 (-3)) (Z_to_bv 64 (le_k e))) with false by
(symmetry; unfold bv_ltu; rewrite (unsigned_lit (le_k e)) by (unfold LH_FREEDv in *; klia);
replace (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613 by (vm_compute; reflexivity);
apply Z.ltb_ge; unfold LH_FREEDv in *; klia).
all: cbv iota.
all: step; norm_sx32; step; step; step; step.
all: step; if_false. all: step; step.

all: cbn [fn_lh_entry_free S4F]; gw_ret_pc_var_tac.
all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SLx : lh_slots segs mx tbl svs) by
(eapply lh_slots_frame; [exact SL | exact MU | exact WM |]; intros i Hi; rewrite <- Hlen in Hbhi, SEP;
apply Forall_cons; [cbn; unfold ent_addr; ((gj_keep_lay; clear - LO LOS Hbhi Hi; gj_intro_lay); lia) | apply Forall_cons; [cbn; unfold ent_addr; ((gj_keep_lay; clear - SEP Hi; gj_intro_lay); lia) | apply Forall_nil]]);
assert (KEYSx : lh_keys segs mx es0) by
(eapply lh_keys_frame; [unfold lh_keys in KEYS |- *; apply Forall_app in KEYS as [K0 _]; exact K0 | exact MU | exact WM |];
intros y Hy; destruct (KF y ltac:(apply in_or_app; left; exact Hy)) as (? & ? & ? & ? & ? & ?);
apply Forall_cons; [cbn; ((gj_keep_lay; clear - LO LOS H1; gj_intro_lay); lia) | apply Forall_cons; [cbn; ((gj_keep_lay; clear - H3; gj_intro_lay); lia) | apply Forall_nil]]);
assert (Gx : GI mx) by
(eapply (GI_munch m mx); [exact G | exact MU | exact WM | apply Forall_cons; [cbn; ((gj_keep_lay; clear - LO LOS; gj_intro_lay); lia) | apply Forall_cons; [cbn; ((gj_keep_lay; clear - Htimg; gj_intro_lay); lia) | apply Forall_nil]]]);
assert (HPRx : heap_pres S4L LB (bv_unsigned sp) m mx) by
(eapply (lh_writes_pres A t tbl size (es0 ++ [e]) LB m md mx); [exact HP | exact MU | exact WM | | ((gj_keep_lay; clear - LO LOS; gj_intro_lay); clia)];
apply Forall_cons; [cbn; left; ((gj_keep_lay; clear - LO LOS; gj_intro_lay); clia) | apply Forall_cons; [cbn; right; left; (clear; lia) | apply Forall_nil]])
end.
all: apply evt_RZ_done;
eapply (lh_entry_free_cps HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ md T A (lh_blocks t tbl size es0 ++ LB)
B (le_k e) (le_kn e) (sv_pad se) 0 _ lo errv);
[ heap_now S4L HIx HPk MU WM MI | exact C | ..]; try alloc_side.
all: try (destruct Hbimg; [left; klia | right; klia]).
all: intros ms2 md2 (m2 & A2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
all: destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->); cbn [hl_segs S4L] in *.
all: rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST2, HPR2 by klia.
all: apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; klia]; cbn [hl_segs S4L] in FR.
all: apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | klia | cbn; klia]]; cbn [hl_segs S4L] in HDR.
all: apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in C; [| eapply client_range_block; [right; left; reflexivity | klia | cbn; klia]]; cbn [hl_segs S4L] in C.
all: try (apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in Cl; [| eapply client_range_block; [right; left; reflexivity | klia | cbn; klia]]; cbn [hl_segs S4L] in Cl).
all: pose proof (lh_slots_pres S4L _ _ _ _ tbl svs size HPR2 ltac:(right; left; reflexivity) Hlen SLx) as SL2; cbn [hl_segs S4L] in SL2.
all: pose proof (lh_keys_pres S4L _ _ _ _ es0 HPR2 ltac:(intros y Hy; apply in_or_app; left; unfold lh_blocks; right; right; apply in_map_iff; exists y; split; [reflexivity | exact Hy]) KEYSx) as KEYS2; cbn [hl_segs S4L] in KEYS2.
all: pose proof (GI_pres _ _ _ _ HPR2 Gx) as G2.
all: assert (HPR' : heap_pres S4L LB (bv_unsigned sp) m0 m2) by
(eapply heap_pres_trans; [exact HPR|]; eapply heap_pres_trans; [exact HPRx|]; eapply heap_pres_weaken; [exact HPR2 | klia | intros b Hb; apply in_or_app; right; exact Hb]).
all: clear MU WM MI SLx KEYSx Gx HPRx HPk.
all: pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2; pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI; cbn [hl_segs S4L] in MI.
all: pose proof (wmono_refl segs m2) as WM.
1: pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (t, t + 56); (B, B + 40)] m2) as MU.
2,3: pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (t, t + 56); (B, B + 40); (Bl, Bl + 40)] m2) as MU.
all: pose proof HP2 as HP2n; change (lh_blocks t tbl size es0 ++ LB) with ((t, 56) :: (tbl, 40 * size) :: (map kblk es0 ++ LB)) in HP2n.
all: reenter MOK2.
all: step; step; step; step. all: replace (tbl + (B - tbl)) with B by klia.
all: stepz. all: stepz.
all: step.
all: replace (bv_eqb (Z_to_bv 64 B) (Z_to_bv 64 B)) with true by (symmetry; apply bv_eqb_refl); cbv iota.
all: step.
1: replace (bv_eqb (Z_to_bv 64 B) (Z_to_bv 64 B)) with true by (symmetry; apply bv_eqb_refl); cbv iota.
2,3: unfold ent_addr; if_falsex; change (tbl + 40 * Z.of_nat (le_ix ef)) with (ent_addr tbl (le_ix ef)).

1: stepz; stepz.
2,3: step; stepz; step; step.
all: stepz; stepz; step; step.
2: assert (Eef : e = ef) by (replace jf with (length es0) in Hef by klia; rewrite Ee in Hef; injection Hef as X; exact X).
1,2: replace (bv_eqb (Z_to_bv 64 B) (Z_to_bv 64 (ent_addr tbl (le_ix ef)))) with true by (symmetry; rewrite <- Eef, <- EB; apply bv_eqb_refl); cbv iota.
1,2: step; step.
1,2: replace (bv_eqb (Z_to_bv 64 B) (Z_to_bv 64 (ent_addr tbl (le_ix ef)))) with true by (symmetry; rewrite <- Eef, <- EB; apply bv_eqb_refl); cbv iota.
3: assert (NEf : le_ix e <> le_ix ef) by (eapply (IXNE (length es0) jf); [exact Ee | exact Hef | klia]).
3: unfold ent_addr; if_falsex; change (tbl + 40 * Z.of_nat (le_ix ef)) with (ent_addr tbl (le_ix ef)).
3: step; step; step.
3: unfold ent_addr; if_falsex; change (tbl + 40 * Z.of_nat (le_ix ef)) with (ent_addr tbl (le_ix ef)).
3: step; step; if_truex.

all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
all: match goal with H : mem_inv segs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into MIF end.
all: assert (HPF : HEAPx A2 (lh_blocks t tbl size es0 ++ LB) mF md2) by (heap_now S4L HIx HP2n MU WM MIF).
all: assert (GF : GI mF) by
(eapply (GI_munch m2 mF); [exact G2 | exact MU | exact WM |];
repeat (apply Forall_cons; [cbn; (first [(gj_keep_lay; clear - LO LOS Htimg Hlen Hix Hbimg HB Hixl HBl; gj_intro_lay) | (gj_keep_lay; clear - LO LOS Htimg Hlen Hix Hbimg HB; gj_intro_lay)]; lia)|]); apply Forall_nil).
all: assert (HPRF : heap_pres S4L LB (bv_unsigned sp) m0 mF) by
(eapply heap_pres_trans; [exact HPR'|]; eapply (lh_writes_pres A2 t tbl size es0 LB m2 md2 mF); [exact HP2 | exact MU | exact WM | | ((gj_keep_lay; clear - LO LOS; gj_intro_lay); clia)];
repeat (apply Forall_cons; [cbn; first [left; ((gj_keep_lay; clear - LO LOS; gj_intro_lay); clia) | right; left; (clear; lia) | right; right; (first [(gj_keep_lay; clear - Hlen Hix HB Hixl HBl; gj_intro_lay) | (gj_keep_lay; clear - Hlen Hix HB; gj_intro_lay)]; lia)] |]); apply Forall_nil).
all: assert (KEYSF : lh_keys segs mF es0) by
(eapply lh_keys_frame; [exact KEYS2 | exact MU | exact WM |];
intros y Hy; destruct (KF y ltac:(apply in_or_app; left; exact Hy)) as (? & ? & ? & ? & ? & ?);
repeat (apply Forall_cons; [cbn; (first [(gj_keep_lay; clear - LO LOS H1 H3 Hlen Hix HB H4 Hixl HBl; gj_intro_lay) | (gj_keep_lay; clear - LO LOS H1 H3 Hlen Hix HB H4; gj_intro_lay)]; lia)|]); apply Forall_nil).
all: assert (C' : rw_cells segs mF (ent_addr tbl (le_ix e)) (slot_cells (del_slot se))) by
(unfold slot_cells, del_slot; cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]; rewrite Ekc, <- EB; exact C).
2,3: assert (Cl' : rw_cells segs mF (ent_addr tbl (le_ix el)) (slot_cells (clr_nx sl))) by
(unfold slot_cells, clr_nx; cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]; rewrite Elk, Elkc, Elv, Elpv, <- EBl; exact Cl).
1: assert (SLF : lh_slots segs mF tbl (upd svs (le_ix e) (del_slot se))) by
(eapply (lh_slots_write1 segs m2 mF tbl svs _ (le_ix e) (del_slot se)); [exact SL2 | exact Hix | exact MU | exact WM | | exact C'];
intros i NE Hi; unfold ivs_miss_slot; rewrite <- Hlen in Hbhi, SEP;
repeat (apply Forall_cons; [cbn; unfold ent_addr; klia|]); apply Forall_nil).
2,3: assert (SLF : lh_slots segs mF tbl (upd (upd svs (le_ix e) (del_slot se)) (le_ix el) (clr_nx sl))) by
(eapply (lh_slots_write2 segs m2 mF tbl svs _ (le_ix e) (del_slot se) (le_ix el) (clr_nx sl));
[exact SL2 | exact Hix | exact Hixl | exact (not_eq_sym NEl) | exact MU | exact WM | | exact C' | exact Cl'];
intros i NE1 NE2 Hi; unfold ivs_miss_slot; rewrite <- Hlen in Hbhi, SEP;
repeat (apply Forall_cons; [cbn; unfold ent_addr; ((gj_keep_lay; clear - LO LOS Hbhi Hi SEP HB NE1 HBl NE2; gj_intro_lay); lia)|]); apply Forall_nil).
1: assert (OPENF : lh_open segs S4F mF t tbl size [] (upd svs (le_ix e) (del_slot se))).
1:{ split; [| split; [exact SLF | split; [exact (lh_link_unsnoc_nil tbl es0 e svs se LINK Ese E0) | split; [constructor | split; [exact Hsz | split; [cbn; klia | rewrite upd_length; exact Hlen]]]]]].
unfold lh_hdrf. rewrite E0 in HDR. exact HDR. }
2,3: assert (OPENF : lh_open segs S4F mF t tbl size es0 (upd (upd svs (le_ix e) (del_slot se)) (le_ix el) (clr_nx sl))).
2:{ split; [| split; [exact SLF | split; [exact (lh_link_unsnoc_cons tbl es0 e svs se LINK Ese es1 el sl E0 Esl) | split; [exact KEYSF | split; [exact Hsz | split; [klia | rewrite !upd_length; exact Hlen]]]]]].
unfold lh_hdrf. rewrite hd_of_nth, Ex0. replace (tl_of tbl es0) with (ent_addr tbl (le_ix el)) by (rewrite E0; symmetry; apply tl_of_app). rewrite <- EBl. exact HDR. }
3:{ split; [| split; [exact SLF | split; [exact (lh_link_unsnoc_cons tbl es0 e svs se LINK Ese es1 el sl E0 Esl) | split; [exact KEYSF | split; [exact Hsz | split; [klia | rewrite !upd_length; exact Hlen]]]]]].
unfold lh_hdrf. rewrite hd_of_nth, Ex0. replace (tl_of tbl es0) with (ent_addr tbl (le_ix el)) by (rewrite E0; symmetry; apply tl_of_app). rewrite <- EBl. exact HDR. }

1: rewrite E0, firstn_nil in KX; rewrite E0 in HPF.
2: rewrite firstn_all2 in KX by klia.
1,2: apply evt_RZ_done; eapply KX; first [exact HPF | exact OPENF | exact GF | exact FR | exact ERR2 | exact HPRF | eapply model_vm_only_trans; [exact VM0 | exact VM2] | eassumption].

replace (Z_to_bv 64 Bl) with (Z_to_bv 64 (ent_addr tbl (le_ix el))) by (rewrite EBl; reflexivity).
rewrite E0, firstn_snoc_le in KX by klia.
rewrite E0 in HPF, OPENF.
apply evt_RZ_done.
eapply (IH es1 el _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mF md2 A2);
first [exact HPF | exact OPENF | exact GF | exact FR | exact ERR2 | exact HPRF | exact KX | exact LO | exact SPA | exact HT | idtac].
+ klia.
+ klia.
+ rewrite <- E0. rewrite nth_error_app1 in Hef by klia. exact Hef.
+ intros j x Hj Hx. apply (VZ j x Hj). rewrite <- E0 in Hx.
rewrite nth_error_app1 by (apply (proj1 (nth_error_Some es0 j)); rewrite Hx; discriminate). exact Hx.
+ eassumption.
+ klia.
+ eapply model_vm_only_trans; [exact VM0 | exact VM2].
Qed.

#[using="GGOT4 GHASH4 GVDSO4 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma del_exit_ok : forall (esf : list lent),
bv_unsigned rac mod 2 = 0 -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 ->
(forall (m : word -> option byte) (md : Model) (A : AS S4L HIx) (svsf : list slotv)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
HEAPx A (lh_blocks t tbl size esf ++ LB) m md -> lh_open segs S4F m t tbl size esf svsf -> GI m ->
stk segs m lo (bv_unsigned sp) -> rw_cells segs m (gTP - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
realizes segs (mkCfg (MS (mkR rac sp gp (Z_to_bv 64 gTP) t0 t1 t2 s0c s1c (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rac) fc None m (seg_rom segs)) md) T) ->
del_exit esf.
Proof. clear - GGOT4 GHASH4 GVDSO4 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free segs gTP S4F HIx sp gp s7 s8 s9 s10 s11 F fc m0 md0 LB lo t tbl size jf ef T rac s0c s1c s2c s3c s4c s5c s6c errv GI GI_munch GI_pres. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_RDATA_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GHASH4x12_GVDSO4 as gL5_; unfold gw_le in gL5_. pose proof LAY_IMG_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GVDSO4_IMG as gL7_; unfold gw_le in gL7_. pose proof LAY_POS_e_fn_lh_entry_free as gL8_; unfold gw_le in gL8_. pose proof LAY_HI_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_.
intros esf RAC LO LOS K. unfold del_exit. intros until svsf; intros HP OPEN G ST FR ERR VM0 HPR.
unfold del_frame in FR. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK; pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI; cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs m) as WM; pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|].
do 10 step.
apply evt_RZ_done. release_frame FR ST (bv_unsigned sp).
eapply K; [exact HP | exact OPEN | exact G | exact ST | exact ERR | exact VM0 | exact HPR].
Qed.
End DelLoop.

#[using="Type"] Lemma true_munch : forall m m' W, (fun _ : word -> option byte => True) m -> munch W m m' -> wmono segs m m' -> Forall (fun iv => gIMG_HI <= fst iv \/ snd iv <= 0x10000) W -> (fun _ : word -> option byte => True) m'.
Proof. clear - segs gIMG_HI HIx. intros; exact I. Qed.
#[using="GGOT4 GHASH4 GVDSO4 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_entry_free gRDATA_LO LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma true_pres : forall m m' LB' SP, heap_pres S4L LB' SP m m' -> (fun _ : word -> option byte => True) m -> (fun _ : word -> option byte => True) m'.
Proof. clear - GGOT4 GHASH4 GVDSO4 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_entry_free gRDATA_LO LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_RDATA_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GHASH4x12_GVDSO4 as gL5_; unfold gw_le in gL5_. pose proof LAY_IMG_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GVDSO4_IMG as gL7_; unfold gw_le in gL7_. pose proof LAY_POS_e_fn_lh_entry_free as gL8_; unfold gw_le in gL8_. pose proof LAY_HI_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_. intros; exact I. Qed.

Definition lh_delete_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (t tbl size : Z) (es : list lent) (jf : nat)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (errv' : word) svs',
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' /\
model_vm_only md md' /\ stk segs m' lo (bv_unsigned sp) /\ heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\ lh_glob4 m' /\
lh_open segs S4F m' t tbl size (firstn jf es) svs' /\ HEAPx A' (lh_blocks t tbl size (firstn jf es) ++ LB) m' md'.

#[using="GGOT4 GHASH4 GVDSO4 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_entry_free_cps AL_e_fn_lh_entry_free RNG_e_fn_lh_entry_free LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free S4F"] Lemma lh_delete_tail_cps2 : lh_delete_tail_stmt2 HIx.
Proof. clear - GGOT4 GHASH4 GVDSO4 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 lh_entry_free_cps AL_e_fn_lh_entry_free RNG_e_fn_lh_entry_free LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free S4F HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOT4_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASH4_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_RDATA_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GHASH4x12_GVDSO4 as gL5_; unfold gw_le in gL5_. pose proof LAY_IMG_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GVDSO4_IMG as gL7_; unfold gw_le in gL7_. pose proof LAY_POS_e_fn_lh_entry_free as gL8_; unfold gw_le in gL8_. pose proof LAY_HI_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_.
unfold lh_delete_tail_stmt2.
intros until ef. intros HP OPEN Hef VZ ST LO LOS SPA HT ERR TP RA A0 A1 K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen). unfold lh_hdr, lh_hdrf in HDR.
destruct (snoc_inv es) as [Enil | (es0 & e & E0)]; [rewrite Enil in Hef; destruct jf; discriminate|].
pose proof (proj1 (nth_error_Some es jf) ltac:(rewrite Hef; discriminate)) as Hjf. rewrite E0, length_app in Hjf. cbn in Hjf.
replace (tl_of tbl es) with (ent_addr tbl (le_ix e)) in HDR by (rewrite E0, tl_of_app; reflexivity).
remember (hd_of tbl es) as HDv eqn:EHD.
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
assert (BELOW : lh_below lo t tbl size es).
{ split; [klia|]. split; [klia|]. split; [klia|]. split; [klia|]. intros x Hx. destruct (KF x Hx). klia. }
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. unfold lh_delete_tail_entry. subst a0 a1 tp.
carve_frame 64%nat ST.
do 9 step.
step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (OPEN1 : lh_open segs S4F mx t tbl size es svs) by
(eapply (lh_open_frame segs S4F _ m mx t tbl size es svs _ lo); [exact OPEN | exact BELOW | exact MU | exact WM | apply Forall_cons; [cbn; klia | apply Forall_nil]]);
assert (HP1 : HEAPx A (lh_blocks t tbl size es ++ LB) mx md) by (heap_now S4L HIx HP MU WM MI);
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m mx) by
(eapply (lh_writes_pres A t tbl size es LB m md mx); [exact HP | exact MU | exact WM | apply Forall_cons; [cbn; left; clia | apply Forall_nil] | clia]);
rename mx into m1
end.
rewrite E0 in HP1, OPEN1, Hef, VZ.
unfold lh_delete_tail_post2 in K. rewrite E0, (firstn_snoc_le _ es0 e jf) in K by klia.
apply evt_RZ_done.
eapply (lh_del_loop sp gp s7 s8 s9 s10 s11 F fc m md LB lo t tbl size jf ef T ra s0 s1 s2 s3 s4 s5 s6 errv (fun _ => True) true_munch true_pres (length es0 - jf) es0 e svs
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md A);
first [reflexivity | exact Hef | exact HP1 | exact OPEN1 | exact VZ | exact I | exact FR | exact ERR | apply model_vm_only_refl | exact HPR1 | exact SPA | exact HT | idtac].
- klia.
- exact ST.
- clia.
- klia.
- apply (del_exit_ok sp gp s7 s8 s9 s10 s11 F fc m md LB lo t tbl size ef T ra s0 s1 s2 s3 s4 s5 s6 errv (fun _ => True) (firstn jf es0) RA ltac:(clia) ltac:(klia)).
intros m' md' A' svsf u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 HPf OPENf Gf STf ERRf VMf HPRf.
apply K. exists m', A', svsf.
split; [unfold ret_state; do 14 eexists; reflexivity|].
split; [exact VMf|]. split; [exact STf|]. split; [|split; [exact ERRf | split; [exact OPENf | exact HPf]]].
exact HPRf.
Qed.
End LhDelete.

End RC__1.

End G.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH QmZZ QKQo Q8Q3 Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

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
#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma gLAYF0 : ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gTP gIMG_LO gIMG_HI. pose proof LAY_TPLO as X1; pose proof LAY_TPHI as X2; unfold gw_le in X1, X2. split; [split; [exact X1 | exact X2] | exact LAY_gIMG_LO]. Qed.
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

Hypothesis printbuf_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqd.gw_all) (@QPIU.Mqd.printbuf_free_cps) e_pbfree)) in exact T).
Hypothesis lh_table_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QAyu.Mq2.gw_all) (@QAyu.Mq2.lh_table_free_cps) e_lhfree)) in exact T).
Hypothesis array_list_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mq0.gw_all) (@QPIU.Mq0.array_list_free_cps) e_alfree)) in exact T).

Definition lh_delete_tail_stmt2 := ltac:(let t := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := eval cbv beta delta [QPIU.Mqh.lh_delete_tail_stmt2] in t in let t := eval cbv delta [e_blk_18934] in t in exact t).
Definition next_post := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let t := eval cbv beta delta [Q7mx.Mq1.next_post] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := gw_subst t x lh_delete_tail_stmt2 in exact t).
Definition zhead := ltac:(let t := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.zhead))) in let t := eval cbv beta delta [QH1t.Mq1.zhead] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := gw_subst t x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let t := gw_subst t x next_post in exact t).
Definition head_stmt := ltac:(let t := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.head_stmt))) in let t := eval cbv beta delta [QH1t.Mq1.head_stmt] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := gw_subst t x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let t := gw_subst t x next_post in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.zhead))) in let t := gw_subst t x zhead in exact t).
Definition desc_stmt := ltac:(let t := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.desc_stmt))) in let t := eval cbv beta delta [QH1t.Mq1.desc_stmt] in t in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let t := gw_subst t x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let t := gw_subst t x next_post in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.zhead))) in let t := gw_subst t x zhead in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.head_stmt))) in let t := gw_subst t x head_stmt in exact t).

Definition zhead_hdr := ltac:(let p := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.zhead_hdr))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let T := gw_subst T x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let T := gw_subst T x next_post in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.zhead))) in let T := gw_subst T x zhead in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.head_stmt))) in let T := gw_subst T x head_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.desc_stmt))) in let T := gw_subst T x desc_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.next_post))) in let T := gw_subst T x next_post in exact (p : T)).
Definition zhead_agree := ltac:(let p := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.zhead_agree))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let T := gw_subst T x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let T := gw_subst T x next_post in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.zhead))) in let T := gw_subst T x zhead in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.head_stmt))) in let T := gw_subst T x head_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.desc_stmt))) in let T := gw_subst T x desc_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.next_post))) in let T := gw_subst T x next_post in exact (p : T)).
Definition zomb_zhead := ltac:(let p := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.zomb_zhead))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let T := gw_subst T x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let T := gw_subst T x next_post in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.zhead))) in let T := gw_subst T x zhead in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.head_stmt))) in let T := gw_subst T x head_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.desc_stmt))) in let T := gw_subst T x desc_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.next_post))) in let T := gw_subst T x next_post in exact (p : T)).
Definition next_post_w := ltac:(let p := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.next_post_w))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QPIU.Mqh.lh_delete_tail_stmt2))) in let T := gw_subst T x lh_delete_tail_stmt2 in let x := constr:(ltac:(gw_ctx2 (@Q7mx.Mq1.next_post))) in let T := gw_subst T x next_post in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.zhead))) in let T := gw_subst T x zhead in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.head_stmt))) in let T := gw_subst T x head_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.desc_stmt))) in let T := gw_subst T x desc_stmt in let x := constr:(ltac:(gw_ctx2 (@QH1t.Mq1.next_post))) in let T := gw_subst T x next_post in exact (p : T)).

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
#[using="w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 joff_24 joff_26 joff_28 joff_34 joff_39 joff_57 joff_63 joff_89 joff_97 joff_101 joff_106 e_pbfree e_alfree e_alread e_17bbc e_17cb0 e_17cb8 e_lhfree e_18934 e_18a54 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_24 E_24 D_26 E_26 D_28 E_28 D_34 E_34 D_39 E_39 D_57 E_57 D_63 E_63 D_89 E_89 D_97 E_97 D_101 E_101 D_106 E_106 LINK_24 LINK_26 LINK_28 LINK_34 LINK_39 LINK_57 LINK_63 LINK_89 LINK_97 LINK_101 LINK_106 CODE_e_18934 AL_e_18934_b4 RNG_e_18934_code AL_e_fn_arr_to_json_string RNG_e_fn_arr_to_json_string LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string AL_e_fn_obj_to_json_string RNG_e_fn_obj_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string printbuf_free_cps lh_table_free_cps array_list_free_cps CODE_e_17a68 CODE_e_18a54 CODE_e_17cb0 CODE_e_17bbc CODE_e_187f8 CODE_e_17cb8 S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

Section Desc.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (sp gp s10 s11 : word) (lo : Z) (errv : word).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -96 - (32 + 32 + 16 + 8256).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis DEL : lh_delete_tail_stmt2 HIx.

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -96)).
Notation TP := (Z_to_bv 64 gTP).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation NEXT := (next_post HIx sp gp s10 s11 lo errv).
Notation head_stmt' := (head_stmt HIx sp gp s10 s11 lo errv).

#[using="w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 e_alfree e_lhfree e_18934 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string"] Lemma descend_tail : forall (isobjc isobjp : bool) (ck kids : list (option jshape))
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS2 bs : list blk) (x q v : Z) (T : TSet),
head_stmt' isobjc ck -> head_stmt' isobjp kids ->
HEAPx A (bs ++ XBS2 ++ LB) m md ->
zhead isobjc m v x ck bs -> zhead isobjp m x q kids XBS2 ->
stk segs m lo (bv_unsigned sp + -96) -> rw_cells segs m (gTP - 164) [C4 errv] ->
(forall ms' md', NEXT q F1 fc1 m md LB ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 v) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x74)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 e_alfree e_lhfree e_18934 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string segs base gTP HIx sp gp s10 s11 lo errv LO LOS SPA HT DEL. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until T. intros HC HK HP ZC ZP ST ERR K.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
destruct (zhead_hdr isobjc m v x ck bs ZC (nodup_app_l _ _ ND)) as (pbc & cfc & INv & _ & _).
assert (HP' : HEAPx A (XBS2 ++ bs ++ LB) m md) by (eapply (heap_perm S4L HIx); [exact HP | hperm]).
destruct (zhead_hdr isobjp m x q kids XBS2 ZP (nodup_app_l _ _ (heap_blk_nodup S4L HIx _ _ _ _ HP'))) as (pbp & cfp & INx & _ & _).
pose proof (heap_blk S4L HIx _ _ _ _ v 48 HP ltac:(in_sub INv)) as (_ & _ & Hvlo & Hvhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP ltac:(in_sub INx)) as (_ & _ & Hxlo & Hxhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi, Hxhi. clear HP'.
pose proof (wmono_refl segs m) as WM. pose proof (munch_refl [] m) as MU.
apply rz_evt; [exact MOK|].
step. step. if_falsex.
apply evt_RZ_done.
eapply HC; [exact HP | exact ZC | exact ST | exact ERR |].
intros ms5 md5 (m5 & A5 & F5 & fc5 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & -> & FS5 & FRM5 & VM5 & HP5 & ST5 & HPR5 & ERR5).
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI5. cbn [hl_segs S4L] in MI5.
clear MU WM MI. pose proof (wmono_refl segs m5) as WM. pose proof (munch_refl [] m5) as MU.
apply rz_evt; [exact MOK5|].
step. step. if_falsex.
apply evt_RZ_done.
eapply HK; [exact HP5 | | exact ST5 | exact ERR5 |].
{ eapply (zhead_agree isobjp (XBS2 ++ LB)); [exact ZP | eapply (agree_of_heap_pres segs S4L); [exact HPR5 | reflexivity | intros b Hb; exact Hb] | intros b Hb; in_sub Hb]. }
intros ms' md' NP. apply K. eapply next_post_w; [exact FS5 | exact FRM5 | exact VM5 | | exact NP].
eapply heap_pres_weaken; [exact HPR5 | lia | intros b Hb; in_sub Hb].
Qed.

#[using="w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 joff_97 e_alfree e_lhfree e_18934 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_97 E_97 LINK_97 LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string LO LOS SPA HT DEL"] Lemma descend_obj : forall c kids,
desc_stmt HIx sp gp s10 s11 lo errv c -> head_stmt' true kids ->
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS1 bs : list blk) (x q v : Z) (T : TSet)
(nz : nat) (t tbl size : Z) (es2 : list lent) (svs2 : list slotv) (e2 : lent),
HEAPx A (bs ++ XBS1 ++ LB) m md ->
zomb segs S4F c m v bs ->
zobj segs S4F m x q kids (S nz) t tbl size es2 svs2 XBS1 -> nth_error es2 (length kids) = Some e2 ->
stk segs m lo (bv_unsigned sp + -96) -> rw_cells segs m (gTP - 164) [C4 errv] ->
(forall ms' md', NEXT q F1 fc1 m md LB ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 v) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (ent_addr tbl (le_ix e2))) x19 x20
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x16c)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_24 w_26 w_28 w_34 w_39 w_57 w_63 w_89 w_97 w_101 w_106 joff_97 e_alfree e_lhfree e_18934 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_97 E_97 LINK_97 LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string LO LOS SPA HT DEL segs base gTP S4F HIx sp gp s10 s11 lo errv. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros c kids KD HK. intros until e2. intros HP ZC Z Hes2 ST ERR K.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct Z as (pb & PBS & KBS & esk & esz & Ees2 & Lz & Fz & EX1 & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L _]. rewrite length_map in L.
assert (VZ : forall j y, (length kids <= j)%nat -> nth_error es2 j = Some y -> le_v y = 0).
{ intros j y Hj Hy. rewrite Ees2, nth_error_app2 in Hy by lia. exact (proj1 (Forall_forall _ _) Fz y (nth_error_In _ _ Hy)). }
destruct (zomb_zhead HIx sp gp s10 s11 lo errv c m v bs ZC KD) as (isobjc & ck & ZCH & HC). clear ZC KD.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
destruct (zhead_hdr isobjc m v 0 ck bs ZCH (nodup_app_l _ _ ND)) as (pbc & cfc & INv & HDRC & CLOSEC).
assert (INv' : In (v, 48) (bs ++ XBS1 ++ LB)) by in_sub INv.
assert (INx : In (x, 48) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_elem).
pose proof (heap_blk S4L HIx _ _ _ _ v 48 HP INv') as (_ & Hval & Hvlo & Hvhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ v 48 HP INv') as Hvimg. cbn [hl_img_lo hl_img_hi S4L] in Hvimg.
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP INx) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP INx) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi, Hxhi.
assert (NVX : forall k, ~ In (v, k) (XBS1 ++ LB)) by (intros k; exact (nodup_prefix_suffix bs (XBS1 ++ LB) v 48 k ND INv)).
assert (Hxv : x <> v) by (intros ->; apply (NVX 48); rewrite EX1; in_elem).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ x 48 v 48 HP INx INv' Hxv) as Dxv.
assert (HPl : HEAPx A (lh_blocks t tbl size es2 ++ ((x, 48) :: concat KBS ++ PBS ++ bs ++ LB)) m md).
{ eapply (heap_perm S4L HIx); [exact HP | rewrite EX1; hperm]. }
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HPl) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & Httb & KEYF).
cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi.
clear HPl. stash KEYF.
pose proof (wmono_refl segs m) as WM. pose proof (munch_refl [(v + 24, v + 40)] m) as MU.
unfold jhdr_cells in HDRC. cbn [app] in HDRC. unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
stepz. step. step. norm_w32. step. step. if_false. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
destruct (blk_write_in S4L HIx _ _ _ _ _ _ _ _ HP INv' MU WM MI ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as [HP1 AGV].
assert (AGX : agree_on segs (XBS1 ++ LB) m m1).
{ eapply agree_on_incl; [exact AGV|]. intros [ba bk] Hb. apply in_others; [in_sub Hb | intros ->; exact (NVX bk Hb)]. }
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp + -96) m m1).
{ eapply (blk_write_in_pres S4L HIx); [exact HP | exact INv' | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]
| intros b Hb; in_sub Hb | intros k Hk; apply (NVX k); in_sub Hk | clia]. }
assert (ZCH1 : zhead isobjc m1 v x ck bs).
{ apply (CLOSEC m1 x); [unfold jhdr_cells; cbn [app]; exact HDRC |].
eapply agree_on_incl; [exact AGV|]. intros [ba bk] Hb. apply in_others_iff in Hb as [Hb Hne]. apply in_others; [in_sub Hb | exact Hne]. }
assert (OPEN1 : lh_open segs S4F m1 t tbl size es2 svs2).
{ eapply lh_open_agree; [exact OPEN | exact AGX | intros b Hb; rewrite EX1; in_sub Hb]. }
clear CLOSEC HDRC MU WM.
apply evt_RZ_done.
eapply DEL with (LB := (x, 48) :: concat KBS ++ PBS ++ bs ++ LB) (es := es2) (svs := svs2) (jf := length kids) (ef := e2) (lo := lo);
[ eapply (heap_perm S4L HIx); [exact HP1 | rewrite EX1; hperm] | exact OPEN1 | exact Hes2 | exact VZ | .. ]; try alloc_side.
intros ms4 md4 (m4 & A4 & svs4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & OPEN4 & HP4). open_ret RS4. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR4 by lia.
replace (firstn (length kids) es2) with esk in OPEN4, HP4 by (rewrite Ees2, <- L; symmetry; apply firstn_app_len).
match goal with H : rw_cells _ m1 x _ |- _ => rename H into HDR1 end.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in HDR1; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR1.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs S4L] in MI4.
pose proof (wmono_refl segs m4) as WM. pose proof (munch_refl [] m4) as MU.
reenter MOK4. step.
apply evt_RZ_done.
eapply (descend_tail isobjc true ck kids) with (XBS2 := ((x, 48) :: lh_blocks t tbl size esk ++ concat KBS) ++ PBS) (bs := bs) (LB := LB) (q := q);
[exact HC | exact HK | eapply (heap_perm S4L HIx); [exact HP4 | hperm] | | | exact ST4 | exact ERR4 |].
- eapply (zhead_agree isobjc); [exact ZCH1 | eapply (agree_of_heap_pres segs S4L); [exact HPR4 | reflexivity | intros b Hb; exact Hb] | intros b Hb; in_sub Hb].
- exists t, tbl, size, esk, svs4. exists pb, PBS, KBS, esk, (@nil lent).
split; [rewrite app_nil_r; reflexivity|]. split; [reflexivity|]. split; [apply Forall_nil|]. split; [reflexivity|].
split; [| split; [unfold jhdr_cells; cbn [app]; exact HDR1 | split; [exact OPEN4|]]].
+ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
* eapply agree_on_incl; [exact AGX | intros b Hb; rewrite EX1; in_sub Hb].
* eapply (agree_of_heap_pres segs S4L); [exact HPR4 | reflexivity | intros b Hb; in_sub Hb].
+ eapply okids_agree; [exact OK | | apply incl_refl]. eapply agree_on_trans.
* eapply agree_on_incl; [exact AGX | intros b Hb; rewrite EX1; in_sub Hb].
* eapply (agree_of_heap_pres segs S4L); [exact HPR4 | reflexivity | intros b Hb; in_sub Hb].
- intros ms' md' NP. apply K. eapply next_post_w; [apply fsaved_refl | intros Hf; exact Hf | exact VM4 | | exact NP].
eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; in_sub Hb]].
Qed.
End Desc.

End RC__1.

End G.
End Mq1.

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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7mx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7mx.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QH1t.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH1t.
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

Hypothesis AL_e_fn_lh_char_equal : gw_b4 e_fn_lh_char_equal.
Hypothesis RNG_e_fn_lh_char_equal : gw_br e_fn_lh_char_equal 4.
Hypothesis LAY_POS_e_fn_lh_char_equal : gw_le 1 e_fn_lh_char_equal.
Hypothesis LAY_HI_e_fn_lh_char_equal : gw_le (e_fn_lh_char_equal + 4) 1099511627776.
Hypothesis AL_e_fn_lh_char_hash : gw_b4 e_fn_lh_char_hash.
Hypothesis RNG_e_fn_lh_char_hash : gw_br e_fn_lh_char_hash 4.
Hypothesis LAY_POS_e_fn_lh_char_hash : gw_le 1 e_fn_lh_char_hash.
Hypothesis LAY_HI_e_fn_lh_char_hash : gw_le (e_fn_lh_char_hash + 4) 1099511627776.

Definition is_free := ltac:(let t := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.is_free))) in let t := eval cbv beta delta [QAyu.Mq3.is_free] in t in exact t).
Definition ins_regs := ltac:(let t := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.ins_regs))) in let t := eval cbv beta delta [QAyu.Mq3.ins_regs] in t in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.is_free))) in let t := gw_subst t x is_free in exact t).
Definition ins_svs := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q7mx.ins_svs))) in let t := eval cbv beta delta [Q7mx.ins_svs] in t in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.is_free))) in let t := gw_subst t x is_free in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.ins_regs))) in let t := gw_subst t x ins_regs in exact t).
Definition ins_frame := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q7mx.ins_frame))) in let t := eval cbv beta delta [Q7mx.ins_frame] in t in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.is_free))) in let t := gw_subst t x is_free in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.ins_regs))) in let t := gw_subst t x ins_regs in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_svs))) in let t := gw_subst t x ins_svs in exact t).
Definition hdr_cells := ltac:(let t := constr:(ltac:(gw_ctx2 (@Q7mx.hdr_cells))) in let t := eval cbv beta delta [Q7mx.hdr_cells] in t in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.is_free))) in let t := gw_subst t x is_free in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.ins_regs))) in let t := gw_subst t x ins_regs in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_svs))) in let t := gw_subst t x ins_svs in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_frame))) in let t := gw_subst t x ins_frame in exact t).
Definition lh_probe_loop := ltac:(let p := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.lh_probe_loop))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.is_free))) in let T := gw_subst T x is_free in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.ins_regs))) in let T := gw_subst T x ins_regs in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_svs))) in let T := gw_subst T x ins_svs in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_frame))) in let T := gw_subst T x ins_frame in let x := constr:(ltac:(gw_ctx2 (@Q7mx.hdr_cells))) in let T := gw_subst T x hdr_cells in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_regs))) in let T := gw_subst T x ins_regs in exact (p : T)).
Arguments lh_probe_loop _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_Z_scope _%_Z_scope _%_Z_scope _%_Z_scope _%_Z_scope _%_Z_scope _%_list_scope _%_nat_scope.

Definition lh_store_block := ltac:(let p := constr:(ltac:(gw_ctx2 (@Q7mx.lh_store_block))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.is_free))) in let T := gw_subst T x is_free in let x := constr:(ltac:(gw_ctx2 (@QAyu.Mq3.ins_regs))) in let T := gw_subst T x ins_regs in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_svs))) in let T := gw_subst T x ins_svs in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_frame))) in let T := gw_subst T x ins_frame in let x := constr:(ltac:(gw_ctx2 (@Q7mx.hdr_cells))) in let T := gw_subst T x hdr_cells in let x := constr:(ltac:(gw_ctx2 (@Q7mx.ins_regs))) in let T := gw_subst T x ins_regs in exact (p : T)).
Arguments lh_store_block _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_Z_scope _%_Z_scope _%_Z_scope _%_Z_scope _%_Z_scope _%_list_scope _%_Z_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_Z_scope _ _%_Z_scope _%_Z_scope _%_Z_scope _%_nat_scope.

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
#[using="w_10 w_11 hi_10 lo_11 G_10770 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_10 E_10 D_11 E_11 ANCH_11 RNG_G_10770 ROM_G_10770 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal AL_e_fn_lh_char_hash RNG_e_fn_lh_char_hash LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Section LhInsertTail.
Variables (sp gp tp : word) (s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v : Z) (es : list lent) (svs : list slotv) (ffn : Z).
Variables (rac s0c s1c s2c s3c s4c s5c : word).

Definition ins_tail_post (cnt lo : Z) (x28 x29 x30 x31 : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (g : nat) (sg : slotv) (ixl : nat) (sl : slotv) (x5 x6 x7 x11 x12 : word) m',
(g < length svs)%nat /\ nth_error svs g = Some sg /\ is_free sg /\ ~ In g (map le_ix es) /\
(es <> [] -> exists jl el, nth_error es jl = Some el /\ (S jl = length es)%nat /\ ixl = le_ix el /\ nth_error svs ixl = Some sl) /\
ms' = MS (mkR rac sp gp tp x5 x6 x7 s0c s1c (Z_to_bv 64 0)
x11 x12 (Z_to_bv 64 (Z.of_nat g)) (Z_to_bv 64 0) (Z_to_bv 64 tbl) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (tbl + 40 * Z.of_nat g))
s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc rac) fc None m' (seg_rom segs)
/\ munch [(t, t + 56); (tbl, tbl + 40 * size)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' t (hdr_cells tbl ffn size (cnt + 1) (match es with [] => ent_addr tbl g | _ => hd_of tbl es end) (ent_addr tbl g))
/\ lh_slots segs m' tbl (ins_svs svs g sg k v (hd_of tbl es) (tl_of tbl es) ixl sl tbl)
/\ stk segs m' lo (bv_unsigned sp).

#[using="w_10 w_11 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash"] Lemma lh_insert_tail :
forall (h cnt lo : Z) (x1 x5 x6 x7 x8 x9 x15 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word) (m : word -> option byte) (junk8 : list byte),
0 <= h < 2^64 -> In size lf_sizes -> Z.of_nat (length svs) = size -> cnt = Z.of_nat (length es) -> cnt < size ->
lh_link tbl es svs -> lh_keys segs m es -> 0 <= k < 2^64 -> 0 <= v < 2^64 -> 0 <= ffn < 2^64 ->
0 <= t -> t + 56 <= lo -> 0 < tbl -> tbl + 40 * size <= lo -> (t + 56 <= tbl \/ tbl + 40 * size <= t) ->
lo <= bv_unsigned sp - 64 ->
mem_inv segs m ->
rw_cells segs m t (hdr_cells tbl ffn size cnt (hd_of tbl es) (tl_of tbl es)) ->
lh_slots segs m tbl svs ->
ins_frame sp rac s0c s1c s2c s3c s4c s5c m junk8 -> stk segs m lo (bv_unsigned sp + -64) ->
evt segs (ins_tail_post cnt lo x28 x29 x30 x31 m)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9
(Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 h) (Z_to_bv 64 0) x15 (Z_to_bv 64 size) x17
x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x44)) fc None m (seg_rom segs)).
Proof. clear - w_10 w_11 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash segs base sp gp tp s6 s7 s8 s9 s10 s11 F fc t tbl size k v es svs ffn rac s0c s1c s2c s3c s4c s5c. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until junk8. intros Hh Hsz Hlen Hcnt Hcs LINK KEYS Hk Hv Hffn Ht0 Ht Hb0 Hb SEP LOS MI HDR SL FR ST.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR. unfold hdr_cells in HDR. pose proof FR as FR0. unfold ins_frame in FR.
pose proof LINK as (LK1 & LK2 & LK3 & LK4).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
step. step. rewrite remu_lit by lia.
pose proof (Z.mod_pos_bound h size ltac:(lia)) as HM. set (n := h mod size) in *.
destruct (nth_error svs (Z.to_nat n)) as [sn|] eqn:Esn.
2:{ exfalso. apply nth_error_None in Esn. lia. }
pose proof (SL _ _ Esn) as C. unfold ent_addr, slot_cells in C. rewrite Z2Nat.id in C by lia.
step. step. rewrite (unsigned_lit n) by lia. step.
replace (tbl + n * 40) with (tbl + 40 * n) by lia. remember (tbl + 40 * n) as B eqn:EB.
step. subst B.

assert (CONT : forall (gz : Z) (sgz : slotv) (x6' x7' x17' : word),
0 <= gz < size -> nth_error svs (Z.to_nat gz) = Some sgz -> is_free sgz -> x17' = Z_to_bv 64 (tbl + gz * 40) ->
evt segs (ins_tail_post cnt lo x28 x29 x30 x31 m)
(MS (ins_regs sp gp tp s6 s7 s8 s9 s10 s11 t tbl size k v 0 x1 x6' x7' x8 x9 gz x17' x18 x19 x20 x21 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x90)) fc None m (seg_rom segs))).
{ intros gz sgz x6' x7' x17' Hgz Esgz FREEz ->.
set (g := Z.to_nat gz).
assert (NIN : ~ In g (map le_ix es)).
{ intros IN. apply in_map_iff in IN as (e & Hix & He). destruct (In_nth_error _ _ He) as [j Hj].
destruct (LK1 j e Hj) as (s' & Es' & Ek & _). rewrite Hix in Es'. unfold g in Es'. rewrite Esgz in Es'. injection Es' as <-.
destruct (LK4 e He) as (K0 & KF & _ & _). unfold is_free, LH_EMPTYv, LH_FREEDv in FREEz. unfold LH_FREEDv in KF.
destruct (lh_key_bytes segs m es e KEYS He) as (_ & _ & KL). destruct FREEz; lia. }

assert (TL : exists ixl sl,
((hd_of tbl es = 0 /\ tl_of tbl es = 0) \/ (hd_of tbl es <> 0 /\ tl_of tbl es = ent_addr tbl ixl /\ nth_error svs ixl = Some sl /\ ixl <> Z.to_nat gz /\ 0 <= hd_of tbl es < 2^64))
/\ (es <> [] -> exists jl el, nth_error es jl = Some el /\ (S jl = length es)%nat /\ ixl = le_ix el /\ nth_error svs ixl = Some sl)).
{ destruct es as [|e0 es'] eqn:EES.
- exists 0%nat, sgz. split; [left; split; reflexivity | intros X; exfalso; apply X; reflexivity].
- rewrite <- EES in *.
assert (HL : (length es - 1 < length es)%nat) by (rewrite EES; cbn; lia).
destruct (nth_error es (length es - 1)) as [el|] eqn:El; [| exfalso; apply nth_error_None in El; lia].
destruct (LK1 _ _ El) as (sl & Esl & _).
destruct (LK1 0%nat e0 ltac:(rewrite EES; reflexivity)) as (s0' & Es0 & _).
pose proof (proj1 (nth_error_Some svs (le_ix e0)) ltac:(rewrite Es0; discriminate)) as Hix0.
pose proof (proj1 (nth_error_Some svs (le_ix el)) ltac:(rewrite Esl; discriminate)) as Hixl.
exists (le_ix el), sl. split.
+ right. assert (HD0 : hd_of tbl es = ent_addr tbl (le_ix e0)) by (rewrite EES; reflexivity). rewrite !HD0. unfold ent_addr.
split; [lia|]. split; [rewrite (tl_of_last tbl es (length es - 1) el El ltac:(lia)); reflexivity|]. split; [exact Esl|]. split; [| lia].
intros X. apply NIN. unfold g. rewrite <- X. apply in_map. eapply nth_error_In. exact El.
+ intros _. exists (length es - 1)%nat, el. repeat split; try assumption. lia. }
destruct TL as (ixl & sl & TAIL & LAST).
eapply evt_mono.
- eapply (lh_store_block sp gp tp s6 s7 s8 s9 s10 s11 F fc t tbl size k v svs ffn rac s0c s1c s2c s3c s4c s5c gz sgz cnt (hd_of tbl es) (tl_of tbl es) ixl sl);
first [exact Esgz | exact Hsz | exact Hlen | exact TAIL | exact MI | exact HDR | exact SL | exact FR0 | exact ST | exact SEP | exact Hffn | lia | idtac].
all: try lia.
- cbv beta. intros ms' (x5' & x11' & x12' & m' & -> & MU' & WM' & MI' & HDR' & SL' & ST').
unfold ins_tail_post. exists g, sgz, ixl, sl, x5', x6', x7', x11', x12', m'.
assert (GZ : Z.of_nat g = gz) by (unfold g; lia).
rewrite GZ.
split; [unfold g; lia|]. split; [exact Esgz|]. split; [exact FREEz|]. split; [exact NIN|]. split; [exact LAST|].
split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [| split; [| exact ST']].
+ destruct es; cbn [hd_of] in HDR' |- *; [exact HDR' |]. unfold ent_addr in HDR' |- *.
destruct (Z.eqb_spec (tbl + 40 * Z.of_nat (le_ix l)) 0); [lia | exact HDR'].
+ replace g with (Z.to_nat gz) by reflexivity. exact SL'. }
step.

assert (LIVEK : forall i s, nth_error svs i = Some s -> ~ is_free s -> 0 <= sv_k s < LH_FREEDv).
{ intros i s E NF. destruct (in_dec Nat.eq_dec i (map le_ix es)) as [IN | NI].
- apply in_map_iff in IN as (e & Hix & He). destruct (In_nth_error _ _ He) as [j Hj].
destruct (LK1 j e Hj) as (s' & Es' & Ek & _). rewrite Hix, E in Es'. injection Es' as <-.
destruct (LK4 e He) as (K0 & KF & _ & _). destruct (lh_key_bytes segs m es e KEYS He) as (_ & _ & KL). rewrite Ek. lia.
- exfalso. apply NF. exact (LK2 i s E NI). }
step.
assert (FD : is_free sn \/ ~ is_free sn).
{ unfold is_free. destruct (Z.eq_dec (sv_k sn) LH_EMPTYv); [left; left; assumption|].
destruct (Z.eq_dec (sv_k sn) LH_FREEDv); [left; right; assumption|]. right. intros [X|X]; contradiction. }
destruct FD as [FRn | NFn].
-
assert (HK : sv_k sn = LH_EMPTYv \/ sv_k sn = LH_FREEDv) by exact FRn. unfold LH_EMPTYv, LH_FREEDv in HK.
unfold bv_ltu. change (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613. rewrite (unsigned_lit (sv_k sn)) by lia. if_true.
apply (CONT n sn); [lia | exact Esn | exact FRn | f_equal; lia].
-
pose proof (LIVEK _ _ Esn NFn) as HKn. unfold LH_FREEDv in HKn.
unfold bv_ltu. change (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613. rewrite (unsigned_lit (sv_k sn)) by lia. if_false.
step.
pose proof (lf_thr_lt size Hsz) as Hlt.
destruct (free_slot_exists (map le_ix es) (length svs) LK3 ltac:(rewrite length_map; lia)) as (f & Hf & NIf).
destruct (nth_error svs f) as [sf|] eqn:Esf; [| exfalso; apply nth_error_None in Esf; lia].
pose proof (LK2 f sf Esf NIf) as FRf.
eapply evt_cut.
{ eapply (lh_probe_loop sp gp tp s6 s7 s8 s9 s10 s11 F fc t tbl size k v 0 svs (Z.to_nat ((Z.of_nat f - n) mod size)) n (Z.of_nat f));
first [exact Hsz | exact Hlen | exact LIVEK | exact MI | exact SL | lia | idtac].
- rewrite Nat2Z.id. exact Esf.
- exact FRf.
- exists sn. split; [exact Esn | exact NFn]. }
cbv beta. intros ms' (g' & sg' & Hg' & Esg' & FRg' & ->).
apply (CONT g' sg'); [exact Hg' | exact Esg' | exact FRg' | reflexivity].
Qed.
End LhInsertTail.

End G.
