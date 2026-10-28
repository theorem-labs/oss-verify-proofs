(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg Qc3B QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj QSL3 UH1t Q6q3 Q3CA Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply Lib.GwApply2 Lib.GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QSL3.
Import UH1t.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q3CA.
Import Q0Hd.

Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.


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
Hypothesis RNG_GGOT4 : gw_br GGOT4 8.
Hypothesis AL_GGOT4 : gw_al GGOT4 8.
Hypothesis RNG_GHASH4 : gw_br GHASH4 8.
Hypothesis AL_GHASH4 : gw_al GHASH4 8.
Hypothesis RNG_GVDSO4 : gw_br GVDSO4 8.
Hypothesis AL_GVDSO4 : gw_al GVDSO4 8.
Hypothesis LAY_GGOT4_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASH4_GVDSO4 : gw_le (GHASH4 + 8) GVDSO4.

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
#[using="GGOT4 GHASH4 GVDSO4 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free JG_CGT_P gRDATA_LO RNG_GGOT4 AL_GGOT4 RNG_GHASH4 AL_GHASH4 RNG_GVDSO4 AL_GVDSO4 LAY_GGOT4_GHASH4 LAY_GHASH4_GVDSO4 AL_e_fn_lh_entry_free RNG_e_fn_lh_entry_free CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_RDATA_GGOT4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.
Local Tactic Notation "gj_rv" ident(h) := try revert h.
Ltac gj_keep_lay := gj_rv gLAYF_; gj_rv gL0_; gj_rv gL1_; gj_rv gL2_; gj_rv gL3_; gj_rv gL4_; gj_rv gL5_; gj_rv gL6_; gj_rv gL7_; gj_rv gL8_; gj_rv gL9_.
Ltac gj_intro_lay := repeat lazymatch goal with |- ((_ <= _)%Z -> _) => intro | |- ((_ /\ _) -> _) => intro end.

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

End LhDelete.

End RC__1.

End G.
End Mq0.
