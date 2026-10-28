(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Mh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Mh.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QAyu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAyu.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXOI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXOI.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QheR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QheR.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwApply2 GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm; gwj_align_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm; gwj_align_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QxiR Q7mx.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Lh2 Require Lh2InsStmt.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_12 w_13 : Z).
Variables (hi_12 : bv 20).
Variables (lo_13 : bv 12).
Variables (G_10760 : Z).
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
Hypothesis CODE : code_at segs base (QxiR.ulhprobe_code w_12 w_13).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 484.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (Auipc 17 hi_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_13 : decode_any (Z_to_bv 32 w_13) = Some (FLoad FMT_D 15 17 lo_13, 4%Z).
Hypothesis E_13 : is_ecall (Z_to_bv 32 w_13) = false.
Hypothesis ANCH_13 : gw_anch (Z.shiftl (bv_signed hi_12) 12 + (base + 48) + bv_signed lo_13)%Z G_10760.
Hypothesis RNG_G_10760 : gw_br G_10760 8.
Hypothesis ROM_G_10760 : ro_bytes segs G_10760 [Z_to_bv 8 31; Z_to_bv 8 133; Z_to_bv 8 235; Z_to_bv 8 81; Z_to_bv 8 184; Z_to_bv 8 30; Z_to_bv 8 229; Z_to_bv 8 63].

Hypothesis ent_addr_mod8 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QXOI.gw_all) (@QXOI.ent_addr_mod8) (base + 484)%Z)) in let T := eval cbv beta delta [QXOI.u_lh_entry_free_entry QXOI.u_lh_table_free_entry] in T in let T := gw_fold_pcs T base (484)%Z [0; 48; 80]%Z in exact T).
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
#[using="w_12 w_13 hi_12 lo_13 G_10760 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI AL_gTP RNG_gTP e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_12 E_12 D_13 E_13 ANCH_13 RNG_G_10760 ROM_G_10760 ent_addr_mod8 U4F"] Lemma gw_all : True. Proof. exact I. Qed.

Section UStore.
Variables (sp gp tp : word) (s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v opts : Z) (es : list lent) (svs : list slotv) (ffn : Z).
Variables (rac s0c s1c s2c s3c s4c : word).

Lemma lh_store_block : ltac:(let u := constr:(ltac:(gw_ctx2 (@Lh2InsStmt.u_store_block_stmt))) in
  exact (u sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc t tbl size k v opts svs ffn rac s0c s1c s2c s3c s4c)).
Proof.
  unfold Lh2InsStmt.u_store_block_stmt.
  clear - w_12 w_13 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE ent_addr_mod8.
  pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
  intros until lo. intros Hg Hsz Hlen Esg Hcnt Hk Hv Hffn Hop TAIL Ht0 Hta Ht Hb0 Hba Hb SEP LOS MI HDR SL FR ST.
  subst opts.
  pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR.
  unfold Lh2InsStmt.u_ins_frame in FR. unfold Lh2InsStmt.hdr_cells in HDR.
  pose proof (SL _ _ Esg) as CG. unfold ent_addr, slot_cells in CG. rewrite Z2Nat.id in CG by lia.
  pose proof (wmono_refl segs m) as WM.
  unfold QxiR.u_ins_regs. replace (tbl + g * 40) with (tbl + 40 * g) by lia.
  destruct TAIL as [[Hhd Htl] | (Hhd & Htl & Esl & NEl & HhdR)].
  -
    subst hd tl.
    pose proof (munch_refl [(t, t + 56); (tbl + 40 * g, tbl + 40 * g + 40)] m) as MU.
    remember (tbl + 40 * g) as B eqn:EB.
    step. step. ub_if_lit.
    do 6 step.
    step. norm_w32. if_falsex.
    do 2 step.
    step. ub_if_lit.
    step. step. stepz. stepz.
    do 8 step.
    lazymatch goal with H : rw_cells segs ?mx (bv_unsigned sp + -48) _ |- _ => release_frame H ST (bv_unsigned sp) end.
    step. subst B.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. intros x Hx. cbn in Hx |- *. lia. }
    split; [exact WM|]. split; [exact MI|].
    split. { unfold Lh2InsStmt.hdr_cells. cbn [Z.eqb]. unfold ent_addr. rewrite Z2Nat.id by lia. assumption. }
    split; [| exact ST].
    unfold Q7mx.ins_svs. cbn [Z.eqb]. eapply (lh_slots_write1 segs m); [exact SL | lia | exact MU | exact WM | | ].
    + intros i NE Hi. unfold ivs_miss_slot. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn; unfold ent_addr.
      * destruct SEP; [right; lia | left; nia].
      * assert (Z.of_nat i + 1 <= g \/ g + 1 <= Z.of_nat i) as [L|R] by lia; [left; nia | right; nia].
    + unfold ent_addr, slot_cells, Q7mx.new_slot. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Z2Nat.id by lia. assumption.
  -
    pose proof (SL _ _ Esl) as CL. unfold ent_addr, slot_cells in CL.
    pose proof (proj1 (nth_error_Some svs ixl) ltac:(rewrite Esl; discriminate)) as Hixl.
    assert (NEg : Z.of_nat ixl <> g) by (intros X; apply NEl; lia).
    assert (TLal : (tbl + 40 * Z.of_nat ixl) mod 8 = 0) by (clear - Hba; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(t, t + 56); (tbl + 40 * g, tbl + 40 * g + 40); (tbl + 40 * Z.of_nat ixl, tbl + 40 * Z.of_nat ixl + 40)] m) as MU.
    remember (tbl + 40 * g) as B eqn:EB. remember (tbl + 40 * Z.of_nat ixl) as TL eqn:ETL.
    replace tl with TL in * by (subst tl TL; unfold ent_addr; reflexivity).
    step. step. ub_if_lit.
    do 6 step.
    step. norm_w32. if_falsex.
    do 2 step.
    step. norm_w32. if_falsex.
    step. step. norm_w32. if_falsex.
    step. step. ub_align_auto.
    step. stepz. step. step. step.
    do 8 step.
    lazymatch goal with H : rw_cells segs ?mx (bv_unsigned sp + -48) _ |- _ => release_frame H ST (bv_unsigned sp) end.
    step. subst B.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. intros x Hx. cbn in Hx |- *. subst TL. lia. }
    split; [exact WM|]. split; [exact MI|].
    split. { unfold Lh2InsStmt.hdr_cells. destruct (Z.eqb_spec hd 0); [lia|]. unfold ent_addr. rewrite Z2Nat.id by lia. assumption. }
    split; [| exact ST].
    unfold Q7mx.ins_svs. destruct (Z.eqb_spec hd 0); [lia|].
    eapply (lh_slots_write2 segs m); [exact SL | lia | exact Hixl | lia | exact MU | exact WM | | | ].
    + intros i NE1 NE2 Hi. unfold ivs_miss_slot. subst TL.
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn; unfold ent_addr.
      * destruct SEP; [right; lia | left; nia].
      * assert (Z.of_nat i + 1 <= g \/ g + 1 <= Z.of_nat i) as [L|R] by lia; [left; nia | right; nia].
      * assert (i + 1 <= ixl \/ ixl + 1 <= i)%nat as [L|R] by lia; [left; nia | right; nia].
    + unfold ent_addr, slot_cells, Q7mx.new_slot. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Z2Nat.id by lia. subst TL. unfold ent_addr in *. assumption.
    + unfold ent_addr, slot_cells. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite Z2Nat.id by lia. subst TL. assumption.
Qed.
End UStore.

End G.
