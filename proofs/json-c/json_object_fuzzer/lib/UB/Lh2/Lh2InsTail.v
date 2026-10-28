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
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm; gwj_align_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm; gwj_align_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QxiR Q7mx.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH1t.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Lh2 Require Lh2InsStmt.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq QrIP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Lh1 Require Lh1Store.

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

Definition u_probe_loop := ltac:(let p := constr:(ltac:(gw_ctx2 (@QxiR.u_lh_probe_loop))) in exact p).

Section UStore.
Variables (sp gp tp : word) (s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v opts : Z) (es : list lent) (svs : list slotv) (ffn : Z).
Variables (rac s0c s1c s2c s3c s4c : word).

#[using="w_12 w_13 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE ent_addr_mod8"] Lemma u_lh_insert_tail :
  ltac:(let s := constr:(ltac:(gw_ctx2 (@Lh2InsStmt.u_store_block_stmt))) in
        let u := constr:(ltac:(gw_ctx2 (@Lh2InsStmt.u_ins_tail_stmt))) in
        exact (s sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc t tbl size k v opts svs ffn rac s0c s1c s2c s3c s4c ->
               u sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc t tbl size k v opts es svs ffn rac s0c s1c s2c s3c s4c)).
Proof.
pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros STORE. unfold Lh2InsStmt.u_ins_tail_stmt.
intros h cnt lo x1 x5 x6 x7 x8 x9 x15 x17 x18 x19 x20 x28 x29 x30 x31 m.
intros Hh Hsz Hlen Hcnt Hcs LINK KEYS Hk Hv Hffn Hopts Ht0 Htal Ht Hb0 Hbal Hb SEP LOS MI HDR SL FR ST.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR.
pose proof HDR as HDR0. unfold Lh2InsStmt.hdr_cells in HDR.
pose proof LINK as (LK1 & LK2 & LK3 & LK4).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
step. if_falsex.
step. step. step. step. step. step. step. step.
rewrite remu_lit by lia.
pose proof (Z.mod_pos_bound h size ltac:(lia)) as HM. set (n := h mod size) in *.
rewrite (unsigned_lit n) by lia.
rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 tbl)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_sltiu_0 (Z_to_bv 64 (n * 40 + tbl)) 1) by (rewrite ?unsigned_lit by lia; lia).
if_falsex.
step. if_falsex.
step. step. step. step. step.
rewrite (mul40_chk n) by lia.
if_falsex.
step. step.

assert (LIVEK : forall i s, nth_error svs i = Some s -> ~ is_free s -> 0 <= sv_k s < LH_FREEDv).
{ intros i s E NF. destruct (in_dec Nat.eq_dec i (map le_ix es)) as [IN | NI].
- apply in_map_iff in IN as (e & Hix & He). destruct (In_nth_error _ _ He) as [j Hj].
destruct (LK1 j e Hj) as (s' & Es' & Ek & _). rewrite Hix, E in Es'. injection Es' as <-.
destruct (LK4 e He) as (K0 & KF & _ & _). destruct (lh_key_bytes segs m es e KEYS He) as (_ & _ & KL). rewrite Ek. lia.
- exfalso. apply NF. exact (LK2 i s E NI). }
pose proof (lf_thr_lt size Hsz) as Hlt.
destruct (free_slot_exists (map le_ix es) (length svs) LK3 ltac:(rewrite length_map; lia)) as (f & Hf & NIf).
destruct (nth_error svs f) as [sf|] eqn:Esf; [| exfalso; apply nth_error_None in Esf; lia].
pose proof (LK2 f sf Esf NIf) as FRf.
eapply evt_cut.
{ eapply (u_probe_loop sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc t tbl size k v opts svs (Z.to_nat ((Z.of_nat f - n) mod size)) n (Z.of_nat f));
  first [exact Hsz | exact Hlen | exact LIVEK | exact MI | exact SL | exact Hbal | lia | idtac].
  - rewrite Nat2Z.id. exact Esf.
  - exact FRf. }
cbv beta. intros ms' (gz & sgz & Hgz & Esgz & FREEz & ->).
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
split; [lia|]. split; [rewrite (QH1t.tl_of_last tbl es (length es - 1) el El ltac:(lia)); reflexivity|]. split; [exact Esl|]. split; [| lia].
intros X. apply NIN. unfold g. rewrite <- X. apply in_map. eapply nth_error_In. exact El.
+ intros _. exists (length es - 1)%nat, el. repeat split; try assumption. lia. }
destruct TL as (ixl & sl & TAIL & LAST).
unfold Lh2InsStmt.u_store_block_stmt in STORE.
eapply evt_mono.
- eapply (STORE gz sgz cnt (hd_of tbl es) (tl_of tbl es) ixl sl);
  first [exact Esgz | exact Hsz | exact Hlen | exact TAIL | exact MI | exact HDR0 | exact SL | exact FR | exact ST | exact SEP | exact Hffn | exact Hopts | exact Htal | exact Hbal | lia | idtac].
  all: try lia.
- cbv beta. intros ms' (x5' & x6' & x7' & x11' & x12' & x13' & x14' & x15' & x16' & x17' & x28' & x29' & x30' & x31' & m' & -> & MU' & WM' & MI' & HDR' & SL' & ST').
unfold Lh2InsStmt.u_ins_tail_post. exists g, sgz, ixl, sl, x5', x6', x7', x11', x12', x13', x14', x15', x16', x17', x28', x29', x30', x31', m'.
split; [unfold g; lia|]. split; [exact Esgz|]. split; [exact FREEz|]. split; [exact NIN|]. split; [exact LAST|].
split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [| split; [| exact ST']].
+ destruct es; cbn [hd_of] in HDR' |- *; [exact HDR' |]. unfold ent_addr in HDR' |- *.
destruct (Z.eqb_spec (tbl + 40 * Z.of_nat (le_ix l)) 0); [lia | exact HDR'].
+ exact SL'.
Qed.
End UStore.

End G.

Section UStoreI.
Variables (sp gp tp : word) (s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v opts : Z) (es : list lent) (svs : list slotv) (ffn : Z).
Variables (rac s0c s1c s2c s3c s4c : word).

#[using="Type"] Lemma u_lh_insert_tail_img : ltac2:(Q6nq.ty2 'QrIP.GwI.segs '(@u_lh_insert_tail) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply2.gw_by_name2 QrIP.GwI.segs (@u_lh_insert_tail) | autorewrite with gw_eqs; GwApply2.gw_by_name2 QrIP.GwI.segs (@u_lh_insert_tail)]. Qed.
#[using="Type"] Lemma lh_store_block_img : ltac2:(Q6nq.ty2 'QrIP.GwI.segs '(@Lh1Store.lh_store_block) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply2.gw_by_name2 QrIP.GwI.segs (@Lh1Store.lh_store_block) | autorewrite with gw_eqs; GwApply2.gw_by_name2 QrIP.GwI.segs (@Lh1Store.lh_store_block)]. Qed.
End UStoreI.
