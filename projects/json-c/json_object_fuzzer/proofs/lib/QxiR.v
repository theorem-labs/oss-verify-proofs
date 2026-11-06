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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Mh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Mh.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAyu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAyu.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXOI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXOI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QheR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QheR.
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

Definition ulhprobe_code (w_12 w_13 : Z) : list Z :=
[0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x01413023; 0x12050e63; 0x00757793; 0x12079a63; 0x00052803; 0x00452783; w_12; w_13; 0xd2078753; 0xd20806d3; 0x12f6f7d3; 0xa2e787d3; 0x06078863; 0x400007b7; 0xfff7879b; 0x0107da63; 0x800007b7; 0xfff7879b; 0x00f81c63; 0x0340006f; 0xc00007b7; 0xfff7879b; 0x0f07d463; 0x0018179b; 0x00068413; 0x00058493; 0x00070913; 0x00060993; 0x00050a13; 0x00078593; 0xdd5ff0ef; 0x00050663; 0xfff00593; 0x1240006f; 0x000a0513; 0x000a2803; 0x00098613; 0x00090713; 0x00048593; 0x00040693; 0x0a080063; 0x01853783; 0x0306f6b3; 0x02800893; 0x031682b3; 0x00f03e33; 0x00f28333; 0x00133393; 0x087e0063; 0x06f36e63; 0x031698b3; 0x43f2d293; 0x0058c8b3; 0x011038b3; 0x06089463; 0x02800293; 0xffd00313; 0x04078e63; 0x025688b3; 0x011788b3; 0x0078fe13; 0x040e1663; 0x0008be03; 0x05c36463; 0x04078063; 0x00168893; 0x0016869b; 0x00d846b3; 0x0016b693; 0xfff68693; 0x0116f6b3; 0x025683b3; 0x00f388b3; 0x00f8ee63; 0x02569e33; 0x43f3d393; 0x007e43b3; 0x00703e33; 0x0018b393; 0xfa0e04e3; 0xc0001073; 0x0013f693; 0xfe069ce3; 0x00452783; 0x00477713; 0x0017869b; 0x00b8b023; 0x00e8a423; 0x00c8b823; 0xfcf6cee3; 0x00853583; 0x00d52223; 0x02058463; 0x01053603; 0xfc0604e3; 0x00767593; 0xfc0590e3; 0x01163c23; 0x0008bc23; 0x02c8b023; 0x01153823; 0x0140006f; 0x01153423; 0x01153823; 0x0008bc23; 0x0208b023; 0x00058513; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x00013a03; 0x03010113; 0x00008067]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

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
Hypothesis CODE : code_at segs base (ulhprobe_code w_12 w_13).
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

Section UProbe.
Variables (sp gp tp : word) (s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v opts : Z) (svs : list slotv).

Definition u_ins_regs (x1 x7 x8 x9 : word) (n : Z) (x17 x18 x19 x20 x28 x29 x30 x31 : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp (Z_to_bv 64 40) (Z_to_bv 64 (-3)) x7 x8 x9
(Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 n) (Z_to_bv 64 opts) (Z_to_bv 64 tbl) (Z_to_bv 64 size) x17
x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31.

#[using="w_12 w_13 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE ent_addr_mod8"] Lemma u_lh_probe_loop :
forall (d : nat) (n f : Z) (x1 x8 x9 x17 x18 x19 x20 x28 x29 x30 x31 : word) (m : word -> option byte) (sf : slotv),
Z.of_nat d = (f - n) mod size ->
0 <= n < size -> 0 <= f < size -> In size lf_sizes -> Z.of_nat (length svs) = size ->
nth_error svs (Z.to_nat f) = Some sf -> is_free sf ->
(forall i s, nth_error svs i = Some s -> ~ is_free s -> 0 <= sv_k s < LH_FREEDv) ->
0 < tbl -> tbl mod 16 = 0 -> tbl + 40 * size < 2^64 ->
mem_inv segs m -> lh_slots segs m tbl svs ->
evt segs (fun ms' => exists (g : Z) (sg : slotv),
0 <= g < size /\ nth_error svs (Z.to_nat g) = Some sg /\ is_free sg /\
ms' = MS (u_ins_regs x1 (Z_to_bv 64 0) x8 x9 g (Z_to_bv 64 (tbl + g * 40)) x18 x19 x20 (Z_to_bv 64 (sv_k sg)) x29 x30 x31)
F (Z_to_bv 64 (base + 0x15c)) fc None m (seg_rom segs))
(MS (u_ins_regs x1 (Z_to_bv 64 0) x8 x9 n x17 x18 x19 x20 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xfc)) fc None m (seg_rom segs)).
Proof. clear - w_12 w_13 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE ent_addr_mod8 segs base sp gp tp s5 s6 s7 s8 s9 s10 s11 F fc t tbl size k v opts svs. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
induction d as [d IH] using lt_wf_ind; intros until sf; intros Hd Hn Hf Hsz Hlen Esf FREE LIVEK Ht0 Hal Htb MI SL.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
destruct (nth_error svs (Z.to_nat n)) as [sn|] eqn:Esn.
2:{ exfalso. apply nth_error_None in Esn. lia. }
pose proof (SL _ _ Esn) as C. unfold ent_addr, slot_cells in C. rewrite Z2Nat.id in C by lia.
unfold u_ins_regs.
step. if_falsex.
step. rewrite (unsigned_lit n) by lia. step.
step. rewrite (unsigned_lit (tbl + n * 40)) by lia.
rewrite (land7_of_mod8 (tbl + n * 40)) by (replace (tbl + n * 40) with (tbl + 40 * Z.of_nat (Z.to_nat n)) by lia; apply ent_addr_mod8; exact Hal).
step. if_false.
replace (tbl + n * 40) with (tbl + 40 * n) by lia. remember (tbl + 40 * n) as B eqn:EB. step. subst B.
step. unfold bv_ltu. change (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613.
assert (FD : is_free sn \/ ~ is_free sn).
{ unfold is_free. destruct (Z.eq_dec (sv_k sn) LH_EMPTYv); [left; left; assumption|].
destruct (Z.eq_dec (sv_k sn) LH_FREEDv); [left; right; assumption|]. right. intros [X|X]; contradiction. }
destruct FD as [FR' | NF].
-
assert (HK : sv_k sn = LH_EMPTYv \/ sv_k sn = LH_FREEDv) by exact FR'. unfold LH_EMPTYv, LH_FREEDv in HK.
rewrite (unsigned_lit (sv_k sn)) by lia. if_true.
apply evt_done. exists n, sn. split; [lia|]. split; [exact Esn|]. split; [exact FR'|].
replace (tbl + 40 * n) with (tbl + n * 40) by lia. reflexivity.
-
assert (NE : n <> f) by (intros ->; rewrite Esf in Esn; injection Esn as ->; exact (NF FREE)).
pose proof (moddist_step n f size Hn Hf NE) as STEP.
pose proof (LIVEK _ _ Esn NF) as HK. unfold LH_FREEDv in HK.
rewrite (unsigned_lit (sv_k sn)) by lia. if_false.
step. if_falsex.
step. step. norm_w32. step. rewrite (unsigned_lit size), (unsigned_lit (n + 1)) by lia.
eapply evt_cut with (P := eq (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp (Z_to_bv 64 40) (Z_to_bv 64 (-3)) (Z_to_bv 64 0) x8 x9
(Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 (next_ix size n)) (Z_to_bv 64 opts) (Z_to_bv 64 tbl) (Z_to_bv 64 size) (Z_to_bv 64 (n + 1))
x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sv_k sn)) x29 x30 x31) F (Z_to_bv 64 (base + 0x134)) fc None m (seg_rom segs))).
{ unfold next_ix. destruct (Z.eqb_spec (n + 1) size) as [EQ|NEQ].
- rewrite <- EQ, Z.lxor_nilpotent. step. rewrite (v_sltiu_1 (Z_to_bv 64 0) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. rewrite (unsigned_lit (n + 1)) by lia. change (bv_unsigned (Z_to_bv 64 (1 + -1))) with 0. rewrite Z.land_0_l. apply evt_done. reflexivity.
- pose proof (lxor_bound size (n + 1) 31 ltac:(lia) ltac:(lia) ltac:(lia)) as LB.
assert (LNZ : Z.lxor size (n + 1) <> 0) by (intros X; apply Z.lxor_eq in X; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (Z.lxor size (n + 1))) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615.
rewrite (unsigned_lit (n + 1)) by lia. rewrite land_ones64_l by lia. apply evt_done. reflexivity. }
intros ms' <-.
assert (Hn' : 0 <= next_ix size n < size) by (unfold next_ix; destruct (Z.eqb_spec (n + 1) size); lia).
step. rewrite (unsigned_lit (next_ix size n)) by lia. step.
step. if_falsex.
step. step. step. step. rewrite (mul40_chk (next_ix size n)) by lia.
step. rewrite (v_sltiu_0 (Z_to_bv 64 (next_ix size n * 40 + tbl)) 1) by (rewrite ?unsigned_lit by lia; lia).
step. if_true.
eapply (IH (Z.to_nat ((f - next_ix size n) mod size)) ltac:(lia) (next_ix size n) f);
first [exact Esf | exact FREE | exact LIVEK | exact MI | exact SL | exact Hsz | exact Hlen | exact Hal | lia | idtac].
Qed.
End UProbe.

End G.
