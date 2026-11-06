(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRGY.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwApply2 GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm; gwj_align_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm; gwj_align_norm.

Definition ulhfree_code (w_21 w_27 : Z) : list Z :=
[0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x02050e63; 0x00050413; 0x00757513; 0x02051863; 0x02043503; 0x02050663; 0x00840493; 0x0004b483; 0x02048063; 0x02043583; 0x00048513; 0x000580e7; 0x0074f513; 0x01848493; 0xfe0502e3; 0xc0001073; 0x01843503; w_21; 0x00040513; 0x01813083; 0x01013403; 0x00813483; 0x02010113; w_27]%Z.

Definition blk_17dac_code (wb17dac_14 wb17dac_16 : Z) : list Z :=
[0xff010113; 0x00113423; 0x00813023; 0x04050663; 0x00757593; 0x04059263; 0x00852583; 0x01053403; 0x00058e63; 0x02040263; 0x00040513; 0x00813083; 0x00013403; 0x01010113; wb17dac_14; 0x00053503; wb17dac_16; 0xfe0412e3; 0x00813083; 0x00013403; 0x01010113; 0x00008067; 0xc0001073]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_2 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_4 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_21 w_27 : Z).
Variables (joff_21 joff_27 : bv 21).
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

Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Hypothesis CODE : code_at segs base (ulhfree_code w_21 w_27).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 112.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Jal 1 joff_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (Jal 0 joff_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis LINK_21 : gw_anch (base + 84 + bv_signed joff_21)%Z e_free.
Hypothesis LINK_27 : gw_anch (base + 108 + bv_signed joff_27)%Z e_free.
Variable e_16ed0 : Z.
Variable wb17dac_14 : Z.  Variable joffb17dac_14 : bv 21.
Hypothesis D_b17dac_14 : decode_any (Z_to_bv 32 wb17dac_14) = Some (Jal 0 joffb17dac_14, 4%Z).
Hypothesis E_b17dac_14 : is_ecall (Z_to_bv 32 wb17dac_14) = false.
Hypothesis LINK_b17dac_14 : gw_anch (e_fn_lh_entry_free + 56 + bv_signed joffb17dac_14)%Z (e_16ed0 + 0)%Z.
Variable wb17dac_16 : Z.  Variable joffb17dac_16 : bv 21.
Hypothesis D_b17dac_16 : decode_any (Z_to_bv 32 wb17dac_16) = Some (Jal 1 joffb17dac_16, 4%Z).
Hypothesis E_b17dac_16 : is_ecall (Z_to_bv 32 wb17dac_16) = false.
Hypothesis LINK_b17dac_16 : gw_anch (e_fn_lh_entry_free + 64 + bv_signed joffb17dac_16)%Z e_free.
Hypothesis CODE_e_blk_17dac : code_at segs e_fn_lh_entry_free (blk_17dac_code wb17dac_14 wb17dac_16).
Hypothesis AL_e_blk_17dac_b4 : gw_b4 e_fn_lh_entry_free.
Hypothesis RNG_e_blk_17dac_code : gw_br e_fn_lh_entry_free 92.

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
Hypothesis LAY_POS_e_fn_lh_entry_free : gw_le 1 e_fn_lh_entry_free.
Hypothesis LAY_HI_e_fn_lh_entry_free : gw_le (e_fn_lh_entry_free + 4) 1099511627776.
Hypothesis AL_e_fn_lh_char_equal : gw_b4 e_fn_lh_char_equal.
Hypothesis RNG_e_fn_lh_char_equal : gw_br e_fn_lh_char_equal 4.
Hypothesis LAY_POS_e_fn_lh_char_equal : gw_le 1 e_fn_lh_char_equal.
Hypothesis LAY_HI_e_fn_lh_char_equal : gw_le (e_fn_lh_char_equal + 4) 1099511627776.
Hypothesis AL_e_fn_lh_char_hash : gw_b4 e_fn_lh_char_hash.
Hypothesis RNG_e_fn_lh_char_hash : gw_br e_fn_lh_char_hash 4.
Hypothesis LAY_POS_e_fn_lh_char_hash : gw_le 1 e_fn_lh_char_hash.
Hypothesis LAY_HI_e_fn_lh_char_hash : gw_le (e_fn_lh_char_hash + 4) 1099511627776.
#[using="w_21 w_27 joff_21 joff_27 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI AL_gTP RNG_gTP e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_21 E_21 D_27 E_27 LINK_21 LINK_27 e_16ed0 wb17dac_14 joffb17dac_14 D_b17dac_14 E_b17dac_14 LINK_b17dac_14 wb17dac_16 joffb17dac_16 D_b17dac_16 E_b17dac_16 LINK_b17dac_16 CODE_e_blk_17dac AL_e_blk_17dac_b4 RNG_e_blk_17dac_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal AL_e_fn_lh_char_hash RNG_e_fn_lh_char_hash LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash U4F"] Lemma gw_all : True. Proof. exact I. Qed.

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
Ltac gj_fn_cbn := try (progress cbn [U4F fn_lh_char_equal fn_lh_char_hash fn_lh_entry_free]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section RC__1.

#[using="Type"] Lemma ent_addr_mod8 : forall tbl i, tbl mod 16 = 0 -> (tbl + 40 * Z.of_nat i) mod 8 = 0.
Proof. clear - segs.
intros tbl i H. apply Z.mod_divide; [lia|]. apply Z.divide_add_r.
- apply (Z.divide_trans 8 16 tbl); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact H]].
- exists (5 * Z.of_nat i). lia.
Qed.

Section ULhFree.
Variable HIx : heap_iface U4L.
Notation HEAPx := (HEAP U4L HIx).

Definition u_lh_entry_free_entry : Z := (e_fn_lh_entry_free + 0x0).
Definition u_lh_table_free_entry : Z := (base + 0x0).

Definition u_lh_entry_free_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS U4L HIx) (r : word),
ret_state U4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres U4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv] /\
HEAPx A' LB m' md'.

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_char_hash e_fn_lh_char_equal wb17dac_14 wb17dac_16 D_b17dac_16 E_b17dac_16 LINK_b17dac_16 CODE_e_blk_17dac AL_e_blk_17dac_b4 RNG_e_blk_17dac_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash joffb17dac_16"] Lemma u_lh_entry_free_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS U4L HIx) (LB : list blk) (p k kn pad nx pv lo : Z) (errv : word),
HEAPx A ((k, kn) :: LB) m md ->
rw_cells segs m p [C8 (Z_to_bv 64 k); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 pad); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 pv)] ->
p + 40 <= alloc_ceiling -> (p + 40 <= 0x10000 \/ gIMG_HI <= p) -> 0 < p -> p mod 8 = 0 ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top U4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 p ->
(forall ms' md', u_lh_entry_free_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo errv ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 u_lh_entry_free_entry) fc None m (seg_rom segs)) md) T.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_char_hash e_fn_lh_char_equal wb17dac_14 wb17dac_16 D_b17dac_16 E_b17dac_16 LINK_b17dac_16 CODE_e_blk_17dac AL_e_blk_17dac_b4 RNG_e_blk_17dac_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash joffb17dac_16 segs gTP gIMG_HI HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_entry_free as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_equal as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_equal as gL5_; unfold gw_le in gL5_. pose proof LAY_POS_e_fn_lh_char_hash as gL6_; unfold gw_le in gL6_. pose proof LAY_HI_e_fn_lh_char_hash as gL7_; unfold gw_le in gL7_.
intros until errv. intros HP ENT Php Pimg PNZ PAL ST LO LOS SPA HT ERR TP RA A0 K.
unfold_consts. word_range sp SPR.
pose proof (rw_cells_bound segs m p _ ENT) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs U4L] in MI.
pose proof (heap_pres_refl U4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. unfold u_lh_entry_free_entry. subst a0.
carve_frame 16%nat ST.
do 3 step.
step. if_falsex. step. step. rewrite (unsigned_lit p) by lia. rewrite (land7_of_mod8 p PAL). if_false.
step. norm_sx32. step. step. if_true.
step. step.

alloc_call (hi_free U4L HIx) U4L HIx HP MU WM MI.
{ right. exists kn. left. reflexivity. }
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. cbn [hl_segs U4L] in *.
rewrite lb_remove_head in HPR2, HP2.
extend_pres U4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs U4L] in FR.
clear MU WM MI ST ENT.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs U4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_false. do 4 step.
apply evt_RZ_done. apply K. unfold u_lh_entry_free_post.
exists m2, A2. eexists.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | exact HP2]]]]].
- unfold ret_state. cbn [hl_segs U4L]. repeat eexists; reflexivity.
- release_frame FR ST2 (bv_unsigned sp). exact ST2.
Qed.

Variables (sp gp : word) (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo t tbl size : Z) (es : list lent) (svs : list slotv) (T : TSet).
Variables (s0c s1c rac : word).

Definition u_free_frame (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells segs m (bv_unsigned sp + -32) [CB 8 junk8; C8 s1c; C8 s0c; C8 rac].

Definition u_free_exit (errv : word) (K0 : machine_state -> Model -> Prop) : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (md : Model) (A : AS U4L HIx) (junk8 : list byte)
(hsz hcnt hhd htl : Z),
HEAPx A ((t, 56) :: (tbl, 40 * size) :: LB) m md ->
rw_cells segs m t [C4 (Z_to_bv 64 hsz); C4 (Z_to_bv 64 hcnt); C8 (Z_to_bv 64 hhd); C8 (Z_to_bv 64 htl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 (fn_lh_entry_free U4F)); C8 (Z_to_bv 64 (fn_lh_char_hash U4F)); C8 (Z_to_bv 64 (fn_lh_char_equal U4F))] ->
stk segs m lo (bv_unsigned sp + -32) ->
u_free_frame m junk8 ->
rw_cells segs m (gTP - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres U4L LB (bv_unsigned sp) m0 m ->
K0 (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x50)) fc None m (seg_rom segs)) md.

#[using="Type"] Lemma u_ent_addr_pos : forall i, 0 < tbl -> 0 < ent_addr tbl i.
Proof. clear - HIx sp gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo t tbl size es svs T s0c s1c rac. intros. unfold ent_addr. lia. Qed.

#[using="w_21 w_27 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER wb17dac_14 wb17dac_16 D_b17dac_16 E_b17dac_16 LINK_b17dac_16 CODE_e_blk_17dac AL_e_blk_17dac_b4 RNG_e_blk_17dac_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash joffb17dac_16"] Lemma u_lh_free_loop :
forall (k j : nat) (e : lent) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS U4L HIx) (errv : word) (junk8 : list byte) (hsz hcnt hhd htl : Z),
(k = length es - S j)%nat -> nth_error es j = Some e ->
HEAPx A (map kblk (skipn j es) ++ (t, 56) :: (tbl, 40 * size) :: LB) m md ->
lh_slots segs m tbl svs -> lh_link tbl es svs -> Z.of_nat (length svs) = size ->
(forall e, In e es -> le_v e = 0) ->
rw_cells segs m t [C4 (Z_to_bv 64 hsz); C4 (Z_to_bv 64 hcnt); C8 (Z_to_bv 64 hhd); C8 (Z_to_bv 64 htl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 (fn_lh_entry_free U4F)); C8 (Z_to_bv 64 (fn_lh_char_hash U4F)); C8 (Z_to_bv 64 (fn_lh_char_equal U4F))] ->
stk segs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top U4L HIx ->
u_free_frame m junk8 ->
rw_cells segs m (gTP - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres U4L LB (bv_unsigned sp) m0 m ->
u_free_exit errv (fun ms md => realizes segs (mkCfg ms md) T) ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 (ent_addr tbl (le_ix e))) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x30)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_21 w_27 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER wb17dac_14 wb17dac_16 D_b17dac_16 E_b17dac_16 LINK_b17dac_16 CODE_e_blk_17dac AL_e_blk_17dac_b4 RNG_e_blk_17dac_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash joffb17dac_16 segs base gTP U4F HIx sp gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo t tbl size es svs T s0c s1c rac. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_entry_free as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_equal as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_equal as gL5_; unfold gw_le in gL5_. pose proof LAY_POS_e_fn_lh_char_hash as gL6_; unfold gw_le in gL6_. pose proof LAY_HI_e_fn_lh_char_hash as gL7_; unfold gw_le in gL7_.
induction k as [|k IH]; intros until htl; intros Hk Hj HP SL LINK Hlen VZ HDR ST LO LOS SPA HT FR ERR VM0 HPR KX.
-
pose proof (proj1 (nth_error_Some es j) ltac:(rewrite Hj; discriminate)) as Hjlt.
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (LK1 j e Hj) as (sv & Esv & Ek & Ekc & Ev & Enx & Epv).
pose proof (SL (le_ix e) sv Esv) as C. unfold slot_cells in C. rewrite Ek, Ekc, Ev, Enx, Epv in C.
rewrite (VZ e (nth_error_In _ _ Hj)) in C.
assert (NX : nx_of tbl es j = 0).
{ unfold nx_of. destruct (nth_error es (S j)) eqn:E2; [|reflexivity].
pose proof (proj1 (nth_error_Some es (S j)) ltac:(rewrite E2; discriminate)). lia. }
rewrite NX in C.
unfold u_free_frame in FR. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs U4L] in MI.
replace (skipn j es) with [e] in HP.
2:{ symmetry. rewrite <- (firstn_skipn j es) in Hj. rewrite nth_error_app2 in Hj by (rewrite length_firstn; lia).
rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hj by lia.
destruct (skipn j es) as [|e' tl] eqn:ES; [discriminate|]. cbn in Hj. injection Hj as ->.
apply (f_equal (@length lent)) in ES. rewrite length_skipn in ES. cbn in ES. destruct tl; [reflexivity | cbn in ES; lia]. }
cbn [map app kblk] in HP.
pose proof (heap_blk U4L HIx _ _ _ _ t 56 HP ltac:(right; left; reflexivity)) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk U4L HIx _ _ _ _ tbl (40 * size) HP ltac:(right; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heap_blk_img U4L HIx _ _ _ _ tbl (40 * size) HP ltac:(right; right; left; reflexivity)) as Hbimg. cbn [hl_img_lo hl_img_hi U4L] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi.
pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Esv; discriminate)) as Hix.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|].
step. unfold ent_addr. if_falsex. change (tbl + 40 * Z.of_nat (le_ix e)) with (ent_addr tbl (le_ix e)). step. step. step.

cbn [fn_lh_entry_free U4F]. gw_ret_pc_var_tac.
apply evt_RZ_done.
eapply (u_lh_entry_free_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md T A ((t, 56) :: (tbl, 40 * size) :: LB)
(ent_addr tbl (le_ix e)) (le_k e) (le_kn e) (sv_pad sv) 0 (pv_of tbl es j) lo errv);
[ heap_now U4L HIx HP MU WM MI | ..]; try alloc_side.
{ unfold ent_addr in *. clia. }
{ unfold ent_addr in *. destruct Hbimg; [left; nia | right; lia]. }
all: try (unfold ent_addr; lia).
all: try (apply ent_addr_mod8; assumption).
intros ms2 md2 (m2 & A2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->). cbn [hl_segs U4L] in *.
rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2 by lia. rewrite (unsigned_lit (bv_unsigned sp + -32)) in HPR2 by lia.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs U4L] in FR.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs U4L] in HDR.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR2) in C; [| eapply client_range_block; [right; left; reflexivity | unfold ent_addr; lia | cbn; unfold ent_addr; nia]]. cbn [hl_segs U4L] in C.
assert (HPR' : heap_pres U4L LB (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; right; right; exact Hb]. }
clear MU WM MI ST.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs U4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. rewrite (unsigned_lit (ent_addr tbl (le_ix e))) by (unfold ent_addr; lia). rewrite (land7_of_mod8 (ent_addr tbl (le_ix e))) by (apply ent_addr_mod8; assumption).
step. step. if_true. step. step. if_true.
apply evt_RZ_done. eapply KX; [exact HP2 | exact HDR | exact ST2 | exact FR | exact ERR2 | eapply model_vm_only_trans; eassumption | exact HPR'].
-
pose proof (proj1 (nth_error_Some es j) ltac:(rewrite Hj; discriminate)) as Hjlt.
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (LK1 j e Hj) as (sv & Esv & Ek & Ekc & Ev & Enx & Epv).
pose proof (SL (le_ix e) sv Esv) as C. unfold slot_cells in C. rewrite Ek, Ekc, Ev, Enx, Epv in C.
rewrite (VZ e (nth_error_In _ _ Hj)) in C.
destruct (nth_error es (S j)) as [e'|] eqn:E2.
2:{ exfalso. apply nth_error_None in E2. lia. }
assert (NX : nx_of tbl es j = ent_addr tbl (le_ix e')) by (unfold nx_of; rewrite E2; reflexivity).
rewrite NX in C.
destruct (LK1 (S j) e' E2) as (sv' & Esv' & _). pose proof (proj1 (nth_error_Some svs (le_ix e')) ltac:(rewrite Esv'; discriminate)) as Hix'.
unfold u_free_frame in FR. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs U4L] in MI.
assert (SK : skipn j es = e :: skipn (S j) es).
{ rewrite <- (firstn_skipn j es) in Hj. rewrite nth_error_app2 in Hj by (rewrite length_firstn; lia).
rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hj by lia.
remember (skipn j es) as sk eqn:ES. destruct sk as [|e0 tl]; [discriminate|]. cbn in Hj. injection Hj as ->.
f_equal. change tl with (skipn 1 (e :: tl)). rewrite ES, skipn_skipn. reflexivity. }
rewrite SK in HP. cbn [map app] in HP. unfold kblk at 1 in HP.
pose proof (heap_blk U4L HIx _ _ _ _ t 56 HP ltac:(right; apply in_or_app; right; left; reflexivity)) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk U4L HIx _ _ _ _ tbl (40 * size) HP ltac:(right; apply in_or_app; right; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heap_blk_img U4L HIx _ _ _ _ tbl (40 * size) HP ltac:(right; apply in_or_app; right; right; left; reflexivity)) as Hbimg. cbn [hl_img_lo hl_img_hi U4L] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi.
pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Esv; discriminate)) as Hix.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|].
step. unfold ent_addr. if_falsex. change (tbl + 40 * Z.of_nat (le_ix e)) with (ent_addr tbl (le_ix e)). step. step. step.

cbn [fn_lh_entry_free U4F]. gw_ret_pc_var_tac.
apply evt_RZ_done.
eapply (u_lh_entry_free_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md T A (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * size) :: LB)
(ent_addr tbl (le_ix e)) (le_k e) (le_kn e) (sv_pad sv) (ent_addr tbl (le_ix e')) (pv_of tbl es j) lo errv);
[ heap_now U4L HIx HP MU WM MI | ..]; try alloc_side.
{ unfold ent_addr in *. clia. }
{ unfold ent_addr in *. destruct Hbimg; [left; nia | right; lia]. }
all: try (unfold ent_addr; lia).
all: try (apply ent_addr_mod8; assumption).
intros ms2 md2 (m2 & A2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->). cbn [hl_segs U4L] in *.
rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2 by lia. rewrite (unsigned_lit (bv_unsigned sp + -32)) in HPR2 by lia.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs U4L] in FR.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [apply in_or_app; right; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs U4L] in HDR.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR2) in C; [| eapply client_range_block; [apply in_or_app; right; right; left; reflexivity | unfold ent_addr; lia | cbn; unfold ent_addr; nia]]. cbn [hl_segs U4L] in C.
assert (HPR' : heap_pres U4L LB (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; apply in_or_app; right; right; right; exact Hb]. }
clear MU WM MI ST.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs U4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. rewrite (unsigned_lit (ent_addr tbl (le_ix e))) by (unfold ent_addr; lia). rewrite (land7_of_mod8 (ent_addr tbl (le_ix e))) by (apply ent_addr_mod8; assumption).
step. step. if_true. step.
apply evt_RZ_done.
eapply (IH (S j) e'); first [exact E2 | exact HP2 | exact HDR | exact ST2 | exact FR | exact ERR2 | exact HPR' | exact KX | idtac].
+ lia.
+ eapply (lh_slots_pres U4L); [exact HPR2 | apply in_or_app; right; right; left; reflexivity | exact Hlen | exact SL].
+ split; [exact LK1 | split; [exact LK2 | split; [exact LK3 | exact LK4]]].
+ exact Hlen.
+ exact VZ.
+ clia.
+ lia.
+ exact SPA.
+ exact HT.
+ eapply model_vm_only_trans; eassumption.
Qed.

Definition u_lh_table_free_post (errv : word) (ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS U4L HIx) (r : word),
ret_statew U4L rac sp gp (Z_to_bv 64 gTP) s0c s1c s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md0 md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres U4L LB (bv_unsigned sp) m0 m' /\
rw_cells segs m' (gTP - 164) [C4 errv] /\
HEAPx A' LB m' md'.

#[using="w_21 w_27 joff_21 joff_27 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_21 E_21 D_27 E_27 LINK_21 LINK_27 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash"] Lemma u_lh_u_free_exit_ok : forall errv,
alloc_ceiling <= lo -> lo <= bv_unsigned sp + -32 - 16 - 8256 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top U4L HIx ->
bv_unsigned rac mod 2 = 0 -> 0 <= size ->
(forall ms' md', u_lh_table_free_post errv ms' md' -> realizes segs (mkCfg ms' md') T) ->
u_free_exit errv (fun ms md => realizes segs (mkCfg ms md) T).
Proof. clear - w_21 w_27 joff_21 joff_27 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_21 E_21 D_27 E_27 LINK_21 LINK_27 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash segs HIx sp gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo t tbl size es svs T s0c s1c rac. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_entry_free as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_equal as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_equal as gL5_; unfold gw_le in gL5_. pose proof LAY_POS_e_fn_lh_char_hash as gL6_; unfold gw_le in gL6_. pose proof LAY_HI_e_fn_lh_char_hash as gL7_; unfold gw_le in gL7_.
intros errv LO LOS SPA HT RA Hsz K. unfold u_free_exit. intros until htl. intros HP HDR ST FR ERR VM0 HPR.
unfold u_free_frame in FR. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs U4L] in MI.
destruct (blocks2 U4L HIx _ _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
cbn [hl_img_lo hl_img_hi U4L] in Himg, Himg2. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (blk_ne_01 U4L HIx _ _ _ _ _ _ _ _ HP) as Hne.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|].
step. step.

alloc_call (hi_free U4L HIx) U4L HIx HP MU WM MI.
{ right. exists (40 * size). right; left. reflexivity. }
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. cbn [hl_segs U4L] in *.
rewrite lb_remove_other in HPR2, HP2 by (cbn; lia). rewrite lb_remove_head in HPR2, HP2.
extend_pres U4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells U4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs U4L] in FR.
clear MU WM MI ST HDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs U4L] in MI.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
do 5 step.
release_frame FR ST2 (bv_unsigned sp).
step.

alloc_call (hi_free U4L HIx) U4L HIx HP2 MU WM MI.
{ right. exists 56. left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs U4L] in *.
rewrite lb_remove_head in HP3, HPR3.
extend_pres U4L HIx HPR MU WM HP2 HPR3.
apply K. unfold u_lh_table_free_post.
exists m3, A3, r3.
split; [| split; [| split; [exact ST3 | split; [exact HPR | split; [exact ERR3 | exact HP3]]]]].
+ apply ret_statew_same.
+ eapply model_vm_only_trans; [| exact VM3]. eapply model_vm_only_trans; eassumption.
Qed.

#[using="w_21 w_27 joff_21 joff_27 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_21 E_21 D_27 E_27 LINK_21 LINK_27 wb17dac_14 wb17dac_16 D_b17dac_16 E_b17dac_16 LINK_b17dac_16 CODE_e_blk_17dac AL_e_blk_17dac_b4 RNG_e_blk_17dac_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash joffb17dac_16"] Lemma u_lh_table_free_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : AS U4L HIx) (kvs : list (Z * Z)) (errv : word),
HEAPx A (lh_blocks t tbl size es ++ LB) m0 md0 ->
lh_open segs U4F m0 t tbl size es svs ->
(forall e, In e es -> le_v e = 0) ->
stk segs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top U4L HIx ->
rw_cells segs m0 (gTP - 164) [C4 errv] ->
bv_unsigned rac mod 2 = 0 ->
a0 = Z_to_bv 64 t ->
(forall ms' md', u_lh_table_free_post errv ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR rac sp gp (Z_to_bv 64 gTP) t0 t1 t2 s0c s1c a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 u_lh_table_free_entry) fc None m0 (seg_rom segs)) md0) T.
Proof. clear - w_21 w_27 joff_21 joff_27 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_21 E_21 D_27 E_27 LINK_21 LINK_27 wb17dac_14 wb17dac_16 D_b17dac_16 E_b17dac_16 LINK_b17dac_16 CODE_e_blk_17dac AL_e_blk_17dac_b4 RNG_e_blk_17dac_code LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_hash LAY_HI_e_fn_lh_char_hash joffb17dac_16 segs gTP U4F HIx sp gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo t tbl size es svs T s0c s1c rac. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_entry_free as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_lh_char_equal as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_lh_char_equal as gL5_; unfold gw_le in gL5_. pose proof LAY_POS_e_fn_lh_char_hash as gL6_; unfold gw_le in gL6_. pose proof LAY_HI_e_fn_lh_char_hash as gL7_; unfold gw_le in gL7_.
intros until errv. intros HP OPEN VZ ST LO LOS SPA HT ERR RA A0 K.
destruct OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. unfold lh_blocks in HP. cbn [app] in HP.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs U4L] in MI.
destruct (blocks2 U4L HIx _ _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
cbn [hl_img_lo hl_img_hi U4L] in Himg, Himg2. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (heap_pres_refl U4L LB (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl segs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m0) as MU.
apply rz_evt; [exact MOK|]. unfold u_lh_table_free_entry. subst a0.
carve_frame 32%nat ST.
do 4 step. step. if_falsex. step. step. step. ubsan_align Hal. step. cbn [fn_lh_entry_free U4F]. step. if_false.
step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPx A ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) m1 md0).
{ eapply (heap_frame U4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok U4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP. }
assert (HPR1 : heap_pres U4L LB (bv_unsigned sp) m0 m1).
{ eapply (heap_pres_of_munch U4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside U4L HIx); [exact HP | intros b Hb; right; right; apply in_or_app; right; exact Hb | clia |].
solve_clientW U4L HIx HP. }
pose proof (u_lh_u_free_exit_ok errv ltac:(clia) ltac:(lia) SPA HT RA ltac:(lia) K) as EXIT.
assert (SL1 : lh_slots segs m1 tbl svs).
{ eapply (lh_slots_frame segs m0 m1 tbl svs _ SL MU WM). intros i Hi. apply Forall_cons; [|apply Forall_nil].
cbn. unfold ent_addr. left. lia. }
rewrite hd_of_nth in *.
destruct (nth_error es 0) as [e0|] eqn:E0.
2:{
step. if_true.
apply evt_RZ_done.
assert (ES : es = []) by (destruct es; [reflexivity | discriminate]). rewrite ES in HP1. cbn [map app] in HP1.
eapply EXIT; [exact HP1 | exact HDR | exact ST | exact FR | exact ERR | apply model_vm_only_refl | exact HPR1]. }
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (LK1 0%nat e0 E0) as (sv0 & Esv0 & _).
pose proof (proj1 (nth_error_Some svs (le_ix e0)) ltac:(rewrite Esv0; discriminate)) as Hix0.
pose proof (proj1 (nth_error_Some es 0) ltac:(rewrite E0; discriminate)) as Hes0.
apply evt_RZ_done.
eapply (u_lh_free_loop (length es - 1) 0 e0);
first [ exact HDR | exact ST | exact FR | exact ERR | exact HPR1 | exact EXIT | exact SL1 | exact Hlen | exact VZ | exact SPA | exact HT
| apply model_vm_only_refl | exact E0 | idtac ].
all: lazymatch goal with
| |- HEAP _ _ _ _ _ _ =>
cbn [skipn]; eapply heap_perm; [exact HP1|];
change ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) with ([(t, 56); (tbl, 40 * size)] ++ (map kblk es ++ LB));
change (map kblk es ++ (t, 56) :: (tbl, 40 * size) :: LB) with (map kblk es ++ [(t, 56); (tbl, 40 * size)] ++ LB);
apply Permutation_app_swap_app
| |- lh_link _ _ _ => split; [exact LK1 | split; [exact LK2 | split; [exact LK3 | exact LK4]]]
| |- _ => first [clia | lia]
end.
Qed.
End ULhFree.

End RC__1.

End G.
