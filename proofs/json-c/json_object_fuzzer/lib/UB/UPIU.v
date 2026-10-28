(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QnCn Q6q3 Q0Hd QRBl Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply Lib.GwApply2 Lib.GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QnCn.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Definition alfree_code (w_23 w_30 : Z) : list Z :=
[0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x01213023; 0x08050e63; 0x00050413; 0x00757513;
0x08051863; 0x00843583; 0x00043503; 0x06058263; 0x00000493; 0x00000913; 0x0180006f; 0x00843583;
0x00043503; 0x00190913; 0x00848493; 0x04b97263; 0x009505b3; 0x00a03633; 0x0015b693; 0x04d60a63;
0x03c95613; 0x04061663; 0x04a5e463; 0x04050263; 0x00a48533; 0x00757513; 0x02051c63; 0x0005b503;
0xfa050ee3; 0x01843583; 0x000580e7; 0xfb1ff06f; w_23; 0x00040513; 0x01813083; 0x01013403;
0x00813483; 0x00013903; 0x02010113; w_30; 0xc0001073]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_2 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_4 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_23 w_30 : Z).
Variables (joff_23 joff_30 : bv 21).
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
Hypothesis CODE : code_at segs base (alfree_code w_23 w_30).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 180.
Hypothesis D_23 : decode_any (Z_to_bv 32 w_23) = Some (Jal 1 joff_23, 4%Z).
Hypothesis E_23 : is_ecall (Z_to_bv 32 w_23) = false.
Hypothesis D_30 : decode_any (Z_to_bv 32 w_30) = Some (Jal 0 joff_30, 4%Z).
Hypothesis E_30 : is_ecall (Z_to_bv 32 w_30) = false.
Hypothesis LINK_23 : gw_anch (base + 144 + bv_signed joff_23)%Z e_free.
Hypothesis LINK_30 : gw_anch (base + 172 + bv_signed joff_30)%Z e_free.

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
#[using="w_23 w_30 joff_23 joff_30 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_23 E_23 D_30 E_30 LINK_23 LINK_30 AL_e_fn_arr_entry_free RNG_e_fn_arr_entry_free LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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
Ltac gj_fn_cbn := try (progress cbn [S4F fn_arr_entry_free]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section RC__1.

#[using="Type"] Lemma al_nth_null : forall ps i, Forall (fun p => p = 0) ps -> al_nth ps i = 0.
Proof. clear - segs.
intros ps i H. unfold al_nth. destruct (nth_error ps (Z.to_nat i)) as [p|] eqn:E.
- rewrite (nth_error_nth _ _ _ E). apply (proj1 (Forall_forall _ _) H). eapply nth_error_In. exact E.
- apply nth_overflow. apply nth_error_None. exact E.
Qed.

Section AlFree.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition array_list_free_entry : Z := (base + 0x0).

#[using="w_23 w_30 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free"] Lemma al_free_loop :
forall (k : nat) (i S1 : Z) (x1 x2 gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a arr len size : Z) (ps : list Z),
Z.of_nat k = len - 1 - i -> 0 <= i < len -> S1 = 8 * i -> len = Z.of_nat (length ps) -> 8 * len < 2^64 ->
0 < arr -> arr mod 16 = 0 -> arr + 8 * len <= alloc_ceiling ->
Forall (fun p => p = 0) ps ->
mem_inv segs m ->
rw_cells segs m a [C8 (Z_to_bv 64 arr); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (fn_arr_entry_free S4F))] ->
u64arr segs m arr (wl ps) ->
evt segs (fun ms => exists a2' a3', ms = MS (mkR x1 x2 gp tp t0 t1 t2 (Z_to_bv 64 a) (Z_to_bv 64 (8 * len)) (Z_to_bv 64 arr) (Z_to_bv 64 len) a2' a3' a4 a5 a6 a7 (Z_to_bv 64 len) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x90)) fc None m (seg_rom segs))
(MS (mkR x1 x2 gp tp t0 t1 t2 (Z_to_bv 64 a) (Z_to_bv 64 S1) (Z_to_bv 64 arr) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 i) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x50)) fc None m (seg_rom segs)).
Proof. clear - w_23 w_30 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free segs base S4F HIx. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_arr_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_arr_entry_free as gL3_; unfold gw_le in gL3_.
induction k as [|k IH]; intros until ps; intros Hk Hi HS1 Hlen H32 Harr0 Harr16 Harrhi NUL MI HDR ARR; subst S1.
- pose proof (u64arr_bound segs m arr (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
step. step. step. step. QRBl.ub_cmp_auto.
step. step. QRBl.ub_cmp_auto.
step. if_falsex.
step. if_falsex.
step. step. rewrite (unsigned_lit (8 * i + arr)) by lia. rewrite (QRBl.ub_land7 (8 * i + arr)) by (Z.div_mod_to_equations; lia).
step. if_false.
pose proof (al_slot_read segs m arr ps i (wa (arr + 8 * i)) ARR ltac:(lia) eq_refl) as RD.
rewrite (al_nth_null ps i NUL) in RD.
step. step. if_true. step. step. step. step. step. if_truex.
apply evt_done. do 2 eexists. replace (i + 1) with len by lia. replace (8 * i + 8) with (8 * len) by lia. reflexivity.
- pose proof (u64arr_bound segs m arr (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
step. step. step. step. QRBl.ub_cmp_auto.
step. step. QRBl.ub_cmp_auto.
step. if_falsex.
step. if_falsex.
step. step. rewrite (unsigned_lit (8 * i + arr)) by lia. rewrite (QRBl.ub_land7 (8 * i + arr)) by (Z.div_mod_to_equations; lia).
step. if_false.
pose proof (al_slot_read segs m arr ps i (wa (arr + 8 * i)) ARR ltac:(lia) eq_refl) as RD.
rewrite (al_nth_null ps i NUL) in RD.
step. step. if_true. step. step. step. step. step. if_falsex.
eapply (IH (i + 1)); [ | | | exact Hlen | | | | | exact NUL | exact MI | exact HDR | exact ARR]; lia.
Qed.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo a : Z) (T : TSet).

Definition array_list_free_post (errv : word) (ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : word),
ret_statew S4L ra sp gp (Z_to_bv 64 gTP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md0 md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m0 m' /\
rw_cells segs m' (gTP - 164) [C4 errv] /\
HEAPx A' LB m' md'.

#[using="w_23 w_30 joff_23 joff_30 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_23 E_23 D_30 E_30 LINK_23 LINK_30 LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free"] Lemma al_free_tail :
forall (x1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x18 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (arr len size : Z) (errv : word),
HEAPx A ((a, AL_SZ) :: (arr, 8 * size) :: LB) m md ->
al_hdr segs S4F m a arr len size ->
stk segs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -32 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells segs m (gTP - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
(forall ms' md', array_list_free_post errv ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 a) x9 (Z_to_bv 64 arr) a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x90)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_23 w_30 joff_23 joff_30 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_23 E_23 D_30 E_30 LINK_23 LINK_30 LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free segs base gTP S4F HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo a T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_arr_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_arr_entry_free as gL3_; unfold gw_le in gL3_.
intros until errv. intros HP HDR ST LO LOS SPA HT FR ERR RA VM0 HPR K.
unfold al_hdr in HDR. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (al_blocks S4L HIx _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
cbn [hl_img_lo hl_img_hi S4L] in Himg, Himg2. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hne.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|].
step.

alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ right. exists (8 * size). right; left. reflexivity. }
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite lb_remove_other in HPR2, HP2 by (cbn; lia). rewrite lb_remove_head in HPR2, HP2.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST HDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
do 6 step.
release_frame FR ST2 (bv_unsigned sp).
step.

alloc_call (hi_free S4L HIx) S4L HIx HP2 MU WM MI.
{ right. exists AL_SZ. left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HP3, HPR3.
extend_pres S4L HIx HPR MU WM HP2 HPR3.
apply K. unfold array_list_free_post.
exists m3, A3, r3.
split; [| split; [| split; [exact ST3 | split; [exact HPR | split; [exact ERR3 | exact HP3]]]]].
+ apply ret_statew_same.
+ eapply model_vm_only_trans; [| exact VM3]. eapply model_vm_only_trans; eassumption.
Qed.

#[using="w_23 w_30 joff_23 joff_30 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_23 E_23 D_30 E_30 LINK_23 LINK_30 LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free"] Lemma array_list_free_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(A : AS S4L HIx) (BS : list blk) (ps : list Z) (errv : word),
HEAPx A (BS ++ LB) m0 md0 ->
alist segs S4F m0 BS a ps -> Forall (fun p => p = 0) ps ->
stk segs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m0 (gTP - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 a ->
(forall ms' md', array_list_free_post errv ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp (Z_to_bv 64 gTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_free_entry) fc None m0 (seg_rom segs)) md0) T.
Proof. clear - w_23 w_30 joff_23 joff_30 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_23 E_23 D_30 E_30 LINK_23 LINK_30 LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free segs gTP S4F HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo a T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_arr_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_arr_entry_free as gL3_; unfold gw_le in gL3_.
intros until errv. intros HP AL NUL ST LO LOS SPA HT ERR RA A0 K.
destruct (alist_open segs S4F m0 BS a ps AL) as (arr & size & junk & -> & HDR & ARR & JK & Hlen & Hsz).
cbn [app] in HP. unfold al_hdr in HDR.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (al_blocks S4L HIx _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
cbn [hl_img_lo hl_img_hi S4L] in Himg, Himg2. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (u64arr_bound segs m0 arr (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length ps) as WL.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl segs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m0) as MU.
apply rz_evt; [exact MOK|]. unfold array_list_free_entry. subst a0.
carve_frame 32%nat ST.
do 5 step. step. if_falsex. step. step. step. ubsan_align Hal. step. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

assert (HP1 : HEAPx A ((a, 32) :: (arr, 8 * size) :: LB) m1 md0).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP. }
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m0 m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia |].
solve_clientW S4L HIx HP. }
destruct (Z.eq_dec (Z.of_nat (length ps)) 0) as [Z0|NZ].
- rewrite Z0. if_true.
apply evt_RZ_done.
eapply (al_free_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A arr 0 size errv);
[exact HP1 | unfold al_hdr; rewrite <- Z0; exact HDR | exact ST | clia | clia | exact SPA | exact HT
| exact FR | exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | exact K].
- if_falsex. step. step. step.
eapply evt_cut.
{ eapply (al_free_loop (Z.to_nat (Z.of_nat (length ps) - 1)) 0 0);
[ | | | reflexivity | | | | | exact NUL | exact MI | exact HDR | exact ARR]; lia. }
intros ms' (a2' & a3' & ->).
apply evt_RZ_done.
eapply (al_free_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A arr (Z.of_nat (length ps)) size errv);
[exact HP1 | exact HDR | exact ST | clia | clia | exact SPA | exact HT
| exact FR | exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | exact K].
Qed.
End AlFree.

End RC__1.

End G.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QnCn.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Definition alnew_code (w_8 w_16 w_21 : Z) : list Z :=
[0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x0405c863; 0x00058413; 0x00050493; 0x02000513;
w_8; 0x04050063; 0x00757593; 0x04059663; 0x00053423; 0x00853823; 0x00953c23; 0x00341413;
0x00050493; 0x00040513; w_16; 0x00050593; 0x00048513; 0x00b4b023; 0x00059663; w_21;
0x00000513; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0x00008067; 0xc0001073]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_2 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_4 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_8 w_16 w_21 : Z).
Variables (joff_8 joff_16 joff_21 : bv 21).
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
Hypothesis CODE : code_at segs base (alnew_code w_8 w_16 w_21).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 124.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Jal 1 joff_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_16 : decode_any (Z_to_bv 32 w_16) = Some (Jal 1 joff_16, 4%Z).
Hypothesis E_16 : is_ecall (Z_to_bv 32 w_16) = false.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Jal 1 joff_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis LINK_8 : gw_anch (base + 32 + bv_signed joff_8)%Z e_malloc.
Hypothesis LINK_16 : gw_anch (base + 72 + bv_signed joff_16)%Z e_malloc.
Hypothesis LINK_21 : gw_anch (base + 92 + bv_signed joff_21)%Z e_free.

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
#[using="w_8 w_16 w_21 joff_8 joff_16 joff_21 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_8 E_8 D_16 E_16 D_21 E_21 LINK_8 LINK_16 LINK_21 AL_e_fn_arr_entry_free RNG_e_fn_arr_entry_free LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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
Ltac gj_fn_cbn := try (progress cbn [S4F fn_arr_entry_free]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section RC__1.

Section AlNew.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition array_list_new2_entry : Z := (base + 0x0).

Definition array_list_new2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, alist segs S4F m' BS r [] /\ HEAPx A' (BS ++ LB) m' md') ).

#[using="w_8 w_16 w_21 joff_8 joff_16 joff_21 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_8 E_8 D_16 E_16 D_21 E_21 LINK_8 LINK_16 LINK_21 LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free"] Lemma array_list_new2_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (isz lo : Z) (errv : word),
HEAPx A LB m md ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 (fn_arr_entry_free S4F) -> a1 = Z_to_bv 64 isz -> 1 <= isz -> 8 * isz < 2^32 ->
(forall ms' md', array_list_new2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_new2_entry) fc None m (seg_rom segs)) md) T.
Proof. clear - w_8 w_16 w_21 joff_8 joff_16 joff_21 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_8 E_8 D_16 E_16 D_21 E_21 LINK_8 LINK_16 LINK_21 LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free segs gTP S4F HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_arr_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_arr_entry_free as gL3_; unfold gw_le in gL3_.
intros until errv. intros HP ST LO LOS SPA HT ERR TP RA A0 A1 Hisz1 Hisz2 K.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. unfold array_list_new2_entry. subst a0 a1.
carve_frame 32%nat ST.
do 5 step. if_falsex. do 4 step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST.
destruct OUT2 as [(-> & HerrHP2 & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_truex. do 5 step.
apply evt_RZ_done. apply K. unfold array_list_new2_post.
exists m2, A2, 0, e2.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | left; auto]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
-
change (Z.to_nat 32) with 32%nat in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r 32 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 32 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 32)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_falsex. step. step. ubsan_align Hal.
stepz.
step.
stepz.
step. rewrite (unsigned_lit isz) by lia. rewrite (Z.shiftl_mul_pow2 isz 3) by lia. change (2^3) with 8.
step. step. step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP2 MU WM MI.
intros ms3 m3 md3 A3 q e3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
clear MU WM MI ST2.
destruct OUT3 as [(-> & HerrHP3 & HP3) | (Hq & [junk1 BLK1] & HP3)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 32)] m3) as MU.
pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. step. stepz. step. if_false. step.

alloc_call (hi_free S4L HIx) S4L HIx HP3 MU WM MI.
{ right. exists 32. left. reflexivity. }
intros ms5 m5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR5, HP5.
extend_pres S4L HIx HPR MU WM HP3 HPR5.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST3 BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m5) as MU.
pose proof (wmono_refl segs m5) as WM.
reenter MOK5.
do 6 step.
apply evt_RZ_done. apply K. unfold array_list_new2_post.
exists m5, A5, 0, e3.
split; [| split; [| split; [| split; [exact HPR | split; [exact ERR5 | left; auto]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; [| exact VM5]. eapply model_vm_only_trans; eassumption.
* release_frame FR ST5 (bv_unsigned sp). exact ST5.
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ q (isz * 8) HP3 ltac:(left; reflexivity)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (isz * 8) HP3 ltac:(left; reflexivity)) as Himg_q. cbn [hl_img_lo hl_img_hi S4L] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP3) as Hqr.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q (isz * 8) r 32 HP3 ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hqr) as Hdj.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 32)] m3) as MU.
pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. step. step. step. if_truex. do 5 step.
apply evt_RZ_done. apply K. unfold array_list_new2_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A3, r, e3 end.
split; [| split; [| split; [| split; [ | split; [ | right]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; eassumption.
* release_frame FR ST3 (bv_unsigned sp). exact ST3.
* eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros b Hb; right; right; exact Hb | clia |].
solve_clientW S4L HIx HP3.
* eassumption.
* split; [exact Hr|]. exists [(r, 32); (q, 8 * isz)]. split.
-- exists q, isz, junk1. split; [reflexivity|]. split; [cbn; lia|]. split; [lia|]. split.
++ cbn [length Z.of_nat]. exact BLK.
++ cbn [map length Z.of_nat app]. rewrite Z.sub_0_r. replace (8 * isz) with (isz * 8) by lia. exact BLK1.
-- assert (HP3' : HEAPx A3 ((r, 32) :: (q, 8 * isz) :: LB) m3 md3).
{ eapply heap_perm; [exact HP3|]. replace (isz * 8) with (8 * isz) by lia. apply perm_swap. }
cbn [app]. eapply (heap_frame S4L HIx); [exact HP3' | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3' MU). solve_frameW_with HP3'.
Qed.
End AlNew.

End RC__1.

End G.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QCcH Q0Ek Qsw7 QJjn.
Import QnCn.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Definition alread_code : list Z :=
[0x06050063; 0x00757613; 0x04061c63; 0x00853603; 0x04c5f463; 0x00053603; 0x00359513; 0x00a60533;
0x00c036b3; 0x00153713; 0x02e68c63; 0x00100693; 0x03c69693; 0x00d585b3; 0x03d5d593; 0x02059263;
0x02c56063; 0x00060e63; 0x00757593; 0x00059a63; 0x00053503; 0x00008067; 0x00000513; 0x00008067;
0xc0001073]%Z.

Definition blk_17cb0_code : list Z :=
[0x00050a63; 0x00757593; 0x00059663; 0x00853503; 0x00008067; 0xc0001073]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (e_blk_17cb0 : Z).
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
Hypothesis CODE : code_at segs base alread_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 100.
Hypothesis CODE_e_blk_17cb0 : code_at segs e_blk_17cb0 blk_17cb0_code.
Hypothesis AL_e_blk_17cb0_b4 : gw_b4 e_blk_17cb0.
Hypothesis RNG_e_blk_17cb0_code : gw_br e_blk_17cb0 24.

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
#[using="e_blk_17cb0 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER CODE_e_blk_17cb0 AL_e_blk_17cb0_b4 RNG_e_blk_17cb0_code S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Definition array_list_length_entry : Z := (e_blk_17cb0 + 0x0).
Definition array_list_get_idx_entry : Z := (base + 0x0).

Definition array_list_length_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (ps : list Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length ps))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE_e_blk_17cb0"] Lemma array_list_length_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (BS : list blk) (a : Z) (ps : list Z),
mem_inv segs m ->
alist segs S4F m BS a ps ->
(forall b n, In (b, n) BS -> 0 < b /\ b mod 16 = 0 /\ b + n <= alloc_ceiling) ->
a0 = Z_to_bv 64 a ->
evt segs (array_list_length_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ps m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_length_entry) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE_e_blk_17cb0 segs S4F. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until ps. intros MI AL HBS A0.
destruct (alist_open segs S4F m BS a ps AL) as (arr & size & junk & -> & HDR & ARR & JK & Hlen & Hsz).
destruct (HBS a 32 ltac:(left; reflexivity)) as (Ha0 & Ha16 & Hahi). clear HBS.
unfold al_hdr in HDR.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
unfold array_list_length_entry. subst a0.
step. if_falsex. step. step. ubsan_align Ha16.
step. step.
finish.
Qed.

Definition array_list_get_idx_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (ps : list Z) (i : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1 a2 a3 a4 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if i <? Z.of_nat (length ps) then al_nth ps i else 0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE"] Lemma array_list_get_idx_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (BS : list blk) (a : Z) (ps : list Z) (i : Z),
mem_inv segs m ->
alist segs S4F m BS a ps ->
(forall b n, In (b, n) BS -> 0 < b /\ b mod 16 = 0 /\ b + n <= alloc_ceiling) ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 i -> 0 <= i < 2^64 ->
evt segs (array_list_get_idx_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ps i m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_get_idx_entry) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE segs S4F. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until i. intros MI AL HBS A0 A1 Hi.
destruct (alist_open segs S4F m BS a ps AL) as (arr & size & junk & -> & HDR & ARR & JK & Hlen & Hsz).
destruct (HBS a 32 ltac:(left; reflexivity)) as (Ha0 & Ha16 & Hahi).
destruct (HBS arr (8 * size) ltac:(right; left; reflexivity)) as (Harr0 & Harr16 & Harrhi). clear HBS.
unfold al_hdr in HDR.
pose proof (u64arr_bound segs m arr (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
unfold array_list_get_idx_entry, array_list_get_idx_post. subst a0 a1.
step. if_falsex. step. step. ubsan_align Ha16.
step. step.
destruct (Z.ltb_spec i (Z.of_nat (length ps))) as [LT|GE].
- if_falsex. step. step.
rewrite (unsigned_lit i) by lia. rewrite (Z.shiftl_mul_pow2 i 3) by lia. change (2^3) with 8.
step.
step. step. step. QRBl.ub_cmp_auto.
step. step. step. step. step. QRBl.ub_cmp_auto.
step. if_falsex.
step. if_falsex.
step. rewrite (unsigned_lit (arr + i * 8)) by lia. rewrite (QRBl.ub_land7 (arr + i * 8)) by (Z.div_mod_to_equations; lia).
step. if_false.
pose proof (al_slot_read segs m arr ps i (wa (arr + i * 8)) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
step. step. finish.
- if_truex. step. step. finish.
Qed.

End G.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QCcH Q0Ek Qsw7 QJjn.
Import QnCn.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Definition alset_code : list Z :=
[0x06050063; 0x00757693; 0x04069c63; 0x00853683; 0x04d5f463; 0x00053503; 0x00359693; 0x00d506b3;
0x00a03733; 0x0016b793; 0x02f70c63; 0x00100713; 0x03c71713; 0x00e585b3; 0x03d5d593; 0x02059263;
0x02a6e063; 0x00050e63; 0x0076f513; 0x00051a63; 0x00c6b023; 0x00008067; 0xfff00513; 0x00008067;
0xc0001073]%Z.

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
Hypothesis CODE : code_at segs base alset_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 100.

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
#[using="RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Definition array_list_set_idx_entry : Z := (base + 0x0).

Definition array_list_set_idx_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (a arr size : Z) (ps : list Z) (idx d : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1 a3 a4 a5 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if idx <? Z.of_nat (length ps) then 0 else 2^64 - 1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(arr, arr + 8 * size)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ alist segs S4F m' [(a, AL_SZ); (arr, 8 * size)] a (if idx <? Z.of_nat (length ps) then upd ps (Z.to_nat idx) d else ps).

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE"] Lemma array_list_set_idx_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a arr size : Z) (ps : list Z) (idx d : Z),
mem_inv segs m ->
alist segs S4F m [(a, AL_SZ); (arr, 8 * size)] a ps ->
(forall b n, In (b, n) [(a, AL_SZ); (arr, 8 * size)] -> 0 < b /\ b mod 16 = 0 /\ b + n <= alloc_ceiling) ->
(a + AL_SZ <= arr \/ arr + 8 * size <= a) ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 idx -> a2 = Z_to_bv 64 d -> 0 <= idx < 2^64 ->
evt segs (array_list_set_idx_post ra sp gp tp t0 t1 t2 s0 s1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc a arr size ps idx d m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_set_idx_entry) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE segs S4F. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until d. intros MI AL HBS SEP A0 A1 A2 Hi.
destruct (alist_openx segs S4F m a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz).
destruct (HBS a AL_SZ ltac:(left; reflexivity)) as (Ha0 & Ha16 & Hahi).
destruct (HBS arr (8 * size) ltac:(right; left; reflexivity)) as (Harr0 & Harr16 & Harrhi). clear HBS.
unfold al_hdr in HDR. unfold al_tail in JK.
pose proof (u64arr_bound segs m arr (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length ps) as WL.
pose proof (munch_refl [(arr, arr + 8 * size)] m) as MU. pose proof (wmono_refl segs m) as WM.
unfold array_list_set_idx_entry, array_list_set_idx_post. subst a0 a1 a2.
step. if_falsex. step. step. ubsan_align Ha16.
step. step.
destruct (Z.ltb_spec idx (Z.of_nat (length ps))) as [LT|GE].
- if_falsex. step. step.
rewrite (unsigned_lit idx) by lia. rewrite (Z.shiftl_mul_pow2 idx 3) by lia. change (2^3) with 8.
step.
step. step. step. QRBl.ub_cmp_auto.
step. step. step. step. step. QRBl.ub_cmp_auto.
step. if_falsex.
step. if_falsex.
step. rewrite (unsigned_lit (arr + idx * 8)) by lia. rewrite (QRBl.ub_land7 (arr + idx * 8)) by (Z.div_mod_to_equations; lia).
step. if_false.
pose proof (u64arr_store_ok segs m arr (wl ps) idx (wa (arr + idx * 8)) ARR ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
step.
pose proof (u64arr_write segs m arr (wl ps) idx (Z_to_bv 64 d) ARR ltac:(lia)) as ARR'.
replace (8 * idx) with (idx * 8) in ARR' by lia. rewrite <- wl_upd in ARR'.
clear ARR. store_done.
step.
apply evt_done. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
eapply alist_close. split; [| split; [exact ARR' | split; [| split; [rewrite upd_length; exact Hlen | exact Hsz]]]].
+ unfold al_hdr. rewrite upd_length. exact HDR.
+ unfold al_tail. rewrite upd_length. exact JK.
- if_truex. step. step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
apply evt_done. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact AL.
Qed.

End G.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QnCn.Mq0.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Definition alshrink_code (w_33 : Z) : list Z :=
[0x0c050063; 0x00050613; 0x00757513; 0x0a051a63; 0xfe010113; 0x00113c23; 0x00813823; 0x00913423;
0x00863403; 0xfff00513; 0x00355693; 0x408686b3; 0x06d5fe63; 0x01063683; 0x00b40433; 0x00d41663;
0x00000513; 0x0680006f; 0x0286fa63; 0x00169593; 0x00b46463; 0x00040593; 0xffd00713; 0x00175713;
0x00d76463; 0x00058413; 0x03d45593; 0x04059063; 0x00060493; 0x00063503; 0x0140006f; 0x00060493;
0x00063503; 0x00143593; 0x00b40433; 0x00341593; w_33; 0x00050593; 0xfff00513; 0x00058863;
0x00000513; 0x00b4b023; 0x0084b823; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0x00008067;
0xc0001073]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_2 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_4 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_33 : Z).
Variables (joff_33 : bv 21).
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
Hypothesis CODE : code_at segs base (alshrink_code w_33).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 196.
Hypothesis D_33 : decode_any (Z_to_bv 32 w_33) = Some (Jal 1 joff_33, 4%Z).
Hypothesis E_33 : is_ecall (Z_to_bv 32 w_33) = false.
Hypothesis LINK_33 : gw_anch (base + 144 + bv_signed joff_33)%Z e_realloc.

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
#[using="w_33 joff_33 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_33 E_33 LINK_33 AL_e_fn_arr_entry_free RNG_e_fn_arr_entry_free LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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
Ltac gj_fn_cbn := try (progress cbn [S4F fn_arr_entry_free]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section RC__1.

#[using="Type"] Lemma v_sltiu1_pos : forall x, 0 < x < 2^64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof. clear - segs.
intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
destruct (Z.ltb_spec x 1); [lia|reflexivity].
Qed.

Section AlShrink.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo a arr size : Z) (ps : list Z) (T : TSet).

Definition array_list_shrink_entry : Z := (base + 0x0).

Definition array_list_shrink_post (ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word) (arr' size' : Z),
ret_statew S4L ra sp gp (Z_to_bv 64 gTP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md0 md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m0 m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
HEAPx A' ((a, AL_SZ) :: (arr', 8 * size') :: LB) m' md' /\
alist segs S4F m' [(a, AL_SZ); (arr', 8 * size')] a ps /\
( (r = 2^64 - 1 /\ arr' = arr /\ size' = size)
\/ (r = 0 /\ size' = Z.max (Z.of_nat (length ps)) 1) ).

#[using="w_33 joff_33 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_33 E_33 LINK_33 LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free"] Lemma array_list_shrink_cps :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : AS S4L HIx) (errv : word),
HEAPx A ((a, AL_SZ) :: (arr, 8 * size) :: LB) m0 md0 ->
alist segs S4F m0 [(a, AL_SZ); (arr, 8 * size)] a ps ->
stk segs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m0 (gTP - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 0 ->
(forall ms' md', array_list_shrink_post ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp (Z_to_bv 64 gTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_shrink_entry) fc None m0 (seg_rom segs)) md0) T.
Proof. clear - w_33 joff_33 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_33 E_33 LINK_33 LAY_POS_e_fn_arr_entry_free LAY_HI_e_fn_arr_entry_free segs gTP S4F HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo a arr size ps T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_arr_entry_free as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_arr_entry_free as gL3_; unfold gw_le in gL3_.
intros until errv. intros HP AL ST LO LOS SPA HT ERR RA A0 A1 K.
destruct (alist_openx segs S4F m0 a arr size ps AL) as (junk & HDR & ARR & JK & Hlen & Hsz).
unfold al_hdr in HDR.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (al_blocks S4L HIx _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
cbn [hl_img_lo hl_img_hi S4L] in Himg, Himg2. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hne.
assert (LJ : length junk = Z.to_nat (8 * (size - Z.of_nat (length ps)))) by (destruct JK as [[[W _] _] _]; exact W).
assert (LJ' : Z.of_nat (length junk) = 8 * (size - Z.of_nat (length ps))) by (rewrite LJ; lia).
pose proof (al_arr_join segs m0 arr size ps junk ARR JK Hlen) as COMB.
assert (ALk : forall mx, rw_cells segs mx a [C8 (Z_to_bv 64 arr); C8 (Z_to_bv 64 (Z.of_nat (length ps))); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (fn_arr_entry_free S4F))] ->
rw_cells segs mx arr [CB (Z.to_nat (8 * size)) ((u64s (wl ps) ++ junk) ++ [])] ->
alist segs S4F mx [(a, AL_SZ); (arr, 8 * size)] a ps).
{ intros mx H1 H2. destruct (al_arr_split segs mx arr size size ps junk [] H2 LJ ltac:(lia)) as [X Y].
rewrite app_nil_r in Y. eapply alist_close. split; [exact H1 | split; [exact X | split; [exact Y | lia]]]. }
clear ARR JK AL LJ.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl segs m0) as WM.
change (gTP - 164) with (gTP + -164) in ERR.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (a, a + 32)] m0) as MU.
apply rz_evt; [exact MOK|]. unfold array_list_shrink_entry. subst a0 a1.
carve_frame 32%nat ST.
step. if_falsex. step. step. step. ubsan_align Hal.
do 4 step.
step. step. step. step.
step. rewrite (unsigned_lit (Z.of_nat (length ps))) by lia. if_falsex.
step. step. replace (Z.of_nat (length ps) + 0) with (Z.of_nat (length ps)) by lia.
step.
destruct (Z.eq_dec (Z.of_nat (length ps)) size) as [EQ|NE].
-
rewrite <- EQ in *. if_falsex. step. step. do 5 step.
apply evt_RZ_done. apply K. unfold array_list_shrink_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A, 0, errv, arr, (Z.of_nat (length ps)) end.
split; [| split; [apply model_vm_only_refl | split; [| split; [ | split; [ exact ERR | split; [ | split; [| right; split; [reflexivity | lia]]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST (bv_unsigned sp). exact ST.
+ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia |].
solve_clientW S4L HIx HP.
+ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP.
+ apply ALk; assumption.
-
if_truex. step. if_truex.
step. step.

eapply evt_cut with (P := eq (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 gTP) t0 t1 t2
(Z_to_bv 64 (Z.max (Z.of_nat (length ps)) 1)) (Z_to_bv 64 a)
(Z_to_bv 64 arr) (v_sltiu (Z_to_bv 64 (Z.of_nat (length ps))) 1) (Z_to_bv 64 a) (Z_to_bv 64 size) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x8c)) fc None _ (seg_rom segs))).
{ destruct (Z.eq_dec (Z.of_nat (length ps)) 0) as [Z0|NZ].
- rewrite !Z0. cbn [Z.max Z.compare Pos.compare]. step. step. apply evt_done. reflexivity.
- step. step. rewrite v_sltiu1_pos by lia. rewrite (unsigned_lit 0) by lia.
apply evt_done. rewrite Z.max_l by lia.
replace (Z.of_nat (length ps) + 0) with (Z.of_nat (length ps)) by lia. reflexivity. }
intros ms' <-.
step. rewrite (unsigned_lit (Z.max (Z.of_nat (length ps)) 1)) by lia.
rewrite (Z.shiftl_mul_pow2 (Z.max (Z.of_nat (length ps)) 1) 3) by lia. change (2^3) with 8.
step.

alloc_call (hi_realloc S4L HIx) S4L HIx HP MU WM MI.
{ right; left. reflexivity. }
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite lb_remove_other in OUT2 by (cbn; lia). rewrite lb_remove_head in OUT2.
destruct OUT2 as [(-> & HerrHP2 & HPR2 & HP2) | (Hr & HPR2 & [junk' BLK] & HP2)].
+
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in COMB; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in COMB.
clear MU WM MI ST.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. step. step. if_true. do 5 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
apply evt_RZ_done. apply K. unfold array_list_shrink_post.
exists m2, A2, (2^64 - 1), e2, arr, size.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [exact HP2| split; [apply ALk; assumption | left; repeat split; reflexivity]]]]]]].
* apply ret_statew_same.
* release_frame FR ST2 (bv_unsigned sp). exact ST2.
+
set (ns := Z.max (Z.of_nat (length ps)) 1) in *.
assert (Hns : Z.of_nat (length ps) <= ns /\ 1 <= ns /\ ns <= size) by (subst ns; lia).
assert (Ens : ns = Z.max (Z.of_nat (length ps)) 1) by reflexivity. clearbody ns.
assert (LO8 : length (u64s (wl ps) ++ junk) = Z.to_nat (8 * size)).
{ rewrite length_app, u64s_length, wl_length. lia. }
rewrite LO8, Z.min_l in BLK by lia. clear LO8.
rewrite firstn_app, u64s_length, wl_length, firstn_all2 in BLK by (rewrite u64s_length, wl_length; lia).
replace (ns * 8) with (8 * ns) in BLK, HP2 by lia.
destruct (al_arr_split segs m2 r ns ns ps (firstn (Z.to_nat (8 * ns) - 8 * length ps) junk) junk' BLK
ltac:(rewrite length_firstn; lia) ltac:(lia)) as [ARR JK]. clear BLK. unfold al_tail in JK.
assert (HP2' : HEAPx A2 ((a, 32) :: (r, 8 * ns) :: LB) m2 md2) by (eapply heap_perm; [exact HP2 | apply perm_swap]). clear HP2.
destruct (al_blocks S4L HIx _ _ _ _ _ _ _ HP2') as (_ & (Hral & Hrlo & Hrhi & Hrimg) & Hrdj).
cbn [hl_img_lo hl_img_hi S4L] in Hrimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
clear MU WM MI ST COMB.
pose proof (wl_length ps) as WL.
pose proof (u64arr_bound segs m2 r (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (heap_model_ok _ _ _ _ _ _ HP2') as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2') as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(a, a + 32)] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. step. step. if_falsex. step. step. step. do 5 step.
apply evt_RZ_done. apply K. unfold array_list_shrink_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A2, 0, e2, r, ns end.
split; [| split; [| split; [| split; [ | split; [ exact ERR2 | split; [ | split; [| right; split; [reflexivity | exact Ens]]]]]]]].
* apply ret_statew_same.
* exact VM2.
* release_frame FR ST2 (bv_unsigned sp). exact ST2.
* eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2' | intros bb Hbb0; right; right; exact Hbb0 | clia |].
solve_clientW S4L HIx HP2'.
* eapply (heap_frame S4L HIx); [exact HP2' | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2' MU). solve_frameW_with HP2'.
* eapply alist_close. split; [| split; [exact ARR | split; [exact JK | lia]]]. unfold al_hdr. assumption.
Qed.
End AlShrink.

End RC__1.

End G.
End Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG QVbl QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q0Ek.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Qsw7.
Import QQLG.Mqb.
Import QVbl.Mq3.
Import QgoP.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition f_strdup_code (w_8 : Z) : list Z :=
[0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00050413; 0x044000ef; 0x00150493; 0x00048513; w_8; 0x02050063; 0x00040593; 0x00048613; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0xff4ff06f; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0x00008067]%Z.

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_3 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_8 : Z).
Variables (joff_8 : bv 21).
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
Hypothesis CODE : code_at segs base (f_strdup_code w_8).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 88.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Jal 1 joff_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis LINK_8 : gw_anch (base + 32 + bv_signed joff_8)%Z e_malloc.

Definition strlen_post := Eval cbv beta delta [QQLG.Mqb.strlen_post] in (@QQLG.Mqb.strlen_post segs).

Definition memcpy_post := ltac:(let t := eval cbv beta delta [QVbl.Mq3.memcpy_post] in (@QVbl.Mq3.memcpy_post segs) in let t := gw_subst t (@QQLG.Mqb.strlen_post segs) strlen_post in exact t).

Hypothesis strlen_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QQLG.Mqb.gw_all) (@QQLG.Mqb.strlen_spec) (base + 88)%Z)) in let T := gw_subst T (@QQLG.Mqb.strlen_post segs) strlen_post in let T := gw_subst T (@QVbl.Mq3.memcpy_post segs) memcpy_post in let T := gw_fold_pcs T base (88)%Z [0; 28; 60; 84; 112]%Z in exact T).

Hypothesis memcpy_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq3.memcpy_spec segs (base + -1996)%Z) 3%nat in let T := gw_subst T (@QQLG.Mqb.strlen_post segs) strlen_post in let T := gw_subst T (@QVbl.Mq3.memcpy_post segs) memcpy_post in let T := gw_fold_pcs T base (-1996)%Z [0; 24; 72; 80; 96; 104; 116; 136; 164; 288; 300; 348; 380; 408; 428; 540; 576; 684; 824; 832; 908; 916; 960]%Z in exact T).

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
#[using="w_8 joff_8 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_8 E_8 LINK_8 strlen_spec memcpy_spec S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

#[using="Type"] Lemma client_range_lower_sp : forall L LB SP SP' A n,
client_range L LB SP A n -> SP' <= SP -> client_range L LB SP' A n.
Proof. clear - segs. intros L LB SP SP' A n [H|[H|H]] HS; [left; lia | right; left; exact H | right; right; exact H]. Qed.

#[using="gTP gIMG_LO gIMG_HI gH2 gH3 LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma fresh_block_sep : forall L (HIx : heap_iface L) A LB m md r n SP S k,
HEAP L HIx A ((r, n) :: LB) m md -> alloc_ceiling <= SP ->
client_range L LB SP S k -> 0 < k -> 0 < n ->
S + k <= r \/ r + n <= S.
Proof. clear - gTP gIMG_LO gIMG_HI gH2 gH3 LAY_gIMG_LO LAY_TPLO LAY_TPHI. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros L HIx A LB m md r n SP S k HP HSP HR Hk Hn0.
pose proof (heap_blk L HIx _ _ _ _ r n HP ltac:(left; reflexivity)) as (Hn & _ & _ & Hhi & _).
destruct (Z.le_gt_cases (S + k) r) as [|H1]; [left; assumption|].
destruct (Z.le_gt_cases (r + n) S) as [|H2]; [right; assumption|].
exfalso.

set (x := Z.max S r).
assert (Hx1 : S <= x < S + k) by (subst x; lia). assert (Hx2 : r <= x < r + n) by (subst x; lia).
destruct (in_block_facts L HIx _ _ _ _ r n x HP ltac:(left; reflexivity) Hx2) as (Hlt & Hns & Hdis).
destruct HR as [HR|[HR|(b & Hb & Hb1 & Hb2)]].
- lia.
- exact (Hns (HR x Hx1)).
- destruct b as [ba bn]. cbn in Hb1, Hb2.
assert (Hne : ba <> r).
{ intros ->. exact (fresh_not_in L HIx _ _ _ _ r n bn HP Hb). }
exact (Hdis ba bn ltac:(right; exact Hb) Hne ltac:(lia)).
Qed.

Section Strdup.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition strdup_entry : Z := (base + 0x0).

Definition strdup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (a0 : word) (str slack : list byte)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
bytes_at segs m' (bv_unsigned a0) (str ++ [b0]) /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ rw_cells segs m' r [CB (Z.to_nat (Z.of_nat (length str) + 1)) (str ++ [b0])]
/\ HEAPx A' ((r, Z.of_nat (length str) + 1) :: LB) m' md') ).

Definition strdup_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (str slack : list byte),
HEAPx A LB m md ->
bytes_at segs m (bv_unsigned a0) (str ++ b0 :: slack) -> ~ In b0 str ->
((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)) ->
client_range S4L LB (bv_unsigned sp) (bv_unsigned a0) (Z.of_nat (length str) + 1) ->
(bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32
\/ bv_unsigned sp <= bv_unsigned a0) ->
Z.of_nat (length str) + 1 < 2^32 ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP ->
bv_unsigned ra mod 2 = 0 ->
(forall ms' md', strdup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo a0 str slack ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 strdup_entry) fc None m (seg_rom segs)) md) T.

#[using="w_8 joff_8 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_8 E_8 LINK_8 strlen_spec memcpy_spec"] Lemma strdup_cps : strdup_stmt.
Proof. clear - w_8 joff_8 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_8 E_8 LINK_8 strlen_spec memcpy_spec HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
unfold strdup_stmt. intros until slack. intros HP STR NONUL PAD CR SEP LEN62 ST LO LOS SPA HT ERR TP RA K.
unfold_consts. word_range sp SPR.
pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. unfold strdup_entry.
carve_frame 32%nat ST.
do 6 step.

call strlen_spec. 1:{ exact STR. } 1:{ exact NONUL. } 1:{ exact PAD. } 1:{ exact MI. }
do 3 zstep.
rename POST into STR1.
lazymatch goal with H : mem_inv segs ?mx |- _ => rename H into MI1; rename mx into m1 end.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI1.
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite ?unsigned_lit in ST2, HPR2 by lia.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
change (str ++ Z_to_bv 8 0 :: slack) with (str ++ [b0] ++ slack) in STR1.
rewrite app_assoc in STR1. apply bytes_at_app in STR1. destruct STR1 as [STR1 _].
apply (heap_pres_bytes_at S4L _ _ _ _ _ _ HPR2) in STR1.
2:{ eapply client_range_lower_sp; [| ]. { rewrite length_app. cbn [length].
replace (Z.of_nat (length str + 1)) with (Z.of_nat (length str) + 1) by lia. exact CR. } lia. }
cbn [hl_segs S4L] in STR1.
clear MU WM MI1 ST ERR.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [bjunk BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_truex. do 4 step.
release_frame FR ST2 (bv_unsigned sp).
step.
apply evt_RZ_done. apply K. unfold strdup_post.
exists m2, A2, 0, e2.
split; [| split; [exact VM2 | split; [exact ST2 | split; [exact HPR | split; [exact ERR2 | split; [exact STR1 | left; auto]]]]]].
unfold ret_state. cbn [hl_segs S4L]. repeat eexists; reflexivity.
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r _ HP2 ltac:(left; reflexivity)) as (_ & Hral & Hrlo & Hrhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r _ HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi.
pose proof (fresh_block_sep S4L HIx _ _ _ _ _ _ (bv_unsigned sp) _ _ HP2 ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia) CR ltac:(lia) ltac:(lia)) as SEP2.
assert (Hur : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
assert (Hun : bv_unsigned (Z_to_bv 64 (Z.of_nat (length str) + 1)) = Z.of_nat (length str) + 1) by (apply unsigned_lit; lia).
pose proof (munch_refl [(bv_unsigned (Z_to_bv 64 r), bv_unsigned (Z_to_bv 64 r) + bv_unsigned (Z_to_bv 64 (Z.of_nat (length str) + 1)))] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_falsex. do 6 step.
release_frame FR ST2 (bv_unsigned sp).
step.

pose proof STR1 as SRC.
call memcpy_spec.
1:{ exact SRC. }
1:{ rewrite length_app. cbn [length]. rewrite Hun. lia. }
1:{ rewrite Hur, Hun. exact BLK. }
1:{ rewrite Hur, Hun. lia. }
1:{ exact MI. }
rewrite ?Hur, ?Hun in *.
apply evt_RZ_done. apply K. unfold strdup_post.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx, A2, r, e2 end.
split; [| split; [exact VM2 | split; [ exact ST2 | split; [| split; [exact ERR2 | split; [exact STR1 | right]]]]]].
+ unfold ret_state. cbn [hl_segs S4L]. repeat eexists; reflexivity.
+
eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros b Hb; cbn; first [exact Hb | tauto] | unfold alloc_ceiling, sp_window_lo, stack_max_size; lia | solve_clientW S4L HIx HP2].
+ split; [exact Hr|]. split; [assumption|].
eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU). solve_frameW.
Qed.
End Strdup.

End RC__1.

End G.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Section G.
Variables (segs : list Segment).

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
Variables (GHASH4 GGOT4 GVDSO4 JG_CGT_P gRDATA_LO : Z).
Hypothesis CS_GHASH4 : forall a, (GHASH4 <= a < GHASH4 + 12)%Z -> gCS a.
Hypothesis CS_GGOT4 : forall a, (GGOT4 <= a < GGOT4 + 8)%Z -> gCS a.
Hypothesis CS_GVDSO4 : forall a, (GVDSO4 <= a < GVDSO4 + 8)%Z -> gCS a.
Hypothesis LAY_RDATA_GGOT4 : gw_le gRDATA_LO GGOT4.
Hypothesis LAY_GGOT4_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASH4x12_GVDSO4 : gw_le (GHASH4 + 12) GVDSO4.
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
#[using="RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free GHASH4 GGOT4 GVDSO4 JG_CGT_P gRDATA_LO CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_GVDSO4_IMG S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

Definition jc_glob_P (m : word -> option byte) : Prop :=
(exists seed : word, rw_cells segs m GHASH4 [C8 (Z_to_bv 64 (fn_lh_char_hash S4F)); C4 seed])
/\ rw_cells segs m GGOT4 [C8 (Z_to_bv 64 (fn_lh_char_equal S4F))]
/\ (exists vf : Z, rw_cells segs m GVDSO4 [C8 (Z_to_bv 64 vf)] /\ (vf = JG_CGT_P \/ vf = 0)).

#[using="Type"] Lemma disjoint_from_Forall : forall W A n,
Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) W -> disjoint_from W A n.
Proof. clear - segs.
induction W as [|[lo hi] W IH]; intros A n H; [exact I|].
apply Forall_cons_iff in H as [H1 H]. cbn [fst snd] in H1. split; [exact H1 | apply IH; exact H].
Qed.

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_GVDSO4_IMG"] Lemma jc_glob_P_pres : forall LB SP m m', heap_pres S4L LB SP m m' -> jc_glob_P m -> jc_glob_P m'.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_GVDSO4_IMG. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_RDATA_GGOT4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GGOT4_GHASH4 as gL3_; unfold gw_le in gL3_. pose proof LAY_GHASH4x12_GVDSO4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GVDSO4_IMG as gL5_; unfold gw_le in gL5_.
intros LB SP m m' HPR ([seed G1] & G2 & (vf & G3 & VF)). split; [| split].
- exists seed. eapply (heap_pres_rw_cells S4L); [exact HPR | exact G1 |]. right; left. intros a Ha. cbn in Ha. cbn. gw_cs.
- eapply (heap_pres_rw_cells S4L); [exact HPR | exact G2 |]. right; left. intros a Ha. cbn in Ha. cbn. gw_cs.
- exists vf. split; [| exact VF]. eapply (heap_pres_rw_cells S4L); [exact HPR | exact G3 |]. right; left. intros a Ha. cbn in Ha. cbn. gw_cs.
Qed.

#[using="Type"] Lemma jc_glob_P_munch : forall m m' W,
jc_glob_P m -> munch W m m' -> wmono segs m m' ->
Forall (fun iv => (GHASH4 + 12 <= fst iv \/ snd iv <= GHASH4) /\ (GGOT4 + 8 <= fst iv \/ snd iv <= GGOT4) /\ (GVDSO4 + 8 <= fst iv \/ snd iv <= GVDSO4)) W ->
jc_glob_P m'.
Proof. clear - segs GHASH4 GGOT4 GVDSO4.
intros m m' W ([seed G1] & G2 & (vf & G3 & VF)) MU WM DJ.
split; [| split].
- exists seed. eapply (rw_cells_transport segs W m m'); [exact G1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
apply disjoint_from_Forall. eapply Forall_impl; [| exact DJ]. intros [lo hi] H. cbn [fst snd] in H |- *. pose proof (proj1 H). lia.
- eapply (rw_cells_transport segs W m m'); [exact G2 | exact MU | exact WM |]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
apply disjoint_from_Forall. eapply Forall_impl; [| exact DJ]. intros [lo hi] H. cbn [fst snd] in H |- *. pose proof (proj1 (proj2 H)). lia.
- exists vf. split; [| exact VF]. eapply (rw_cells_transport segs W m m'); [exact G3 | exact MU | exact WM |]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
apply disjoint_from_Forall. eapply Forall_impl; [| exact DJ]. intros [lo hi] H. cbn [fst snd] in H |- *. pose proof (proj2 (proj2 H)). lia.
Qed.

End RC__1.

End G.
End Mq6.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw Q8tj QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Definition localestmt_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Definition blk_1983c_code (wb1983c_5 wb1983c_9 wb1983c_10 : Z) : list Z :=
[0xff010113; 0x00113423; 0x00813023; 0x00050413; 0x03000513; wb1983c_5; 0x04050263; 0xfff00593; 0x00b41663; wb1983c_9; wb1983c_10; 0x02843583; 0x02b53423; 0x02043583; 0x02b53023; 0x01843583; 0x00b53c23; 0x01043583; 0x00b53823; 0x00843583; 0x00b53423; 0x00043583; 0x00b53023; 0x00813083; 0x00013403; 0x01010113; 0x00008067]%Z.

Definition blk_198a8_code (wb198a8_4 wb198a8_10 : Z) : list Z :=
[0xff010113; 0x00113423; 0x00813023; 0x00050413; wb198a8_4; 0x00050c63; 0x00040513; 0x00813083; 0x00013403; 0x01010113; wb198a8_10; 0x00813083; 0x00013403; 0x01010113; 0x00008067]%Z.

Definition blk_1993c_code (wb1993c_10 wb1993c_11 wb1993c_14 wb1993c_15 wb1993c_16 wb1993c_25 wb1993c_26 wb1993c_40 wb1993c_41 wb1993c_55 wb1993c_56 wb1993c_70 wb1993c_71 wb1993c_85 wb1993c_86 wb1993c_98 wb1993c_99 wb1993c_106 wb1993c_107 wb1993c_109 wb1993c_110 wb1993c_114 wb1993c_115 wb1993c_136 wb1993c_138 wb1993c_140 wb1993c_143 wb1993c_147 wb1993c_148 wb1993c_181 wb1993c_186 wb1993c_190 wb1993c_194 wb1993c_195 wb1993c_196 wb1993c_209 : Z) : list Z :=
[0xf9010113; 0x06113423; 0x06813023; 0x04913c23; 0x05213823; 0x05313423; 0x05413023; 0x00060413; 0x00058493; 0x00050913; wb1993c_10; wb1993c_11; 0x0009b503; 0x02a13c23; wb1993c_14; wb1993c_15; wb1993c_16; 0x00197513; 0x00051863; 0x00040663; 0x00043503; 0x0200006f; 0x00050663; 0x00048593; 0x00c0006f; wb1993c_25; wb1993c_26; 0x00000513; 0x324000ef; 0xfff00593; 0x00a13423; 0x28b50463; 0x00297513; 0x00051863; 0x00040663; 0x00843503; 0x0200006f; 0x00050663; 0x00048593; 0x00c0006f; wb1993c_40; wb1993c_41; 0x00100513; 0x2e8000ef; 0xfff00593; 0x00a13823; 0x24b50663; 0x00497513; 0x00051863; 0x00040663; 0x01043503; 0x0200006f; 0x00050663; 0x00048593; 0x00c0006f; wb1993c_55; wb1993c_56; 0x00200513; 0x2ac000ef; 0xfff00593; 0x00a13c23; 0x20b50863; 0x00897513; 0x00051863; 0x00040663; 0x01843503; 0x0200006f; 0x00050663; 0x00048593; 0x00c0006f; wb1993c_70; wb1993c_71; 0x00300513; 0x270000ef; 0xfff00593; 0x02a13023; 0x1cb50a63; 0x01097513; 0x00051863; 0x00040663; 0x02043503; 0x0200006f; 0x00050663; 0x00048593; 0x00c0006f; wb1993c_85; wb1993c_86; 0x00400513; 0x234000ef; 0xfff00593; 0x02a13423; 0x18b50c63; 0x02097513; 0x00051863; 0x00040663; 0x02843503; 0x01c0006f; 0x00051663; wb1993c_98; wb1993c_99; 0x00500513; 0x00048593; 0x1fc000ef; 0xfff00593; 0x02a13823; 0x16b50063; wb1993c_106; wb1993c_107; 0x038a0493; wb1993c_109; wb1993c_110; 0x04940c63; 0x008a0513; 0x04a40863; wb1993c_114; wb1993c_115; 0x04a40263; 0x04040063; 0x03240e63; 0x03013503; 0x02a43423; 0x02813503; 0x02a43023; 0x02013503; 0x00a43c23; 0x01813503; 0x00a43823; 0x01013503; 0x00a43423; 0x00813503; 0x00a43023; 0x00040913; 0x0f80006f; 0x00810513; 0x03000613; 0x00090593; wb1993c_136; 0x0e050263; wb1993c_138; 0x00810513; wb1993c_140; 0x03000613; 0x00090593; wb1993c_143; 0x0c050463; 0x000a4503; 0x06051e63; wb1993c_147; wb1993c_148; 0x00000513; 0x00040593; 0x138000ef; 0x00aa3423; 0x00100513; 0x00100913; 0x00040593; 0x124000ef; 0x00aa3823; 0x00200513; 0x00040593; 0x114000ef; 0x00aa3c23; 0x00300513; 0x00040593; 0x104000ef; 0x02aa3023; 0x00400513; 0x00040593; 0x0f4000ef; 0x02aa3423; 0x00500513; 0x00040593; 0x0e4000ef; 0x008a3583; 0x012a0023; 0x02aa3823; 0x02ba3c23; 0x008a0913; 0x00810513; 0x03000613; 0x00090593; wb1993c_181; 0x02050863; 0x00810513; 0x03000613; 0x00048593; wb1993c_186; 0x00048913; 0x00050c63; 0x03000513; wb1993c_190; 0x00050413; 0xec051ee3; 0x00000913; wb1993c_194; wb1993c_195; wb1993c_196; 0x0009b503; 0x03813583; 0x02b51463; 0x00090513; 0x06813083; 0x06013403; 0x05813483; 0x05013903; 0x04813983; 0x04013a03; 0x07010113; 0x00008067; wb1993c_209]%Z.

Definition blk_1a51c_code (wb1a51c_2 wb1a51c_3 : Z) : list Z :=
[0x00020613; 0xfd063583; wb1a51c_2; wb1a51c_3; 0x00050a63; 0xfff00713; 0x00e51463; 0x03868513; 0xfca63823; 0x03868513; 0x00a5c533; 0x00a03533; 0xfff50513; 0x00b56533; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (CNAME GLOBLOC LOCALE_LOCK : Z).
Variables (e_blk_1983c e_blk_198a8 e_blk_1993c e_blk_1a51c : Z).
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
Hypothesis CODE : code_at segs base localestmt_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 12.
Variable wb1983c_9 : Z.
Variable wb1983c_10 : Z.
Variable e_1a694 : Z.
Variable wb1983c_5 : Z.  Variable joffb1983c_5 : bv 21.
Hypothesis D_b1983c_5 : decode_any (Z_to_bv 32 wb1983c_5) = Some (Jal 1 joffb1983c_5, 4%Z).
Hypothesis E_b1983c_5 : is_ecall (Z_to_bv 32 wb1983c_5) = false.
Hypothesis LINK_b1983c_5 : gw_anch (e_blk_1983c + 20 + bv_signed joffb1983c_5)%Z (e_1a694 + 0)%Z.
Hypothesis CODE_e_blk_1983c : code_at segs e_blk_1983c (blk_1983c_code wb1983c_5 wb1983c_9 wb1983c_10).
Hypothesis AL_e_blk_1983c_b4 : gw_b4 e_blk_1983c.
Hypothesis RNG_e_blk_1983c_code : gw_br e_blk_1983c 108.
Variable e_198e4 : Z.
Variable wb198a8_4 : Z.  Variable joffb198a8_4 : bv 21.
Hypothesis D_b198a8_4 : decode_any (Z_to_bv 32 wb198a8_4) = Some (Jal 1 joffb198a8_4, 4%Z).
Hypothesis E_b198a8_4 : is_ecall (Z_to_bv 32 wb198a8_4) = false.
Hypothesis LINK_b198a8_4 : gw_anch (e_blk_198a8 + 16 + bv_signed joffb198a8_4)%Z (e_198e4 + 0)%Z.
Variable wb198a8_10 : Z.  Variable joffb198a8_10 : bv 21.
Hypothesis D_b198a8_10 : decode_any (Z_to_bv 32 wb198a8_10) = Some (Jal 0 joffb198a8_10, 4%Z).
Hypothesis E_b198a8_10 : is_ecall (Z_to_bv 32 wb198a8_10) = false.
Hypothesis LINK_b198a8_10 : gw_anch (e_blk_198a8 + 40 + bv_signed joffb198a8_10)%Z e_free2.
Hypothesis CODE_e_blk_198a8 : code_at segs e_blk_198a8 (blk_198a8_code wb198a8_4 wb198a8_10).
Hypothesis AL_e_blk_198a8_b4 : gw_b4 e_blk_198a8.
Hypothesis RNG_e_blk_198a8_code : gw_br e_blk_198a8 60.
Variable wb1993c_10 : Z.
Variable wb1993c_11 : Z.
Variable wb1993c_14 : Z.
Variable wb1993c_15 : Z.
Variable wb1993c_25 : Z.
Variable wb1993c_26 : Z.
Variable wb1993c_40 : Z.
Variable wb1993c_41 : Z.
Variable wb1993c_55 : Z.
Variable wb1993c_56 : Z.
Variable wb1993c_70 : Z.
Variable wb1993c_71 : Z.
Variable wb1993c_85 : Z.
Variable wb1993c_86 : Z.
Variable wb1993c_98 : Z.
Variable wb1993c_99 : Z.
Variable wb1993c_106 : Z.
Variable wb1993c_107 : Z.
Variable wb1993c_109 : Z.
Variable wb1993c_110 : Z.
Variable wb1993c_114 : Z.
Variable wb1993c_115 : Z.
Variable wb1993c_138 : Z.
Variable wb1993c_140 : Z.
Variable wb1993c_147 : Z.
Variable wb1993c_148 : Z.
Variable wb1993c_194 : Z.
Variable wb1993c_195 : Z.
Variable e_2607c : Z.
Variable wb1993c_16 : Z.  Variable joffb1993c_16 : bv 21.
Hypothesis D_b1993c_16 : decode_any (Z_to_bv 32 wb1993c_16) = Some (Jal 1 joffb1993c_16, 4%Z).
Hypothesis E_b1993c_16 : is_ecall (Z_to_bv 32 wb1993c_16) = false.
Hypothesis LINK_b1993c_16 : gw_anch (e_blk_1993c + 64 + bv_signed joffb1993c_16)%Z (e_2607c + 0)%Z.
Variable e_24f50 : Z.
Variable wb1993c_136 : Z.  Variable joffb1993c_136 : bv 21.
Hypothesis D_b1993c_136 : decode_any (Z_to_bv 32 wb1993c_136) = Some (Jal 1 joffb1993c_136, 4%Z).
Hypothesis E_b1993c_136 : is_ecall (Z_to_bv 32 wb1993c_136) = false.
Hypothesis LINK_b1993c_136 : gw_anch (e_blk_1993c + 544 + bv_signed joffb1993c_136)%Z (e_24f50 + 0)%Z.
Variable wb1993c_143 : Z.  Variable joffb1993c_143 : bv 21.
Hypothesis D_b1993c_143 : decode_any (Z_to_bv 32 wb1993c_143) = Some (Jal 1 joffb1993c_143, 4%Z).
Hypothesis E_b1993c_143 : is_ecall (Z_to_bv 32 wb1993c_143) = false.
Hypothesis LINK_b1993c_143 : gw_anch (e_blk_1993c + 572 + bv_signed joffb1993c_143)%Z (e_24f50 + 0)%Z.
Variable wb1993c_181 : Z.  Variable joffb1993c_181 : bv 21.
Hypothesis D_b1993c_181 : decode_any (Z_to_bv 32 wb1993c_181) = Some (Jal 1 joffb1993c_181, 4%Z).
Hypothesis E_b1993c_181 : is_ecall (Z_to_bv 32 wb1993c_181) = false.
Hypothesis LINK_b1993c_181 : gw_anch (e_blk_1993c + 724 + bv_signed joffb1993c_181)%Z (e_24f50 + 0)%Z.
Variable wb1993c_186 : Z.  Variable joffb1993c_186 : bv 21.
Variable wb1993c_190 : Z.
Hypothesis D_b1993c_186 : decode_any (Z_to_bv 32 wb1993c_186) = Some (Jal 1 joffb1993c_186, 4%Z).
Hypothesis E_b1993c_186 : is_ecall (Z_to_bv 32 wb1993c_186) = false.
Hypothesis LINK_b1993c_186 : gw_anch (e_blk_1993c + 744 + bv_signed joffb1993c_186)%Z (e_24f50 + 0)%Z.
Variable e_26304 : Z.
Variable wb1993c_196 : Z.  Variable joffb1993c_196 : bv 21.
Hypothesis D_b1993c_196 : decode_any (Z_to_bv 32 wb1993c_196) = Some (Jal 1 joffb1993c_196, 4%Z).
Hypothesis E_b1993c_196 : is_ecall (Z_to_bv 32 wb1993c_196) = false.
Hypothesis LINK_b1993c_196 : gw_anch (e_blk_1993c + 784 + bv_signed joffb1993c_196)%Z (e_26304 + 0)%Z.
Variable e_197bc : Z.
Variable wb1993c_209 : Z.  Variable joffb1993c_209 : bv 21.
Hypothesis D_b1993c_209 : decode_any (Z_to_bv 32 wb1993c_209) = Some (Jal 1 joffb1993c_209, 4%Z).
Hypothesis E_b1993c_209 : is_ecall (Z_to_bv 32 wb1993c_209) = false.
Hypothesis LINK_b1993c_209 : gw_anch (e_blk_1993c + 836 + bv_signed joffb1993c_209)%Z (e_197bc + 0)%Z.
Hypothesis CODE_e_blk_1993c : code_at segs e_blk_1993c (blk_1993c_code wb1993c_10 wb1993c_11 wb1993c_14 wb1993c_15 wb1993c_16 wb1993c_25 wb1993c_26 wb1993c_40 wb1993c_41 wb1993c_55 wb1993c_56 wb1993c_70 wb1993c_71 wb1993c_85 wb1993c_86 wb1993c_98 wb1993c_99 wb1993c_106 wb1993c_107 wb1993c_109 wb1993c_110 wb1993c_114 wb1993c_115 wb1993c_136 wb1993c_138 wb1993c_140 wb1993c_143 wb1993c_147 wb1993c_148 wb1993c_181 wb1993c_186 wb1993c_190 wb1993c_194 wb1993c_195 wb1993c_196 wb1993c_209).
Hypothesis AL_e_blk_1993c_b4 : gw_b4 e_blk_1993c.
Hypothesis RNG_e_blk_1993c_code : gw_br e_blk_1993c 840.
Variable wb1a51c_2 : Z.
Variable wb1a51c_3 : Z.
Hypothesis CODE_e_blk_1a51c : code_at segs e_blk_1a51c (blk_1a51c_code wb1a51c_2 wb1a51c_3).
Hypothesis AL_e_blk_1a51c_b4 : gw_b4 e_blk_1a51c.
Hypothesis RNG_e_blk_1a51c_code : gw_br e_blk_1a51c 60.
Hypothesis RNG_CNAME : gw_br CNAME 8.
Hypothesis RNG_GLOBLOC : gw_br GLOBLOC 8.
Hypothesis AL_GLOBLOC : gw_al GLOBLOC 8.
Hypothesis RNG_LOCALE_LOCK : gw_br LOCALE_LOCK 8.
Hypothesis AL_LOCALE_LOCK : gw_al LOCALE_LOCK 8.
Hypothesis LAY_CNAME_GLOBLOC : gw_le (CNAME + 8) GLOBLOC.
Hypothesis LAY_GLOBLOC_LOCALE_LOCK : gw_le (GLOBLOC + 8) LOCALE_LOCK.

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
#[using="CNAME GLOBLOC LOCALE_LOCK e_blk_1983c e_blk_198a8 e_blk_1993c e_blk_1a51c RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER wb1983c_9 wb1983c_10 e_1a694 wb1983c_5 joffb1983c_5 D_b1983c_5 E_b1983c_5 LINK_b1983c_5 CODE_e_blk_1983c AL_e_blk_1983c_b4 RNG_e_blk_1983c_code e_198e4 wb198a8_4 joffb198a8_4 D_b198a8_4 E_b198a8_4 LINK_b198a8_4 wb198a8_10 joffb198a8_10 D_b198a8_10 E_b198a8_10 LINK_b198a8_10 CODE_e_blk_198a8 AL_e_blk_198a8_b4 RNG_e_blk_198a8_code wb1993c_10 wb1993c_11 wb1993c_14 wb1993c_15 wb1993c_25 wb1993c_26 wb1993c_40 wb1993c_41 wb1993c_55 wb1993c_56 wb1993c_70 wb1993c_71 wb1993c_85 wb1993c_86 wb1993c_98 wb1993c_99 wb1993c_106 wb1993c_107 wb1993c_109 wb1993c_110 wb1993c_114 wb1993c_115 wb1993c_138 wb1993c_140 wb1993c_147 wb1993c_148 wb1993c_194 wb1993c_195 e_2607c wb1993c_16 joffb1993c_16 D_b1993c_16 E_b1993c_16 LINK_b1993c_16 e_24f50 wb1993c_136 joffb1993c_136 D_b1993c_136 E_b1993c_136 LINK_b1993c_136 wb1993c_143 joffb1993c_143 D_b1993c_143 E_b1993c_143 LINK_b1993c_143 wb1993c_181 joffb1993c_181 D_b1993c_181 E_b1993c_181 LINK_b1993c_181 wb1993c_186 joffb1993c_186 D_b1993c_186 E_b1993c_186 LINK_b1993c_186 e_26304 wb1993c_196 joffb1993c_196 D_b1993c_196 E_b1993c_196 LINK_b1993c_196 e_197bc wb1993c_209 joffb1993c_209 D_b1993c_209 E_b1993c_209 LINK_b1993c_209 CODE_e_blk_1993c AL_e_blk_1993c_b4 RNG_e_blk_1993c_code wb1a51c_2 wb1a51c_3 CODE_e_blk_1a51c AL_e_blk_1a51c_b4 RNG_e_blk_1a51c_code RNG_CNAME RNG_GLOBLOC AL_GLOBLOC RNG_LOCALE_LOCK AL_LOCALE_LOCK LAY_CNAME_GLOBLOC LAY_GLOBLOC_LOCALE_LOCK S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

Definition LOCCELL : Z := gTP - 48.
Definition LC_GLOBAL : Z := 2^64 - 1.

Definition usl_new (cur nw : Z) : Z := if nw =? 0 then cur else if nw =? LC_GLOBAL then GLOBLOC else nw.
Definition usl_ret (cur : Z) : Z := if cur =? GLOBLOC then LC_GLOBAL else cur.

Section LocaleStmt.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition uselocale_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cur nw : Z),
rw_cells segs m LOCCELL [C8 (Z_to_bv 64 cur)] -> 0 <= cur < 2^64 -> 0 <= nw < 2^64 ->
tp = Z_to_bv 64 gTP -> mem_inv segs m ->
evt segs (fun ms' => exists m' a1' a2' a3' a4',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (usl_ret cur)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(LOCCELL, LOCCELL + 8)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' LOCCELL [C8 (Z_to_bv 64 (usl_new cur nw))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_blk_1a51c + 0x0)) fc None m (seg_rom segs)).

Definition errno_location_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
tp = Z_to_bv 64 gTP ->
evt segs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (gTP - 164)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).

Definition duplocale_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word),
HEAPx A LB m md ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - hl_stack S4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only md md' ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres S4L LB (bv_unsigned sp) m m' ->
rw_cells segs m' (gTP - 164) [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ (exists junk, rw_cells segs m' r [CB 48 junk]) /\ HEAPx A' ((r, 48) :: LB) m' md') ) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LC_GLOBAL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_blk_1983c + 0x0)) fc None m (seg_rom segs)) md) T.

Definition newlocale_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo d : Z) (junk : list byte) (errv : word),
HEAPx A LB m md -> In (d, 48) LB -> rw_cells segs m d [CB 48 junk] ->
rw_cells segs m LOCALE_LOCK [C4 (Z_to_bv 64 0)] ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 496 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
(forall ms' m' (r : Z) (junk' : list byte),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres S4L (lb_remove d LB) (bv_unsigned sp) m m' ->
rw_cells segs m' d [CB 48 junk'] ->
rw_cells segs m' LOCALE_LOCK [C4 (Z_to_bv 64 0)] ->
rw_cells segs m' (gTP - 164) [C4 errv] ->
HEAPx A LB m' md ->
(r = d \/ r = 0) ->
realizes segs (mkCfg ms' md) T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) (Z_to_bv 64 CNAME) (Z_to_bv 64 d) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_blk_1993c + 0x0)) fc None m (seg_rom segs)) md) T.

Definition freelocale_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo d n : Z) (errv : word),
HEAPx A LB m md -> In (d, n) LB ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - hl_stack S4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
(forall ms' m' md' A' (r : word),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only md md' ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres S4L (lb_remove d LB) (bv_unsigned sp) m m' ->
rw_cells segs m' (gTP - 164) [C4 errv] ->
HEAPx A' (lb_remove d LB) m' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_blk_198a8 + 0x0)) fc None m (seg_rom segs)) md) T.
End LocaleStmt.

End RC__1.

End G.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Definition pbfree_code (w_7 w_12 : Z) : list Z :=
[0x02050e63; 0x00757593; 0x02059c63; 0xff010113; 0x00113423; 0x00813023; 0x00053583; 0x00050413;
0x00058513; w_7; 0x00040513; 0x00813083; 0x00013403; 0x01010113; w_12; 0x00008067;
0xc0001073]%Z.

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_2 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_7 w_12 : Z).
Variables (joff_7 joff_12 : bv 21).
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
Hypothesis CODE : code_at segs base (pbfree_code w_7 w_12).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 68.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Jal 1 joff_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (Jal 0 joff_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis LINK_7 : gw_anch (base + 36 + bv_signed joff_7)%Z e_free.
Hypothesis LINK_12 : gw_anch (base + 56 + bv_signed joff_12)%Z e_free.

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
#[using="w_7 w_12 joff_7 joff_12 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_7 E_7 D_12 E_12 LINK_7 LINK_12 S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

Section PbFree.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition printbuf_free_entry : Z := (base + 0x0).

Definition printbuf_free_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv] /\
HEAPx A' LB m' md'.

#[using="w_7 w_12 joff_7 joff_12 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_7 E_7 D_12 E_12 LINK_7 LINK_12"] Lemma printbuf_free_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB BS : list blk) (p lo : Z) (errv : word),
HEAPx A (BS ++ LB) m md ->
((p = 0 /\ BS = []) \/ (p <> 0 /\ pbufw segs m BS p)) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 p ->
(forall ms' md', printbuf_free_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo errv ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_free_entry) fc None m (seg_rom segs)) md) T.
Proof. clear - w_7 w_12 joff_7 joff_12 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_7 E_7 D_12 E_12 LINK_7 LINK_12 segs gTP HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until errv. intros HP Hp ST LO LOS SPA HT ERR TP RA A0 K.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
apply rz_evt; [exact MOK|]. unfold printbuf_free_entry. subst a0.
destruct Hp as [(-> & ->) | (Hp & PB)].
-
step. if_truex. step.
apply evt_RZ_done. apply K. unfold printbuf_free_post.
exists m, A, (Z_to_bv 64 0). cbn [app] in HP.
split; [| split; [apply model_vm_only_refl | split; [exact ST | split; [exact HPR | split; [exact ERR | exact HP]]]]].
apply ret_statew_same.
-
destruct PB as (buf & bpos & size & content & -> & Hbp & Hsz & Hlen & PBS & PBUF).
pose proof (heap_blk S4L HIx _ _ _ _ p PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p PB_SZ HP ltac:(left; reflexivity)) as Himg_p. cbn [hl_img_lo hl_img_hi S4L] in Himg_p.
pose proof (heap_blk S4L HIx _ _ _ _ buf size HP ltac:(right; left; reflexivity)) as (_ & _ & Hblo & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ buf size HP ltac:(right; left; reflexivity)) as Himg_buf. cbn [hl_img_lo hl_img_hi S4L] in Himg_buf.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hbhi.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
step. if_falsex. step. step. ubsan_align Hal.
carve_frame 16%nat ST.
do 7 step.

alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ right. exists size. right; left. reflexivity. }
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS.
cbn [hl_segs S4L app] in *.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hpb.
rewrite lb_remove_other in HPR2, HP2 by (cbn; lia). rewrite lb_remove_head in HPR2, HP2.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST PBS PBUF.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
do 4 step.
release_frame FR ST2 (bv_unsigned sp).
step.

alloc_call (hi_free S4L HIx) S4L HIx HP2 MU WM MI.
{ right. exists PB_SZ. left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3.
cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HP3, HPR3.
extend_pres S4L HIx HPR MU WM HP2 HPR3.
apply K. unfold printbuf_free_post.
exists m3, A3, r3.
split; [| split; [| split; [exact ST3 | split; [exact HPR | split; [exact ERR3 | exact HP3]]]]].
+ apply ret_statew_same.
+ eapply model_vm_only_trans; eassumption.
Qed.
End PbFree.

End RC__1.

End G.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.Mq0.
Import QQLG.Mq9.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition pbmemappend_code (w_14 w_47 w_70 : Z) : list Z :=
[0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423;
0x02064c63; 0x1e050663; 0x00757693; 0x1e069263; 0x00852683; 0x80000737; 0xfff7079b; 0x40d78733;
0x40d787bb; 0x1ce79663; 0x0007079b; 0xfff7071b; 0x1cf75063; 0x02c75263; w_14; 0x1a050a63;
0x00357593; 0x1a059663; 0x01b00593; 0x00b52023; 0xfff00513; 0x1700006f; 0x00c68733; 0x00c686bb;
0x18e69863; 0x0007069b; 0x0017071b; 0x18d74263; 0x00c52903; 0x00053403; 0x01275663; 0x00040693;
0x0c00006f; 0x00040693; 0x06e95e63; 0x800006b7; 0xff86869b; 0xfad752e3; 0x400006b7; 0x00d94c63;
0x00058993; 0x00050a93; 0x00060a13; 0x0087049b; 0x02c0006f; 0xc00006b7; 0xfff6869b; 0x1326da63;
0x0019149b; 0x0087071b; 0x00974463; 0x00070493; 0x00058993; 0x00050a93; 0x00060a13; 0x00040513;
0x00048593; w_47; 0x10050063; 0x00050693; 0x000a8513; 0x00dab023; 0x009aa623; 0x000a0613;
0x00098593; 0x0085b733; 0x408587b3; 0x0127b833; 0x40e0073b; 0xfff80813; 0x00f76733; 0x01076733;
0x0007071b; 0x00074e63; 0x00e685b3; 0x0cd5e263; 0x00d03733; 0x0015b793; 0x00f74733; 0x0a070a63;
0x00852783; 0x00d78733; 0x00d03833; 0x00173893; 0x0b180063; 0x0007a793; 0x00d736b3; 0x00f6c6b3;
0x0016c693; 0x08068663; 0x00050493; 0x00070513; 0x00060413; w_70; 0x0084a583; 0x00858733;
0x008585bb; 0x06e59663; 0x0004b603; 0x0007079b; 0x00f605b3; 0x00c03833; 0x0015b893; 0x00e4a423;
0x05180863; 0x00c5b6b3; 0x0007a713; 0x00e6c6b3; 0x0016c693; 0x02068e63; 0x02060c63; 0x00040513;
0x00058023; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83;
0x04010113; 0x00008067; 0xfff00513; 0xfd9ff06f; 0xc0001073]%Z.

Definition blk_194bc_code : list Z := [0x00020513; 0xf5c50513; 0x00008067]%Z.

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
Hypothesis LAY_TPAL : ((gTP - 164) mod 4 = 0)%Z.
#[using="gH2 gH3 LAY_gIMG_LO"] Lemma gLAYF : ((0 <= gIMG_LO /\ gIMG_HI <= alloc_ceiling) /\ (gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - gH2 gH3 LAY_gIMG_LO gTP gIMG_LO gIMG_HI. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.

Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Hypothesis CODE : code_at segs base (pbmemappend_code w_14 w_47 w_70).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 532.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Jal 1 joff_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_47 : decode_any (Z_to_bv 32 w_47) = Some (Jal 1 joff_47, 4%Z).
Hypothesis E_47 : is_ecall (Z_to_bv 32 w_47) = false.
Hypothesis D_70 : decode_any (Z_to_bv 32 w_70) = Some (Jal 1 joff_70, 4%Z).
Hypothesis E_70 : is_ecall (Z_to_bv 32 w_70) = false.
Hypothesis LINK_14 : gw_anch (base + 88 + bv_signed joff_14)%Z (e_194bc + 0)%Z.
Hypothesis LINK_47 : gw_anch (base + 260 + bv_signed joff_47)%Z e_realloc.
Hypothesis LINK_70 : gw_anch (base + 404 + bv_signed joff_70)%Z (e_memmove + 0)%Z.

Definition memmove_post := Eval cbv beta delta [QQLG.Mq9.memmove_post] in (@QQLG.Mq9.memmove_post segs).
Definition memmove_stmt := ltac:(let t := eval cbv beta delta [QQLG.Mq9.memmove_stmt] in (@QQLG.Mq9.memmove_stmt segs e_memmove) in let t := gw_subst t (@QQLG.Mq9.memmove_post segs) memmove_post in exact t).

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
#[using="w_14 w_47 w_70 joff_14 joff_47 joff_70 e_194bc e_memmove RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI LAY_TPAL e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_14 E_14 D_47 E_47 D_70 E_70 LINK_14 LINK_47 LINK_70 CODE_e_194bc S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

Section PbMemappend.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.

Definition printbuf_memappend_entry : Z := (base + 0x0).

Definition memmove_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(D, D + n)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' D [CB (Z.to_nat n) src].

#[using="MEMMOVE"] Lemma memmove_specZ :
forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
0 <= D < 2^64 -> 0 <= S < 2^64 -> 0 <= n < 2^63 ->
bytes_at segs m S src ->
length src = Z.to_nat n ->
rw_cells segs m D [CB (Z.to_nat n) junk] ->
mem_inv segs m ->
evt segs (memmove_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D n src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_memmove + 0x0)) fc None m (seg_rom segs)).
Proof. clear - MEMMOVE segs e_memmove HIx.
intros until junk. intros HD HS Hn SRC L DST MI.
pose proof (MEMMOVE ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m src junk) as X.
rewrite !unsigned_lit in X by lia.
eapply evt_mono; [eapply X; [exact SRC | exact L | exact DST | lia | exact MI] |].
intros ms' P. unfold memmove_post in P. unfold memmove_postZ.
rewrite !unsigned_lit in P by lia. exact P.
Qed.

Definition pbufx (m : word -> option byte) (pb buf bpos cap : Z) (content : list byte) : Prop :=
pbuf_core segs m pb buf bpos cap content.

Definition memappend_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (pb buf bpos cap : Z) (content : list byte) (n lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word) (buf' cap' : Z),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
HEAPx A' ((pb, PB_SZ) :: (buf', cap') :: LB) m' md' /\
((r = n /\ pbuf segs m' [(pb, PB_SZ); (buf', cap')] pb)
\/ (r = 2^64 - 1 /\ buf' = buf /\ cap' = cap /\ pbuf_core segs m' pb buf bpos cap content)).

Definition memappend_post_c (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (pb buf bpos cap : Z) (content src : list byte) (n lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word) (buf' cap' : Z),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
HEAPx A' ((pb, PB_SZ) :: (buf', cap') :: LB) m' md' /\
((r = n /\ pbufc segs m' [(pb, PB_SZ); (buf', cap')] pb (firstn (Z.to_nat bpos) content ++ src))
\/ (r = 2^64 - 1 /\ buf' = buf /\ cap' = cap /\ pbuf_core segs m' pb buf bpos cap content)).

#[using="Type"] Lemma memappend_post_c_weak : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB pb buf bpos cap content src n lo ms' md',
memappend_post_c ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB pb buf bpos cap content src n lo ms' md' ->
memappend_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB pb buf bpos cap content n lo ms' md'.
Proof. clear - HIx MEMMOVE.
intros. destruct H as (m' & A' & r & errv' & buf' & cap' & H1 & H2 & H3 & H4 & H5 & H6 & H7).
exists m', A', r, errv', buf', cap'. repeat (split; [assumption|]).
destruct H7 as [[Hr PB] | Hx]; [left; split; [exact Hr | apply pbufc_pbuf in PB; exact PB] | right; exact Hx].
Qed.

Section Tail.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo : Z) (pb buf0 bpos0 cap0 n : Z) (content0 : list byte) (T : TSet).

#[using="w_14 w_47 w_70 joff_70 e_memmove LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_70 E_70 LINK_70 MEMMOVE"] Lemma memappend_tail :
forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(buf bpos cap b : Z) (content src : list byte) (errv : word) (framejunk : list byte),
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbufx m pb buf bpos cap content ->
bpos + n + 1 <= cap -> 0 <= n < 2^31 ->
bytes_at segs m b src -> Z.of_nat (length src) = n ->
0 <= b < 2^64 -> b + n <= 2^64 ->
a0 = Z_to_bv 64 pb -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 buf ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (bv_unsigned sp + -64) [CB 8 framejunk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
bpos = bpos0 -> firstn (Z.to_nat bpos) content = firstn (Z.to_nat bpos0) content0 ->
(forall ms' md', memappend_post_c ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB pb buf0 bpos0 cap0 content0 src n lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x160)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_14 w_47 w_70 joff_70 e_memmove LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_70 E_70 LINK_70 MEMMOVE segs base gTP HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo pb buf0 bpos0 cap0 n content0 T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until framejunk. intros HP PBX ROOM Hn SRC SRCL Hb0 Hbn A0 A1 A2 A3 ST LO LOS SPA HT FR ERR TP RA VM0 HPR Ebpos Epre K.
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
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
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (buf, buf + cap); (pb, pb + 16)] m) as MU.
subst a0 a1 a2 a3.

destruct (rw_cells_CB_cut segs _ _ _ _ (Z.to_nat bpos) PBUF ltac:(lia)) as [PB0 PB1].
destruct (rw_cells_CB_cut segs _ _ _ _ (Z.to_nat n) PB1 ltac:(lia)) as [PBD PB2].
clear PBUF PB1.
replace (Z.of_nat (Z.to_nat bpos)) with bpos in PBD, PB2 by lia.
replace (Z.of_nat (Z.to_nat n)) with n in PB2 by lia.
apply rz_evt; [exact MOK|].
step. norm_sx32. step. step. step.
step. QRBl.ub_cmp_auto.
step. step. step. step.
step. QRBl.ub_cmp_auto. step. step. step. step.
replace (bpos + buf) with (buf + bpos) by lia.
call memmove_specZ; [lia | lia | lia | exact SRC | lia | exact PBD | exact MI |].
step. step. step.
step. norm_w32. if_falsex.
step. step. step. step. step. norm_w32.
stepz.
step. QRBl.ub_cmp_auto.
step. step. step. step.
step. QRBl.ub_cmp_auto.
step. if_falsex.
step.
replace (buf + (bpos + n + 0)) with (buf + bpos + n) by lia.
match goal with H : rw_cells _ _ (buf + bpos + n) _ |- _ => rename H into PB2' end.
destruct (rw_cells_CB_cut segs _ _ _ _ 1%nat PB2' ltac:(lia)) as [PBZ PB3]. clear PB2'.
set (ez := buf + bpos + n) in *.
stepz.
subst ez.
do 9 step.
apply evt_RZ_done. apply K. unfold memappend_post_c.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A, n, errv, buf, cap end.
split; [| split; [exact VM0 | split; [| split; [| split; [ | split; [| left; split; [reflexivity|]]]]]]].
- apply ret_statew_same.
- release_frame FR ST (bv_unsigned sp). exact ST.
- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia |].
solve_clientW S4L HIx HP.
- exact ERR.
- eapply (heap_frame S4L HIx); [exact HP | | exact WM | ].
+ eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP.
+ assumption.
-
match goal with P0 : rw_cells segs ?mf buf [CB _ ?l0], P1 : rw_cells segs _ (buf + bpos) [CB _ src] |- _ =>
rename P0 into Q0; rename P1 into Q1 end.
rewrite <- Epre.
exists buf, (bpos + n), cap, (skipn 1 (skipn (Z.to_nat n) (skipn (Z.to_nat bpos) content))).
split; [reflexivity|]. split. { rewrite length_app, length_firstn. lia. }
unfold pbuf_core. split; [lia|]. split; [lia|]. split; [| split; [eassumption|]].
{ rewrite !length_app, length_firstn, !length_skipn. cbn [length]. lia. }

pose proof (rw_cells_CB_join segs _ _ _ _ _ _ Q0 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos)) with (buf + bpos) by lia; exact Q1)) as J1.
apply (rw_cells_recast segs _ _ _ [CB 1 [Z_to_bv 8 0]]) in PBZ; [| cbn; auto | reflexivity | reflexivity].
pose proof (rw_cells_CB_join segs _ _ _ _ _ _ J1 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos + Z.to_nat n)) with (buf + bpos + n) by lia; exact PBZ)) as J2.
pose proof (rw_cells_CB_join segs _ _ _ _ _ _ J2 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos + Z.to_nat n + 1)) with (buf + bpos + n + 1) by lia; exact PB3)) as J3.
replace (Z.to_nat bpos + Z.to_nat n + 1 + (Z.to_nat cap - Z.to_nat bpos - Z.to_nat n - 1))%nat with (Z.to_nat cap) in J3 by lia.
revert J3. rewrite <- ?app_assoc. intros J3. rewrite <- ?app_assoc in J3. exact J3.
Qed.
End Tail.
End PbMemappend.

End RC__1.

End G.
End Mqe.

Module Mqf.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QVbl.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition pbmemset_code (w_25 w_48 w_56 w_80 : Z) : list Z :=
[0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423;
0xfff00713; 0x00e58663; 0x0006de63; 0x03c0006f; 0x1e050063; 0x00757593; 0x1c059c63; 0x00852583;
0x0206c463; 0xfff00713; 0x02e5c063; 0x80000737; 0xfff7079b; 0x40b78733; 0x40b787bb; 0x1ae79a63;
0x0007071b; 0x04d75263; w_25; 0x1a050263; 0x00357593; 0x18059e63; 0x01b00593; 0x00b52023;
0xfff00513; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83;
0x04010113; 0x00008067; 0x00d584bb; 0x00d58733; 0x16e49063; 0x14050e63; 0x00757713; 0x14071a63;
0x00c52703; 0x08975263; 0x800007b7; 0xff87879b; 0xf8f4dce3; 0x400007b7; 0x00f74c63; 0x00058993;
0x00060913; 0x00068a13; 0x0084841b; 0x02c0006f; 0xc00007b7; 0xfff7879b; 0x10e7dc63; 0x0017141b;
0x0084871b; 0x00874463; 0x00070413; 0x00058993; 0x00060913; 0x00068a13; 0x00050a93; 0x00053503;
0x00040593; w_80; 0xf4050ce3; 0x00050593; 0x000a8513; 0x00bab023; 0x008aa623; 0x000a0693;
0x00090613; 0x00098593; 0x00852803; 0x00053783; 0x06b85663; 0x01078733; 0x00f038b3; 0x00173293;
0x0a588863; 0x00f737b3; 0x00082893; 0x0117c7b3; 0x0017c793; 0x08078e63; 0x410587b3; 0x4105883b;
0x08f81863; 0x0007879b; 0x00050413; 0x00070513; 0x00058913; 0x00000593; 0x00060993; 0x00078613;
0x00068a13; w_48; 0x00090593; 0x00098613; 0x000a0693; 0x00040513; 0x00043783; 0x00b78733;
0x00f03833; 0x00173893; 0x05180463; 0x00f737b3; 0x0005a593; 0x00b7c5b3; 0x0015c593; 0x02058a63;
0x00050413; 0x00070513; 0x00060593; 0x00068613; w_56; 0x00842503; 0x00955863; 0x00000513;
0x00942423; 0xe81ff06f; 0x00000513; 0xe79ff06f; 0xc0001073]%Z.

Definition blk_194bc_code : list Z := [0x00020513; 0xf5c50513; 0x00008067]%Z.

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_3 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_25 w_48 w_56 w_80 : Z).
Variables (joff_25 joff_48 joff_56 joff_80 : bv 21).
Variables (e_194bc e_memset : Z).
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
Hypothesis LAY_TPAL : ((gTP - 164) mod 4 = 0)%Z.
#[using="gH2 gH3 LAY_gIMG_LO"] Lemma gLAYF : ((0 <= gIMG_LO /\ gIMG_HI <= alloc_ceiling) /\ (gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - gH2 gH3 LAY_gIMG_LO gTP gIMG_LO gIMG_HI. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.

Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Hypothesis CODE : code_at segs base (pbmemset_code w_25 w_48 w_56 w_80).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 532.
Hypothesis D_25 : decode_any (Z_to_bv 32 w_25) = Some (Jal 1 joff_25, 4%Z).
Hypothesis E_25 : is_ecall (Z_to_bv 32 w_25) = false.
Hypothesis D_48 : decode_any (Z_to_bv 32 w_48) = Some (Jal 1 joff_48, 4%Z).
Hypothesis E_48 : is_ecall (Z_to_bv 32 w_48) = false.
Hypothesis D_56 : decode_any (Z_to_bv 32 w_56) = Some (Jal 1 joff_56, 4%Z).
Hypothesis E_56 : is_ecall (Z_to_bv 32 w_56) = false.
Hypothesis D_80 : decode_any (Z_to_bv 32 w_80) = Some (Jal 1 joff_80, 4%Z).
Hypothesis E_80 : is_ecall (Z_to_bv 32 w_80) = false.
Hypothesis LINK_25 : gw_anch (base + 104 + bv_signed joff_25)%Z (e_194bc + 0)%Z.
Hypothesis LINK_48 : gw_anch (base + 420 + bv_signed joff_48)%Z (e_memset + 0)%Z.
Hypothesis LINK_56 : gw_anch (base + 496 + bv_signed joff_56)%Z (e_memset + 0)%Z.
Hypothesis LINK_80 : gw_anch (base + 292 + bv_signed joff_80)%Z e_realloc.

Definition memset_post__cal := Eval cbv beta delta [QVbl.Mq4.memset_post] in (@QVbl.Mq4.memset_post segs).

Hypothesis memset_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq4.memset_spec segs e_memset) 3%nat in let T := gw_subst T (@QVbl.Mq4.memset_post segs) memset_post__cal in exact T).

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
#[using="w_25 w_48 w_56 w_80 joff_25 joff_48 joff_56 joff_80 e_194bc e_memset RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI LAY_TPAL e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_25 E_25 D_48 E_48 D_56 E_56 D_80 E_80 LINK_25 LINK_48 LINK_56 LINK_80 memset_spec CODE_e_194bc S4F"] Lemma gw_all : True. Proof. exact I. Qed.

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

Ltac uck := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ match goal with H : ?p mod 16 = 0 |- context [Z.land (bv_unsigned (Z_to_bv 64 ?p)) _] => ubsan_align H end | match goal with H : ?p mod 16 = 0 |- context [Z.land ?p _] => ubsan_align H end | QRBl.ub_align_auto | if_falsex | QRBl.ub_cmp_auto ] end.
Ltac uw := repeat (step; try norm_w32; try uck).
Section RC__1.

Section PbMemset.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition printbuf_memset_entry : Z := (base + 0x0).

#[using="memset_spec"] Lemma memset_specZ :
forall ra sp gp tp t0 t1 t2 s0 s1 (cv : word) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D n : Z) (junk : list byte),
0 <= D < 2^64 -> D + n <= 2^64 -> 0 <= n < 2^63 ->
rw_cells segs m D [CB (Z.to_nat n) junk] ->
mem_inv segs m ->
evt segs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(D, D + n)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' D [CB (Z.to_nat n) (repeat (Z_to_bv 8 (bv_unsigned cv mod 256)) (Z.to_nat n))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) cv (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_memset + 0x0)) fc None m (seg_rom segs)).
Proof. clear - memset_spec segs e_memset HIx.
intros until junk. intros HD HDn Hn DST MI.
pose proof (memset_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) cv (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk) as X.
rewrite (unsigned_lit D), (unsigned_lit n) in X by lia.
eapply evt_mono; [eapply X; [exact DST | exact MI] |].
intros ms' P. unfold memset_post__cal in P. rewrite (unsigned_lit D), (unsigned_lit n) in P by lia. exact P.
Qed.

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (pb buf bpos cap : Z) (content : list byte) (len lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word) (buf' cap' : Z),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
HEAPx A' ((pb, PB_SZ) :: (buf', cap') :: LB) m' md' /\
((r = 0 /\ exists content', pbuf_core segs m' pb buf' (bpos + len) cap' content')
\/ (r = 2^64 - 1 /\ buf' = buf /\ cap' = cap /\ pbuf_core segs m' pb buf bpos cap content)).

Section Blocks.
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo : Z) (pb buf0 bpos0 cap0 len : Z) (content0 : list byte) (cv : word) (T : TSet).
Notation K_ok md := (forall ms' md', memset_post ra sp gp (Z_to_bv 64 gTP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md LB pb buf0 bpos0 cap0 content0 len lo ms' md' ->
realizes segs (mkCfg ms' md') T).
Notation FRAME m junk8 := (rw_cells segs m (bv_unsigned sp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

#[using="w_25 w_48 w_56 w_80 joff_25 e_194bc LAY_gIMG_LO LAY_TPLO LAY_TPHI LAY_TPAL CODE BASE4 BASER D_25 E_25 LINK_25 CODE_e_194bc"] Lemma pbmemset_efbig :
forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(m : word -> option byte) (A : AS S4L HIx) (errv : word) (junk8 : list byte),
HEAPx A ((pb, PB_SZ) :: (buf0, cap0) :: LB) m md0 ->
pbuf_core segs m pb buf0 bpos0 cap0 content0 ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 ->
bv_unsigned sp <= hi_top S4L HIx ->
FRAME m junk8 -> rw_cells segs m (gTP + -164) [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
heap_pres S4L LB (bv_unsigned sp) m0 m ->
K_ok md0 ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x68)) fc None m (seg_rom segs)) md0) T.
Proof. clear - w_25 w_48 w_56 w_80 joff_25 e_194bc LAY_gIMG_LO LAY_TPLO LAY_TPHI LAY_TPAL CODE BASE4 BASER D_25 E_25 LINK_25 CODE_e_194bc segs base gTP HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo pb buf0 bpos0 cap0 len content0 cv T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until junk8. intros HP PB ST LO LOS HT FR ERR RA HPR K.
destruct PB as (Hbp & Hcp & Hlen & PBS & PBUF).
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
pose proof (heap_blk S4L HIx _ _ _ _ buf0 cap0 HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ buf0 cap0 HP ltac:(right; left; reflexivity)) as Hbimg. cbn [hl_img_lo hl_img_hi S4L] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hbhi.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); ((gTP + -164), (gTP + -160))] m) as MU.
apply rz_evt; [exact MOK|].
step. do 3 step. step. uck. step. step. uck. step. stepz. step. do 9 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
apply evt_RZ_done. apply K. unfold memset_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A, (2^64 - 1), (Z_to_bv 64 27), buf0, cap0 end.
split; [| split; [apply model_vm_only_refl | split; [| split; [| split; [| split; [| right; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|] ]]]]]].
all: lazymatch goal with
| |- ret_statew _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply ret_statew_same
| |- stk _ _ _ _ => release_frame FR ST (bv_unsigned sp); exact ST
| |- heap_pres _ _ _ _ _ =>
eapply heap_pres_trans; [exact HPR|];
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb0; right; right; exact Hbb0 | clia |];
solve_clientW S4L HIx HP
| |- rw_cells _ _ _ _ => eassumption
| |- pbuf_core _ _ _ _ _ _ _ => unfold pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- HEAP _ _ _ _ _ _ =>
eapply (heap_frame S4L HIx); [exact HP | | exact WM | assumption];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU); solve_frameW_with HP
end.
Qed.

#[using="w_25 w_48 w_56 w_80 joff_56 e_memset LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_56 E_56 LINK_56 memset_spec"] Lemma pbmemset_tail :
forall (x1 t0 t1 t2 x8 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(buf cap : Z) (content : list byte) (errv : word) (junk8 : list byte),
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbuf_core segs m pb buf bpos0 cap content ->
bpos0 + len <= cap -> 0 <= len < 2^31 ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
FRAME m junk8 -> rw_cells segs m (gTP - 164) [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
K_ok md0 ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) t0 t1 t2 x8 (Z_to_bv 64 (bpos0 + len))
(Z_to_bv 64 pb) (Z_to_bv 64 bpos0) cv (Z_to_bv 64 len) a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x148)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_25 w_48 w_56 w_80 joff_56 e_memset LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_56 E_56 LINK_56 memset_spec segs base gTP HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo pb buf0 bpos0 cap0 len content0 cv T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until junk8. intros HP PB ROOM Hn ST LO LOS SPA HT FR ERR RA VM0 HPR K.
destruct PB as (Hbp & Hcap & Hlen & PBS & PBUF).
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
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (buf, buf + cap); (pb, pb + 16)] m) as MU.

destruct (rw_cells_CB_cut segs _ _ _ _ (Z.to_nat bpos0) PBUF ltac:(lia)) as [PB0 PB1].
destruct (rw_cells_CB_cut segs _ _ _ _ (Z.to_nat len) PB1 ltac:(lia)) as [PBD PB2].
clear PBUF PB1.
replace (Z.of_nat (Z.to_nat bpos0)) with bpos0 in PBD, PB2 by lia.
replace (Z.of_nat (Z.to_nat len)) with len in PB2 by lia.
apply rz_evt; [exact MOK|].
do 3 (step; try norm_w32). if_truex. do 14 (step; try norm_w32; try uck).
call memset_specZ; [lia | lia | lia | exact PBD | exact MI |].
step.
step.
norm_w32.
destruct (Z.eq_dec len 0) as [L0|Lpos].
-
if_truex. step. step. do 9 step.
apply evt_RZ_done. apply K. unfold memset_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A, 0, errv, buf, cap end.
split; [| split; [exact VM0 | split; [| split; [| split; [ | split; [| left; split; [reflexivity|]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST (bv_unsigned sp). exact ST.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia |].
solve_clientW S4L HIx HP.
+ exact ERR.
+ eapply (heap_frame S4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP.
+ subst len. exists content. unfold pbuf_core. rewrite Z.add_0_r.
split; [lia|]. split; [lia|]. split; [lia|]. split; [eassumption|].
match goal with P0 : rw_cells segs ?mf buf [CB _ ?l0], P1 : rw_cells segs _ (buf + bpos0) [CB _ (repeat _ _)] |- _ =>
rename P0 into Q0; rename P1 into Q1 end.
pose proof (rw_cells_CB_join segs _ _ _ _ _ _ Q0 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos0)) with (buf + bpos0) by lia; exact Q1)) as J1.
pose proof (rw_cells_CB_join segs _ _ _ _ _ _ J1 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos0 + Z.to_nat 0)) with (buf + bpos0 + 0) by lia; exact PB2)) as J2.
replace (Z.to_nat bpos0 + Z.to_nat 0 + (Z.to_nat cap - Z.to_nat bpos0 - Z.to_nat 0))%nat with (Z.to_nat cap) in J2 by lia.
change (Z.to_nat 0) with 0%nat in J2. cbn [repeat] in J2. rewrite app_nil_r, skipn_O, firstn_skipn in J2. exact J2.
-
if_falsex. step. stepz. step. do 9 step.
apply evt_RZ_done. apply K. unfold memset_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A, 0, errv, buf, cap end.
split; [| split; [exact VM0 | split; [| split; [| split; [ | split; [| left; split; [reflexivity|]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST (bv_unsigned sp). exact ST.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia |].
solve_clientW S4L HIx HP.
+ exact ERR.
+ eapply (heap_frame S4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP.
+ exists (firstn (Z.to_nat bpos0) content ++ repeat (Z_to_bv 8 (bv_unsigned cv mod 256)) (Z.to_nat len) ++ skipn (Z.to_nat len) (skipn (Z.to_nat bpos0) content)).
unfold pbuf_core.
split; [lia|]. split; [lia|]. split; [rewrite !length_app, length_firstn, repeat_length, !length_skipn; lia|]. split; [eassumption|].
match goal with P0 : rw_cells segs ?mf buf [CB _ ?l0], P1 : rw_cells segs _ (buf + bpos0) [CB _ (repeat _ _)] |- _ =>
rename P0 into Q0; rename P1 into Q1 end.
pose proof (rw_cells_CB_join segs _ _ _ _ _ _ Q0 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos0)) with (buf + bpos0) by lia; exact Q1)) as J1.
pose proof (rw_cells_CB_join segs _ _ _ _ _ _ J1 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos0 + Z.to_nat len)) with (buf + bpos0 + len) by lia; exact PB2)) as J2.
replace (Z.to_nat bpos0 + Z.to_nat len + (Z.to_nat cap - Z.to_nat bpos0 - Z.to_nat len))%nat with (Z.to_nat cap) in J2 by lia.
rewrite <- app_assoc in J2. exact J2.
Qed.

#[using="w_25 w_48 w_56 w_80 joff_56 joff_80 e_memset LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_56 E_56 D_80 E_80 LINK_56 LINK_80 memset_spec"] Lemma pbmemset_grow :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (A : AS S4L HIx) (ns : Z) (errv : word) (junk8 : list byte),
HEAPx A ((pb, PB_SZ) :: (buf0, cap0) :: LB) m md0 ->
pbuf_core segs m pb buf0 bpos0 cap0 content0 ->
bpos0 + len <= ns -> cap0 <= ns < 2^31 -> 0 <= len < 2^31 ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
FRAME m junk8 -> rw_cells segs m (gTP - 164) [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
heap_pres S4L LB (bv_unsigned sp) m0 m ->
K_ok md0 ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) t0 t1 t2 (Z_to_bv 64 ns) (Z_to_bv 64 (bpos0 + len))
(Z_to_bv 64 pb) a1 a2 a3 a4 a5 a6 a7 cv (Z_to_bv 64 bpos0) (Z_to_bv 64 len) (Z_to_bv 64 pb) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x11c)) fc None m (seg_rom segs)) md0) T.
Proof. clear - w_25 w_48 w_56 w_80 joff_56 joff_80 e_memset LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_56 E_56 D_80 E_80 LINK_56 LINK_80 memset_spec segs base gTP HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo pb buf0 bpos0 cap0 len content0 cv T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until junk8. intros HP PB ROOM Hns Hn ST LO LOS SPA HT FR ERR RA HPR K.
pose proof PB as PB'. destruct PB as (Hbp & Hcap & Hlen & PBS & PBUF).
assert (LEN : length content0 = Z.to_nat cap0) by (destruct PBUF as [[[Hwf _] _] _]; exact Hwf).
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
pose proof (heap_blk S4L HIx _ _ _ _ buf0 cap0 HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ buf0 cap0 HP ltac:(right; left; reflexivity)) as Hbimg. cbn [hl_img_lo hl_img_hi S4L] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hbhi.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hpbbuf.
pose proof (wmono_refl segs m) as WM.
change (gTP - 164) with (gTP + -164) in ERR.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (pb, pb + 16); ((gTP + -164), (gTP + -160))] m) as MU.
rewrite <- (app_nil_r content0) in PBUF.
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
step. if_truex. step. do 9 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
apply evt_RZ_done. apply K. unfold memset_post.
exists m2, A2, (2^64 - 1), errv2, buf0, cap0.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [exact HP2| right]]]]]].
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
step. if_falsex. step. step. stepz. stepz. step. step. step.
apply evt_RZ_done.
eapply (pbmemset_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md2 A2 r ns (content0 ++ junk) errv2 junk8);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- HEAP _ _ _ _ _ _ =>
eapply (heap_frame S4L HIx); [ eapply heap_perm; [exact HP2 | apply perm_swap] | | exact WM | exact MI ];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ (heap_perm _ _ _ _ _ _ _ HP2 (perm_swap _ _ _)) MU); solve_frameW_with HP2
| |- pbuf_core _ _ _ _ _ _ _ =>
unfold pbuf_core; split; [lia|]; split; [lia|]; split; [destruct BLK as [[[Hwf _] _] _]; rewrite Hwf; lia|]; split; [eassumption|];
exact BLK
| |- model_vm_only _ _ => eapply model_vm_only_trans; eassumption
| |- heap_pres _ _ _ _ _ =>
eapply heap_pres_trans; [exact HPR|];
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outside S4L HIx); [exact HP2 | intros bb Hbb0; right; right; exact Hbb0 | clia |];
solve_clientW S4L HIx HP2
| |- _ => unfold_consts; lia
end.
Qed.
End Blocks.

#[using="Type"] Lemma lxor_ones31 : forall b, 0 <= b < 2^31 -> Z.lxor b 2147483647 = 2147483647 - b.
Proof. clear - HIx.
intros b Hb. change 2147483647 with (Z.ones 31).
assert (Hl : Z.log2 b < 31) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
rewrite <- Z.ldiff_ones_l_low by lia. symmetry. apply Z.sub_nocarry_ldiff. apply Z.ldiff_ones_r_low; lia.
Qed.

#[using="w_25 w_48 w_56 w_80 joff_25 joff_56 joff_80 e_194bc e_memset LAY_gIMG_LO LAY_TPLO LAY_TPHI LAY_TPAL CODE BASE4 BASER D_25 E_25 D_56 E_56 D_80 E_80 LINK_25 LINK_56 LINK_80 memset_spec CODE_e_194bc"] Lemma pbmemset_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (pb buf bpos cap len lo : Z) (content : list byte) (errv : word),
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbuf_core segs m pb buf bpos cap content ->
0 <= len < 2^31 ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 pb -> a1 = Z_to_bv 64 (-1) -> a3 = Z_to_bv 64 len ->
(forall ms' md', memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB pb buf bpos cap content len lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_memset_entry) fc None m (seg_rom segs)) md) T.
Proof. clear - w_25 w_48 w_56 w_80 joff_25 joff_56 joff_80 e_194bc e_memset LAY_gIMG_LO LAY_TPLO LAY_TPHI LAY_TPAL CODE BASE4 BASER D_25 E_25 D_56 E_56 D_80 E_80 LINK_25 LINK_56 LINK_80 memset_spec CODE_e_194bc segs gTP HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until errv. intros HP PB Hn ST LO LOS SPA HT ERR TP RA A0 A1 A3 K.
pose proof PB as PB0.
destruct PB as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as Hbimg. cbn [hl_img_lo hl_img_hi S4L] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hbhi.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
change (gTP - 164) with (gTP + -164) in ERR.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU.
subst a0 a1 a3 tp.
apply rz_evt; [exact MOK|]. unfold printbuf_memset_entry.
carve_frame 64%nat ST.
do 8 step.
assert (HPRm : forall mx, munch [(bv_unsigned sp + -64, bv_unsigned sp)] m mx -> wmono segs m mx ->
heap_pres S4L LB (bv_unsigned sp) m mx).
{ intros mx MUx WMx. eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MUx | exact WMx |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb0; right; right; exact Hbb0 | clia |]. solve_clientW S4L HIx HP. }
assert (HPm : forall mx, munch [(bv_unsigned sp + -64, bv_unsigned sp)] m mx -> wmono segs m mx -> mem_inv segs mx ->
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) mx md).
{ intros mx MUx WMx MIx. eapply (heap_frame S4L HIx); [exact HP | | exact WMx | exact MIx].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MUx). solve_frameW_with HP. }
uw.
destruct (Z.lt_ge_cases (2147483647 - bpos) len) as [Hbig|Hok].
{
if_falsex. apply evt_RZ_done.
eapply pbmemset_efbig; first [exact (HPm _ MU WM MI) | exact (HPRm _ MU WM) | exact PB0 | eassumption | lia | idtac].
unfold pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption. }
if_truex.
uw.
destruct (Z.le_gt_cases (bpos + len) cap) as [Hfit|Hgrow].
-
if_truex.
apply evt_RZ_done.
eapply (pbmemset_tail ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo pb buf bpos cap len content a2 T
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md A buf cap content errv _);
first [ reflexivity | exact (HPm _ MU WM MI) | exact (HPRm _ MU WM) | apply model_vm_only_refl | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbuf_core _ _ _ _ _ _ _ => unfold pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- _ => unfold_consts; lia
end.
- if_falsex. uw.
destruct (Z.lt_ge_cases (bpos + len) 2147483640) as [Hok2|Hbig2].
2:{ if_truex. apply evt_RZ_done.
eapply pbmemset_efbig; first [exact (HPm _ MU WM MI) | exact (HPRm _ MU WM) | exact PB0 | eassumption | lia | idtac].
unfold pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption. }
if_falsex.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
assert (GROW : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (ns : Z),
bpos + len <= ns -> cap <= ns < 2^31 ->
evt segs (RZ segs md T)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) x5 x6 x7 (Z_to_bv 64 ns) (Z_to_bv 64 (bpos + len))
(Z_to_bv 64 pb) x11 x12 x13 x14 x15 x16 x17 a2 (Z_to_bv 64 bpos) (Z_to_bv 64 len) (Z_to_bv 64 pb)
s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 (base + 0x11c)) fc None mcur (seg_rom segs)))
end.
{ intros until ns. intros Hns1 Hns2. apply evt_RZ_done.
eapply (pbmemset_grow ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo pb buf bpos cap len content a2 T
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A ns errv _);
first [ reflexivity | exact (HPm _ MU WM MI) | exact (HPRm _ MU WM) | exact PB0 | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbuf_core _ _ _ _ _ _ _ => unfold pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- _ => unfold_consts; lia
end. }
uw.
destruct (Z.lt_ge_cases cap 1073741824) as [Hsmall|Hlarge].
+ if_truex. uw.
try rewrite (unsigned_lit cap) by lia. rewrite (Z.shiftl_mul_pow2 cap 1) by lia. change (2^1) with 2.
rewrite (swrap32_id (cap * 2)) by lia. try norm_w32.
destruct (Z.lt_ge_cases (bpos + len + 8) (cap * 2)) as [Hlt3|Hge3].
* if_truex. do 4 step. apply (GROW _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cap * 2)); lia.
* if_falsex. do 5 step. apply (GROW _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bpos + len + 8)); lia.
+ if_falsex. do 6 (step; try norm_w32). apply (GROW _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bpos + len + 8)); lia.
Qed.
End PbMemset.

End RC__1.

End G.
End Mqf.

Module Mqg.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Definition pbnew_code (w_6 w_12 w_19 : Z) : list Z :=
[0xff010113; 0x00113423; 0x00813023; 0x00100513; 0x01000593; w_6; 0x04050263; 0x00757593;
0x04059663; 0x00100593; 0x02559593; 0x00b53423; 0x00050413; 0x02000513; w_12; 0x00050593;
0x00040513; 0x00b43023; 0x00058663; 0x00058023; 0x00c0006f; w_19; 0x00000513; 0x00813083;
0x00013403; 0x01010113; 0x00008067; 0xc0001073]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_6 w_12 w_19 : Z).
Variables (joff_6 joff_12 joff_19 : bv 21).
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
Hypothesis CODE : code_at segs base (pbnew_code w_6 w_12 w_19).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 112.
Hypothesis D_6 : decode_any (Z_to_bv 32 w_6) = Some (Jal 1 joff_6, 4%Z).
Hypothesis E_6 : is_ecall (Z_to_bv 32 w_6) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (Jal 1 joff_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (Jal 1 joff_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis LINK_6 : gw_anch (base + 20 + bv_signed joff_6)%Z e_calloc.
Hypothesis LINK_12 : gw_anch (base + 56 + bv_signed joff_12)%Z e_malloc.
Hypothesis LINK_19 : gw_anch (base + 84 + bv_signed joff_19)%Z e_free.

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
#[using="w_6 w_12 w_19 joff_6 joff_12 joff_19 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_6 E_6 D_12 E_12 D_19 E_19 LINK_6 LINK_12 LINK_19 S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Ltac solve_condx := unfold_cond; fold_lit_ux; rewrite ?unsigned_lit by lia; solve_cond_rec.
Ltac if_truex :=
lazymatch goal with
| |- evt ?segs_ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with true; [cbv iota| symmetry; solve_condx]
end.
Ltac if_falsex :=
lazymatch goal with
| |- evt ?segs_ ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with false; [cbv iota| symmetry; solve_condx]
end.
Import Q6q3.
Section RC__1.

#[using="Type"] Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. clear - segs. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
#[using="Type"] Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. clear - segs. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
#[using="Type"] Lemma le1_lit : forall z, (0 <= z < 256)%Z -> Z_to_le_bytes 1 z = [Z_to_bv 8 z].
Proof. clear - segs. intros z Hz. cbn [Z_to_le_bytes]. reflexivity. Qed.
End RC__1.
Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
is_Zlit z; let b := eval vm_compute in (Z.modulo z 256) in
replace (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 b] by (apply (f_equal (fun x => [x])); apply bv_eq; vm_compute; reflexivity)
| _ => idtac
end.

Ltac stepz := step; try (fix_litstore; mem_after_store).
Section RC__2.

#[using="Type"] Lemma rw_cells_recast : forall segs_ m A cs cs',
rw_cells segs_ m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
rw_cells segs_ m A cs'.
Proof. clear - segs.
intros segs_ m A cs cs' [[Hwf HB] HW] Hwf' HBe HSe. split; [split; [exact Hwf'| rewrite HBe; exact HB]| rewrite HSe; exact HW].
Qed.

#[using="Type"] Lemma pbn_bytes_eq_by_unsigned : forall l1 l2 : list byte,
map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof. clear - segs.
induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as Hb Hl. f_equal; [apply bv_eq; exact Hb | apply IH; exact Hl].
Qed.

Section PbNew.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition printbuf_new_entry : Z := (base + 0x0).

Definition printbuf_new_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, pbuf segs m' BS r /\ HEAPx A' (BS ++ LB) m' md') ).

#[using="w_6 w_12 w_19 joff_6 joff_12 joff_19 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_6 E_6 D_12 E_12 D_19 E_19 LINK_6 LINK_12 LINK_19"] Lemma printbuf_new_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word),
HEAPx A LB m md ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP ->
bv_unsigned ra mod 2 = 0 ->
(forall ms' md', printbuf_new_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_new_entry) fc None m (seg_rom segs)) md) T.
Proof. clear - w_6 w_12 w_19 joff_6 joff_12 joff_19 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_6 E_6 D_12 E_12 D_19 E_19 LINK_6 LINK_12 LINK_19 segs gTP HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until errv. intros HP ST LO LOS SPA HT ERR TP RA K.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl segs m) as WM.
apply rz_evt; [exact MOK|].
unfold printbuf_new_entry.
carve_frame 16%nat ST.
do 6 step.

apply evt_RZ_done. eapply (hi_calloc S4L HIx).
{ eapply (heap_frame _ HIx); [exact HP | | exact WM | exact MI].
intros a Ha Hna Hns. apply MU. rewrite wa_unsigned by lia. cbn [outside].
split; [|exact I]. intros Hin. apply Hna. pose proof (hi_top_hi S4L HIx). split; [left|]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia. }
all: cbn [hl_segs hl_stack hl_tp S4L].
all: rewrite ?unsigned_lit by lia.
{ exact ST. }
{ unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. }
{ lia. }
{ replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) by lia. rewrite Zminus_mod, SPA. reflexivity. }
{ lia. }
{ exact ERR. }
{ exact TP. }
{ reflexivity. }
{ reflexivity. }
{ lia. }
{ lia. }
{ lia. }
intros ms2 m2 md2 A2 r errv2 RS VM2 ST2 HPR2 ERR2 OUT.
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->).
cbn [hl_segs S4L] in *.

assert (HPRacc : heap_pres S4L LB (bv_unsigned sp) m m2).
{ eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
intros a Ha Hc. cbn. split; [|exact I].
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia | pose proof (hl_static_in_img S4L a Hc) as Hsi; cbn [hl_img_lo hl_img_hi S4L] in Hsi; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |].
destruct b as [ba bn]. cbn in Hr.
pose proof (heap_blk _ HIx _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia.
- eapply heap_pres_weaken; [exact HPR2 | lia | auto]. }

apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
cbn [hl_segs S4L] in FR.
clear MU WM MI ST.
pose proof (wmono_refl segs m2) as WM.
destruct OUT as [(-> & _ & HP2) | (Hr & BLK & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m2) as MU.
apply rz_evt; [exact MOK2|].
try g_ret_pc_any.
step. if_true.
do 4 step.
apply evt_RZ_done. apply K. unfold printbuf_new_post.
exists m2, A2, 0, errv2. split; [| split; [exact VM2 | split; [| split; [exact HPRacc | split; [exact ERR2 | left; auto]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
-
change (Z.to_nat (1 * 16)) with 16%nat in BLK. change (1 * 16) with 16 in HP2. cbn [repeat] in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk _ HIx _ _ _ _ r 16 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 16 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 16)] m2) as MU.
apply rz_evt; [exact MOK2|].
try g_ret_pc_any.
step. if_falsex. step. step. Qsw7.ubsan_align Hal.
step. step. stepz. do 3 step.

apply evt_RZ_done. eapply (hi_malloc S4L HIx).
{ eapply (heap_frame _ HIx); [exact HP2 | | exact WM | exact MI].
intros a Ha Hna Hns. apply MU. rewrite wa_unsigned by lia. cbn [outside].
pose proof (hi_top_hi S4L HIx) as HTH.
split; [|split; [|exact I]]; intros Hin; apply Hna.
- split; [left|]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
- split; [right; right; exists (r, 16); split; [left; reflexivity| cbn; lia] | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia]. }
all: cbn [hl_segs hl_stack hl_tp S4L].
all: rewrite ?unsigned_lit by lia.
{ exact ST2. }
{ unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. }
{ lia. }
{ replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) by lia. rewrite Zminus_mod, SPA. reflexivity. }
{ lia. }
{ exact ERR2. }
{ exact TP. }
{ reflexivity. }
{ lia. }
intros ms3 m3 md3 A3 q errv3 RS3 VM3 ST3 HPR3 ERR3 OUT3.
destruct RS3 as (w0 & w1 & w2 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & w3 & w4 & w5 & w6 & ->).
assert (HPRacc3 : heap_pres S4L LB (bv_unsigned sp) m m3).
{ eapply heap_pres_trans; [exact HPRacc|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
intros a Ha Hc. cbn.
destruct Hc as [Hc|[Hc|(b & Hb & Hbr)]]; [split; [lia| split; [lia| exact I]] | pose proof (hl_static_in_img S4L a Hc) as Hsi; cbn [hl_img_lo hl_img_hi S4L] in Hsi; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; repeat split; try exact I; lia |].
destruct b as [ba bn]. cbn in Hbr.
pose proof (heap_blk _ HIx _ _ _ _ _ _ HP2 ltac:(right; exact Hb)) as (_ & _ & _ & Hbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
assert (ba <> r).
{ intros ->. pose proof (heap_blk_nodup _ HIx _ _ _ _ HP2) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. apply Hni. exact (in_map blk_addr _ _ Hb). }
pose proof (heap_blk_disjoint _ HIx _ _ _ _ r 16 ba bn HP2 ltac:(left; reflexivity) ltac:(right; exact Hb) ltac:(congruence)) as Hdj.
split; [lia| split; [lia| exact I]].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; right; exact Hb]. }

apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity| lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
clear MU WM MI ST2 HPR2.
pose proof (wmono_refl segs m3) as WM.
assert (MOK3 : model_ok md3) by (destruct OUT3 as [(_ & _ & H)|(_ & _ & H)]; exact (heap_model_ok _ _ _ _ _ _ H)).
apply rz_evt; [exact MOK3|].
try g_ret_pc_any.
destruct OUT3 as [(-> & _ & HP3) | (Hq & BLKQ & HP3)].
+
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 16)] m3) as MU.
do 2 step. stepz. step. if_truex. step.

apply evt_RZ_done. eapply (hi_free S4L HIx) with (p := r).
{ eapply (heap_frame _ HIx); [exact HP3 | | exact WM | exact MI].
intros a Ha Hna Hns. apply MU. rewrite wa_unsigned by lia. cbn [outside].
pose proof (hi_top_hi S4L HIx) as HTH.
split; [|split; [|exact I]]; intros Hin; apply Hna.
- split; [left|]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
- split; [right; right; exists (r, 16); split; [left; reflexivity| cbn; lia] | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia]. }
{ right. exists 16. left. reflexivity. }
all: cbn [hl_segs hl_stack hl_tp S4L].
all: rewrite ?unsigned_lit by lia.
{ exact ST3. }
{ unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. }
{ lia. }
{ replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) by lia. rewrite Zminus_mod, SPA. reflexivity. }
{ lia. }
{ exact ERR3. }
{ exact TP. }
{ reflexivity. }
intros ms4 m5 md4 A4 rv4 RS4 VM4 ST4 HPR4 ERR4 HP4.
destruct RS4 as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & ->).
rewrite lb_remove_head in HPR4, HP4.
assert (HPRacc4 : heap_pres S4L LB (bv_unsigned sp) m m5).
{ eapply heap_pres_trans; [exact HPRacc3|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
intros a Ha Hc. cbn.
destruct Hc as [Hc|[Hc|(b & Hb & Hbr)]]; [split; [lia| split; [lia| exact I]] | pose proof (hl_static_in_img S4L a Hc) as Hsi; cbn [hl_img_lo hl_img_hi S4L] in Hsi; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; repeat split; try exact I; lia |].
destruct b as [ba bn]. cbn in Hbr.
pose proof (heap_blk _ HIx _ _ _ _ _ _ HP3 ltac:(right; exact Hb)) as (_ & _ & _ & Hbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
assert (ba <> r).
{ intros ->. pose proof (heap_blk_nodup _ HIx _ _ _ _ HP3) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. apply Hni. exact (in_map blk_addr _ _ Hb). }
pose proof (heap_blk_disjoint _ HIx _ _ _ _ r 16 ba bn HP3 ltac:(left; reflexivity) ltac:(right; exact Hb) ltac:(congruence)) as Hdj.
split; [lia| split; [lia| exact I]].
- eapply heap_pres_weaken; [exact HPR4 | lia | auto]. }
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST3 HPR3 BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
apply rz_evt; [exact MOK4|].
try g_ret_pc_any.
do 5 step.
apply evt_RZ_done. apply K. unfold printbuf_new_post.
exists m5, A4, 0, errv3. split; [| split; [| split; [| split; [exact HPRacc4 | split; [exact ERR4 | left; auto]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; [| exact VM4]. eapply model_vm_only_trans; eassumption.
* release_frame FR ST4 (bv_unsigned sp). exact ST4.
+
change (Z.to_nat 32) with 32%nat in BLKQ. destruct BLKQ as [junkq BLKQ].
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk _ HIx _ _ _ _ q 32 HP3 ltac:(left; reflexivity)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q 32 HP3 ltac:(left; reflexivity)) as Himg_q. cbn [hl_img_lo hl_img_hi S4L] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
assert (Hqr0 : q <> r).
{ intros E. pose proof (heap_blk_nodup _ HIx _ _ _ _ HP3) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heap_blk_disjoint _ HIx _ _ _ _ q 32 r 16 HP3 ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hqr0) as Hqr.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 16); (q, q + 32)] m3) as MU.
do 4 step. if_falsex. stepz. step.
do 4 step.
apply evt_RZ_done. apply K. unfold printbuf_new_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] =>
exists mf, A3, r, errv3 end.
split; [| split; [| split; [| split; [ | split; [exact ERR3 | right]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; eassumption.
* release_frame FR ST3 (bv_unsigned sp). exact ST3.
* eapply heap_pres_trans; [exact HPRacc3|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
intros a Ha Hc. cbn.
destruct Hc as [Hc|[Hc|(b & Hb & Hbr)]]; [split; [lia| split; [lia| split; [lia|exact I]]] | pose proof (hl_static_in_img S4L a Hc) as Hsi; cbn [hl_img_lo hl_img_hi S4L] in Hsi; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; repeat split; try exact I; lia |].
destruct b as [ba bn]. cbn in Hbr.
pose proof (heap_blk _ HIx _ _ _ _ _ _ HP3 ltac:(right; right; exact Hb)) as (_ & _ & _ & Hbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
pose proof (heap_blk_nodup _ HIx _ _ _ _ HP3) as ND. cbn in ND.
assert (ba <> r /\ ba <> q) as [Hbar Hbaq].
{ inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|xx2 ll2 Hni2 Hnd2]; subst.
split; intros ->; [apply Hni2; exact (in_map blk_addr _ _ Hb) | apply Hni; right; exact (in_map blk_addr _ _ Hb)]. }
pose proof (heap_blk_disjoint _ HIx _ _ _ _ r 16 ba bn HP3 ltac:(right; left; reflexivity) ltac:(right; right; exact Hb) ltac:(congruence)) as Hdj1.
pose proof (heap_blk_disjoint _ HIx _ _ _ _ q 32 ba bn HP3 ltac:(left; reflexivity) ltac:(right; right; exact Hb) ltac:(congruence)) as Hdj2.
split; [lia| split; [lia| split; [lia| exact I]]].
* split; [exact Hr|]. exists [(r, 16); (q, 32)]. split.
-- unfold pbuf. exists q, 0, 32, [], (skipn 1 junkq).
split; [reflexivity|]. split; [reflexivity|]. unfold pbuf_core.
split; [lia|]. split; [lia|].
split. { destruct BLKQ as [[Hwf0 _] _]. cbn in Hwf0. destruct Hwf0 as [_ [Hwf0 _]]. rewrite !length_app. cbn [length]. lia. }
split.
++ eapply rw_cells_recast; [exact BLK | cbn; repeat split; reflexivity | cbn [cells_bytes cbytes]; f_equal; apply pbn_bytes_eq_by_unsigned; vm_compute; reflexivity | reflexivity].
++ destruct BLKQ as [[Hwf HBq] HWq]. cbn in Hwf. destruct Hwf as [_ [Hwf _]].
split; [split|]; [ | exact HBq | exact HWq ].
cbn. split; [|exact I]. rewrite Hwf. reflexivity.
-- eapply heap_frame; [ eapply heap_perm; [exact HP3 | apply perm_swap] | | | ].
++ intros a Ha Hna Hns. apply MU. rewrite wa_unsigned by lia. cbn [outside].
pose proof (hi_top_hi S4L HIx) as HTH.
pose proof (heap_blk _ HIx _ _ _ _ r 16 HP3 ltac:(right; left; reflexivity)) as (_ & _ & _ & Hrhi2 & _).
split; [|split; [|split; [|exact I]]]; intros Hin; apply Hna.
** split; [left|]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
** split; [right; right; exists (r, 16); split; [left; reflexivity| cbn; lia] | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia].
** split; [right; right; exists (q, 32); split; [right; left; reflexivity| cbn; lia] | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia].
++ match goal with H : wmono segs m3 ?mf |- _ => exact H end.
++ match goal with H : mem_inv segs ?mf |- _ => exact H end.
Qed.
End PbNew.

End RC__2.

End G.
End Mqg.

Module Mqh.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Section G.
Variables (segs : list Segment).
Variables (e_blk_18934 : Z).

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
#[using="e_blk_18934 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

Section P.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition lh_delete_tail_post2 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (jf : nat)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) svs',
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' /\
model_vm_only md md' /\ stk segs m' lo (bv_unsigned sp) /\ heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv] /\
lh_open segs S4F m' t tbl size (firstn jf es) svs' /\ HEAPx A' (lh_blocks t tbl size (firstn jf es) ++ LB) m' md'.

Definition lh_delete_tail_stmt2 : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (svs : list slotv) (jf : nat) (ef : lent),
HEAPx A (lh_blocks t tbl size es ++ LB) m md ->
lh_open segs S4F m t tbl size es svs ->
nth_error es jf = Some ef -> (forall j x, (jf <= j)%nat -> nth_error es j = Some x -> le_v x = 0) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 (ent_addr tbl (le_ix ef)) ->
(forall ms' md', lh_delete_tail_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo errv t tbl size es jf ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_blk_18934 + 0x0)) fc None m (seg_rom segs)) md) T.
End P.

End RC__1.

End G.
End Mqh.

Module Mqi.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Section G.
Variables (segs : list Segment).
Variables (e_blk_16158 : Z).

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
#[using="e_blk_16158 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

Section PutStmt.
Variable L : heap_layout.
Variable HIx : heap_iface L.
Variable fn : fnaddrs.
Variable put_entry : Z.
Variable put_stk : Z.
Notation segs_ := (hl_segs L).

Definition put_pre (s : option jshape) (m : word -> option byte) (BS : list blk) (p rc : Z) : Prop :=
match s with
| None => p = 0 /\ BS = []
| Some s' => p <> 0 /\ 1 <= rc < 2^31 /\ jval segs_ fn s' m BS p rc
end.

Definition put_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word)
(s : option jshape) (BS : list blk) (p rc : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS L HIx) (r : word),
ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md md' /\
stk segs_ m' lo (bv_unsigned sp) /\
heap_pres L LB (bv_unsigned sp) m m' /\
rw_cells segs_ m' (hl_tp L - 164) [C4 errv] /\
( ((s = None \/ rc = 1) /\ HEAP L HIx A' LB m' md')
\/ (exists s', s = Some s' /\ 2 <= rc /\ jval segs_ fn s' m' BS p (rc - 1) /\ HEAP L HIx A' (BS ++ LB) m' md') ).

Definition put_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB : list blk) (lo : Z) (errv : word)
(s : option jshape) (BS : list blk) (p rc : Z),
HEAP L HIx A (BS ++ LB) m md ->
put_pre s m BS p rc ->
a0 = Z_to_bv 64 p ->
stk segs_ m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - put_stk ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top L HIx ->
rw_cells segs_ m (hl_tp L - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
bv_unsigned ra mod 2 = 0 ->
(forall ms' md', put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo errv s BS p rc ms' md' ->
realizes segs_ (mkCfg ms' md') T) ->
realizes segs_ (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 put_entry) fc None m (seg_rom segs_)) md) T.
End PutStmt.

Definition put_stk_P : Z := 112 + 48 + 48 + 32 + 32 + 8256.
Definition put_entry_P : Z := (e_blk_16158 + 0x0).
Definition put_stmt_P (HIx : heap_iface S4L) : Prop := put_stmt S4L HIx S4F put_entry_P put_stk_P.

End RC__1.

End G.
End Mqi.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbVh QlEo QWxq Qc3B Q9A7 QZAi QfYR QhAd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqj.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q0Ek.
Import QCcH.
Import QsjA QEpW QZDE QbVh QlEo QWxq Qc3B Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi QfYR.
Import QhAd.

Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Definition strtodstmt_code (w_7 w_8 w_17 w_21 w_30 w_40 : Z) : list Z :=
[0xef010113; 0x10113423; 0x10813023; 0x0e913c23; 0x0f213823; 0x00058413; 0x00050493; w_7; w_8; 0x00093503; 0x0ea13423; 0xfff00513; 0x04913c23; 0x00913423; 0x00a13823; 0x00010513; 0x00000593; w_17; 0x00010513; 0x00100593; 0x00100613; w_21; 0x02040063; 0x00813603; 0x05813683; 0x0c813703; 0x40d60633; 0x00e48733; 0x00c70633; 0x00c43023; w_30; 0x00093503; 0x0e813583; 0x00b51e63; 0x10813083; 0x10013403; 0x0f813483; 0x0f013903; 0x11010113; 0x00008067; w_40]%Z.

Definition blk_21e3c_code : list Z := [0x00853683; 0x01053603; 0x05853703; 0x00b037b3; 0x40d60833; 0x0105a833; 0x0107f7b3; 0x40d70733; 0x0cb53023; 0x0ce53423; 0x00078463; 0x00b68633; 0x0ac53c23; 0x00008067]%Z.

Definition blk_2205c_code : list Z := [0x81010113; 0x7e113423; 0x7e813023; 0x7c913c23; 0x7d213823; 0x7d313423; 0x7d413023; 0x7b513c23; 0x7b613823; 0x7b713423; 0x7b813023; 0x79913c23; 0x79a13823; 0x79b13423; 0x78813027; 0x000016b7; 0x40d10133; 0x00013023; 0x80010113; 0xf1010113; 0x00060b93; 0x00050a93]%Z.

Definition blk_24628_code : list Z := [0xffffc637; 0x00159713; 0x01059693; 0x3ff6061b; 0x03175713; 0x00c70633; 0x7fd00793; 0x0106d693; 0x02c7ea63; 0x03c55713; 0x00469693; 0x00451793; 0x00100813; 0x00d76533; 0x0047d693; 0x03b81713; 0x00170793; 0x00160613; 0x04f6ec63; 0x00150513; 0x05c0006f; 0x00d56633; 0x02060863; 0x00008637; 0xfff6061b; 0x02c71263; 0x03c55513; 0x00469693; 0x00100613; 0x03361613; 0x00c56533; 0x00d56533; 0x7ff00613; 0x0380006f; 0x00004637; 0x3fe6079b; 0x04e7f463; 0x00000513; 0x7ff00613; 0x0200006f; 0x00e69663; 0x00157693; 0x00a68533; 0x03455693; 0xfff68713; 0x00a77533; 0x00c68633; 0x03f5d593]%Z.

Definition blk_197bc_code : list Z := [0x00000023; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_7 w_8 w_17 w_21 w_30 w_40 : Z).
Variables (hi_7 : bv 20).
Variables (lo_8 : bv 12).
Variables (joff_17 joff_21 joff_30 joff_40 : bv 21).
Variables (e_197bc e_21e3c e_2205c e_24628 : Z).
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
Hypothesis CODE : code_at segs base (strtodstmt_code w_7 w_8 w_17 w_21 w_30 w_40).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 164.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 10 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Load SZ8 true 18 10 lo_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_17 : decode_any (Z_to_bv 32 w_17) = Some (Jal 1 joff_17, 4%Z).
Hypothesis E_17 : is_ecall (Z_to_bv 32 w_17) = false.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Jal 1 joff_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis D_30 : decode_any (Z_to_bv 32 w_30) = Some (Jal 1 joff_30, 4%Z).
Hypothesis E_30 : is_ecall (Z_to_bv 32 w_30) = false.
Hypothesis D_40 : decode_any (Z_to_bv 32 w_40) = Some (Jal 1 joff_40, 4%Z).
Hypothesis E_40 : is_ecall (Z_to_bv 32 w_40) = false.
Hypothesis ANCH_8 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_8)%Z gGOTG.
Hypothesis LINK_17 : gw_anch (base + 68 + bv_signed joff_17)%Z (e_21e3c + 0)%Z.
Hypothesis LINK_21 : gw_anch (base + 84 + bv_signed joff_21)%Z (e_2205c + 0)%Z.
Hypothesis LINK_30 : gw_anch (base + 120 + bv_signed joff_30)%Z (e_24628 + 0)%Z.
Hypothesis LINK_40 : gw_anch (base + 160 + bv_signed joff_40)%Z (e_197bc + 0)%Z.

Definition is_numch := ltac:(let t := constr:(ltac:(gw_ctx2 (@QhAd.is_numch))) in let t := eval cbv beta delta [QhAd.is_numch] in t in exact t).

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
Hypothesis CODE_e_21e3c : code_at segs e_21e3c blk_21e3c_code.
Hypothesis CODE_e_2205c : code_at segs e_2205c blk_2205c_code.
Hypothesis CODE_e_24628 : code_at segs e_24628 blk_24628_code.
Hypothesis CODE_e_197bc : code_at segs e_197bc blk_197bc_code.
#[using="w_7 w_8 w_17 w_21 w_30 w_40 hi_7 lo_8 joff_17 joff_21 joff_30 joff_40 e_197bc e_21e3c e_2205c e_24628 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_7 E_7 D_8 E_8 D_17 E_17 D_21 E_21 D_30 E_30 D_40 E_40 ANCH_8 LINK_17 LINK_21 LINK_30 LINK_40 CODE_e_21e3c CODE_e_2205c CODE_e_24628 CODE_e_197bc S4F"] Lemma gw_all : True. Proof. exact I. Qed.
Definition RERRNO : Z := (gTP - 164).
Definition RATP : Z := gTP.
Definition ssp_guard : Z := gGUARD.
Definition got_ssp : Z := gGOTG.

Notation mem := (word -> option byte).

Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
rw_cells segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells segs m ssp_guard [C8 canary].

Definition RSTRTOD : Z := (base + 0x0).
Definition RGLOBALS_TOP : Z := gIMG_HI.
Definition RIMG_LO : Z := 65536.
Definition RSTRTOD_DEPTH : Z := 8928.

Definition rstrtod_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(T PE : Z) (txt : list Z) (npre bits used lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ev' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom segs)
/\ munch [(lo, bv_unsigned sp); (PE, PE + 8); (RERRNO, RERRNO + 4)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ frm0 fc'
/\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
/\ reg_get F' 10 = Z_to_bv 64 bits
/\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' PE [C8 (Z_to_bv 64 (T + used))]
/\ bytes_at segs m' T (map (Z_to_bv 8) txt)
/\ ssp_cells m' canary
/\ rw_cells segs m' RERRNO [C4 ev']
/\ 0 <= used <= npre.

Definition rstrtod_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(T PE : Z) (txt pre post : list Z) (bits used : Z) (ejunk : word) (lo : Z) (canary ev : word),
bytes_at segs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> zlength pre < 2^30 -> zlength txt <= 2^40 ->
rw_cells segs m PE [C8 ejunk] ->
scan_strtod txt = Some (bits, used) ->
stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSTRTOD_DEPTH -> RGLOBALS_TOP <= lo -> bv_unsigned sp < 2^62 ->
0 < T ->
(((T + zlength txt <= RIMG_LO \/ RGLOBALS_TOP <= T) /\ T + zlength txt <= lo) \/ bv_unsigned sp <= T) ->

T + 2^41 <= 2^63 -> bv_unsigned sp <= PE -> PE + 8 <= 2^63 ->
(PE + 8 <= T \/ T + zlength txt <= PE) ->
ssp_cells m canary -> rw_cells segs m RERRNO [C4 ev] ->
mem_inv segs m -> frm0 fc ->
tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 PE ->
evt segs (rstrtod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PE txt (zlength pre) bits used lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RSTRTOD) fc None m (seg_rom segs)).

End G.
End Mqj.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwApply2 GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Definition aladd_code (w_27 : Z) : list Z :=
[0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x01413023; 0x0e050663;
0x00757613; 0x0e061263; 0x00853483; 0x00148913; 0xfff00413; 0x0a090863; 0x01053603; 0x00c97663;
0x00053603; 0x0540006f; 0x00161693; 0x00d96463; 0x00090693; 0xffd00713; 0x00175713; 0x00c76463;
0x00068913; 0x03d95613; 0x06061e63; 0x00058993; 0x00050a13; 0x00053503; 0x00391593; w_27;
0x06050263; 0x00050613; 0x000a0513; 0x00ca3023; 0x012a3823; 0x00098593; 0x00349693; 0x00d606b3;
0x00c03733; 0x0016b793; 0x06f70063; 0x00100713; 0x03c71713; 0x00e48733; 0x03d75713; 0x04071663;
0x04c6e463; 0x04060263; 0x0076f613; 0x02061e63; 0x00000413; 0x00853603; 0x00b6b023; 0x00160613;
0x00c53423; 0x00040513; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x00013a03;
0x03010113; 0x00008067; 0xc0001073]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_2 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_4 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

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
Hypothesis BASER : gw_br base 268.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (Jal 1 joff_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis LINK_27 : gw_anch (base + 124 + bv_signed joff_27)%Z e_realloc.

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

Section AlAdd.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo a arr size d : Z) (ps : list Z) (T : TSet).

Definition array_list_add_entry : Z := (base + 0x0).

Definition array_list_add_post (ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word) (arr' size' : Z),
ret_statew S4L ra sp gp (Z_to_bv 64 gTP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md0 md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m0 m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
HEAPx A' ((a, AL_SZ) :: (arr', 8 * size') :: LB) m' md' /\
( (r = 2^64 - 1 /\ arr' = arr /\ size' = size /\ alist segs S4F m' [(a, AL_SZ); (arr, 8 * size)] a ps)
\/ (r = 0 /\ alist segs S4F m' [(a, AL_SZ); (arr', 8 * size')] a (ps ++ [d])
/\ ((size' = size /\ arr' = arr /\ Z.of_nat (length ps) + 1 < size)
\/ (size' = 2 * size /\ size <= Z.of_nat (length ps) + 1))) ).

Definition add_frame (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells segs m (bv_unsigned sp + -48) [CB 8 junk8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="w_27 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE"] Lemma al_add_store :
forall (x1 t0 t1 t2 x8 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (r size' : Z) (junk : list byte) (errv : word),
HEAPx A ((a, AL_SZ) :: (r, 8 * size') :: LB) m md ->
al_hdr segs S4F m a r (Z.of_nat (length ps)) size' ->
u64arr segs m r (wl ps) ->
al_tail segs m r size' (length ps) junk ->
Z.of_nat (length ps) + 1 <= size' -> (1 <= size' /\ 8 * size' < 2^64) ->
((size' = size /\ r = arr /\ Z.of_nat (length ps) + 1 < size) \/ (size' = 2 * size /\ size <= Z.of_nat (length ps) + 1)) ->
0 <= d < 2^64 ->
stk segs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
add_frame m (le8 s4) ->
rw_cells segs m (gTP - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
(forall ms' md', array_list_add_post ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 gTP) t0 t1 t2
x8 (Z_to_bv 64 (Z.of_nat (length ps)))
(Z_to_bv 64 a) (Z_to_bv 64 d) (Z_to_bv 64 r) a3 a4 a5 a6 a7 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x98)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_27 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE segs base gTP S4F HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo a arr size d ps T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until errv. intros HP HDR ARR JK ROOM Hsz CASES Hd ST LO LOS SPA HT FR ERR RA VM0 HPR K.
unfold al_hdr in HDR. unfold al_tail in JK. unfold add_frame in FR.
assert (FR0 : rw_cells segs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (destruct FR as [[[_ W] B] S]; split; [split; [split; [exact I | exact W] | exact B] | exact S]). clear FR. rename FR0 into FR.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (al_blocks S4L HIx _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
cbn [hl_img_lo hl_img_hi S4L] in Himg, Himg2. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (u64arr_bound segs m r (wl ps) ARR) as AB. rewrite wl_length in AB.
pose proof (wl_length ps) as WL.
assert (LJ : length junk = Z.to_nat (8 * (size' - Z.of_nat (length ps)))) by (destruct JK as [[[W _] _] _]; exact W).

apply (rw_cells_CB_cut segs m _ _ junk 8) in JK; [|lia]. destruct JK as [J1 J2]. clear LJ.
pose proof (wmono_refl segs m) as WM.
change (gTP - 164) with (gTP + -164) in ERR.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 32); (r, r + 8 * size')] m) as MU.
apply rz_evt; [exact MOK|].
do 5 step. rewrite (unsigned_lit (Z.of_nat (length ps))) by lia. rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length ps)) 3) by lia. change (2^3) with 8. QRBl.ub_cmp_auto.
do 5 step. QRBl.ub_cmp_auto.
step. if_falsex.
step. if_falsex.
step. step. rewrite (unsigned_lit (r + Z.of_nat (length ps) * 8)) by lia. rewrite (QRBl.ub_land7 (r + Z.of_nat (length ps) * 8)) by (Z.div_mod_to_equations; lia). if_false.
step. step.
assert (SOK : store_ok segs m (wa (r + 8 * Z.of_nat (length ps))) 8 = true).
{ destruct J1 as [_ W]. cbn [cells_size csize Nat.add] in W.
replace (r + 8 * Z.of_nat (length ps)) with (r + 8 * Z.of_nat (length ps) + 0) by lia.
eapply wr_at_store_ok; [exact W | lia | cbn; lia]. }
step.
pose proof (rw_cells_write segs m _ _ 0 _ (C8 (Z_to_bv 64 d)) J1 eq_refl eq_refl I) as J1'.
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub cbytes] in J1'.
replace (r + 8 * Z.of_nat (length ps) + Z.of_nat 0) with (r + 8 * Z.of_nat (length ps)) in J1' by lia.
clear J1. store_done.
step. step.
do 9 step.
apply evt_RZ_done. apply K. unfold array_list_add_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A, 0, errv, r, size' end.
split; [| split; [exact VM0 | split; [| split; [ | split; [ eassumption | split; [ | right]]]]]].
- apply ret_statew_same.
- release_frame FR ST (bv_unsigned sp). exact ST.
- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia |].
solve_clientW S4L HIx HP.
- eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP.
- split; [reflexivity|]. split; [| exact CASES].
eapply alist_close. split; [| split; [| split; [| split; [rewrite length_app; cbn [length]; lia | exact Hsz]]]].
+ unfold al_hdr. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. eassumption.
+ eapply u64arr_snoc; [eassumption|]. eassumption.
+ unfold al_tail. rewrite length_app. cbn [length].
replace (r + 8 * Z.of_nat (length ps + 1)) with (r + 8 * Z.of_nat (length ps) + Z.of_nat 8) by lia.
replace (Z.to_nat (8 * (size' - Z.of_nat (length ps + 1)))) with (Z.to_nat (8 * (size' - Z.of_nat (length ps))) - 8)%nat by lia.
exact J2.
Qed.

#[using="w_27 joff_27 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_27 E_27 LINK_27"] Lemma al_add_grow :
forall (x1 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (junk : list byte) (errv : word),
HEAPx A ((a, AL_SZ) :: (arr, 8 * size) :: LB) m md ->
al_hdr segs S4F m a arr (Z.of_nat (length ps)) size ->
u64arr segs m arr (wl ps) ->
al_tail segs m arr size (length ps) junk ->
Z.of_nat (length ps) <= size -> (1 <= size /\ 8 * size < 2^64) -> size <= Z.of_nat (length ps) + 1 ->
0 <= d < 2^64 ->
stk segs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
add_frame m (le8 s4) ->
rw_cells segs m (gTP - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
(forall ms' md', array_list_add_post ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 gTP) t0 t1 t2
(Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.of_nat (length ps)))
(Z_to_bv 64 a) (Z_to_bv 64 d) (Z_to_bv 64 size) a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length ps) + 1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x48)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_27 joff_27 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_27 E_27 LINK_27 segs base gTP S4F HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo a arr size d ps T. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until errv. intros HP HDR ARR JK Hlen Hsz GROWS Hd ST LO LOS SPA HT FR ERR RA VM0 HPR K.
unfold al_hdr in HDR. unfold add_frame in FR.
assert (FR0 : rw_cells segs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (destruct FR as [[[_ W] B] S]; split; [split; [split; [exact I | exact W] | exact B] | exact S]). clear FR. rename FR0 into FR.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (al_blocks S4L HIx _ _ _ _ _ _ _ HP) as ((Hal & Hlo & Hhi & Himg) & (Hal2 & Hlo2 & Hhi2 & Himg2) & Hdj).
cbn [hl_img_lo hl_img_hi S4L] in Himg, Himg2. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hhi2.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hne.
assert (LJ : length junk = Z.to_nat (8 * (size - Z.of_nat (length ps)))) by (destruct JK as [[[W _] _] _]; exact W).
assert (LJ' : Z.of_nat (length junk) = 8 * (size - Z.of_nat (length ps))) by (rewrite LJ; lia).
pose proof (al_arr_join segs m arr size ps junk ARR JK Hlen) as COMB. clear LJ.
pose proof (wmono_refl segs m) as WM.
change (gTP - 164) with (gTP + -164) in ERR.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (a, a + 32)] m) as MU.
apply rz_evt; [exact MOK|].
step. rewrite (unsigned_lit size) by lia. rewrite (Z.shiftl_mul_pow2 size 1) by lia. change (2^1) with 2.

eapply evt_cut with (P := eq (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 gTP) t0 t1 t2
(Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.of_nat (length ps)))
(Z_to_bv 64 a) (Z_to_bv 64 d) (Z_to_bv 64 size) (Z_to_bv 64 (size * 2)) a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length ps) + 1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x54)) fc None m (seg_rom segs))).
{ destruct (Z.lt_ge_cases (Z.of_nat (length ps) + 1) (size * 2)) as [LT|GE].
- step. if_truex. apply evt_done. reflexivity.
- step. if_falsex. step. apply evt_done. replace (size * 2) with (Z.of_nat (length ps) + 1) by lia. reflexivity. }
intros ms' <-.
step. step. step. if_falsex. step.
step. rewrite (unsigned_lit (size * 2)) by lia. rewrite (Z.shiftr_div_pow2 (size * 2) 61) by lia.
destruct (Z.lt_ge_cases (size * 2) (2^61)) as [SMALL | HUGE].
2:{
pose proof (Z.div_str_pos (size * 2) (2^61) ltac:(lia)) as DP.
step. if_truex. do 9 step.
lazymatch goal with H : rw_cells segs ?mx (bv_unsigned sp + -48) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => release_frame H ST (bv_unsigned sp) end.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
apply evt_RZ_done. apply K. unfold array_list_add_post.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
exists mx, A, (2^64 - 1), errv, arr, size end.
split; [apply ret_statew_same|]. split; [exact VM0|]. split; [assumption|].
split; [| split; [assumption | split; [| left]]].
- eapply heap_pres_trans; [exact HPR|]. eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb0; right; right; exact Hbb0 | clia |]. solve_clientW S4L HIx HP.
- eapply (heap_frame S4L HIx); [exact HP | | exact WM | assumption]. eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP.
- split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
eapply alist_close. split; [exact HDR | split; [exact ARR | split; [exact JK | lia]]]. }
rewrite (Z.div_small (size * 2) (2^61)) by lia.
clear ARR JK.
step. if_false.
step. step. step.
step. rewrite (unsigned_lit (size * 2)) by lia. rewrite (Z.shiftl_mul_pow2 (size * 2) 3) by lia. change (2^3) with 8.
step.

alloc_call (hi_realloc S4L HIx) S4L HIx HP MU WM MI.
{ right; left. reflexivity. }
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite lb_remove_other in OUT2 by (cbn; lia). rewrite lb_remove_head in OUT2.
destruct OUT2 as [(-> & HerrHP2 & HPR2 & HP2) | (Hr & HPR2 & [junk' BLK] & HP2)].
-
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in COMB; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in COMB.
destruct (al_arr_split segs m2 arr size size ps junk [] COMB ltac:(apply Nat2Z.inj; rewrite LJ', Z2Nat.id by lia; reflexivity) ltac:(lia)) as [ARR JK].
clear MU WM MI ST COMB.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_true. do 9 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
apply evt_RZ_done. apply K. unfold array_list_add_post.
exists m2, A2, (2^64 - 1), e2, arr, size.
split; [| split; [eapply model_vm_only_trans; [exact VM0 | exact VM2] | split; [| split; [exact HPR | split; [exact ERR2 | split; [exact HP2| left]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
rewrite app_nil_r in JK. eapply alist_close. split; [exact HDR | split; [exact ARR | split; [exact JK | lia]]].
-
assert (LO8 : length (u64s (wl ps) ++ junk) = Z.to_nat (8 * size)).
{ rewrite length_app, u64s_length, wl_length. lia. }
rewrite LO8, Z.min_r, firstn_all2 in BLK by (rewrite ?LO8; lia). clear LO8.
replace (size * 2 * 8) with (8 * (2 * size)) in BLK, HP2 by lia.
destruct (al_arr_split segs m2 r size (2 * size) ps junk junk' BLK ltac:(apply Nat2Z.inj; rewrite LJ', Z2Nat.id by lia; reflexivity) ltac:(lia)) as [ARR JK]. clear BLK. unfold al_tail in JK.
assert (HP2' : HEAPx A2 ((a, 32) :: (r, 8 * (2 * size)) :: LB) m2 md2) by (eapply heap_perm; [exact HP2 | apply perm_swap]). clear HP2.
destruct (al_blocks S4L HIx _ _ _ _ _ _ _ HP2') as (_ & (Hral & Hrlo & Hrhi & Hrimg) & Hrdj).
cbn [hl_img_lo hl_img_hi S4L] in Hrimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
clear MU WM MI ST COMB.
pose proof (wl_length ps) as WL.
pose proof (heap_model_ok _ _ _ _ _ _ HP2') as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2') as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(a, a + 32)] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_falsex. step. step. step. step. step.
replace (size * 2) with (2 * size) in * by lia.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
apply evt_RZ_done.
eapply (al_add_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 md2 A2 r (2 * size) (junk ++ junk') e2);
first [exact ARR | exact JK | exact ST2 | exact SPA | exact HT | exact RA | exact K | idtac].
all: lazymatch goal with
| |- HEAP _ _ _ _ _ _ =>
eapply (heap_frame S4L HIx); [exact HP2' | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2' MU); solve_frameW_with HP2'
| |- al_hdr _ _ _ _ _ _ _ => unfold al_hdr; exact HDR
| |- add_frame _ _ => unfold add_frame; destruct FR as [[[_ W] B] S]; split; [split; [split; [reflexivity | exact W] | exact B] | exact S]
| |- rw_cells _ _ _ _ => first [exact ERR2 | exact FR]
| |- model_vm_only _ _ => eapply model_vm_only_trans; eassumption
| |- heap_pres _ _ _ _ _ =>
eapply heap_pres_trans; [exact HPR|];
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outside S4L HIx); [exact HP2' | intros bb Hbb0; right; right; exact Hbb0 | clia |];
solve_clientW S4L HIx HP2'
| |- _ \/ _ => right; split; [reflexivity | lia]
| |- _ => clia
end.
Qed.
End AlAdd.

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
do 7 step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (HP1 : HEAPx A ((a, 32) :: (arr, 8 * size) :: LB) m1 md0).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP. }
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m0 m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; right; right; exact Hb | clia |].
solve_clientW S4L HIx HP. }
step. if_falsex.
step. step. ubsan_align Hal.
step. step. step. step. if_falsex. step. step.
destruct (Z.lt_ge_cases (Z.of_nat (length ps) + 1) size) as [LT|GE].
-
if_falsex. step. step.
apply evt_RZ_done.
eapply (al_add_store HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo a arr size d ps T
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A arr size junk errv);
first [exact HP1 | exact ARR | exact JK | exact ST | exact SPA | exact HT | exact RA | exact K | exact HPR1
| apply model_vm_only_refl | idtac].
all: lazymatch goal with
| |- al_hdr _ _ _ _ _ _ _ => unfold al_hdr; exact HDR
| |- add_frame _ _ _ _ _ _ _ _ => unfold add_frame; destruct FR as [[[_ W] B] S]; split; [split; [split; [reflexivity | exact W] | exact B] | exact S]
| |- rw_cells _ _ _ _ => exact ERR
| |- _ \/ _ => left; split; [reflexivity | split; [reflexivity | lia]]
| |- _ => clia
end.
-
if_truex.
apply evt_RZ_done.
eapply (al_add_grow HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo a arr size d ps T
_ _ _ _ _ _ _ _ _ _ _ _ _ m1 md0 A junk errv);
first [exact HP1 | exact ARR | exact JK | exact ST | exact SPA | exact HT | exact RA | exact K | exact HPR1
| apply model_vm_only_refl | idtac].
all: lazymatch goal with
| |- al_hdr _ _ _ _ _ _ _ => unfold al_hdr; exact HDR
| |- add_frame _ _ _ _ _ _ _ _ => unfold add_frame; destruct FR as [[[_ W] B] S]; split; [split; [split; [reflexivity | exact W] | exact B] | exact S]
| |- rw_cells _ _ _ _ => exact ERR
| |- _ => clia
end.
Qed.
End AlAdd2.

End RC__1.

End G.
