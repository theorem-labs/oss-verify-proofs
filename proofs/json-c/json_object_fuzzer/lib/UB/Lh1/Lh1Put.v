(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo Q8tj QSL3 Q8Q3 Q6WR Q9Mh QPIU QAyu QnCn Q6q3 Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply2 Lib.GwApplyJ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Lh1 Require Lh1Mf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3.
Import Q8Q3.
Import Q6WR Q6WR.Mq0.
Import Q9Mh.Mq7.
Import QPIU.Mqd QPIU.Mqb QAyu.Mq2 QnCn.Mq0 QPIU.Mq2 QPIU.Mq0.
Import Q9Mh.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top.TopUbTac.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m.

Definition putloop1_code (w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119 : Z) : list Z :=
[0xfa010113; 0x04113c23; 0x04813823; 0x04913423; 0x05213023; 0x03313c23; 0x03413823; 0x03513423; 0x03613023; 0x01713c23; 0x01813823; 0x01913423; 0x1a050c63; 0x00050413; 0x00000593; 0x1e4000ef; 0x00200a93; 0x1b551263; 0x00400b13; 0x00600b93; 0x00500c13; 0xfff00c93; 0x0240006f; 0x02843503; w_24; 0x01043503; w_26; 0x00040513; w_28; 0x00048413; 0x16048663; 0x00747513; 0x18051e63; 0x00042583; 0x02843503; 0x03659263; w_36; 0x02843583; 0x18058263; 0x0075f613; 0x16061e63; 0x0105b903; 0x00051a63; 0x0a80006f; w_44; 0x00000913; 0x08050e63; 0x00042583; 0xfff50993; 0x00100a13; 0x0100006f; 0xfff98993; 0x001a0a13; 0x09998063; 0x03858263; 0xff6598e3; 0x12090e63; 0x00797513; 0x12051a63; 0x01093483; 0x00093823; 0x02049863; 0x03c0006f; 0x02843503; 0x00098593; w_65; 0x02843583; 0x00050493; 0x00058513; 0x00098593; 0x00000613; w_71; 0x00048a63; 0x00048513; 0x00000593; 0x0f4000ef; 0x07550463; 0x00042583; 0xf9659ae3; 0x0e090063; 0x00797513; 0x0c051c63; 0x02093903; 0x00400593; 0xf7dff06f; 0x00442503; 0x02043483; 0xf0051ce3; 0x01843603; 0x00060863; 0x00040513; 0x00048593; 0x000600e7; 0x00042503; 0x00043c23; 0x02043023; 0x05750863; 0xed850ce3; 0xed651ee3; 0x02843503; w_100; 0xed1ff06f; 0x0074f513; 0x08051063; 0x0004bc23; 0x0284b023; 0x00042583; 0x02843503; 0x01659863; 0x00090593; w_110; 0xeb9ff06f; 0x00098593; 0x000a0613; w_114; 0xea9ff06f; 0x02843503; 0xe80558e3; 0x03043503; w_119; 0xe85ff06f; 0x00100513; 0x05813083; 0x05013403; 0x04813483; 0x04013903; 0x03813983; 0x03013a03; 0x02813a83; 0x02013b03; 0x01813b83; 0x01013c03; 0x00813c83; 0x06010113; 0x00008067; 0xc0001073]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119 : Z).
Variables (joff_24 joff_26 joff_28 joff_100 joff_110 : bv 21).
Variables (e_pbfree e_alfree e_lhfree e_18934 : Z).
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
Hypothesis CODE : code_at segs base (putloop1_code w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 544.
Hypothesis D_24 : decode_any (Z_to_bv 32 w_24) = Some (Jal 1 joff_24, 4%Z).
Hypothesis E_24 : is_ecall (Z_to_bv 32 w_24) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Jal 1 joff_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_28 : decode_any (Z_to_bv 32 w_28) = Some (Jal 1 joff_28, 4%Z).
Hypothesis E_28 : is_ecall (Z_to_bv 32 w_28) = false.
Hypothesis D_100 : decode_any (Z_to_bv 32 w_100) = Some (Jal 1 joff_100, 4%Z).
Hypothesis E_100 : is_ecall (Z_to_bv 32 w_100) = false.
Hypothesis D_110 : decode_any (Z_to_bv 32 w_110) = Some (Jal 1 joff_110, 4%Z).
Hypothesis E_110 : is_ecall (Z_to_bv 32 w_110) = false.
Hypothesis LINK_24 : gw_anch (base + 96 + bv_signed joff_24)%Z (e_alfree + 0)%Z.
Hypothesis LINK_26 : gw_anch (base + 104 + bv_signed joff_26)%Z (e_pbfree + 0)%Z.
Hypothesis LINK_28 : gw_anch (base + 112 + bv_signed joff_28)%Z e_free.
Hypothesis LINK_100 : gw_anch (base + 400 + bv_signed joff_100)%Z (e_lhfree + 0)%Z.
Hypothesis LINK_110 : gw_anch (base + 440 + bv_signed joff_110)%Z (e_18934 + 0)%Z.

Hypothesis LAY_POS_e_fn_arr_to_json_string : gw_le 1 e_fn_arr_to_json_string.
Hypothesis LAY_HI_e_fn_arr_to_json_string : gw_le (e_fn_arr_to_json_string + 4) 1099511627776.
Hypothesis LAY_POS_e_fn_obj_to_json_string : gw_le 1 e_fn_obj_to_json_string.
Hypothesis LAY_HI_e_fn_obj_to_json_string : gw_le (e_fn_obj_to_json_string + 4) 1099511627776.

Hypothesis maybe_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@Lh1Mf.gw_all) (@Lh1Mf.maybe_free_cps) (base + 544)%Z)) in let T := gw_fold_pcs T base (544)%Z [0]%Z in exact T).
Hypothesis printbuf_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mqd.gw_all) (@QPIU.Mqd.printbuf_free_cps) e_pbfree)) in exact T).
Hypothesis lh_table_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QAyu.Mq2.gw_all) (@QAyu.Mq2.lh_table_free_cps) e_lhfree)) in exact T).
Hypothesis array_list_free_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QPIU.Mq0.gw_all) (@QPIU.Mq0.array_list_free_cps) e_alfree)) in exact T).

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
#[using="All"] Lemma gw_all : True. Proof. exact I. Qed.

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

Section Loop.
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
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] -> tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 (ent_addr tbl (le_ix ef)) ->
(forall ms' md', lh_delete_tail_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo errv t tbl size es jf ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_18934 + 0)) fc None m (seg_rom segs)) md) T.

Variables (sp gp s10 s11 : word) (lo : Z) (errv : word).

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -96)).
Notation TP := (Z_to_bv 64 gTP).
Notation CM1 := (Z_to_bv 64 18446744073709551615).

Definition next_post (q : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (m : word -> option byte) (md : Model) (LB : list blk)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (F' : bvmap 5 word) (fc' : bv 32)
(x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word),
ms' = MS (mkR x1 SPR gp TP t0 t1 t2 x8 (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 (base + 0x74)) fc' None m' (seg_rom segs) /\
fsaved F1 F' /\ (frm0 fc1 -> frm0 fc') /\ model_vm_only md md' /\
HEAPx A' LB m' md' /\ stk segs m' lo (bv_unsigned sp + -96) /\
heap_pres S4L LB (bv_unsigned sp + -96) m m' /\ rw_cells segs m' (gTP - 164) [C4 errv].
Notation NEXT := next_post.

Definition tyof (isobj : bool) : Z := if isobj then 4 else 5.

Definition zhead (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (XBS : list blk) : Prop :=
if isobj then zobjc segs S4F m x q kids XBS else zarrc segs S4F m x q kids XBS.

Definition head_stmt (isobj : bool) (kids : list (option jshape)) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS : list blk) (x q : Z) (T : TSet),
HEAPx A (XBS ++ LB) m md ->
zhead isobj m x q kids XBS ->
stk segs m lo (bv_unsigned sp + -96) -> rw_cells segs m (gTP - 164) [C4 errv] ->
(forall ms' md', NEXT q F1 fc1 m md LB ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x7c)) fc1 None m (seg_rom segs)) md) T.

Definition desc_stmt (c : jshape) : Prop :=
match c with Sobj kids => head_stmt true kids | Sarr kids => head_stmt false kids | _ => True end.
Definition desc_opt (k : option jshape) : Prop := match k with Some c => desc_stmt c | None => True end.
Definition kids_desc (kids : list (option jshape)) : Prop := forall k, In k kids -> desc_opt k.

Definition zcont (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (nz : nat) (cur : Z) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs, zobj segs S4F m x q kids nz t tbl size es svs XBS /\
(forall kids1 kl, kids = kids1 ++ [kl] -> exists e, nth_error es (length kids1) = Some e /\ cur = ent_addr tbl (le_ix e))
else exists a arr size, zarr segs S4F m x q kids nz a arr size XBS.

Definition cont_stmt (isobj : bool) (kids : list (option jshape)) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS : list blk) (x q : Z) (T : TSet) (nz : nat) (cur : Z),
HEAPx A (XBS ++ LB) m md ->
zcont isobj m x q kids nz cur XBS ->
stk segs m lo (bv_unsigned sp + -96) -> rw_cells segs m (gTP - 164) [C4 errv] ->
(forall ms' md', NEXT q F1 fc1 m md LB ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 (Z_to_bv 64 (tyof isobj)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz))
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0xcc)) fc1 None m (seg_rom segs)) md) T.

Definition zbodyp (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (k : option jshape) (nz : nat) (cur : Z) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs e, zobj segs S4F m x q (kids ++ [k]) nz t tbl size es svs XBS /\
nth_error es (length kids) = Some e /\ cur = ent_addr tbl (le_ix e)
else exists a arr size, zarr segs S4F m x q (kids ++ [k]) nz a arr size XBS.

Definition body_stmt (isobj : bool) (kids : list (option jshape)) (k : option jshape) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS : list blk) (x q : Z) (T : TSet) (nz : nat) (cur : Z),
HEAPx A (XBS ++ LB) m md ->
zbodyp isobj m x q kids k nz cur XBS ->
stk segs m lo (bv_unsigned sp + -96) -> rw_cells segs m (gTP - 164) [C4 errv] ->
(forall ms' md', NEXT q F1 fc1 m md LB ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 (Z_to_bv 64 (tyof isobj)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0xd8)) fc1 None m (seg_rom segs)) md) T.

Definition tojs_of (isobj : bool) : Z := if isobj then fn_obj_to_json_string S4F else fn_arr_to_json_string S4F.
Notation head_stmt' := head_stmt.

Definition zpop (isobj : bool) (m : word -> option byte) (x q : Z) (nz : nat) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs, zobj segs S4F m x q [] nz t tbl size es svs XBS
else exists a arr size, zarr segs S4F m x q [] nz a arr size XBS.

#[using="Type"] Lemma zhead_hdr : forall isobj m x q kids XBS,
zhead isobj m x q kids XBS -> List.NoDup (map blk_addr XBS) ->
exists pb cf, In (x, 48) XBS /\
rw_cells segs m x (jhdr_cells (tyof isobj) 0 (tojs_of isobj) pb 0 q ++ [C8 (Z_to_bv 64 cf)]) /\
(forall m' q', rw_cells segs m' x (jhdr_cells (tyof isobj) 0 (tojs_of isobj) pb 0 q' ++ [C8 (Z_to_bv 64 cf)]) ->
agree_on segs (others x XBS) m m' -> zhead isobj m' x q' kids XBS).
Proof. clear - segs HIx sp gp s10 s11 lo errv. intros isobj. destruct isobj; [apply zobjc_hdr | apply zarrc_hdr]. Qed.

#[using="Type"] Lemma zhead_agree : forall isobj BS m m' x q kids XBS,
zhead isobj m x q kids XBS -> agree_on segs BS m m' -> incl XBS BS -> zhead isobj m' x q kids XBS.
Proof. clear - segs HIx sp gp s10 s11 lo errv. intros isobj. destruct isobj; [apply zobjc_agree | apply zarrc_agree]. Qed.

#[using="Type"] Lemma zomb_zhead : forall c m v bs, zomb segs S4F c m v bs -> desc_stmt c ->
exists isobj ck, zhead isobj m v 0 ck bs /\ head_stmt isobj ck.
Proof. clear - segs S4F HIx sp gp s10 s11 lo errv.
intros c m v bs ZC KD. destruct c as [| | | |ck|ck]; cbn in ZC; try contradiction.
- exists true, ck. split; [exact (proj2 ZC) | exact KD].
- exists false, ck. split; [exact (proj2 ZC) | exact KD].
Qed.

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string"] Lemma next_post_w : forall q F1 fc1 F2 fc2 m1 m2 md1 md2 LB ms md,
fsaved F1 F2 -> (frm0 fc1 -> frm0 fc2) -> model_vm_only md1 md2 ->
heap_pres S4L LB (bv_unsigned sp + -96) m1 m2 ->
NEXT q F2 fc2 m2 md2 LB ms md -> NEXT q F1 fc1 m1 md1 LB ms md.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string HIx sp gp s10 s11 lo errv. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_arr_to_json_string as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_arr_to_json_string as gL3_; unfold gw_le in gL3_. pose proof LAY_POS_e_fn_obj_to_json_string as gL4_; unfold gw_le in gL4_. pose proof LAY_HI_e_fn_obj_to_json_string as gL5_; unfold gw_le in gL5_.
intros until md. intros FS FRM VM HPR NP. unfold next_post in *.
destruct NP as (m' & A' & F' & fc' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & E & FS' & FRM' & VM' & HP' & ST' & HPR' & ERR').
exists m', A', F', fc'. do 20 eexists. split; [exact E|].
split; [eapply fsaved_trans; [exact FS | exact FS']|]. split; [intros Hf; exact (FRM' (FRM Hf))|].
split; [eapply model_vm_only_trans; [exact VM | exact VM']|]. split; [exact HP'|]. split; [exact ST'|].
split; [eapply heap_pres_trans; [exact HPR | exact HPR'] | exact ERR'].
Qed.

#[using="Type"] Lemma nodup_app_l : forall (BS LB : list blk), List.NoDup (map blk_addr (BS ++ LB)) -> List.NoDup (map blk_addr BS).
Proof. clear - HIx. intros BS LB ND. rewrite map_app in ND. exact (NoDup_app_remove_r _ _ ND). Qed.

Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -96 - 8432.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis DEL : lh_delete_tail_stmt2.

#[using="w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119 joff_26 joff_28 e_pbfree LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_26 E_26 D_28 E_28 LINK_26 LINK_28 printbuf_free_cps LO LOS SPA HT"] Lemma pop_tail :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB PBS : list blk) (x q pb ty tojs cf : Z) (T : TSet),
HEAPx A ((x, 48) :: PBS ++ LB) m md ->
rw_cells segs m x (jhdr_cells ty 0 tojs pb 0 0 ++ [C8 (Z_to_bv 64 cf)]) ->
opt_pbuf segs m PBS pb ->
stk segs m lo (bv_unsigned sp + -96) -> rw_cells segs m (gTP - 164) [C4 errv] ->
(forall ms' md', next_post q F1 fc1 m md LB ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x64)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119 joff_26 joff_28 e_pbfree LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_26 E_26 D_28 E_28 LINK_26 LINK_28 printbuf_free_cps LO LOS SPA HT segs base gTP HIx sp gp s10 s11 lo errv. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until T. intros HP HDR OPB ST ERR K.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
pose proof (wmono_refl segs m) as WM. pose proof (munch_refl [] m) as MU.
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. step.
apply evt_RZ_done.
eapply (printbuf_free_cps HIx) with (BS := PBS) (LB := (x, 48) :: LB) (p := pb) (lo := lo);
[ eapply (heap_perm S4L HIx); [exact HP | perm] | exact OPB | .. ]; try alloc_side.
intros ms2 md2 (m2 & A2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR2 by lia.
clear MU WM MI HDR OPB ST.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. step.
alloc_call (hi_free S4L HIx) S4L HIx HP2 MU WM MI.
{ right. exists 48. left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR3 by lia.
rewrite lb_remove_head in HPR3, HP3.
apply K. unfold next_post.
exists m3, A3, F2, fc2. do 20 eexists.
split; [try g_ret_pc_any; reflexivity |].
split; [exact FS2|]. split; [exact FRM2|]. split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|].
split; [exact HP3|]. split; [exact ST3|]. split; [| exact ERR3].
eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; right; exact Hb] | exact HPR3].
Qed.

#[using="w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119 joff_24 joff_26 joff_28 joff_100 e_pbfree e_alfree e_lhfree LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_24 E_24 D_26 E_26 D_28 E_28 D_100 E_100 LINK_24 LINK_26 LINK_28 LINK_100 printbuf_free_cps lh_table_free_cps array_list_free_cps LO LOS SPA HT"] Lemma pop_ok : forall (isobj : bool)
(x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS : list blk) (x q : Z) (nz : nat) (T : TSet),
HEAPx A (XBS ++ LB) m md ->
zpop isobj m x q nz XBS ->
stk segs m lo (bv_unsigned sp + -96) -> rw_cells segs m (gTP - 164) [C4 errv] ->
(forall ms' md', next_post q F1 fc1 m md LB ms' md' -> realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 (base + 0x154)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119 joff_24 joff_26 joff_28 joff_100 e_pbfree e_alfree e_lhfree LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_24 E_24 D_26 E_26 D_28 E_28 D_100 E_100 LINK_24 LINK_26 LINK_28 LINK_100 printbuf_free_cps lh_table_free_cps array_list_free_cps LO LOS SPA HT segs base gTP HIx sp gp s10 s11 lo errv. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until T. intros HP ZP ST ERR K.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl segs m) as WM. pose proof (munch_refl [(x, x + 40)] m) as MU.
destruct isobj.
- destruct ZP as (t & tbl & size & es & svs & Z0).
destruct (zobj_nil_shape segs S4F _ _ _ _ _ _ _ _ _ _ Z0) as (pb & PBS & EX & OPB & HDR & OPEN & VZ & Lz). clear Z0.
subst XBS. rewrite <- app_assoc in HP. cbn [app] in HP.
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. norm_w32. step. step. if_false. step. step. if_true. step. norm_w32. stepz. stepz.
step. if_false. step. if_false. step. if_false. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp + -96) HP MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; in_sub Hb) ltac:(clia))
as (HP2 & AG2 & HPR2).
assert (OPEN2 : lh_open segs S4F m2 t tbl size es svs).
{ eapply lh_open_agree; [exact OPEN | exact AG2 | intros b Hb; in_sub Hb]. }
apply evt_RZ_done.
eapply (lh_table_free_cps HIx) with (LB := (x, 48) :: PBS ++ LB) (lo := lo) (kvs:=[]) (tbl := tbl) (size := size) (es := es) (svs := svs);
[ eapply (heap_perm S4L HIx); [exact HP2 | perm] | exact OPEN2 | exact VZ | .. ]; try alloc_side.
intros ms4 md4 (m4 & A4 & r4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & HP4).
destruct RS4 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F4 & fc4 & -> & FS4 & FRM4).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR4 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
assert (OPB4 : opt_pbuf segs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
- eapply agree_on_incl; [exact AG2 | intros b Hb; in_sub Hb].
- eapply (agree_of_heap_pres segs S4L); [exact HPR4 | reflexivity | intros b Hb; in_sub Hb]. }
clear MU WM MI ST OPEN OPEN2.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
reenter MOK4. step.
apply evt_RZ_done.
eapply pop_tail; [exact HP4 | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB4 | exact ST4 | exact ERR4 |].
intros ms5 md5 (m5 & A5 & F5 & fc5 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & -> & FS5 & FRM5 & VM5 & HP5 & ST5 & HPR5 & ERR5).
apply K. unfold next_post. exists m5, A5, F5, fc5. do 20 eexists.
split; [reflexivity|]. split; [eapply fsaved_trans; [exact FS4 | exact FS5]|]. split; [intros Hf; exact (FRM5 (FRM4 Hf))|].
split; [eapply model_vm_only_trans; [exact VM4 | exact VM5]|]. split; [exact HP5|]. split; [exact ST5|]. split; [| exact ERR5].
eapply heap_pres_trans; [exact HPR2|]. eapply heap_pres_trans; [| exact HPR5].
eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; in_sub Hb].
- destruct ZP as (a & arr & size & Z0).
destruct (zarr_nil_vals segs S4F _ _ _ _ _ _ _ _ Z0) as (pb & PBS & EX & OPB & HDR & AL). clear Z0.
subst XBS. rewrite <- app_assoc in HP. cbn [app] in HP.
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. norm_w32. step. step. if_false. step. step. if_true. step. norm_w32. stepz. stepz.
step. if_false. step. if_true. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp + -96) HP MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; in_sub Hb) ltac:(clia))
as (HP2 & AG2 & HPR2).
assert (AL2 : alist segs S4F m2 [(a, 32); (arr, 8 * size)] a (repeat 0 nz)).
{ eapply alist_agree; [exact AL | exact AG2 | intros b Hb; in_sub Hb]. }
apply evt_RZ_done.
eapply (array_list_free_cps HIx) with (LB := (x, 48) :: PBS ++ LB) (lo := lo) (BS := [(a, 32); (arr, 8 * size)]);
[ eapply (heap_perm S4L HIx); [exact HP2 | perm] | exact AL2 | apply Forall_repeat0 | .. ]; try alloc_side.
intros ms4 md4 (m4 & A4 & r4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & HP4).
destruct RS4 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F4 & fc4 & -> & FS4 & FRM4).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR4 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
assert (OPB4 : opt_pbuf segs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
- eapply agree_on_incl; [exact AG2 | intros b Hb; in_sub Hb].
- eapply (agree_of_heap_pres segs S4L); [exact HPR4 | reflexivity | intros b Hb; in_sub Hb]. }
clear MU WM MI ST AL AL2.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
try g_ret_pc_any.
eapply pop_tail; [exact HP4 | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB4 | exact ST4 | exact ERR4 |].
intros ms5 md5 (m5 & A5 & F5 & fc5 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & -> & FS5 & FRM5 & VM5 & HP5 & ST5 & HPR5 & ERR5).
apply K. unfold next_post. exists m5, A5, F5, fc5. do 20 eexists.
split; [reflexivity|]. split; [eapply fsaved_trans; [exact FS4 | exact FS5]|]. split; [intros Hf; exact (FRM5 (FRM4 Hf))|].
split; [eapply model_vm_only_trans; [exact VM4 | exact VM5]|]. split; [exact HP5|]. split; [exact ST5|]. split; [| exact ERR5].
eapply heap_pres_trans; [exact HPR2|]. eapply heap_pres_trans; [| exact HPR5].
eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; in_sub Hb].
Qed.

#[using="w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119 e_alfree e_lhfree e_18934 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string"] Lemma descend_tail : forall (isobjc isobjp : bool) (ck kids : list (option jshape))
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
Proof. clear - w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119 e_alfree e_lhfree e_18934 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string segs base gTP HIx sp gp s10 s11 lo errv LO LOS SPA HT DEL. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
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

#[using="w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119 joff_110 e_alfree e_lhfree e_18934 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_110 E_110 LINK_110 LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string LO LOS SPA HT DEL"] Lemma descend_obj : forall c kids,
desc_stmt c -> head_stmt' true kids ->
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
F1 (Z_to_bv 64 (base + 0x198)) fc1 None m (seg_rom segs)) md) T.
Proof. clear - w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119 joff_110 e_alfree e_lhfree e_18934 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_110 E_110 LINK_110 LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string LO LOS SPA HT DEL segs base gTP S4F HIx sp gp s10 s11 lo errv. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros c kids KD HK. intros until e2. intros HP ZC Z Hes2 ST ERR K.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct Z as (pb & PBS & KBS & esk & esz & Ees2 & Lz & Fz & EX1 & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L _]. rewrite length_map in L.
assert (VZ : forall j y, (length kids <= j)%nat -> nth_error es2 j = Some y -> le_v y = 0).
{ intros j y Hj Hy. rewrite Ees2, nth_error_app2 in Hy by lia. exact (proj1 (Forall_forall _ _) Fz y (nth_error_In _ _ Hy)). }
destruct (zomb_zhead c m v bs ZC KD) as (isobjc & ck & ZCH & HC). clear ZC KD.
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
step. step. ub_align_auto. stepz. step. step. norm_w32. step. step. if_false. step. step.
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

#[using="w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119 joff_110 e_alfree e_lhfree e_18934 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_110 E_110 LINK_110 LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string maybe_free_cps S4F LO LOS SPA HT DEL"] Lemma body_obj_ok : forall kids k,
desc_opt k ->
cont_stmt true kids ->
head_stmt true kids ->
body_stmt true kids k.
Proof. clear - w_24 w_26 w_28 w_36 w_44 w_65 w_71 w_100 w_110 w_114 w_119 joff_110 e_alfree e_lhfree e_18934 LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER D_110 E_110 LINK_110 LAY_POS_e_fn_arr_to_json_string LAY_HI_e_fn_arr_to_json_string LAY_POS_e_fn_obj_to_json_string LAY_HI_e_fn_obj_to_json_string maybe_free_cps S4F LO LOS SPA HT DEL HIx sp gp s10 s11 lo errv. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros kids k KD CONT HEADK.
unfold body_stmt. intros until cur. intros HP ZB ST ERR K.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct ZB as (t & tbl & size & es & svs & e0 & Z0 & He0 & Ecur).
destruct (zobj_last segs S4F _ _ _ _ _ _ _ _ _ _ _ _ Z0) as (pb & PBS & KBS1 & bs & esk1 & e & esz & Ees & Lk & Lz & Fz & EX & OPB & HDR & OPEN & OK1 & Hk).
assert (Ee : e0 = e) by (rewrite Ees, <- Lk, nth_error_app_len in He0; injection He0 as He0; symmetry; exact He0). subst e0.
clear Z0.

pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as NDall.
assert (HPl : HEAPx A (lh_blocks t tbl size es ++ ((x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB)) m md).
{ eapply (heap_perm S4L HIx); [exact HP | rewrite EX; perm]. }
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HPl) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & Httb & KEYF).
cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP INx) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP INx) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
assert (INtb : In (tbl, 40 * size) (XBS ++ LB)) by (rewrite EX; unfold lh_blocks; in_elem).
assert (NXT : x <> tbl).
{ intros E. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HPl) as ND. unfold lh_blocks in ND. cbn [map blk_addr fst app] in ND.
inversion ND as [|y l Hn1 ND1]; subst. inversion ND1 as [|y' l' Hn2 ND2]; subst. apply Hn2.
rewrite map_app. apply in_or_app. right. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ x 48 tbl (40 * size) HP INx INtb NXT) as Dxtb.

destruct (lh_open_slot segs S4F _ _ _ _ _ _ _ (length kids) e OPEN ltac:(rewrite Ees, <- Lk; apply nth_error_app_len)) as (sl & Esl & Hix & SLOT).
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
assert (Hixz : 0 <= Z.of_nat (le_ix e) /\ Z.of_nat (le_ix e) + 1 <= size) by lia.
unfold ent_addr in SLOT, Ecur. subst cur.
set (ea := tbl + 40 * Z.of_nat (le_ix e)) in *.
assert (EAR : tbl <= ea /\ ea + 40 <= tbl + 40 * size) by (subst ea; lia).
assert (EA0 : 0 < ea) by (subst ea; lia).
assert (EA8 : ea mod 8 = 0) by (subst ea; clear - Hbal; Z.div_mod_to_equations; lia).
pose proof (wmono_refl segs m) as WM. pose proof (munch_refl [(ea + 16, ea + 24)] m) as MU.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app] in HDR.
stash Hk. stash KEYF. stash OPB. stash OK1. stash HDR0. cbn [tyof].
apply rz_evt; [exact MOK|].
step. if_false. step. if_false. step. if_falsex. step. step. ub_align_auto. step. stepz.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
assert (HPtb : HEAPx A ((tbl, 40 * size) :: (t, 56) :: map kblk es ++ (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB) m md).
{ eapply (heap_perm S4L HIx); [exact HPl | unfold lh_blocks; perm]. }
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp + -96) HPtb MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; in_sub Hb) ltac:(clia))
as (HP2 & AG2 & HPR2).
unstash KEYF.
assert (OPEN2 : lh_open segs S4F m2 t tbl size (esk1 ++ with_v e 0 :: esz) (upd svs (le_ix e) (sv_with_v sl 0))).
{ replace (esk1 ++ with_v e 0 :: esz) with (upd es (length kids) (with_v e 0)) by (rewrite Ees, <- Lk; apply upd_app_len').
eapply (lh_open_set_val segs S4F); [exact OPEN | rewrite Ees, <- Lk; apply nth_error_app_len | exact Esl | lia | exact MU | exact WM | | exact Httb | | ].
- apply Forall_cons; [cbn; subst ea; unfold ent_addr; lia | apply Forall_nil].
- intros y Hy. destruct (KEYF y Hy) as (_ & _ & _ & _ & _ & D). exact D.
- unfold ent_addr. fold ea. exact SLOT. }
stash KEYF.

set (es2 := esk1 ++ with_v e 0 :: esz) in OPEN2.
set (svs2 := upd svs (le_ix e) (sv_with_v sl 0)) in OPEN2.
set (XBS1 := ((x, 48) :: lh_blocks t tbl size es ++ concat KBS1) ++ PBS).
assert (ELB : lh_blocks t tbl size es2 = lh_blocks t tbl size es).
{ subst es2. rewrite Ees. unfold lh_blocks. rewrite !map_app. reflexivity. }
assert (Z2 : zobj segs S4F m2 x q kids (S nz) t tbl size es2 svs2 XBS1).
{ unstash HDR0. unstash OPB. unstash OK1. subst XBS1. rewrite <- ELB.
eapply (zobj_last_close segs S4F m m2); [exact Lz | exact Fz | exact OPB | exact HDR0 | exact OK1 | exact OPEN2 | ].
eapply agree_on_incl; [exact AG2 | intros b Hb; in_sub Hb]. }
assert (Hes2 : nth_error es2 (length kids) = Some (with_v e 0)) by (subst es2; rewrite <- Lk; apply nth_error_app_len).
assert (VZ2 : forall j y, (length kids <= j)%nat -> nth_error es2 j = Some y -> le_v y = 0).
{ intros j y Hj Hy. subst es2. rewrite nth_error_app2 in Hy by lia.
destruct (j - length esk1)%nat as [|j'] eqn:Ej; cbn in Hy.
- injection Hy as <-. reflexivity.
- exact (proj1 (Forall_forall _ _) Fz y (nth_error_In _ _ Hy)). }
clear HDR0 OPB OK1 OPEN.
step.
unstash Hk. destruct k as [c|].
-
destruct Hk as [Hv J].
assert (J2 : jval segs S4F c m2 bs (le_v e) 1) by (eapply jval_agree; [exact J | exact AG2 | intros b Hb; in_sub Hb]). clear J.
assert (HPc : HEAPx A (bs ++ XBS1 ++ LB) m2 md) by (eapply (heap_perm S4L HIx); [exact HP2 | subst XBS1; hperm]).
pose proof (nodup_app_l _ _ (heap_blk_nodup S4L HIx _ _ _ _ HPc)) as NDbs.
destruct (jval_hdr segs S4F c m2 bs (le_v e) 1 J2 NDbs) as (cn & tojs_ & pb_ & udel_ & ud_ & rest_ & INc & _ & N48c & _ & _).
pose proof (heap_blk S4L HIx _ _ _ _ (le_v e) cn HPc ltac:(in_sub INc)) as (_ & Hcal & Hclo & Hchi & _). clear tojs_ pb_ udel_ ud_ rest_.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hchi.
if_truex. step. step. step.
apply evt_RZ_done.
eapply (maybe_free_cps HIx) with (s := c) (BS := bs) (LB := XBS1 ++ LB) (x := le_v e) (rc := 1) (lo := lo);
[ exact HPc | lia | lia | exact J2 | .. ]; try alloc_side.
intros ms3 md3 (m3 & A3 & r & RS3 & VM3 & ST3 & HPR3 & ERR3 & OUT3).
destruct RS3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR3 by lia.
match goal with H : rw_cells _ m2 x _ |- _ => rename H into HDR2 end.
match goal with H : rw_cells _ m2 ea _ |- _ => rename H into SLOT2 end.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in HDR2; [| eapply client_range_block; [subst XBS1; in_elem | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in SLOT2; [| eapply (client_range_block S4L _ _ _ _ tbl (40 * size)); [subst XBS1; unfold lh_blocks; in_elem | lia | cbn; lia]]. cbn [hl_segs S4L] in SLOT2.
assert (Z3 : zobj segs S4F m3 x q kids (S nz) t tbl size es2 svs2 XBS1).
{ eapply (zobj_agree segs S4F (XBS1 ++ LB)); [exact Z2 | eapply (agree_of_heap_pres segs S4L); [exact HPR3 | reflexivity | intros b Hb; exact Hb] | intros b Hb; in_sub Hb]. }
assert (HPR23 : heap_pres S4L LB (bv_unsigned sp + -96) m m3).
{ eapply heap_pres_trans; [exact HPR2 | eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; in_sub Hb]]. }
clear MU WM MI HP2 HPtb HPl HP AG2 Z2 ST J2 HPc.
destruct OUT3 as [(_ & Habs & _) | [(-> & _ & HP3) | (-> & _ & ZC & HP3)]]; [lia | |].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m3) as MU. pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. if_falsex. step. norm_w32. step. if_false. step. if_falsex. step. step. ub_align_auto. step. step. step.
apply evt_RZ_done.
replace (Z.of_nat nz + 1) with (Z.of_nat (S nz)) by lia.
eapply CONT; [exact HP3 | | exact ST3 | exact ERR3 |].
* exists t, tbl, size, es2, svs2. split; [exact Z3|].
intros kids1 kl Ek.
assert (Hj : (length kids1 < length esk1)%nat) by (rewrite Lk, Ek, length_app; cbn; lia).
destruct (nth_error esk1 (length kids1)) as [e'|] eqn:En; [| apply nth_error_None in En; lia].
exists e'. split; [subst es2; rewrite nth_error_app1 by lia; exact En|].
rewrite pv_of_spec, Ek, length_app. cbn [length]. rewrite Nat.add_1_r. cbn [pv_of].
rewrite Ees, nth_error_app1 by lia. rewrite En. reflexivity.
* intros ms' md' NP. apply K. eapply next_post_w; [exact FS3 | exact FRM3 | exact VM3 | exact HPR23 | exact NP].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m3) as MU. pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. if_true.
apply evt_RZ_done.
eapply (descend_obj c kids KD HEADK) with (e2 := with_v e 0); [exact HP3 | exact ZC | exact Z3 | exact Hes2 | exact ST3 | exact ERR3 |].
intros ms' md' NP. apply K. eapply next_post_w; [exact FS3 | exact FRM3 | exact VM3 | exact HPR23 | exact NP].
-
destruct Hk as [Hv Ebs]. rewrite Hv. if_false. step. step. norm_w32. step. if_false. step. if_falsex. step. step. ub_align_auto. step. step. step.
apply evt_RZ_done.
replace (Z.of_nat nz + 1) with (Z.of_nat (S nz)) by lia.
assert (HPn : HEAPx A (XBS1 ++ LB) m2 md) by (eapply (heap_perm S4L HIx); [exact HP2 | subst XBS1 bs; hperm]).
eapply CONT; [exact HPn | | exact ST | | ].
+ exists t, tbl, size, es2, svs2. split; [exact Z2|].
intros kids1 kl Ek.
assert (Hj : (length kids1 < length esk1)%nat) by (rewrite Lk, Ek, length_app; cbn; lia).
destruct (nth_error esk1 (length kids1)) as [e'|] eqn:En; [| apply nth_error_None in En; lia].
exists e'. split; [subst es2; rewrite nth_error_app1 by lia; exact En|].
rewrite pv_of_spec, Ek, length_app. cbn [length]. rewrite Nat.add_1_r. cbn [pv_of].
rewrite Ees, nth_error_app1 by lia. rewrite En. reflexivity.
+ assumption.
+ intros ms' md' NP. apply K. eapply next_post_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | exact HPR2 | exact NP].
Qed.
End Loop.

End RC__1.

End G.
