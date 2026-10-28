(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QCcH Q0Ek Qsw7 QJjn QQLG QnCn Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply Lib.GwApply2 Lib.GwApplyJ QRjH QHnV QfLs QRUw QgoP Q6q3 Q8tj QVbl QSL3 QjDH QmZZ QKQo Q6WR Qvbw QRBl.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPIU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.Mq0.
Import UPIU.Mqe.
Import QQLG.Mq9.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
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

Definition pbufx := ltac:(let t := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.pbufx))) in let t := eval cbv beta delta [UPIU.Mqe.pbufx] in t in exact t).
Definition memappend_post_c := ltac:(let t := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post_c))) in let t := eval cbv beta delta [UPIU.Mqe.memappend_post_c] in t in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.pbufx))) in let t := gw_subst t x pbufx in exact t).
Definition memappend_tail := ltac:(let p := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_tail))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.pbufx))) in let T := gw_subst T x pbufx in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post_c))) in let T := gw_subst T x memappend_post_c in exact (p : T)).

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
F (Z_to_bv 64 (base + 0x124)) fc None m (seg_rom segs)) md) T.
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
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
step. if_falsex. step.
step. if_falsex.
step. step. step.
step. QRBl.ub_cmp_auto.
assert (src = []) as -> by (destruct src; [reflexivity | cbn in SRCL; lia]).
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
F (Z_to_bv 64 (base + 0xfc)) fc None m (seg_rom segs)) md) T.
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

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.Mq0.
Import UPIU.Mqe.
Import Mq6.
Import QQLG.Mq9.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

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

Definition pbufx := ltac:(let t := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.pbufx))) in let t := eval cbv beta delta [UPIU.Mqe.pbufx] in t in exact t).
Definition memappend_post := ltac:(let t := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post))) in let t := eval cbv beta delta [UPIU.Mqe.memappend_post] in t in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.pbufx))) in let t := gw_subst t x pbufx in exact t).
Definition memappend_post_c := ltac:(let t := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post_c))) in let t := eval cbv beta delta [UPIU.Mqe.memappend_post_c] in t in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.pbufx))) in let t := gw_subst t x pbufx in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post))) in let t := gw_subst t x memappend_post in exact t).
Definition src_cls := ltac:(let t := constr:(ltac:(gw_ctx2 (@Mq6.src_cls))) in let t := eval cbv beta delta [Mq6.src_cls] in t in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.pbufx))) in let t := gw_subst t x pbufx in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post))) in let t := gw_subst t x memappend_post in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post_c))) in let t := gw_subst t x memappend_post_c in exact t).
Definition memappend_post_c_weak := ltac:(let p := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post_c_weak))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.pbufx))) in let T := gw_subst T x pbufx in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post))) in let T := gw_subst T x memappend_post in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post_c))) in let T := gw_subst T x memappend_post_c in let x := constr:(ltac:(gw_ctx2 (@Mq6.src_cls))) in let T := gw_subst T x src_cls in let x := constr:(ltac:(gw_ctx2 (@Mq6.pbufx))) in let T := gw_subst T x pbufx in let x := constr:(ltac:(gw_ctx2 (@Mq6.memappend_post_c))) in let T := gw_subst T x memappend_post_c in exact (p : T)).
Definition memappend_tail := ltac:(let p := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_tail))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.pbufx))) in let T := gw_subst T x pbufx in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post))) in let T := gw_subst T x memappend_post in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post_c))) in let T := gw_subst T x memappend_post_c in let x := constr:(ltac:(gw_ctx2 (@Mq6.src_cls))) in let T := gw_subst T x src_cls in let x := constr:(ltac:(gw_ctx2 (@Mq6.pbufx))) in let T := gw_subst T x pbufx in let x := constr:(ltac:(gw_ctx2 (@Mq6.memappend_post_c))) in let T := gw_subst T x memappend_post_c in exact (p : T)).

Definition src_cls_transport := ltac:(let p := constr:(ltac:(gw_ctx2 (@Mq6.src_cls_transport))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.pbufx))) in let T := gw_subst T x pbufx in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post))) in let T := gw_subst T x memappend_post in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post_c))) in let T := gw_subst T x memappend_post_c in let x := constr:(ltac:(gw_ctx2 (@Mq6.src_cls))) in let T := gw_subst T x src_cls in let x := constr:(ltac:(gw_ctx2 (@Mq6.pbufx))) in let T := gw_subst T x pbufx in let x := constr:(ltac:(gw_ctx2 (@Mq6.memappend_post_c))) in let T := gw_subst T x memappend_post_c in exact (p : T)).
Definition memappend_rebase := ltac:(let p := constr:(ltac:(gw_ctx2 (@Mq6.memappend_rebase))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.pbufx))) in let T := gw_subst T x pbufx in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post))) in let T := gw_subst T x memappend_post in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post_c))) in let T := gw_subst T x memappend_post_c in let x := constr:(ltac:(gw_ctx2 (@Mq6.src_cls))) in let T := gw_subst T x src_cls in let x := constr:(ltac:(gw_ctx2 (@Mq6.pbufx))) in let T := gw_subst T x pbufx in let x := constr:(ltac:(gw_ctx2 (@Mq6.memappend_post_c))) in let T := gw_subst T x memappend_post_c in exact (p : T)).
Definition memappend_grow := ltac:(let p := constr:(ltac:(gw_ctx2 (@Mq6.memappend_grow))) in let T := type of p in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.pbufx))) in let T := gw_subst T x pbufx in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post))) in let T := gw_subst T x memappend_post in let x := constr:(ltac:(gw_ctx2 (@UPIU.Mqe.memappend_post_c))) in let T := gw_subst T x memappend_post_c in let x := constr:(ltac:(gw_ctx2 (@Mq6.src_cls))) in let T := gw_subst T x src_cls in let x := constr:(ltac:(gw_ctx2 (@Mq6.pbufx))) in let T := gw_subst T x pbufx in let x := constr:(ltac:(gw_ctx2 (@Mq6.memappend_post_c))) in let T := gw_subst T x memappend_post_c in exact (p : T)).

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

Section PbMemappendTop.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.

Definition printbuf_memappend_entry : Z := (base + 0x0).

#[using="w_14 w_47 w_70 joff_14 e_194bc LAY_gIMG_LO LAY_TPLO LAY_TPHI LAY_TPAL CODE BASE4 BASER D_14 E_14 LINK_14 CODE_e_194bc"] Lemma memappend_efbig :
forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(m0 m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB : list blk)
(pb buf bpos cap n lo : Z) (content src : list byte) (errv : word) (framejunk : list byte) (T : TSet),
HEAP S4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbuf_core segs m pb buf bpos cap content ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 ->
bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (bv_unsigned sp + -64) [CB 8 framejunk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells segs m (gTP + -164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
heap_pres S4L LB (bv_unsigned sp) m0 m ->
(forall ms' md', memappend_post_c HIx ra sp gp (Z_to_bv 64 gTP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md LB pb buf bpos cap content src n lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x58)) fc None m (seg_rom segs)) md) T.
Proof. clear - w_14 w_47 w_70 joff_14 e_194bc LAY_gIMG_LO LAY_TPLO LAY_TPHI LAY_TPAL CODE BASE4 BASER D_14 E_14 LINK_14 CODE_e_194bc segs base gTP HIx MEMMOVE. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until T. intros HP PB ST LO LOS HT FR ERR RA HPR K.
destruct PB as (Hbp & Hcp & Hlen & PBS & PBUF).
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as Hbimg. cbn [hl_img_lo hl_img_hi S4L] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hbhi.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); ((gTP + -164), (gTP + -160))] m) as MU.
apply rz_evt; [exact MOK|].
do 5 step. if_falsex. step. step. QRBl.ub_align_auto. step. stepz. step. step. do 9 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
apply evt_RZ_done. apply K. unfold memappend_post_c.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A, (2^64 - 1), (Z_to_bv 64 27), buf, cap end.
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

#[using="w_14 w_47 w_70 joff_14 joff_47 joff_70 e_194bc e_memmove LAY_gIMG_LO LAY_TPLO LAY_TPHI LAY_TPAL CODE BASE4 BASER D_14 E_14 D_47 E_47 D_70 E_70 LINK_14 LINK_47 LINK_70 CODE_e_194bc MEMMOVE"] Lemma memappend_cps_c :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (pb buf bpos cap b n lo : Z) (content src : list byte) (errv : word),
HEAP S4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbuf_core segs m pb buf bpos cap content ->
0 <= n < 2^31 ->
bytes_at segs m b src -> Z.of_nat (length src) = n -> src_cls LB n (bv_unsigned sp) b src ->
0 <= b -> b + n < 2^64 ->
(b + n <= buf \/ buf + cap <= b) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 pb -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 n ->
(forall ms' md', memappend_post_c HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB pb buf bpos cap content src n lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_memappend_entry) fc None m (seg_rom segs)) md) T.
Proof. clear - w_14 w_47 w_70 joff_14 joff_47 joff_70 e_194bc e_memmove LAY_gIMG_LO LAY_TPLO LAY_TPHI LAY_TPAL CODE BASE4 BASER D_14 E_14 D_47 E_47 D_70 E_70 LINK_14 LINK_47 LINK_70 CODE_e_194bc MEMMOVE segs gTP HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until errv. intros HP PB Hn SRC SRCL SCL Hb0 Hbn SEP ST LO LOS SPA HT ERR TP RA A0 A1 A2 K.
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
subst a0 a1 a2 tp.

assert (SRCk : True -> bytes_at segs m b src) by (intros _; exact SRC). clear SRC.
apply rz_evt; [exact MOK|]. unfold printbuf_memappend_entry.
carve_frame 64%nat ST.
do 8 step.

assert (HPRm : forall mx, munch [(bv_unsigned sp + -64, bv_unsigned sp)] m mx -> wmono segs m mx ->
heap_pres S4L LB (bv_unsigned sp) m mx).
{ intros mx MUx WMx. eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MUx | exact WMx |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb0; right; right; exact Hbb0 | clia |]. solve_clientW S4L HIx HP. }
assert (HPm : forall mx, munch [(bv_unsigned sp + -64, bv_unsigned sp)] m mx -> wmono segs m mx -> mem_inv segs mx ->
HEAP S4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) mx md).
{ intros mx MUx WMx MIx. eapply (heap_frame S4L HIx); [exact HP | | exact WMx | exact MIx].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MUx). solve_frameW_with HP. }
assert (SRCm : forall mx, heap_pres S4L LB (bv_unsigned sp) m mx -> mem_inv segs mx -> bytes_at segs mx b src).
{ intros mx HPRx MIx. eapply (src_cls_transport LB n (bv_unsigned sp) (bv_unsigned sp) LB);
[exact SCL | exact SRCL | exact (SRCk I) | exact HPRx | lia | intros x Hx; exact Hx | exact MIx | lia | lia]. }
step. if_falsex.
step. if_falsex. step. step.
ubsan_align Hal.
step. step. step. step. step.
step.
norm_w32. if_falsex.
step. step.
step.
norm_w32. if_falsex.
step.
destruct (Z.le_gt_cases n (2147483646 - bpos)) as [Hroom0|Hbig0].
2:{
if_falsex. apply evt_RZ_done.
eapply memappend_efbig; first [exact (HPm _ MU WM MI) | exact (HPRm _ MU WM) | eassumption | lia | idtac].
unfold pbuf_core. repeat (split; [first [lia | eassumption] |]). eassumption. }
if_truex.
step. step.
step.
norm_w32. if_falsex.
step. step.
step.
norm_w32. if_falsex.
step. step.
step.
norm_w32.
destruct (Z.lt_ge_cases (bpos + n + 1) cap) as [Hfit|Hgrow].
-
if_falsex. step. step.
apply evt_RZ_done.
eapply (memappend_tail HIx MEMMOVE ra sp gp (Z_to_bv 64 gTP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo pb buf bpos cap n content T
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md A buf bpos cap b content src errv _);
first [ reflexivity | exact (HPm _ MU WM MI) | exact (HPRm _ MU WM) | apply model_vm_only_refl | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- bytes_at _ _ _ _ => apply SRCm; [exact (HPRm _ MU WM) | exact MI]
| |- _ => unfold_consts; lia
end.
- if_truex. step. step.
destruct (Z.lt_ge_cases (bpos + n) cap) as [Heq1|Hge1].
+
if_truex. apply evt_RZ_done.
eapply (memappend_rebase HIx MEMMOVE ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo pb n T buf bpos cap content
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md A buf cap buf bpos cap b content src errv _);
first [ reflexivity | exact (HPm _ MU WM MI) | exact (HPRm _ MU WM) | apply model_vm_only_refl | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- bytes_at _ _ _ _ => apply SRCm; [exact (HPRm _ MU WM) | exact MI]
| |- _ => unfold_consts; lia
end.
+ if_falsex. step. step. step.
destruct (Z.lt_ge_cases (bpos + n) 2147483639) as [Hok2|Hbig2].
2:{ if_truex. apply evt_RZ_done.
eapply memappend_efbig; first [exact (HPm _ MU WM MI) | exact (HPRm _ MU WM) | eassumption | lia | idtac].
unfold pbuf_core. repeat (split; [first [lia | eassumption] |]). eassumption. }
if_falsex. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
assert (GROW : forall (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (ns : Z),
bpos + n + 1 <= ns -> cap <= ns < 2^31 ->
evt segs (RZ segs md T)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 gTP) x5 x6 x7 (Z_to_bv 64 buf) (Z_to_bv 64 ns)
(Z_to_bv 64 pb) (Z_to_bv 64 b) (Z_to_bv 64 n) x13 x14 x15 x16 x17 (Z_to_bv 64 cap) (Z_to_bv 64 b) (Z_to_bv 64 n) (Z_to_bv 64 pb)
s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 (base + 0xfc)) fc None mcur (seg_rom segs)))
end.
{ intros until ns. intros Hns1 Hns2. apply evt_RZ_done.
eapply (memappend_grow HIx MEMMOVE ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo pb n T
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md A buf bpos cap ns b content src errv _);
first [ reflexivity | exact (HPm _ MU WM MI) | exact (HPRm _ MU WM) | apply model_vm_only_refl | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- bytes_at _ _ _ _ => apply SRCm; [exact (HPRm _ MU WM) | exact MI]
| |- src_cls _ _ _ _ _ => exact SCL
| |- _ => unfold_consts; lia
end. }
destruct (Z.lt_ge_cases cap 1073741824) as [Hsmall|Hlarge].
*
if_truex. step. step. step.
if_falsex. step. step.
rewrite (unsigned_lit cap) by lia. rewrite (Z.shiftl_mul_pow2 cap 1) by lia. change (2^1) with 2.
rewrite (swrap32_id (cap * 2)) by lia. norm_w32.
step.
destruct (Z.lt_ge_cases (bpos + n + 9) (cap * 2)) as [Hlt3|Hge3].
-- if_truex. step. step. step. apply (GROW _ _ _ _ _ _ _ _ _ _ _ _ (cap * 2)); lia.
-- if_falsex. step. step. step. step. apply (GROW _ _ _ _ _ _ _ _ _ _ _ _ (bpos + n + 9)); lia.
*
if_falsex. step. step. step. step. norm_w32. step.
apply (GROW _ _ _ _ _ _ _ _ _ _ _ _ (bpos + n + 9)); lia.
Qed.

#[using="w_14 w_47 w_70 joff_14 joff_47 joff_70 e_194bc e_memmove LAY_gIMG_LO LAY_TPLO LAY_TPHI LAY_TPAL CODE BASE4 BASER D_14 E_14 D_47 E_47 D_70 E_70 LINK_14 LINK_47 LINK_70 CODE_e_194bc MEMMOVE"] Lemma memappend_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (pb buf bpos cap b n lo : Z) (content src : list byte) (errv : word),
HEAP S4L HIx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbuf_core segs m pb buf bpos cap content ->
0 <= n < 2^31 ->
bytes_at segs m b src -> Z.of_nat (length src) = n -> src_cls LB n (bv_unsigned sp) b src ->
0 <= b -> b + n < 2^64 ->
(b + n <= buf \/ buf + cap <= b) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 pb -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 n ->
(forall ms' md', memappend_post HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB pb buf bpos cap content n lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_memappend_entry) fc None m (seg_rom segs)) md) T.
Proof. clear - w_14 w_47 w_70 joff_14 joff_47 joff_70 e_194bc e_memmove LAY_gIMG_LO LAY_TPLO LAY_TPHI LAY_TPAL CODE BASE4 BASER D_14 E_14 D_47 E_47 D_70 E_70 LINK_14 LINK_47 LINK_70 CODE_e_194bc MEMMOVE segs gTP HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_.
intros until errv. intros HP PB Hn SRC SRCL SCL Hb0 Hbn SEP ST LO LOS SPA HT ERR TP RA A0 A1 A2 K.
eapply memappend_cps_c; [exact HP | exact PB | exact Hn | exact SRC | exact SRCL | exact SCL | exact Hb0 | exact Hbn | exact SEP
| exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact RA | exact A0 | exact A1 | exact A2 |].
intros ms' md' P. apply K. eapply memappend_post_c_weak. exact P.
Qed.
End PbMemappendTop.

End RC__1.

End G.
End Mq5.
