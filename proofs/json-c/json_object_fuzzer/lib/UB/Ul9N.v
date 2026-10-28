(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.CodeAt Lib.StepGen Lib.GwInst Lib.GwEq Lib.GwEqH Lib.GwApply Lib.GwApply2 UGwP UC8c QCcH Q0Ek UPZI UhI1 UeL5.
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B QRjH QHnV QfLs Qsw7 QJjn QRUw Q8tj QSL3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULLZ UAIk UIX4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3 Q3CA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import UEQM.
Import Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import UC8c.Mq0.
Import Qsw7 QJjn QRUw Q8tj.
Import QSL3.
Import UhI1 UeL5 ULLZ UAIk.
Import UIX4.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
Import Q6q3.
Import Q3CA.

Module GwI.
Definition segs := rsegs.
Definition base := 0x28ab4%Z.
Definition GGOT4 := Eval cbv in GGOT4.
Definition GHASH4 := Eval cbv in GHASH4.
Definition GVDSO4 := Eval cbv in GVDSO4.
Definition JG_CGT_P := Eval cbv in UPZI.Mq0.JG_CGT_P.
Lemma BASE4 : (0x28ab4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x28ab4 /\ 0x28ab4 + 288 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Notation gw_RC := Q6q3.RunConsts (only parsing).
Local Ltac gw_lay t := let v := eval cbv beta iota delta [UC8c.Mq0.S4L QCcH.hl_malloc QCcH.hl_free QCcH.hl_calloc QCcH.hl_realloc QCcH.hl_malloc2 QCcH.hl_free2 QCcH.hl_tp QCcH.hl_got_guard QCcH.hl_guard QCcH.hl_auxv QCcH.hl_libc QCcH.hl_img_lo QCcH.hl_img_hi QCcH.hl_consts] in t in lazymatch v with (fun _ => ?n) => exact n end.
Local Ltac gw_hex k := let v := eval cbv beta iota delta [UC8c.Mq0.S4L QCcH.hl_consts] in (fun RC__ : gw_RC => @QCcH.hl_consts RC__ (@UC8c.Mq0.S4L RC__)) in
lazymatch v with (fun _ => cons (pair ?a (?f1 (?f2 ?b))) (cons (pair _ (?f3 (?f4 ?c))) nil)) => lazymatch k with 0%nat => exact a | 1%nat => exact b | _ => exact c end end.
Definition e_malloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_free : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_calloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_calloc RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_realloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_realloc RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_malloc2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc2 RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_free2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free2 RC__ (@UC8c.Mq0.S4L RC__))).
Definition gTP : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_tp RC__ (@UC8c.Mq0.S4L RC__))).
Definition gGOTG : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_got_guard RC__ (@UC8c.Mq0.S4L RC__))).
Definition gGUARD : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_guard RC__ (@UC8c.Mq0.S4L RC__))).
Definition gAUXV : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_auxv RC__ (@UC8c.Mq0.S4L RC__))).
Definition gLIBC : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_libc RC__ (@UC8c.Mq0.S4L RC__))).
Definition gIMG_LO : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_lo RC__ (@UC8c.Mq0.S4L RC__))).
Definition gIMG_HI : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_hi RC__ (@UC8c.Mq0.S4L RC__))).
Definition gHEXGOT : Z := ltac:(gw_hex 0%nat).  Definition gHEXPTR : Z := ltac:(gw_hex 1%nat).  Definition gHEXCHARS : Z := ltac:(gw_hex 2%nat).
Definition gVOL := UC8c.Mq0.s4_volatile.  Definition gCS := UC8c.Mq0.s4_client_static.
Definition gH1 := fun RC__ : gw_RC => @QCcH.hl_static_in_img RC__ (@UC8c.Mq0.S4L RC__).
Definition gH2 := fun RC__ : gw_RC => @QCcH.hl_img_range RC__ (@UC8c.Mq0.S4L RC__).
Definition gH3 := fun RC__ : gw_RC => @QCcH.hl_scratch_in_img RC__ (@UC8c.Mq0.S4L RC__).
Definition gH4 := fun RC__ : gw_RC => @QCcH.hl_scratch_not_static RC__ (@UC8c.Mq0.S4L RC__).
Definition gH5 := fun RC__ : gw_RC => @QCcH.hl_consts_ok RC__ (@UC8c.Mq0.S4L RC__).
Definition e_fn_obj_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_obj_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_obj_to_json_string UC8c.Mq0.S4F).
Definition e_fn_arr_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_arr_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_arr_to_json_string UC8c.Mq0.S4F).
Definition e_fn_bool_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_bool_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_bool_to_json_string UC8c.Mq0.S4F).
Definition e_fn_dbl_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_dbl_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_dbl_to_json_string UC8c.Mq0.S4F).
Definition e_fn_int_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_int_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_int_to_json_string UC8c.Mq0.S4F).
Definition e_fn_str_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_str_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_str_to_json_string UC8c.Mq0.S4F).
Definition e_fn_ud_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_ud_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_ud_to_json_string UC8c.Mq0.S4F).
Definition e_fn_free_userdata := Eval cbv beta iota delta [Q0Ek.fn_free_userdata UC8c.Mq0.S4F] in (Q0Ek.fn_free_userdata UC8c.Mq0.S4F).
Definition e_fn_lh_entry_free := Eval cbv beta iota delta [Q0Ek.fn_lh_entry_free UC8c.Mq0.S4F] in (Q0Ek.fn_lh_entry_free UC8c.Mq0.S4F).
Definition e_fn_lh_char_hash := Eval cbv beta iota delta [Q0Ek.fn_lh_char_hash UC8c.Mq0.S4F] in (Q0Ek.fn_lh_char_hash UC8c.Mq0.S4F).
Definition e_fn_lh_char_equal := Eval cbv beta iota delta [Q0Ek.fn_lh_char_equal UC8c.Mq0.S4F] in (Q0Ek.fn_lh_char_equal UC8c.Mq0.S4F).
Definition e_fn_arr_entry_free := Eval cbv beta iota delta [Q0Ek.fn_arr_entry_free UC8c.Mq0.S4F] in (Q0Ek.fn_arr_entry_free UC8c.Mq0.S4F).
Definition gRDATA_LO : Z := ltac:(let v := eval cbv delta [s4_client_static] in s4_client_static in lazymatch v with (fun a => (?lo <= a < _) /\ _) => exact lo end).
Definition lh_glob_client := @UhI1.lh_glob_client.
Definition lh_entry_free_cps := @UeL5.lh_entry_free_cps.
Lemma LAY_gIMG_LO : ltac2:(GwEq.gw_fact_ty 'segs '(@UGwP.Mq0.gw_all) @LAY_gIMG_LO). Proof. GwApply.gw_side. Qed.
Lemma LAY_TPLO : ltac2:(GwEq.gw_fact_ty 'segs '(@UGwP.Mq0.gw_all) @LAY_TPLO). Proof. GwApply.gw_side. Qed.
Lemma LAY_TPHI : ltac2:(GwEq.gw_fact_ty 'segs '(@UGwP.Mq0.gw_all) @LAY_TPHI). Proof. GwApply.gw_side. Qed.
Lemma LAY_GGOT4_GHASH4 : ltac2:(GwEq.gw_fact_ty 'segs '(@UGwP.Mq0.gw_all) @LAY_GGOT4_GHASH4). Proof. GwApply.gw_side. Qed.
Lemma LAY_GHASH4_GVDSO4 : ltac2:(GwEq.gw_fact_ty 'segs '(@UGwP.Mq0.gw_all) @LAY_GHASH4_GVDSO4). Proof. GwApply.gw_side. Qed.
Lemma LAY_IMG_GGOT4 : ltac2:(GwEq.gw_fact_ty 'segs '(@UGwP.Mq0.gw_all) @LAY_IMG_GGOT4). Proof. GwApply.gw_side. Qed.
Lemma LAY_GVDSO4_IMG : ltac2:(GwEq.gw_fact_ty 'segs '(@UGwP.Mq0.gw_all) @LAY_GVDSO4_IMG). Proof. GwApply.gw_side. Qed.
End GwI.
Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2.gw_side_extra ::= intros; unfold s4_client_static, s4_volatile; lia. Local Ltac mkr__gw_side_extra_0 := intros; unfold s4_client_static, s4_volatile; lia.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Local Ltac rpc := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
Local Ltac ultf := lazymatch goal with |- evt _ _ (MS _ _ (if bv_ltu ?a ?b then _ else _) _ _ _ _) => replace (bv_ltu a b) with false by (symmetry; unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_ge; lia); cbv iota end.
Local Ltac eqf := lazymatch goal with |- evt _ _ (MS _ _ (if bv_eqb ?a ?b then _ else _) _ _ _ _) => replace (bv_eqb a b) with false by (symmetry; unfold ent_addr; solve_condx); cbv iota end.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition lh_delete_tail_entry : Z := 0x28ab4.

Definition del_slot (s : slotv) : slotv := SV LH_FREEDv (sv_kc s) (sv_pad s) 0 0 0.
Definition clr_nx (s : slotv) : slotv := SV (sv_k s) (sv_kc s) (sv_pad s) (sv_v s) 0 (sv_pv s).

#[using="Type"] Lemma snoc_inv : forall (l : list lent), l = [] \/ exists l' x, l = l' ++ [x].
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UGwP.Mq0.snoc_inv) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UGwP.Mq0.snoc_inv)]. Qed.

#[using="Type"] Lemma firstn_snoc_le : forall (A : Type) (l : list A) x n, (n <= length l)%nat -> firstn n (l ++ [x]) = firstn n l.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UGwP.Mq0.firstn_snoc_le) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UGwP.Mq0.firstn_snoc_le)]. Qed.

#[using="Type"] Lemma pv_of_snoc2 : forall tbl es1 el e, pv_of tbl ((es1 ++ [el]) ++ [e]) (length (es1 ++ [el])) = ent_addr tbl (le_ix el).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UGwP.Mq0.pv_of_snoc2) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UGwP.Mq0.pv_of_snoc2)]. Qed.
#[using="Type"] Lemma perm_key_front : forall t tbl size es0 e LB,
Permutation (lh_blocks t tbl size (es0 ++ [e]) ++ LB) (kblk e :: lh_blocks t tbl size es0 ++ LB).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UGwP.Mq0.perm_key_front) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UGwP.Mq0.perm_key_front)]. Qed.

Section Unsnoc.
Variables (tbl : Z) (es0 : list lent) (e : lent) (svs : list slotv) (se : slotv).
Hypothesis LINK : lh_link tbl (es0 ++ [e]) svs.
Hypothesis Ese : nth_error svs (le_ix e) = Some se.

#[using="LINK Ese"] Lemma lh_link_unsnoc_nil : es0 = [] -> lh_link tbl [] (upd svs (le_ix e) (del_slot se)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UGwP.Mq0.lh_link_unsnoc_nil) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UGwP.Mq0.lh_link_unsnoc_nil)]. Qed.

#[using="LINK Ese"] Lemma lh_link_unsnoc_cons : forall es1 el sl,
es0 = es1 ++ [el] -> nth_error svs (le_ix el) = Some sl ->
lh_link tbl es0 (upd (upd svs (le_ix e) (del_slot se)) (le_ix el) (clr_nx sl)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@UGwP.Mq0.lh_link_unsnoc_cons) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@UGwP.Mq0.lh_link_unsnoc_cons)]. Qed.
End Unsnoc.

Lemma sltiu_xor_ne : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> a <> b -> v_sltiu (Z_to_bv 64 (Z.lxor a b)) 1 = Z_to_bv 64 0.
Proof.
intros a b Ha Hb NE. rewrite v_sltiu_b2z. rewrite unsigned_lit by (apply zr_lxor; unfold inr64; lia).
assert (X0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
assert (X1 : Z.lxor a b <> 0) by (intro X; exact (NE (proj1 (zb_lxor_eq0 a b) X))).
replace (bv_wrap 64 1) with 1 by reflexivity.
replace (Z.lxor a b <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Section LhDelete.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation lh_glob4 := (lh_glob rsegs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).

Lemma lh_writes_pres : forall A t tbl size es LB m md m' W SP,
HEAPx A (lh_blocks t tbl size es ++ LB) m md -> munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP) \/ (t <= fst iv /\ snd iv <= t + 56) \/ (tbl <= fst iv /\ snd iv <= tbl + 40 * size)) W ->
alloc_ceiling <= SP ->
heap_pres S4L LB SP m m'.
Proof.
intros A t tbl size es LB m md m' W SP HP MU WM HW HSP.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
eapply (heap_pres_of_munch S4L LB SP); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; exact Hb | exact HSP |].
clear - HW ND. induction W as [|[a b] W IH]; [apply Forall_nil|].
apply Forall_cons_iff in HW as [H1 HW]. apply Forall_cons; [| apply IH; exact HW]. cbn [fst snd] in *.
destruct H1 as [H1 | [H1 | H1]].
- left. exact H1.
- right; left. exists t, 56. split; [left; reflexivity|]. split; [| lia].
intros IN. eapply (nodup_prefix_suffix (lh_blocks t tbl size es) LB t 56 56); [exact ND | left; reflexivity | exact IN].
- right; left. exists tbl, (40 * size). split; [right; left; reflexivity|]. split; [| lia].
intros IN. eapply (nodup_prefix_suffix (lh_blocks t tbl size es) LB tbl (40 * size) (40 * size)); [exact ND | right; left; reflexivity | exact IN].
Qed.

Section DelLoop.
Variables (sp gp : word) (s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo t tbl size : Z) (jf : nat) (ef : lent) (T : TSet).
Variables (rac s0c s1c s2c s3c : word) (junk8 : list byte).
Variable errv : word.

Definition del_frame (m : word -> option byte) : Prop :=
rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk8; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

Definition del_exit (esf : list lent) : Prop :=
forall (x1 t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (svsf : list slotv),
HEAPx A (lh_blocks t tbl size esf ++ LB) m md ->
lh_open rsegs S4F m t tbl size esf svsf ->
stk rsegs m lo (bv_unsigned sp + -48) -> del_frame m ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 s0 s1
(Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x28b60) fc None m (seg_rom rsegs)) md) T.

Lemma lh_del_loop :
forall (d : nat) (es0 : list lent) (e : lent) (svs : list slotv)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : Model) (A : AS S4L HIx),
(d = length es0 - jf)%nat -> (jf <= length es0)%nat -> nth_error (es0 ++ [e]) jf = Some ef ->
HEAPx A (lh_blocks t tbl size (es0 ++ [e]) ++ LB) m md ->
lh_open rsegs S4F m t tbl size (es0 ++ [e]) svs ->
(forall j x, (jf <= j)%nat -> nth_error (es0 ++ [e]) j = Some x -> le_v x = 0) ->
stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
del_frame m -> rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m -> del_exit (firstn jf es0) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 (ent_addr tbl (le_ix ef))) (Z_to_bv 64 t)
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ent_addr tbl (le_ix e))) x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x28af0) fc None m (seg_rom rsegs)) md) T.
Proof.
induction d as [|d IH]; intros until A; intros Hd Hjf Hef HP OPEN VZ ST LO LOS SPA HT FR ERR VM0 HPR KX.
all: pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen); unfold lh_hdr, lh_hdrf in HDR.
all: rewrite UH1t.tl_of_app in HDR.
all: pose proof LINK as (LK1 & LK2 & LK3 & LK4).
all: assert (Ee : nth_error (es0 ++ [e]) (length es0) = Some e) by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
all: destruct (LK1 (length es0) e Ee) as (se & Ese & Ek & Ekc & Ev & Enx & Epv).
all: pose proof (SL (le_ix e) se Ese) as C; unfold slot_cells in C; rewrite Ek, Ekc, Ev, Enx, Epv in C.
all: rewrite (VZ (length es0) e ltac:(lia) Ee) in C; rewrite (UH1t.nx_of_app_new tbl es0 e (length es0) eq_refl) in C.
all: pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Ese; discriminate)) as Hix.
all: destruct (LK4 e ltac:(apply in_or_app; right; left; reflexivity)) as (Hk0 & HkF & Hkn31 & Hv).
all: unfold del_frame in FR; unfold_consts; word_range sp SPR.
all: pose proof (lf_thr_lt size Hsz) as Hlt; pose proof (lf_size_range size Hsz) as HSR.
all: assert (LEN : Z.of_nat (length (es0 ++ [e])) = Z.of_nat (length es0) + 1) by (rewrite length_app; cbn; lia); rewrite LEN in HDR, Hcnt.
all: pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK; pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI; cbn [hl_segs S4L] in MI.
all: destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
all: cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg; unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
all: destruct (KF e ltac:(apply in_or_app; right; left; reflexivity)) as (Hkn0 & _ & Hkhi & Hkimg & DKt & DKb); cbn [hl_img_lo hl_img_hi S4L] in Hkimg.
all: stash Hkimg; stash DKt; stash DKb; stash Htimg.
all: assert (IXNE : forall j1 j2 y1 y2, nth_error (es0 ++ [e]) j1 = Some y1 -> nth_error (es0 ++ [e]) j2 = Some y2 -> j1 <> j2 -> le_ix y1 <> le_ix y2) by
(intros j1 j2 y1 y2 H1 H2 NE X; apply NE; eapply (proj1 (NoDup_nth_error _) LK3 j1 j2);
[ rewrite length_map; apply (proj1 (nth_error_Some _ j1)); rewrite H1; discriminate
| erewrite nth_error_map, H1, nth_error_map, H2; cbn; rewrite X; reflexivity ]).
all: destruct (LK1 jf ef Hef) as (sf & Esf & _); pose proof (proj1 (nth_error_Some svs (le_ix ef)) ltac:(rewrite Esf; discriminate)) as Hixf; clear sf Esf.
all: assert (HPk : HEAPx A ((le_k e, le_kn e) :: (t, 56) :: (tbl, 40 * size) :: (map kblk es0 ++ LB)) m md) by (eapply heap_perm; [exact HP | apply perm_key_front]).
all: remember (ent_addr tbl (le_ix e)) as B eqn:EB.
all: assert (HB : B = tbl + 40 * Z.of_nat (le_ix e)) by (rewrite EB; reflexivity).
all: assert (HB0 : 0 < B < 2^64) by lia.
all: assert (HB8 : B mod 8 = 0) by (rewrite EB; apply UeL5.ent_addr_mod8; exact Hbal).
all: pose proof (wmono_refl rsegs m) as WM; pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (t, t + 56)] m) as MU.
all: apply rz_evt; [exact MOK|].
all: do 5 bstep.
all: carve_frame 32%nat ST.
all: do 6 bstepz.
all: rewrite (unsigned_lit B), (unsigned_lit tbl) by lia; if_falsex.
all: bstepz.
all: try replace (tbl + (B - tbl)) with B by lia.
all: do 3 bstepz.
all: replace (bv_ltu (Z_to_bv 64 (-3)) (Z_to_bv 64 (le_k e))) with false by
(symmetry; unfold bv_ltu; rewrite (unsigned_lit (le_k e)) by (unfold LH_FREEDv in *; lia);
replace (bv_unsigned (Z_to_bv 64 (-3))) with 18446744073709551613 by (vm_compute; reflexivity);
apply Z.ltb_ge; unfold LH_FREEDv in *; lia).
all: cbn [negb]; cbv iota.
all: step; norm_sx32; step; step.
all: rewrite (unsigned_lit (Z.of_nat (length es0) + 1)) by lia; rewrite (swrap32_id (Z.of_nat (length es0) + 1 + -1)) by lia; if_falsex.
all: do 3 bstepz.
all: replace (fn_lh_entry_free S4F) with 0x25470 by reflexivity; if_false.
all: do 3 bstepz.
all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SLx : lh_slots rsegs mx tbl svs) by
(eapply lh_slots_frame; [exact SL | exact MU | exact WM |]; intros i Hi; rewrite <- Hlen in Hbhi, SEP;
apply Forall_cons; [cbn; unfold ent_addr; lia | apply Forall_cons; [cbn; unfold ent_addr; lia | apply Forall_nil]]);
assert (KEYSx : lh_keys rsegs mx es0) by
(eapply lh_keys_frame; [unfold lh_keys in KEYS |- *; apply Forall_app in KEYS as [K0 _]; exact K0 | exact MU | exact WM |];
intros y Hy; destruct (KF y ltac:(apply in_or_app; left; exact Hy)) as (? & ? & ? & HyI & ? & ?); clear HyI;
apply Forall_cons; [cbn; lia | apply Forall_cons; [cbn; lia | apply Forall_nil]]);
assert (HPRx : heap_pres S4L LB (bv_unsigned sp) m mx) by
(eapply (lh_writes_pres A t tbl size (es0 ++ [e]) LB m md mx); [exact HP | exact MU | exact WM | | lia];
apply Forall_cons; [cbn; left; lia | apply Forall_cons; [cbn; right; left; lia | apply Forall_nil]])
end.
all: apply evt_RZ_done;
eapply (lh_entry_free_cps HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ md T A (lh_blocks t tbl size es0 ++ LB)
B (le_k e) (le_kn e) (sv_pad se) 0 _ lo errv);
[ heap_now S4L HIx HPk MU WM MI | exact C | ..].
all: try (unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia).
all: try (rewrite unsigned_lit by lia; lia).
all: try (destruct Hbimg; [left; lia | right; cbn; lia]).
all: try assumption.
all: try (rewrite unsigned_lit by lia; assumption).
all: try (rewrite unsigned_lit by lia; unfold hi_top in *; lia).
all: try reflexivity.
all: try (cbn [hl_tp S4L]; reflexivity).
all: intros ms2 md2 (mq & A2 & r2 & RS & VM2 & ST2 & HPR2 & ERR2 & HP2).
all: destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ->); cbn [hl_segs S4L] in *.
all: clear ERR; stash ERR2.
all: rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST2, HPR2 by lia.
all: apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]; cbn [hl_segs S4L] in FR.
all: apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR0; [| left; cbn; lia]; cbn [hl_segs S4L] in FR0.
all: apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]; cbn [hl_segs S4L] in HDR; fold (es0 ++ [e]) in HDR.
all: apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in C; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]]; cbn [hl_segs S4L] in C.
all: pose proof (lh_slots_pres S4L _ _ _ _ tbl svs size HPR2 ltac:(right; left; reflexivity) Hlen SLx) as SL2; cbn [hl_segs S4L] in SL2.
all: pose proof (lh_keys_pres S4L _ _ _ _ es0 HPR2 ltac:(intros y Hy; apply in_or_app; left; unfold lh_blocks; right; right; apply in_map_iff; exists y; split; [reflexivity | exact Hy]) KEYSx) as KEYS2; cbn [hl_segs S4L] in KEYS2.
all: assert (HPR' : heap_pres S4L LB (bv_unsigned sp) m0 mq) by
(eapply heap_pres_trans; [exact HPR|]; eapply heap_pres_trans; [exact HPRx|]; eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; apply in_or_app; right; exact Hb]).
all: clear MU WM MI SLx KEYSx HPRx HPk.
all: pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2; pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI; cbn [hl_segs S4L] in MI.
all: pose proof (wmono_refl rsegs mq) as WM.
all: destruct (snoc_inv es0) as [E0 | (es1 & el & E0)]; [| destruct (LK1 (length es1) el ltac:(rewrite E0, <- app_assoc; cbn; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity)) as (sl & Esl & Elk & Elkc & Elv & Elnx & Elpv)].
3:{ exfalso. subst es0. cbn in Hd. lia. }
2,3: (pose proof (SL2 (le_ix el) sl Esl) as Cl; unfold slot_cells in Cl; rewrite Elk, Elkc, Elv, Elnx, Elpv in Cl;
pose proof (proj1 (nth_error_Some svs (le_ix el)) ltac:(rewrite Esl; discriminate)) as Hixl;
assert (L0 : length es0 = S (length es1)) by (rewrite E0, length_app; cbn; lia);
assert (NXl : nx_of tbl (es0 ++ [e]) (length es1) = B) by (unfold nx_of; rewrite <- L0, Ee, EB; reflexivity); rewrite NXl in Cl;
assert (PV : pv_of tbl (es0 ++ [e]) (length es0) = ent_addr tbl (le_ix el)) by (rewrite E0; apply pv_of_snoc2); rewrite PV in C;
assert (NEl : le_ix el <> le_ix e) by
(eapply (IXNE (length es1) (length es0)); [rewrite E0, <- app_assoc; cbn; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | exact Ee | lia]);
destruct (nth_error es0 0) as [x0|] eqn:Ex0; [| exfalso; apply nth_error_None in Ex0; lia];
assert (HD0 : hd_of tbl (es0 ++ [e]) = ent_addr tbl (le_ix x0)) by (rewrite hd_of_nth, nth_error_app1, Ex0 by lia; reflexivity);
assert (NE0 : le_ix x0 <> le_ix e) by (eapply (IXNE 0%nat (length es0)); [rewrite nth_error_app1 by lia; exact Ex0 | exact Ee | lia]);
destruct (LK1 0%nat x0 ltac:(rewrite nth_error_app1 by lia; exact Ex0)) as (sx0 & Esx0 & _);
pose proof (proj1 (nth_error_Some svs (le_ix x0)) ltac:(rewrite Esx0; discriminate)) as Hix0;
rewrite HD0 in HDR;
destruct (KF el ltac:(rewrite E0; apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as (_ & Hlklo & Hlkhi & _ & DKlt & DKlb); stash DKlt; stash DKlb).
1: replace (pv_of tbl (es0 ++ [e]) (length es0)) with 0 in C by (rewrite E0; reflexivity);
replace (hd_of tbl (es0 ++ [e])) with B in HDR by (rewrite E0, EB; reflexivity);
rewrite E0 in Hef, Hjf; cbn [app] in Hef; cbn in Hjf; assert (Hjf0 : jf = 0%nat) by lia;
rewrite Hjf0 in Hef; cbn in Hef; injection Hef as Eef.
2,3: remember (pv_of tbl (es0 ++ [e]) (length es1)) as PVl eqn:EPVl.
2,3: (remember (ent_addr tbl (le_ix el)) as Bl eqn:EBl; assert (HBl : Bl = tbl + 40 * Z.of_nat (le_ix el)) by (rewrite EBl; reflexivity);
assert (HBl0 : 0 < Bl < 2^64) by lia; assert (HBl8 : Bl mod 8 = 0) by (rewrite EBl; apply UeL5.ent_addr_mod8; exact Hbal)).
2,3: fold (es0 ++ [e]); rewrite PV.
1: pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (t, t + 56); (B, B + 40)] mq) as MU.
2,3: pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (t, t + 56); (B, B + 40); (Bl, Bl + 40)] mq) as MU.
all: pose proof HP2 as HP2n; change (lh_blocks t tbl size es0 ++ LB) with ((t, 56) :: (tbl, 40 * size) :: (map kblk es0 ++ LB)) in HP2n.
all: apply rz_evt; [exact MOK2|].
all: rpc.
all: do 2 bstepz.
all: step. all: step.
all: ultf.
all: do 4 step.
all: ub_cmp_auto_c.
all: step.
all: if_falsex.
all: do 3 step.
all: replace (tbl + (B - tbl)) with B by lia; ub_align_auto.
all: stepz. all: step.
all: if_falsex.
all: try replace (B - tbl + tbl) with B by lia; try replace (tbl + (B - tbl)) with B by lia.
all: do 4 stepz.
all: replace (bv_eqb (Z_to_bv 64 B) (Z_to_bv 64 B)) with true by (symmetry; apply bv_eqb_refl); cbn [negb]; cbv iota.
all: do 2 stepz.
1: replace (bv_eqb (Z_to_bv 64 B) (Z_to_bv 64 B)) with true by (symmetry; apply bv_eqb_refl); cbv iota.
2,3: eqf.
all: do 2 stepz.
2,3: eqf.
2,3: stepz.
2,3: replace (bv_eqb (Z_to_bv 64 B) (Z_to_bv 64 B)) with true by (symmetry; apply bv_eqb_refl); cbv iota.
2,3: do 2 stepz.
2,3: if_falsex.
2,3: do 2 stepz.
2,3: ub_align_auto.
2,3: do 3 stepz.
all: do 3 stepz.
all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
all: match goal with H : mem_inv rsegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into MIF end.
all: assert (HPF : HEAPx A2 (lh_blocks t tbl size es0 ++ LB) mF md2) by (heap_now S4L HIx HP2n MU WM MIF).
all: assert (HPRF : heap_pres S4L LB (bv_unsigned sp) m0 mF) by
(eapply heap_pres_trans; [exact HPR'|]; eapply (lh_writes_pres A2 t tbl size es0 LB mq md2 mF); [exact HP2 | exact MU | exact WM | | lia];
repeat (apply Forall_cons; [cbn; first [left; lia | right; left; lia | right; right; lia]|]); apply Forall_nil).
all: assert (KEYSF : lh_keys rsegs mF es0) by
(eapply lh_keys_frame; [exact KEYS2 | exact MU | exact WM |];
intros y Hy; destruct (KF y ltac:(apply in_or_app; left; exact Hy)) as (? & ? & ? & HyI & ? & ?); clear HyI;
repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil).
all: assert (C' : rw_cells rsegs mF (ent_addr tbl (le_ix e)) (slot_cells (del_slot se))) by
(unfold slot_cells, del_slot; cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]; rewrite Ekc, <- EB; exact C).
2,3: assert (Cl' : rw_cells rsegs mF (ent_addr tbl (le_ix el)) (slot_cells (clr_nx sl))) by
(unfold slot_cells, clr_nx; cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]; rewrite Elk, Elkc, Elv, Elpv, <- EBl; try rewrite <- EPVl; exact Cl).
1: assert (SLF : lh_slots rsegs mF tbl (upd svs (le_ix e) (del_slot se))) by
(eapply (lh_slots_write1 rsegs mq mF tbl svs _ (le_ix e) (del_slot se)); [exact SL2 | exact Hix | exact MU | exact WM | | exact C'];
intros i NE Hi; unfold ivs_miss_slot; rewrite <- Hlen in Hbhi, SEP;
repeat (apply Forall_cons; [cbn; unfold ent_addr; lia|]); apply Forall_nil).
2,3: assert (SLF : lh_slots rsegs mF tbl (upd (upd svs (le_ix e) (del_slot se)) (le_ix el) (clr_nx sl))) by
(eapply (lh_slots_write2 rsegs mq mF tbl svs _ (le_ix e) (del_slot se) (le_ix el) (clr_nx sl));
[exact SL2 | exact Hix | exact Hixl | exact (not_eq_sym NEl) | exact MU | exact WM | | exact C' | exact Cl'];
intros i NE1 NE2 Hi; unfold ivs_miss_slot; rewrite <- Hlen in Hbhi, SEP;
repeat (apply Forall_cons; [cbn; unfold ent_addr; lia|]); apply Forall_nil).
1: assert (OPENF : lh_open rsegs S4F mF t tbl size [] (upd svs (le_ix e) (del_slot se))) by
(split; [unfold lh_hdrf; rewrite E0 in HDR; exact HDR | split; [exact SLF | split; [exact (lh_link_unsnoc_nil tbl es0 e svs se LINK Ese E0) | split; [constructor | split; [exact Hsz | split; [cbn; lia | rewrite upd_length; exact Hlen]]]]]]).
2,3: assert (OPENF : lh_open rsegs S4F mF t tbl size es0 (upd (upd svs (le_ix e) (del_slot se)) (le_ix el) (clr_nx sl))) by
(split; [unfold lh_hdrf; rewrite hd_of_nth, Ex0; replace (tl_of tbl es0) with (ent_addr tbl (le_ix el)) by (rewrite E0; symmetry; apply UH1t.tl_of_app); rewrite <- EBl; exact HDR
| split; [exact SLF | split; [exact (lh_link_unsnoc_cons tbl es0 e svs se LINK Ese es1 el sl E0 Esl) | split; [exact KEYSF | split; [exact Hsz | split; [lia | rewrite !upd_length; exact Hlen]]]]]]).
1: rewrite E0 in HPF.
all: do 5 bstepz.
all: try rpc.
all: release_frame FR0 ST2 (bv_unsigned sp + -48).
all: stepz.
all: ub_if_lit_c.
all: do 4 stepz.
2: assert (Eef : e = ef) by (replace jf with (length es0) in Hef by lia; rewrite Ee in Hef; injection Hef as X; exact X).
3: assert (NEf : le_ix e <> le_ix ef) by (eapply (IXNE (length es0) jf); [exact Ee | exact Hef | lia]).
all: rewrite (unsigned_lit B), (unsigned_lit (ent_addr tbl (le_ix ef))) by (unfold ent_addr; lia).
1,2: replace (Z.lxor B (ent_addr tbl (le_ix ef))) with 0 by (rewrite <- Eef, <- EB; symmetry; apply Z.lxor_nilpotent).
3: rewrite (sltiu_xor_ne B (ent_addr tbl (le_ix ef))) by (unfold ent_addr; lia).
all: ub_if_lit_c.
all: do 2 stepz.
1,2: ub_if_lit_c.
1,2: do 2 stepz.
3: eqf.
3: do 2 stepz.
3: ub_if_lit_c.
3: do 2 stepz.
3: if_falsex.
all: unstash ERR2; eapply (QWxq.rw_cells_transport rsegs _ mq mF) in ERR2; [| exact MU | exact WM | cbn [disjoint_from]; change (Z.of_nat (cells_size [C4 errv])) with 4; unstash Htimg; pose proof rc_ceil_range; repeat split; lia].
1: rewrite E0, firstn_nil in KX.
2: rewrite firstn_all2 in KX by lia.
1,2: apply evt_RZ_done; eapply KX; first [exact HPF | exact OPENF | exact FR | exact ERR2 | exact HPRF | eapply model_vm_only_trans; [exact VM0 | exact VM2] | eassumption].
all: replace (Z_to_bv 64 Bl) with (Z_to_bv 64 (ent_addr tbl (le_ix el))) by (rewrite EBl; reflexivity).
all: rewrite E0, firstn_snoc_le in KX by lia.
all: rewrite E0 in HPF, OPENF.
all: apply evt_RZ_done.
all: eapply (IH es1 el _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mF md2 A2);
first [exact HPF | exact OPENF | exact FR | exact ERR2 | exact HPRF | exact KX | exact LO | exact LOS | exact SPA | exact HT | idtac].
all: try lia.
all: try (eapply model_vm_only_trans; [exact VM0 | exact VM2]).
all: try (rewrite <- E0; rewrite nth_error_app1 in Hef by lia; exact Hef).
all: try (intros j x Hj Hx; apply (VZ j x Hj); rewrite <- E0 in Hx; rewrite nth_error_app1 by (apply (proj1 (nth_error_Some es0 j)); rewrite Hx; discriminate); exact Hx).
all: try eassumption.
Qed.

Lemma del_exit_ok : forall (esf : list lent),
bv_unsigned rac mod 2 = 0 -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 ->
(forall (m : word -> option byte) (md : Model) (A : AS S4L HIx) (svsf : list slotv)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
HEAPx A (lh_blocks t tbl size esf ++ LB) m md -> lh_open rsegs S4F m t tbl size esf svsf ->
stk rsegs m lo (bv_unsigned sp) -> rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
realizes rsegs (mkCfg (MS (mkR rac sp gp (Z_to_bv 64 0x77c00) t0 t1 t2 s0c s1c (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2c s3c s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rac) fc None m (seg_rom rsegs)) md) T) ->
del_exit esf.
Proof.
intros esf RAC LO LOS K. unfold del_exit. intros until svsf; intros HP OPEN ST FR ERR VM0 HPR.
unfold del_frame in FR. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK; pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI; cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM; pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|].
do 7 bstep.
apply evt_RZ_done. release_frame FR ST (bv_unsigned sp).
eapply K; [exact HP | exact OPEN | exact ST | exact ERR | exact VM0 | exact HPR].
Qed.
End DelLoop.

#[using="Type"] Lemma lh_delete_tail_cps2 : lh_delete_tail_stmt2 HIx.
Proof.
unfold lh_delete_tail_stmt2.
intros until ef. intros HP OPEN Hef VZ ST LO LOS SPA HT ERR TP RA A0 A1 K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen). unfold lh_hdr, lh_hdrf in HDR.
destruct (snoc_inv es) as [Enil | (es0 & e & E0)]; [rewrite Enil in Hef; destruct jf; discriminate|].
pose proof (proj1 (nth_error_Some es jf) ltac:(rewrite Hef; discriminate)) as Hjf. rewrite E0, length_app in Hjf. cbn in Hjf.
replace (tl_of tbl es) with (ent_addr tbl (le_ix e)) in HDR by (rewrite E0, UH1t.tl_of_app; reflexivity).
remember (hd_of tbl es) as HDv eqn:EHD.
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros x Hx. destruct (KF x Hx). lia. }
stash Htimg.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. subst a0 a1 tp.
carve_frame 48%nat ST.
do 10 bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (OPEN1 : lh_open rsegs S4F mx t tbl size es svs) by
(eapply (lh_open_frame rsegs S4F _ m mx t tbl size es svs _ lo); [exact OPEN | exact BELOW | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]]);
assert (HP1 : HEAPx A (lh_blocks t tbl size es ++ LB) mx md) by (heap_now S4L HIx HP MU WM MI);
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m mx) by
(eapply (lh_writes_pres A t tbl size es LB m md mx); [exact HP | exact MU | exact WM | apply Forall_cons; [cbn; left; lia | apply Forall_nil] | lia]);
rename mx into m1
end.
rewrite E0 in HP1, OPEN1, Hef, VZ.
unfold lh_delete_tail_post2 in K. rewrite E0, (firstn_snoc_le _ es0 e jf) in K by lia.
apply evt_RZ_done.
eapply (lh_del_loop sp gp s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo t tbl size jf ef T ra s0 s1 s2 s3 _ errv (length es0 - jf) es0 e svs
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md A);
first [reflexivity | exact Hef | exact HP1 | exact OPEN1 | exact VZ | exact ERR | exact FR | exact ST | apply model_vm_only_refl | exact HPR1 | exact SPA | exact HT | idtac].
all: try lia.
eapply del_exit_ok; [exact RA | lia | lia |].
intros m' md' A' svsf u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 HPf OPENf STf ERRf VMf HPRf.
apply K. exists m', A', svsf.
split; [unfold ret_state; do 14 eexists; reflexivity|].
split; [exact VMf|]. split; [exact STf|]. split; [exact HPRf|]. split; [exact ERRf|]. split; [exact OPENf | exact HPf].
Qed.
End LhDelete.

End RC__1.
End Mq0.
