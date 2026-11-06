(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek QjDH Qtgi Qsw7 QJjn QKQo QPZI QlCE QhHQ Q5Ki QRUw QkMG QG8z Qdyh Q2Sr QLbz Q6WR QrPc QbFI QXUB Qhd4 Qwm6 QlKV Q30W QsKa Qiiq QSHS Ql4f Q1Y6 QrQv Qc5u QZUC Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki. Import QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq2 Q2Sr QLbz.
Import Q6WR.Mq0 QrPc.
Import QbFI QXUB. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh Q30W.Mq6 QlKV.Mqf QsKa.Mqd QlKV.Mqc Qiiq QSHS Ql4f.Mq4 Q1Y6.Mq4 QlKV.Mqe QrQv.
Import Qc5u QZUC.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section PeOutLoopB.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.

Lemma lvl_shadowAg : forall A LB LM FR B m md q mxd i,
HEAPAx A LB LM FR B m md -> In (q, 32 * mxd) LB -> q mod 8 = 0 -> 1 <= mxd -> (i < Z.to_nat mxd)%nat ->
ro_cells asegs m ((q + 32 * Z.of_nat i) / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md q mxd i HP Hin Hal Hm Hi.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH.
replace (shadow_bytes (32 * mxd)) with (shadow_bytes (8 * (4 * mxd))) in SH by (f_equal; lia). rewrite shadow_bytes_mul8 in SH by lia.
apply (bytes_at_repeat_sub asegs m _ _ _ (4 * i) 4) in SH; [| cbn; lia].
replace ((q + 32 * Z.of_nat i) / 8 + A_SB) with (q / 8 + A_SB + Z.of_nat (4 * i)) by (unfold A_SB; Z.div_mod_to_equations; nia).
exact (ro_cells_of_repeat asegs m _ _ 4 SH).
Qed.

Definition PE_RA2 : Z := 0x9385c.

Definition po_body_postB (pf : pe_fix) (pa : pe_fixA) (gp s4 s6 s7 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : config) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (l : tlevel) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (B' : bud) F' fc' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (Z.of_nat i)) s4 (Z_to_bv 64 (-1)) s6 s7 (Z_to_bv 64 (pf_tk pf)) s9 (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x99af0) fc' None m' (seg_rom asegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only (cfg_model md) (cfg_model md') /\
HEAPAx A' REST LM ((pa_F pa, 2) :: FRS) B' m' md' /\
tstack asegs m' q (lupd levels i lvl_reset) /\
rw_cells asegs m' (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb depth q x) /\
pe_frameA asegs m' pf pa cb nb pj sv /\
stk asegs m' lo (pf_spf pf) /\
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) me m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
agree_on asegs P mpre m' /\
bB B - 512 * (Z.of_nat (length (lvl_blocks l)) + 1) <= bB B' /\ bD B <= bD B'.

Lemma po_bodyB :
forall (pf : pe_fix) (pa : pe_fixA) (i : nat) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s9 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (l : tlevel) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved),
PE_STATIC_A HIx pf pa lo ->
nth_error levels i = Some l -> (i < Z.to_nat (pf_mxd pf))%nat -> length levels = Z.to_nat (pf_mxd pf) ->
HEAPAx A (lvl_blocks l ++ REST) LM ((pa_F pa, 2) :: FRS) B m md ->
REST = P ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0 ->
lvl_ok asegs A4F m l ->
tstack asegs m q levels ->
rw_cells asegs m (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb depth q x) ->
pe_frameA asegs m pf pa cb nb pj sv ->
stk asegs m lo (pf_spf pf) ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) me m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
512 * (Z.of_nat (length (lvl_blocks l)) + 1) <= bB B ->
(forall ms' md' A', po_body_postB pf pa gp s4 s6 s7 s9 s11 F fc md REST LB0 P LM FRS B me m lo errv q pb depth x levels i l cb nb pj sv ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md (MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (Z.of_nat i)) s4 (Z_to_bv 64 (-1)) s6 s7 (Z_to_bv 64 (pf_tk pf)) s9 (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x99ae4) fc None m (seg_rom asegs)).
Proof.
intros until sv. intros STC Hl Hi LEN HP EREST LOK TS BLK FR ST HPR ERR BB K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
destruct LOK as [JO NM].
reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
evt_done5.
eapply (tok_reset_level_B_cps HIx PUT) with (i := i) (l := l) (levels := levels) (P := P) (LB0 := LB0) (LM := LM) (REST := REST)
(FRS := (pa_F pa, 2) :: FRS) (B := B) (lo := lo) (errv := errv) (q := q) (r := pf_tk pf) (pb := pb) (depth := depth) (mxd := pf_mxd pf) (fl := pf_fl pf)
(x := x) (rc := 1) (me := m);
[ exact Hl | lia | exact (proj1 (proj2 RR)) | exact LEN | exact HP | exact EREST
| unfold put_pre; destruct (tl_cs l) as [s'|]; [destruct JO as [Hp J]; split; [exact Hp | split; [lia | exact J]] | exact JO]
| exact NM | exact TS | exact BLK
| rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; unfold put_stk_A; clear - LOS; lia
| rewrite unsigned_lit by lia; clear - Gspf; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; clear - HT Gle; lia
| apply heap_pres_refl | exact ERR
| unfold put_costA; destruct (tl_cs l); [rewrite Z.eqb_refl; unfold lvl_blocks in BB; rewrite length_app, Nat2Z.inj_add in BB; lia | lia]
| rewrite unsigned_lit by lia; reflexivity | ].
intros ms2 md2 A2 (m2 & B2 & rv & RS2 & VM2 & OUT2 & TS2 & TOK2 & ST2 & HPR2 & ERR2 & AG2 & BB2 & BD2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
apply K. unfold po_body_postB.
exists m2, B2, F2, fc2. do 16 eexists.
split; [reflexivity|]. split; [exact FS2|]. split; [exact FRM2|]. split; [exact VM2|].
split.
{ destruct OUT2 as [(_ & H) | (s' & _ & Hrc & _)]; [exact H | exfalso; lia]. }
split; [exact TS2|]. split; [exact TOK2|].
split.
{ eapply pe_frameA_pres; [exact HPR2 | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
split; [exact ST2|]. split; [eapply heap_pres_trans; [exact HPR | exact HPR2]|]. split; [exact ERR2|]. split; [exact AG2|].
unfold put_costA in BB2. destruct (tl_cs l); [rewrite Z.eqb_refl in BB2; unfold lvl_blocks; rewrite length_app, Nat2Z.inj_add; lia | unfold lvl_blocks in *; cbn [length] in *; lia].
Qed.

Definition po_loop_postB (pf : pe_fix) (pa : pe_fixA) (gp s4 s6 s7 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : config) (BASE LB0 PBS LM : list blk) (FRS : list frame) (B : bud) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (B' : bud) F' fc' levels' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3',
ms' = MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3' s4 (Z_to_bv 64 (-1)) s6 s7 (Z_to_bv 64 (pf_tk pf)) s9 (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x99af8) fc' None m' (seg_rom asegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only (cfg_model md) (cfg_model md') /\
HEAPAx A' BASE LM ((pa_F pa, 2) :: FRS) B' m' md' /\
length levels' = Z.to_nat (pf_mxd pf) /\
(forall j, (j <= i)%nat -> nth_error levels' j = Some lvl_reset) /\
(forall j, (i < j)%nat -> nth_error levels' j = nth_error levels j) /\
tstack asegs m' q levels' /\
rw_cells asegs m' (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb depth q x) /\
pe_frameA asegs m' pf pa cb nb pj sv /\
stk asegs m' lo (pf_spf pf) /\
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) me m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
agree_on asegs PBS mpre m' /\
bB B - 512 * (Z.of_nat (length (lvblocks levels (S i))) + Z.of_nat (S i)) <= bB B' /\ bD B <= bD B'.

Lemma po_loopB :
forall (i : nat) (pf : pe_fix) (pa : pe_fixA) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s9 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (PBS LB0 LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved),
PE_STATIC_A HIx pf pa lo ->
(i < Z.to_nat (pf_mxd pf))%nat -> length levels = Z.to_nat (pf_mxd pf) ->
HEAPAx A (lvblocks levels (S i) ++ PBS ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) LM ((pa_F pa, 2) :: FRS) B m md ->
(forall j l, nth_error levels j = Some l -> (j <= i)%nat -> lvl_ok asegs A4F m l) ->
tstack asegs m q levels ->
rw_cells asegs m (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb depth q x) ->
pe_frameA asegs m pf pa cb nb pj sv ->
stk asegs m lo (pf_spf pf) ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) me m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
512 * (Z.of_nat (length (lvblocks levels (S i))) + Z.of_nat (S i)) <= bB B ->
(forall ms' md' A', po_loop_postB pf pa gp s4 s6 s7 s9 s11 F fc md (PBS ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) LB0 PBS LM FRS B me m lo errv q pb depth x levels i cb nb pj sv ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md (MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (Z.of_nat i)) s4 (Z_to_bv 64 (-1)) s6 s7 (Z_to_bv 64 (pf_tk pf)) s9 (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x99ae4) fc None m (seg_rom asegs)).
Proof.
induction i as [|i IH]; intros until sv; intros STC Hi LEN HP LOK TS BLK FR ST HPR ERR BB K;
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR).
-
destruct (nth_error levels 0) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP, BB. rewrite <- app_assoc in HP. rewrite lvblocks_0, app_nil_r in BB.
eapply (po_bodyB pf pa 0) with (P := PBS); [exact STC | exact Hl | lia | exact LEN | exact HP | rewrite lvblocks_0; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact HPR | exact ERR | cbn [Z.of_nat length] in BB |- *; lia |].
intros ms1 md1 A1 (m1 & B1 & F1 & fc1 & y1 & u0 & u1 & u2 & w0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1 & BB1 & BD1).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [] m1) as MU.
unfold_consts. reenterA asegs A4L HIx asegs_wx HP1.
step.
step. if_false.
evt_done5. apply K. unfold po_loop_postB.
exists m1, B1, F1, fc1, (lupd levels 0 lvl_reset). do 17 eexists.
split; [reflexivity|]. split; [exact FS1|]. split; [exact FRM1|]. split; [exact VM1|].
split; [rewrite lvblocks_0 in HP1; heap_nowA A4L HIx HP1 MU WM MI1|].
split; [rewrite lupd_length; exact LEN|].
split; [intros j Hj; replace j with 0%nat by lia; apply nth_error_lupd_eq; lia|].
split; [intros j Hj; apply nth_error_lupd_neq; lia|].
split; [exact TS1|]. split; [exact BLK1|]. split; [exact FR1|]. split; [exact ST1|]. split; [exact HPR1 |]. split; [exact ERR1|]. split; [exact AG1|].
rewrite (lvblocks_S _ _ _ Hl), lvblocks_0, app_nil_r. change (Z.of_nat 1) with 1. lia.
-
destruct (nth_error levels (S i)) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP, BB. rewrite <- app_assoc in HP. rewrite length_app, Nat2Z.inj_add in BB.
eapply (po_bodyB pf pa (S i)) with (P := lvblocks levels (S i) ++ PBS); [exact STC | exact Hl | lia | exact LEN | exact HP | rewrite <- app_assoc; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact HPR | exact ERR | lia |].
intros ms1 md1 A1 (m1 & B1 & F1 & fc1 & y1 & u0 & u1 & u2 & w0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1 & BB1 & BD1).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [] m1) as MU.
unfold_consts. reenterA asegs A4L HIx asegs_wx HP1.
step.
norm_w32.
step. if_truex.
replace (Z.of_nat (S i) + -1) with (Z.of_nat i) by lia.
evt_done5.
eapply (IH pf pa _ gp _ _ _ _ _ _ _ _ _ _ _ s4 s6 s7 s9 s11 _ _ _ _ F1 fc1 m1 me md1 T A1 PBS LB0 LM FRS B1 lo errv q pb depth x (lupd levels (S i) lvl_reset) cb nb pj sv);
[exact STC | lia | rewrite lupd_length; exact LEN | rewrite lvblocks_lupd_ge by lia; heap_nowA A4L HIx HP1 MU WM MI1 | | exact TS1 | exact BLK1 | exact FR1 | exact ST1 | exact HPR1 | exact ERR1 | rewrite lvblocks_lupd_ge by lia; lia |].
+ intros j l' Hj Hji. rewrite nth_error_lupd_neq in Hj by lia.
eapply lvl_ok_agree; [eapply LOK; [exact Hj | lia] | exact AG1 | apply incl_appl; eapply incl_tran; [| eapply lvblocks_incl; [exact Hj | lia]]; unfold lvl_blocks; apply incl_appl; apply incl_refl].
+ intros ms2 md2 A2 (m2 & B2 & F2 & fc2 & levels2 & y1' & u0' & u1' & u2' & w0' & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & s6' & -> & FS2 & FRM2 & VM2 & HP2 & LEN2 & RES2 & SAME2 & TS2 & BLK2 & FR2 & ST2 & HPR2 & ERR2 & AG2 & BB2 & BD2).
apply K. unfold po_loop_postB.
exists m2, B2, F2, fc2, levels2. do 17 eexists.
split; [reflexivity|]. split; [eapply fsaved_trans; [exact FS1 | exact FS2]|]. split; [intros Hf; apply FRM2, FRM1, Hf|].
split; [eapply model_vm_only_trans; [exact VM1 | exact VM2]|].
split; [exact HP2|]. split; [exact LEN2|].
split. { intros j Hj. destruct (PeanoNat.Nat.eq_dec j (S i)) as [->|NE]; [| apply RES2; lia]. rewrite SAME2 by lia. apply nth_error_lupd_eq. lia. }
split. { intros j Hj. rewrite SAME2 by lia. apply nth_error_lupd_neq. lia. }
split; [exact TS2|]. split; [exact BLK2|]. split; [exact FR2|]. split; [exact ST2|]. split; [exact HPR2 |]. split; [exact ERR2|].
split; [eapply agree_on_trans; [eapply agree_on_incl; [exact AG1 | apply incl_appr; apply incl_refl] | exact AG2] |].
rewrite (lvblocks_S _ _ _ Hl), length_app. rewrite lvblocks_lupd_ge in BB2 by lia. rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ in *. lia.
Qed.
End PeOutLoopB.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlCE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlCE.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhHQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhHQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Ki.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Ki. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ey.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Ey. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section PeOutLoopA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.

Lemma lvl_shadowAg : forall A LB LM FR B m md q mxd i,
HEAPAx A LB LM FR B m md -> In (q, 32 * mxd) LB -> q mod 8 = 0 -> 1 <= mxd -> (i < Z.to_nat mxd)%nat ->
ro_cells asegs m ((q + 32 * Z.of_nat i) / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md q mxd i HP Hin Hal Hm Hi.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH.
replace (shadow_bytes (32 * mxd)) with (shadow_bytes (8 * (4 * mxd))) in SH by (f_equal; lia). rewrite shadow_bytes_mul8 in SH by lia.
apply (bytes_at_repeat_sub asegs m _ _ _ (4 * i) 4) in SH; [| cbn; lia].
replace ((q + 32 * Z.of_nat i) / 8 + A_SB) with (q / 8 + A_SB + Z.of_nat (4 * i)) by (unfold A_SB; Z.div_mod_to_equations; nia).
exact (ro_cells_of_repeat asegs m _ _ 4 SH).
Qed.

Definition PE_RA2 : Z := 0x93080.

Definition po_body_postA (pf : pe_fix) (pa : pe_fixA) (gp s3 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : config) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (l : tlevel) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (B' : bud) F' fc' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 1) (Z_to_bv 64 (32 * Z.of_nat i + 16 - 32)) (Z_to_bv 64 (-16))
(Z_to_bv 64 (pf_tk pf / 8 + SB7)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (pf_tk pf + 56)) s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x982b4) fc' None m' (seg_rom asegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only (cfg_model md) (cfg_model md') /\
HEAPAx A' REST LM ((pa_F pa, 2) :: FRS) B' m' md' /\
tstack asegs m' q (lupd levels i lvl_reset) /\
rw_cells asegs m' (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb depth q x) /\
pe_frameA asegs m' pf pa cb nb pj sv /\
stk asegs m' lo (pf_spf pf) /\
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
agree_on asegs P mpre m' /\
bB B - 512 * (Z.of_nat (length (lvl_blocks l)) + 1) <= bB B' /\ bD B <= bD B'.

Lemma po_bodyA :
forall (pf : pe_fix) (pa : pe_fixA) (i : nat) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (l : tlevel) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved),
PE_STATIC_A HIx pf pa lo ->
nth_error levels i = Some l -> (i < Z.to_nat (pf_mxd pf))%nat -> length levels = Z.to_nat (pf_mxd pf) ->
HEAPAx A (lvl_blocks l ++ REST) LM ((pa_F pa, 2) :: FRS) B m md ->
REST = P ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0 ->
lvl_ok asegs A4F m l ->
tstack asegs m q levels ->
rw_cells asegs m (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb depth q x) ->
pe_frameA asegs m pf pa cb nb pj sv ->
stk asegs m lo (pf_spf pf) ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
pe_s0 sv = Z_to_bv 64 (pf_tk pf) -> pe_ra sv = Z_to_bv 64 PE_RA2 ->
512 * (Z.of_nat (length (lvl_blocks l)) + 1) <= bB B ->
(forall ms' md' A', po_body_postA pf pa gp s3 s11 F fc md REST LB0 P LM FRS B me m lo errv q pb depth x levels i l cb nb pj sv ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 1) (Z_to_bv 64 (32 * Z.of_nat i + 16)) (Z_to_bv 64 (-16))
(Z_to_bv 64 (pf_tk pf / 8 + SB7)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (pf_tk pf + 56)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x981d4) fc None m (seg_rom asegs)).
Proof.
intros until sv. intros STC Hl Hi LEN HP EREST LOK TS BLK FR ST HPR ERR S0V RAV BB K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct pf as [r oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold_consts. unfold A_SB, A_TP, A_ERRNO, SB7, shA, PE_RA2 in *. unfold A_SB in *.
assert (MXB : 1 <= mxd <= 32) by lia.
assert (INrR : In (r, 72) REST) by (rewrite EREST; apply in_or_app; right; left; reflexivity).
assert (INqR : In (q, 32 * mxd) REST) by (rewrite EREST; apply in_or_app; right; right; left; reflexivity).
assert (INr : In (r, 72) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INq : In (q, 32 * mxd) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INqR).
assert (INr2 : In (r, 72) ((lvl_blocks l ++ REST) ++ LM)) by (apply in_or_app; left; exact INr).
assert (INq2 : In (q, 32 * mxd) ((lvl_blocks l ++ REST) ++ LM)) by (apply in_or_app; left; exact INq).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 72 HP INr2) as (_ & Hral & Hrlo & Hrhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r 72 HP INr2) as Himg_r.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP INq2) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP INq2) as Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi, Hqhi.
assert (Hqr : q <> r).
{ intros ->. pose proof (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. rewrite EREST, !map_app in ND. cbn [map blk_addr fst] in ND.
apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q (32 * mxd) r 72 HP INq2 INr2 Hqr) as Hdqr.
pose proof (TS i l Hl) as LV. unfold srec_cells in LV.
remember (q + 32 * Z.of_nat i) as bse eqn:Hbse in LV.
pose proof (nth_error_Some_length Hl) as HiL.
unfold tok_cells_g in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof alloc_ceiling_range as ACR.
assert (SHAD : forall Ax LBx Bx mdx mc, HEAPAx Ax LBx LM ((Ff, 2) :: FRS) Bx mc mdx -> In (r, 72) LBx -> In (q, 32 * mxd) LBx ->
ro_cells asegs mc (r / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ ro_cells asegs mc (bse / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ intros Ax LBx Bx mdx mc HPc Ir Iq. split.
- pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ r 72 HPc Ir) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. a4l. exact SH.
- pose proof (lvl_shadowAg _ _ _ _ _ _ _ q mxd i HPc Iq ltac:(lia) ltac:(lia) Hi) as SH. unfold A_SB in SH. rewrite <- Hbse in SH. exact SH. }
destruct (SHAD _ _ _ _ m HP INr INq) as [SHr SHl].
stash FR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_true.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step.
replace (bse + 16 + -16) with bse by lia.
asan_chkA.
stepz.
step. replace (bse + 16 + -12) with (bse + 4) by lia.
asan_chkA.
step.
asan_chkA.
step. step.
try clear SHr; try clear SHl.
set (l1 := TL 0 1 (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS1 : tstack asegs mc q (lupd levels i l1)) end.
{ subst bse. eapply (tstack_put asegs m _ q levels i l1 []); [exact TS | lia | exact MU | exact WM | intros; exact I | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name l1]; assumption]. }
lazymatch goal with H : rw_cells asegs _ bse _ |- _ => rename H into LV1 end.
clear TS.
assert (PDJ : forall a n, In (a, n) P -> a + n <= q \/ q + 32 * mxd <= a).
{ intros a n Hin.
assert (Haq : a <> q) by (eapply (nodup_P_notq (lvl_blocks l)); [rewrite <- EREST; exact (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) | exact Hin]).
exact (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n q (32 * mxd) HP ltac:(apply in_or_app; left; apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hin) INq2 Haq). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGP : agree_on asegs P m mc) by (eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]) end.
unstash FR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (FR1 : pe_frameA asegs mc (PEF r oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx _ _ _ _ _ _ _ m mc); [exact STC | exact HP | | exact FR | exact MU | exact WM];
apply Forall_cons; [| apply Forall_nil]; exists q, (32 * mxd); cbn [fst snd]; split; [exact INq2 | lia]) end.
clear FR.
assert (SPA : spf mod 16 = 0) by (clear - Gspf; Z.div_mod_to_equations; lia).

destruct LOK as [JO NM].
unfold lvl_blocks in HP. rewrite <- app_assoc in HP.
evt_done5.
assert (INq3 : In (q, 32 * mxd) (tl_cbs l ++ tl_nbs l ++ REST)) by (apply in_or_app; right; apply in_or_app; right; exact INqR).
assert (INq4 : In (q, 32 * mxd) ((tl_cbs l ++ tl_nbs l ++ REST) ++ LM)) by (apply in_or_app; left; exact INq3).
pose proof PUT as PUTx. unfold put_stmt_A, put_stmtA in PUTx.
eapply PUTx with (s := tl_cs l) (BS := tl_cbs l) (LB := tl_nbs l ++ REST) (p := tl_cur l) (rc := 1) (lo := lo) (errv := errv);
[ heap_nowA A4L HIx HP MU WM MI | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
{ lazymatch goal with |- put_pre _ _ _ ?mc _ _ _ => assert (AG : agree_on asegs (tl_cbs l) m mc) end.
{ eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a n Hin. cbn. split; [|exact I].
assert (Haq : a <> q).
{ intros ->. refine (nodup_prefix_suffix (tl_cbs l) (tl_nbs l ++ REST) q n (32 * mxd) (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) Hin _).
apply in_or_app; right. exact INqR. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n q (32 * mxd) HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact INqR) Haq). lia. }
unfold put_pre. destruct (tl_cs l) as [s'|]; [|exact JO].
destruct JO as [Hc J]. split; [exact Hc|]. split; [lia|]. eapply jval_agree; [exact J | exact AG | apply incl_refl]. }
all: try eassumption.
all: try (unfold put_stk_A; lia).
all: try (unfold put_costA; destruct (tl_cs l); [rewrite Z.eqb_refl; unfold lvl_blocks in BB; rewrite length_app in BB|]; lia).
intros ms2 md2 A2 (m2 & r2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
destruct OUT2 as [[_ HP2] | (s2 & _ & Habs & _)]; [| lia].
assert (INrN : In (r, 72) (tl_nbs l ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INqN : In (q, 32 * mxd) (tl_nbs l ++ REST)) by (apply in_or_app; right; exact INqR).
pose proof (pe_frameA_pres (PEF r oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ _ _ _ _ _ _ _ HPR2 ltac:(cbn [pf_spf]; lia) GEO
ltac:(apply in_or_app; right; apply in_or_app; right; cbn [pa_F fr_ivs flat_map app fr_base fr_class fst snd]; left; reflexivity)
ltac:(apply in_or_app; right; apply in_or_app; right; cbn [pa_F fr_ivs flat_map app fr_base fr_class fst snd]; right; left; unfold shad, shA, A_SB; cbn [hl_sb A4L]; reflexivity)
FR1) as FR2. clear FR1.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in BLK; [| eapply client_range_block; [apply in_or_app; left; exact INrN | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in LV1; [| eapply client_range_block; [apply in_or_app; left; exact INqN | lia | cbn; lia]]. a4l.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 ltac:(apply in_or_app; left; exact INqN)) in TS1; [| rewrite lupd_length; exact LEN]. a4l.
assert (NQ0 : ~ In (q, 32 * mxd) LB0).
{ pose proof (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. rewrite EREST in ND. exact (nodup_mid_notin _ _ _ _ _ _ _ _ (32 * mxd) ND). }
assert (NQM : ~ In (q, 32 * mxd) (LB0 ++ LM ++ fr_ivs A4L FRS)).
{ apply not_in_app3; [| ].
- intros Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [exact (NQ0 Hx)|].
exact (nodup_prefix_suffix _ LM q (32 * mxd) (32 * mxd) (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) INq3 Hx).
- intros Hx. apply (QlKV.Mq8.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INq4). cbn [fr_ivs flat_map app]. right; right. exact Hx. }
assert (HPRa : heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) sp0 me m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB0 ++ LM ++ fr_ivs A4L FRS) sp0); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; cbn [fr_ivs flat_map app]; right; right; exact Hbb]] | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, (32 * mxd). split; [exact INq4|]. split; [exact NQM | lia].
- eapply heap_pres_weaken; [exact HPR2 | lia | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; cbn [fr_ivs flat_map app]; right; right; exact Hbb]]]. }
assert (AGP2 : agree_on asegs P m m2).
{ eapply agree_on_trans; [exact AGP|]. eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hb]. }
clear MU WM MI HPR AGP PUTx.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP2) as [HB2 HD2].

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
destruct (SHAD _ _ _ _ m2 HP2 INrN INqN) as [SHr SHl].
stash FR2.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. if_true.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
asan_chkA.
stepz.
try clear SHr; try clear SHl.
destruct (SHAD _ _ _ _ _ ltac:(heap_nowA A4L HIx HP2 MU WM MI) INrN INqN) as [SHr SHl].
step. asan_chkA.
step. step.
try clear SHr; try clear SHl.
set (l2 := TL 0 1 0 None [] (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS2 : tstack asegs mc q (lupd levels i l2)) end.
{ rewrite <- (lupd_lupd levels i l1 l2). subst bse.
eapply (tstack_put asegs m2 _ q (lupd levels i l1) i l2 []); [exact TS1 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name l2]; assumption]. }
clear TS1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGP3 : agree_on asegs P m mc) by (eapply agree_on_trans; [exact AGP2|]; eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]) end.
unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (FR3 : pe_frameA asegs mc (PEF r oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx _ _ _ _ _ _ _ m2 mc); [exact STC | exact HP2 | | exact FR2 | exact MU | exact WM];
apply Forall_cons; [| apply Forall_nil]; exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INqN | lia]) end.
clear FR2.
assert (UWB : bytes_at asegs m0 (sp0 - 16) (le8 (Z_to_bv 64 r) ++ le8 (Z_to_bv 64 602240))).
{ destruct FR3 as (_ & _ & SV & _). unfold pe_savedA_cells in SV. cbn [pa_sp0] in SV. destruct SV as [[_ SVB] _].
cbn [cells_bytes cbytes app] in SVB. rewrite <- ?app_assoc in SVB.
do 11 (apply bytes_at_app in SVB as [_ SVB]; rewrite length_le8 in SVB).
rewrite S0V, RAV in SVB. eapply bytes_at_ext; [| reflexivity].
match type of SVB with bytes_at _ _ ?a _ => replace a with (sp0 - 16) in SVB by lia end. exact SVB. }
alloc_callA (hiA_free A4L HIx) blk (tl_name l) uw (UWfp 602240 r) A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ destruct NM as [[Hn0 _] | [Hn0 [nn Hnbs]]]; [left; exact Hn0 | right; exists nn; rewrite Hnbs; left; reflexivity]. }
{ split; [lia|]. split; [clear - Gsp0; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact UWB | split; [left; lia | lia]]. }
{ clear - BB BB2 BD2 HB2 HD2. unfold put_costA in *; unfold lvl_blocks in *; rewrite ?length_app in *; destruct (tl_cs l); rewrite ?Z.eqb_refl in *; cbn [bB bD charge uw_cost] in *; lia. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPR3 by lia.
assert (ELB : lb_remove (tl_name l) (tl_nbs l ++ REST) = REST).
{ destruct NM as [[Hn0 Hnbs] | [Hn0 [nn Hnbs]]].
- rewrite Hn0, Hnbs. cbn [app]. apply lb_remove_notin. intros nn Hin.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ 0 nn HP2 ltac:(apply in_or_app; left; rewrite Hnbs; exact Hin)) as (_ & _ & H0 & _). lia.
- rewrite Hnbs. cbn [app]. apply lb_remove_head. }
rewrite ELB in HPR3, HP3.
pose proof (pe_frameA_pres (PEF r oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ _ _ _ _ _ _ _ HPR3 ltac:(cbn [pf_spf]; lia) GEO
ltac:(apply in_or_app; right; apply in_or_app; right; cbn [pa_F fr_ivs flat_map app fr_base fr_class fst snd]; left; reflexivity)
ltac:(apply in_or_app; right; apply in_or_app; right; cbn [pa_F fr_ivs flat_map app fr_base fr_class fst snd]; right; left; unfold shad, shA, A_SB; cbn [hl_sb A4L]; reflexivity)
FR3) as FR4. clear FR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [apply in_or_app; left; exact INrR | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in LV1; [| eapply client_range_block; [apply in_or_app; left; exact INqR | lia | cbn; lia]]. a4l.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR3 ltac:(apply in_or_app; left; exact INqR)) in TS2; [| rewrite lupd_length; exact LEN]. a4l.
assert (HPRb : heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) sp0 me m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB0 ++ LM ++ fr_ivs A4L FRS) sp0); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; cbn [fr_ivs flat_map app]; right; right; exact Hbb]] | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, (32 * mxd). split; [apply in_or_app; left; exact INqN|]. split; [exact NQM | lia].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; cbn [fr_ivs flat_map app]; right; right; exact Hbb]]]. }
assert (AGP4 : agree_on asegs P m m3).
{ eapply agree_on_trans; [exact AGP3|]. eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity |].
intros b Hb. apply in_or_app; left. rewrite EREST. apply in_or_app; left; exact Hb. }
clear MU WM MI HPRa AGP3.

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. a4l.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(bse, bse + 32)] m3) as MU.
destruct (SHAD _ _ _ _ m3 HP3 INrR INqR) as [SHr SHl].
stash FR4.
reenterA asegs A4L HIx asegs_wx HP3.
step. step. if_true.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
step. asan_chkA.
step. stepz.
try clear SHr; try clear SHl.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS3 : tstack asegs mc q (lupd levels i lvl_reset)) end.
{ rewrite <- (lupd_lupd levels i l2 lvl_reset). subst bse.
eapply (tstack_put asegs m3 _ q (lupd levels i l2) i lvl_reset []); [exact TS2 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name lvl_reset]; assumption]. }
unstash FR4.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (FR5 : pe_frameA asegs mc (PEF r oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx _ _ _ _ _ _ _ m3 mc); [exact STC | exact HP3 | | exact FR4 | exact MU | exact WM];
apply Forall_cons; [| apply Forall_nil]; exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INqR | lia]) end.
clear FR4.
evt_done5. apply K. unfold po_body_postA. cbn [pf_spf pa_sp0 pa_F pf_tk pf_mxd pf_fl]. unfold shA, SB7, A_SB, A_TP, A_ERRNO.
replace (32 * Z.of_nat i + -16) with (32 * Z.of_nat i + 16 - 32) by (f_equal; lia).
do 20 eexists.
split; [reflexivity|].
split; [exact FS2|]. split; [exact FRM2|].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|].
split; [heap_nowA A4L HIx HP3 MU WM MI |].
split; [exact TS3|]. split; [unfold tok_cells_g; exact BLK|]. split; [exact FR5|].
split; [assumption|].
split.
{ eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch A4H (LB0 ++ LM ++ fr_ivs A4L FRS) sp0); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP3 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; cbn [fr_ivs flat_map app]; right; right; exact Hbb]] | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, (32 * mxd). split; [apply in_or_app; left; exact INqR|]. split; [exact NQM | lia]. }
split; [assumption|].
split; [eapply agree_on_trans; [exact AGP4|]; eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]] |].
clear - BB BB2 BD2 HB2 HD2. unfold put_costA in BB2. unfold lvl_blocks in *. rewrite ?length_app in *.
destruct (tl_cs l); rewrite ?Z.eqb_refl in BB2; destruct (tl_name l =? 0); cbn [bB bD charge uw_cost] in *; lia.
Qed.

Definition po_loop_postA (pf : pe_fix) (pa : pe_fixA) (gp s3 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : config) (BASE LB0 PBS LM : list blk) (FRS : list frame) (B : bud) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (B' : bud) F' fc' levels' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5',
ms' = MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 1) s5' (Z_to_bv 64 (-16))
(Z_to_bv 64 (pf_tk pf / 8 + SB7)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (pf_tk pf + 56)) s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x982b8) fc' None m' (seg_rom asegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only (cfg_model md) (cfg_model md') /\
HEAPAx A' BASE LM ((pa_F pa, 2) :: FRS) B' m' md' /\
length levels' = Z.to_nat (pf_mxd pf) /\
(forall j, (j <= i)%nat -> nth_error levels' j = Some lvl_reset) /\
(forall j, (i < j)%nat -> nth_error levels' j = nth_error levels j) /\
tstack asegs m' q levels' /\
rw_cells asegs m' (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb depth q x) /\
pe_frameA asegs m' pf pa cb nb pj sv /\
stk asegs m' lo (pf_spf pf) /\
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
agree_on asegs PBS mpre m' /\
bB B - 512 * (Z.of_nat (length (lvblocks levels (S i))) + Z.of_nat (S i)) <= bB B' /\ bD B <= bD B'.

Lemma po_loopA :
forall (i : nat) (pf : pe_fix) (pa : pe_fixA) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (PBS LB0 LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved),
PE_STATIC_A HIx pf pa lo ->
(i < Z.to_nat (pf_mxd pf))%nat -> length levels = Z.to_nat (pf_mxd pf) ->
HEAPAx A (lvblocks levels (S i) ++ PBS ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) LM ((pa_F pa, 2) :: FRS) B m md ->
(forall j l, nth_error levels j = Some l -> (j <= i)%nat -> lvl_ok asegs A4F m l) ->
tstack asegs m q levels ->
rw_cells asegs m (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb depth q x) ->
pe_frameA asegs m pf pa cb nb pj sv ->
stk asegs m lo (pf_spf pf) ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
pe_s0 sv = Z_to_bv 64 (pf_tk pf) -> pe_ra sv = Z_to_bv 64 PE_RA2 ->
512 * (Z.of_nat (length (lvblocks levels (S i))) + Z.of_nat (S i)) <= bB B ->
(forall ms' md' A', po_loop_postA pf pa gp s3 s11 F fc md (PBS ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) LB0 PBS LM FRS B me m lo errv q pb depth x levels i cb nb pj sv ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 1) (Z_to_bv 64 (32 * Z.of_nat i + 16)) (Z_to_bv 64 (-16))
(Z_to_bv 64 (pf_tk pf / 8 + SB7)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (pf_tk pf + 56)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x981d4) fc None m (seg_rom asegs)).
Proof.
induction i as [|i IH]; intros until sv; intros STC Hi LEN HP LOK TS BLK FR ST HPR ERR S0V RAV BB K;
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR).
-
destruct (nth_error levels 0) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP, BB. rewrite <- app_assoc in HP. rewrite lvblocks_0, app_nil_r in BB.
eapply (po_bodyA pf pa 0) with (P := PBS); [exact STC | exact Hl | lia | exact LEN | exact HP | rewrite lvblocks_0; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact HPR | exact ERR | exact S0V | exact RAV | cbn [Z.of_nat length] in BB |- *; lia |].
intros ms1 md1 A1 (m1 & B1 & F1 & fc1 & y1 & u0 & u1 & u2 & w0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1 & BB1 & BD1).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [] m1) as MU.
unfold_consts. reenterA asegs A4L HIx asegs_wx HP1.
step. if_false.
evt_done5. apply K. unfold po_loop_postA.
exists m1, B1, F1, fc1, (lupd levels 0 lvl_reset). do 17 eexists.
split; [reflexivity|]. split; [exact FS1|]. split; [exact FRM1|]. split; [exact VM1|].
split; [rewrite lvblocks_0 in HP1; heap_nowA A4L HIx HP1 MU WM MI1|].
split; [rewrite lupd_length; exact LEN|].
split; [intros j Hj; replace j with 0%nat by lia; apply nth_error_lupd_eq; lia|].
split; [intros j Hj; apply nth_error_lupd_neq; lia|].
split; [exact TS1|]. split; [exact BLK1|]. split; [exact FR1|]. split; [exact ST1|]. split; [exact HPR1 |]. split; [exact ERR1|]. split; [exact AG1|].
rewrite (lvblocks_S _ _ _ Hl), lvblocks_0, app_nil_r. change (Z.of_nat 1) with 1. lia.
-
destruct (nth_error levels (S i)) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
rewrite (lvblocks_S _ _ _ Hl) in HP, BB. rewrite <- app_assoc in HP. rewrite length_app, Nat2Z.inj_add in BB.
eapply (po_bodyA pf pa (S i)) with (P := lvblocks levels (S i) ++ PBS); [exact STC | exact Hl | lia | exact LEN | exact HP | rewrite <- app_assoc; reflexivity
| eapply LOK; [exact Hl | lia] | exact TS | exact BLK | exact FR | exact ST | exact HPR | exact ERR | exact S0V | exact RAV | lia |].
intros ms1 md1 A1 (m1 & B1 & F1 & fc1 & y1 & u0 & u1 & u2 & w0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & FS1 & FRM1 & VM1 & HP1 & TS1 & BLK1 & FR1 & ST1 & HPR1 & ERR1 & AG1 & BB1 & BD1).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1.
pose proof (wmono_refl asegs m1) as WM. pose proof (munch_refl [] m1) as MU.
unfold_consts. reenterA asegs A4L HIx asegs_wx HP1.
step. if_truex.
replace (32 * Z.of_nat (S i) + 16 - 32) with (32 * Z.of_nat i + 16) by lia.
evt_done5.
eapply (IH pf pa _ gp _ _ _ _ _ _ _ _ _ _ _ s3 s11 _ _ _ _ F1 fc1 m1 me md1 T A1 PBS LB0 LM FRS B1 lo errv q pb depth x (lupd levels (S i) lvl_reset) cb nb pj sv);
[exact STC | lia | rewrite lupd_length; exact LEN | rewrite lvblocks_lupd_ge by lia; heap_nowA A4L HIx HP1 MU WM MI1 | | exact TS1 | exact BLK1 | exact FR1 | exact ST1 | exact HPR1 | exact ERR1 | exact S0V | exact RAV | rewrite lvblocks_lupd_ge by lia; lia |].
+ intros j l' Hj Hji. rewrite nth_error_lupd_neq in Hj by lia.
eapply lvl_ok_agree; [eapply LOK; [exact Hj | lia] | exact AG1 | apply incl_appl; eapply incl_tran; [| eapply lvblocks_incl; [exact Hj | lia]]; unfold lvl_blocks; apply incl_appl; apply incl_refl].
+ intros ms2 md2 A2 (m2 & B2 & F2 & fc2 & levels2 & y1' & u0' & u1' & u2' & w0' & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & s6' & -> & FS2 & FRM2 & VM2 & HP2 & LEN2 & RES2 & SAME2 & TS2 & BLK2 & FR2 & ST2 & HPR2 & ERR2 & AG2 & BB2 & BD2).
apply K. unfold po_loop_postA.
exists m2, B2, F2, fc2, levels2. do 17 eexists.
split; [reflexivity|]. split; [eapply fsaved_trans; [exact FS1 | exact FS2]|]. split; [intros Hf; apply FRM2, FRM1, Hf|].
split; [eapply model_vm_only_trans; [exact VM1 | exact VM2]|].
split; [exact HP2|]. split; [exact LEN2|].
split. { intros j Hj. destruct (PeanoNat.Nat.eq_dec j (S i)) as [->|NE]; [| apply RES2; lia]. rewrite SAME2 by lia. apply nth_error_lupd_eq. lia. }
split. { intros j Hj. rewrite SAME2 by lia. apply nth_error_lupd_neq. lia. }
split; [exact TS2|]. split; [exact BLK2|]. split; [exact FR2|]. split; [exact ST2|]. split; [exact HPR2 |]. split; [exact ERR2|].
split; [eapply agree_on_trans; [eapply agree_on_incl; [exact AG1 | apply incl_appr; apply incl_refl] | exact AG2] |].
rewrite (lvblocks_S _ _ _ Hl), length_app. rewrite lvblocks_lupd_ge in BB2 by lia. rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ in *. lia.
Qed.
End PeOutLoopA.
End RC__1.
