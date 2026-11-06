(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek QjDH Qtgi Qsw7 QJjn QKQo QPZI QlCE QhHQ QRUw QkMG QG8z Qdyh Q2Sr QLbz Q6WR QrPc Q7UD QXUB Qhd4 Qwm6 QlKV Q30W QsKa Qiiq Q1Ey Ql4f Q1Y6 QrQv QGdd Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ. Import QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq2. Import QJjn.Mq0. Import Q2Sr QLbz.
Import Q6WR.Mq0 QrPc.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 Q30W.Mq3 QlKV.Mq5 QsKa.Mq4 QlKV.Mq1 Qiiq.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QlKV.Mq4 QrQv.Mq0 QGdd.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section PeOutA.
Variable HIx : heap_iface_A A4L.

End PeOutA.
End RC__1.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ. Import QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq2. Import QJjn.Mq0. Import Q2Sr QLbz.
Import Q6WR.Mq0 QrPc.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 Q30W.Mq3 QlKV.Mq5 QsKa.Mq4 QlKV.Mq1 Qiiq.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QlKV.Mq4 QrQv.Mq0 QGdd.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section PeOutA.
Variable HIx : heap_iface_A A4L.

Ltac if_vm := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
first [ replace c with true by (vm_compute; reflexivity); cbv iota | replace c with false by (vm_compute; reflexivity); cbv iota ] end.

Lemma out_checksAJ :
forall (m : word -> option byte) (tk oldl newl len lenr sb spf : Z) (pmd : Model) (mxd fl : Z) (sp0 Ff oldloc newloc bsl dsl : Z) (depth : nat)
(isd stpos choff err ucs high : word) (quote : bv 8) (l : tlevel) (pb q : Z) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32) (K : machine_state -> Prop),
rw_cells asegs m tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stpos choff err ucs high quote)) ->
pe_frameA asegs m (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv ->
rw_cells asegs m (q + 32 * Z.of_nat depth) (srec_cells l) ->
ro_cells asegs m (tk / 8 + A_SB)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
ro_cells asegs m ((q + 32 * Z.of_nat depth) / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
(depth < Z.to_nat mxd)%nat -> 1 <= mxd <= 32 -> 0 <= fl < 2^32 ->
0 < tk -> tk + 72 <= alloc_ceiling -> tk mod 16 = 0 -> 0 < q -> q + 32 * mxd <= alloc_ceiling -> q mod 16 = 0 ->
(tk + 72 <= q \/ q + 32 * mxd <= tk) -> (Ff + 256 <= tk \/ tk + 72 <= Ff) ->
(tk + 72 + 8 <= 2147450880 \/ (2 ^ 47 - 1) / 8 + 2147450880 + 1 <= tk) ->
(q + 32 * mxd + 8 <= 2147450880 \/ (2 ^ 47 - 1) / 8 + 2147450880 + 1 <= q) ->
pe_geomA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) -> alloc_ceiling <= spf ->
0 <= tl_st l <= 26 -> 0 <= tl_ss l <= 26 ->
mem_inv asegs m ->
(forall mc (a0' a1' a2' a3' a4' : word) (e' : word),
(e' = err \/ bv_unsigned (sx32 e') = 3 \/ bv_unsigned (sx32 e') = 4 \/ bv_unsigned (sx32 e') = 14) ->
rw_cells asegs mc tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stpos choff e' ucs high quote)) ->
munch [(tk + 36, tk + 40)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs K
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) a0' a1' a2' a3' a4' a5 a6 a7
(Z_to_bv 64 (shA Ff)) (Z_to_bv 64 (tk / 8 + SB2)) (Z_to_bv 64 (tk + 20)) (Z_to_bv 64 Ff) (Z_to_bv 64 (tk + 36))
(Z_to_bv 64 (tk / 8 + SB7)) (Z_to_bv 64 Ff) (Z_to_bv 64 A_SB) (Z_to_bv 64 (tk + 56)) s11
(Z_to_bv 64 (tk + 64)) t4 (Z_to_bv 64 (tk / 8 + SB8)) t6)
F (Z_to_bv 64 0x98140) fc None mc (seg_rom asegs))) ->
evt asegs K (pe_msO asegs (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) APE_OUT
x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 (Z_to_bv 64 (tk + 56)) s11 t4 t6 F fc m).
Proof.
intros until K. intros TOK FR LVL SHT SHL D32 MXB FLB Htlo Hthi Htal Hqlo Hqhi Hqal Dtq DFt APt APq GEO SPFlo ST26 SS26 MI TAIL.
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk). cbn [pf_spf pa_sp0 pa_F pf_tk] in Gspf, Gsp0, Gle, GF, GF0, GFc, Gtk.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, GAP, SAVED, FF, FSH.
unfold srec_cells in LVL. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse.
unfold pe_msO. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc]. unfold APE_OUT.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof alloc_ceiling_range as ACR.
assert (Hbse32 : bse + 32 <= q + 32 * mxd) by nia || (assert (Hbse32 : bse + 32 <= q + 32 * mxd) by lia).
assert (Hbse0 : q <= bse) by lia.
unfold shA, SB2, SB4, SB7, SB8, A_SB, A_TP in *. unfold A_SB in *.
clear GAP SAVED.

assert (JOIN : forall mc (a0x : word) (e1 : word),
(e1 = err \/ bv_unsigned (sx32 e1) = 14) ->
rw_cells asegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 choff; C4 e1; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(tk + 36, tk + 40)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs K
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) a0x (Z_to_bv 64 fl) a2 (Z_to_bv 64 (Ff + 64)) a4 a5 a6 a7
(Z_to_bv 64 (Ff / 8 + 2147450880)) (Z_to_bv 64 (tk / 8 + 2147450882)) (Z_to_bv 64 (tk + 20)) s5 (Z_to_bv 64 (tk + 36))
(Z_to_bv 64 (tk / 8 + 2147450887)) (Z_to_bv 64 Ff) (Z_to_bv 64 2147450880) (Z_to_bv 64 (tk + 56)) s11
(Z_to_bv 64 (tk + 64)) t4 (Z_to_bv 64 (tk / 8 + 2147450888)) t6)
F (Z_to_bv 64 0x980a0) fc None mc (seg_rom asegs))).
{ intros mc a0x e1 HE1 TOKc MUc WMc MIc.
assert (SLc : rw_cells asegs mc spf (pe_slotsA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) nb pj)).
{ eapply rw_cells_transport; [exact SLOTS | exact MUc | exact WMc | rewrite pe_slotsA_size; cbn [disjoint_from]; lia]. }
unfold pe_slotsA in SLc. cbn zeta in SLc. cbn [pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SLc. unfold A_SB in SLc.
assert (FFc : rw_cells asegs mc Ff (ff_cellsA cb pj)).
{ eapply rw_cells_transport; [exact FF | exact MUc | exact WMc | unfold ff_cellsA; cbn [disjoint_from cells_size csize Nat.add length]; lia]. }
unfold ff_cellsA in FFc.
assert (LVLc : rw_cells asegs mc bse [C4 (Z_to_bv 64 (tl_st l)); C4 (Z_to_bv 64 (tl_ss l)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))]).
{ eapply rw_cells_transport; [exact LVL | exact MUc | exact WMc | cbn; lia]. }
assert (SHTc : ro_cells asegs mc (tk / 8 + 2147450880)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ eapply ro_cells_transport; [exact SHT | exact MUc | cbn; lia]. }
assert (SHLc : ro_cells asegs mc (bse / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ eapply ro_cells_transport; [exact SHL | exact MUc | cbn; Z.div_mod_to_equations; lia]. }
clear SLOTS FF LVL TOK MI SHT SHL. pose proof MUc as MU. pose proof WMc as WM. clear MUc WMc.
assert (GO : forall mf (a0' a1' a2' a3' a4' : word) e',
(e' = e1 \/ bv_unsigned (sx32 e') = 3 \/ bv_unsigned (sx32 e') = 4) ->
rw_cells asegs mf tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 choff; C4 e'; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(tk + 36, tk + 40)] m mf -> wmono asegs m mf -> mem_inv asegs mf ->
evt asegs K
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) a0' a1' a2' a3' a4' a5 a6 a7
(Z_to_bv 64 (Ff / 8 + 2147450880)) (Z_to_bv 64 (tk / 8 + 2147450882)) (Z_to_bv 64 (tk + 20)) (Z_to_bv 64 Ff) (Z_to_bv 64 (tk + 36))
(Z_to_bv 64 (tk / 8 + 2147450887)) (Z_to_bv 64 Ff) (Z_to_bv 64 2147450880) (Z_to_bv 64 (tk + 56)) s11
(Z_to_bv 64 (tk + 64)) t4 (Z_to_bv 64 (tk / 8 + 2147450888)) t6)
F (Z_to_bv 64 0x98140) fc None mf (seg_rom asegs))).
{ intros mf a0' a1' a2' a3' a4' e' HE' TOK' MU' WM' MI'. apply (TAIL mf a0' a1' a2' a3' a4' e'); [| | exact MU' | exact WM' | exact MI'].
{ destruct HE' as [-> | [H | H]]; [destruct HE1 as [-> | H1]; [left; reflexivity | right; right; right; exact H1] | right; left; exact H | right; right; left; exact H]. }
unfold tok_cells_g. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote]. exact TOK'. }
clear TAIL.
step. step. if_true.
step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step. step. step. step. if_false.
step. norm_sx32. step. step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
replace (q + Z.of_nat depth * 32) with bse by lia.
asan_chkA.
step. norm_sx32.
step.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [CB0 | CBn].
-
rewrite CB0. if_vm.
step.
destruct (Z.eq_dec (tl_st l) 2) as [ST2 | STn].
+ rewrite ST2. step. if_vm. eapply GO; [left; reflexivity | exact TOKc | exact MU | exact WM | exact MIc].
+ step. if_falsex.
step.
asan_chkA.
step. norm_sx32. step.
destruct (Z.eq_dec (tl_ss l) 2) as [SS2 | SSn].
* rewrite SS2. step. if_vm. eapply GO; [left; reflexivity | exact TOKc | exact MU | exact WM | exact MIc].
* step. if_falsex. step.
step. step. step. rewrite ?sxb_zero. if_vm.
stepz.
eapply GO; [ | | exact MU | exact WM | ]; [ | eassumption | assumption]. first [right; left; vm_compute; reflexivity | right; right; vm_compute; reflexivity].
-
if_falsex.
destruct (PeanoNat.Nat.eq_dec depth 0) as [D0 | Dn].
+ subst depth. cbn [Z.of_nat] in *. step. if_false.
step. rewrite (unsigned_lit fl) by lia. step. step.
destruct (Z.eq_dec (Z.land fl 3) 1) as [F3 | F3].
* rewrite F3. if_vm. step. step.
destruct (Z.eq_dec (tl_st l) 2) as [ST2 | STn].
-- rewrite ST2. if_vm. step. step.
step. step. step. rewrite ?sxb_zero. if_vm.
stepz. eapply GO; [ | | exact MU | exact WM | ]; [ | eassumption | assumption]. first [right; left; vm_compute; reflexivity | right; right; vm_compute; reflexivity].
-- if_truex. eapply GO; [left; reflexivity | exact TOKc | exact MU | exact WM | exact MIc].
* pose proof (land3_range fl). if_truex. eapply GO; [left; reflexivity | exact TOKc | exact MU | exact WM | exact MIc].
+ step. if_truex. eapply GO; [left; reflexivity | exact TOKc | exact MU | exact WM | exact MIc]. }

pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk + 36, tk + 40)] m) as MU.
step. step. if_false.
step. rewrite (zx32_small fl) by lia.
step. rewrite (unsigned_lit fl) by lia.
step. step.
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
- step. if_true. eapply JOIN; [left; reflexivity | exact TOK | exact MU | exact WM | exact MI].
- step. if_false. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd; cbv iota end.
+ eapply JOIN; [left; reflexivity | exact TOK | exact MU | exact WM | exact MI].
+ step. step. step. rewrite ?sxb_zero. if_vm.
step. stepz.
eapply JOIN; [ | | exact MU | exact WM | ]; [ | eassumption | assumption]. right; vm_compute; reflexivity.
Qed.
End PeOutA.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIsM Q4v2 QugP QEUF QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2. Import QPZI.Mq4. Import QkMG. Import QG8z QIsM.Mq2.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QugP.Mq1 QlKV.Mq5 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSCallA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

Lemma pe_memappend_g :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (xb xn bnd : Z) (src : list byte)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts bnd -> bnd + xn <= t_co ts + 1 -> 0 <= xn < 2^31 ->
forall kB : nat, BOK pf pa ts B kB -> bv_unsigned ra mod 2 = 0 ->
bytes_at asegs m xb src -> Z.of_nat (length src) = xn -> 0 <= xb ->
src_locA ((t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) ((pa_F pa, 2) :: FRS) xb xn ->
(0 < xn -> unpoisoned asegs m A_SB xb xn) ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2 ->
(r = xn /\ PBOKat m2 (ts_pbs ts pbs2) (bnd + xn) /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 xb) (Z_to_bv 64 xn) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9a0ac) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK Hbn Hn kB BK RA SRC SRCL Hb0 SLOC UNP K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
destruct PBK as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1 & Hbp).
pose proof (proj1 REST1) as HP1. unfold pe_blocksA, tstate_blocks in HP1. rewrite Epbs in HP1. cbn [app] in HP1.
pose proof REST1 as (_ & _ & _ & ST1 & ERR1 & _ & _ & _ & _ & _ & _ & BUD1).
assert (Hbp0 : 0 <= bpos) by (destruct CORE1 as (C1 & _); lia).
pose proof (BOK_memappend pf pa ts B kB (t_pb ts) buf cap bpos xn BK Epbs BSL Hbp0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BUDM.
assert (SPF1 : lo <= pf_spf pf - 112 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF1 as (SPF1 & SPF2 & SPF3 & SPF4).
set (LBc := (t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) in *.
eapply MAPP with (lo := lo) (b := xb) (src := src) (n := xn) (pb := t_pb ts) (buf := buf) (bpos := bpos) (cap := cap);
[ exact HP1 | exact CORE1 | exact Hn | exact SRC | exact SRCL | exact Hb0 | exact SLOC | exact UNP
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2
| rewrite unsigned_lit by lia; exact SPF3
| exact ERR1 | reflexivity | exact RA | reflexivity | reflexivity | reflexivity
| exact (proj1 BUDM) | ].
intros ms2 md2 A2 (m2 & r & errv2 & buf' & cap' & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
set (pbs2 := [(t_pb ts, 16); (buf', cap')]).
assert (INq2 : In (q, 32 * pf_mxd pf) LBc) by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (pf_tk pf, 72) LBc) by (apply in_or_app; right; left; reflexivity).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR2 | lia | exact GEO | | | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk2 | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl INq2))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (BUD2 : PE_BUD pf pa (ts_pbs ts pbs2) B2).
{ destruct OUT2 as [(_ & Ec & _) | (_ & Eb & Ec & _ & _)].
- subst cap'. exact (BOK_weak _ _ _ _ _ (proj2 BUDM buf' B2 HB2 HD2)).
- subst buf' cap'. unfold pbs2. change 16 with PB_SZ. rewrite <- Epbs. replace (ts_pbs ts (t_pbs ts)) with ts by (destruct ts; reflexivity).
exact (BOK_memappend_fail pf pa ts B B2 kB (t_pb ts) buf cap bpos xn BK Epbs Hbp0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HB2 HD2). }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) errv2).
{ eapply (PE_REST_A_call_pb HIx GA GA_pres) with (ts := ts) (LBc := LBc);
[exact STC | exact REST1 | exact VM2 | exact HPR2 | | | exact ST2 | exact ERR2 | exact BUD2].
- unfold LBc; intros b Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]].
- unfold pe_blocksA, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs]; exact HP2. }
assert (PBany : pbuf asegs m2 pbs2 (t_pb ts)).
{ destruct OUT2 as [(_ & _ & PBS) | (_ & -> & -> & _ & PC)]; [eapply pbufc_pbuf; exact PBS|].
exists buf, bpos, cap, pre, post. split; [reflexivity|]. split; [exact Lpre | exact PC]. }
assert (INV2 : PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2).
{ split; [| exact REST2]. unfold PE_CORE_A, ts_pbs; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR2]. }
assert (Hbl : 0 <= bpos <= Z.of_nat (length (pre ++ [Z_to_bv 8 0] ++ post))) by (destruct CORE1 as (C1 & _ & C3 & _); lia).
eapply (K m2 md2 A2 B2 pbs2 errv2 r); [exact INV2 | | exact FS2 | exact FRM2].
destruct OUT2 as [(-> & Ec & PBS) | (-> & -> & -> & _ & _)].
- left. split; [reflexivity|]. split.
+ eapply (PBOKat_appended m2 _ (bnd + xn) (t_pb ts) buf' cap' bpos (pre ++ [Z_to_bv 8 0] ++ post) src); [reflexivity | reflexivity | exact PBS | exact Hbl |]. lia.
+ unfold pbs2. rewrite Ec. exact (proj2 BUDM buf' B2 HB2 HD2).
- right. split; [reflexivity|]. unfold pbs2. change 16 with PB_SZ. symmetry. exact Epbs.
Qed.

Lemma pe_memappend_c :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts 0 -> forall kB : nat, BOK pf pa ts B kB -> t_co ts < pf_len pf -> bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2 ->
(r = 1 /\ PBOK m2 (ts_pbs ts pbs2) 1 /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9a0ac) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK kB BK Hco RA K.
pose proof STC as (_ & _ & GEO & _). pose proof GEO as (_ & _ & _ & GF & GF0 & _).
pose proof INV as [(_ & _ & _ & _ & _ & _ & _ & _ & FR1) _].
eapply (pe_memappend_g pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T (pa_F pa + 64) 1 (t_co ts + 0) [cb]);
[exact STC | exact BSL | exact INV | exact PBK | lia | lia | exact BK | exact RA
| exact (pe_frameA_cbyte _ _ _ _ _ _ _ FR1) | reflexivity | lia
| right; first [left | idtac]; exists (pa_F pa), 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| intros _; exact (pe_frameA_c_unpoisoned _ _ _ _ _ _ _ GEO FR1) |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
eapply (K m2 md2 A2 B2 pbs2 errv2 r); [exact INV2 | | exact FS2 | exact FRM2].
destruct OUT2 as [(-> & PBK2 & BK2) | [-> E]]; [left | right; split; [reflexivity | exact E]].
split; [reflexivity|]. split; [| exact BK2]. unfold PBOK, ts_pbs. cbn [t_co]. replace (t_co ts + 1) with (t_co ts + 0 + 1) by lia. exact PBK2.
Qed.

Lemma pe_memappend_p :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (co0 xn : Z)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts co0 -> 0 <= co0 -> 0 <= xn -> co0 + xn <= t_co ts + 1 -> co0 + xn <= pf_len pf -> 0 < pf_len pf ->
forall kB : nat, BOK pf pa ts B kB -> bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2 ->
(r = xn /\ PBOKat m2 (ts_pbs ts pbs2) (co0 + xn) /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 xn) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9a0ac) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK Hco0 Hxn Hle1 Hle2 Hlen0 kB BK RA K.
pose proof STC as (_ & _ & _ & _ & _ & LEN & SB0 & _).
pose proof INV as [(_ & _ & CO & _) REST]. pose proof REST as (HP & _ & _ & _ & _ & STR & PLEN & SBin & _).
destruct SBin as [L0 | PL]; [exfalso; lia|].
pose proof (bytes_at_sub A4H m (pf_sb pf) payload (Z.to_nat co0) (Z.to_nat xn) STR ltac:(lia)) as SRC. cbn [hl_segs hla_base A4L A4H] in SRC. rewrite Z2Nat.id in SRC by lia.
eapply (pe_memappend_g pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T (pf_sb pf + co0) xn co0 (firstn (Z.to_nat xn) (skipn (Z.to_nat co0) payload)));
[exact STC | exact BSL | exact INV | exact PBK | exact Hle1 | lia | exact BK | exact RA | exact SRC
| rewrite length_firstn, length_skipn; lia | lia | | | exact K].
- destruct PL as [([b0 n0] & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)]; cbn [blk_addr blk_size fst snd] in *.
+ left. exists b0, n0. split; [apply in_or_app; right; right; right; exact Hb | lia].
+ right. first [left | idtac]. exists Fh, kh. split; [right; exact HFh | lia].
- intros Hn0. destruct PL as [([b0 n0] & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & UPS)]; cbn [blk_addr blk_size fst snd] in *.
+ eapply (unpoisoned_of_blk HIx); [exact HP | unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb | lia | lia | exact Hn0].
+ eapply unpoisoned_sub2; [exact UPS | lia | lia | exact Hn0].
Qed.

Lemma pe_pbreset :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (Q : machine_state -> Prop)
(ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 (a1' a2' a3' a4' : word),
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts cb nb pj sv errv ->
PBOK m2 ts 0 -> pbufc asegs m2 (t_pbs ts) (t_pb ts) [] ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts + 8)) a1' a2' a3' a4' a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9a64c) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC INV RA K.
destruct ts as [depth levels co pbx pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
destruct PB as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1).
pose proof HP as HP1. unfold pe_blocksA, tstate_blocks in HP1. rewrite Epbs in HP1. cbn [app] in HP1.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
set (LBc := (objbs ++ concat (map lvl_blocks levels)) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) in *.
eapply (printbuf_reset_A HIx) with (lo := lo); [exact HP1 | exact CORE1 | rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; lia | exact RA |].
intros a1' a2' a3' a4' m2 MU WM MI2 CORE2 ST2. rewrite unsigned_lit in MU, ST2 by lia.
set (pb := pbx) in *.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as ND. cbn [map app blk_addr fst] in ND.
apply List.NoDup_cons_iff in ND as [NDpb ND]. apply List.NoDup_cons_iff in ND as [NDbuf ND].
assert (Npb : forall k, ~ In (pb, k) (LBc ++ LM)) by (intros k Hin; apply NDpb; right; exact (in_map blk_addr _ _ Hin)).
assert (Nbuf : forall k, ~ In (buf, k) (LBc ++ LM)) by (intros k Hin; apply NDbuf; exact (in_map blk_addr _ _ Hin)).
assert (INpb : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LBc) ++ LM)) by (left; reflexivity).
assert (INbuf : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LBc) ++ LM)) by (right; left; reflexivity).
pose proof (blk_not_fr_iv HIx _ _ _ _ _ _ _ _ _ HP1 INpb) as NFpb. pose proof (blk_not_fr_iv HIx _ _ _ _ _ _ _ _ _ HP1 INbuf) as NFbuf.
assert (Hcap0 : 0 < cap) by (destruct CORE1 as (_ & C2 & _); lia).
assert (HW : Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= pf_spf pf)
\/ (exists a n, In (a, n) (((pb, PB_SZ) :: (buf, cap) :: LBc) ++ LM) /\ ~ In (a, n) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) ((pa_F pa, 2) :: FRS) /\ ~ In (F, fr_size k - 8) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) /\ ~ In (shad A4L F, fr_shadow_len k) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) /\
((F <= fst iv /\ snd iv <= F + fr_size k) \/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k))))
[(buf, buf + 1); (pb + 8, pb + 12); (pf_spf pf - 16, pf_spf pf)]).
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd].
- right; left. exists buf, cap. split; [exact INbuf|]. split; [| lia].
intros Hin. rewrite app_assoc in Hin. apply in_app_or in Hin as [Hin | Hin]; [exact (Nbuf _ Hin) | exact (NFbuf Hin)].
- right; left. exists pb, PB_SZ. split; [exact INpb|]. split; [| lia].
intros Hin. rewrite app_assoc in Hin. apply in_app_or in Hin as [Hin | Hin]; [exact (Npb _ Hin) | exact (NFpb Hin)].
- left. lia. }
assert (HPRc : heap_pres A4H (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2).
{ eapply (heap_pres_of_munch A4H); [exact MU | exact WM |].
eapply (client_outsideF HIx); [exact HP1 | | lia | exact HW].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb | Hb]; [left | right; exact Hb].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; right; right; exact Hb | apply in_or_app; right; exact Hb]. }
set (ts := TST depth levels co pb pbs x obj objs objbs) in *.
assert (HP2 : HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m2 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI2]. eapply (frame_writes_okF A4L HIx); [exact HP | exact MU |].
unfold pe_blocksA, tstate_blocks, ts; cbn [t_pbs t_objbs t_levels]. rewrite Epbs. cbn [app].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd].
- right; left. exists buf, cap. split; [exact INbuf | lia].
- right; left. exists pb, PB_SZ. split; [exact INpb | lia].
- left. lia. }
assert (INq2 : In (q, 32 * pf_mxd pf) LBc) by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (pf_tk pf, 72) LBc) by (apply in_or_app; right; left; reflexivity).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPRc | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPRc) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk2 | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPRc (in_or_app _ _ _ (or_introl INq2))) in TSK; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK.
assert (ERR2 : rw_cells asegs m2 A_ERRNO [C4 errv]).
{ pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP1 INpb) as Ipb. pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP1 INbuf) as Ibuf.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Ipb, Ibuf. pose proof alloc_ceiling_range as ACR.
eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat disjoint_from fst snd]. unfold A_ERRNO, A_TP. repeat split; try lia. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts errv).
{ eapply (PE_REST_A_call_pb HIx GA GA_pres) with (ts := ts) (LBc := LBc) (co2 := co) (pb2 := pb) (pbs2 := pbs) (x2 := x);
[exact STC | exact REST | apply model_vm_only_refl | exact HPRc | | exact HP2 | exact ST2 | exact ERR2 | exact BUD].
unfold LBc, ts; cbn [t_objbs t_levels]; intros b Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]]. }
assert (PBC2 : pbufc asegs m2 pbs pb []).
{ exists buf, 0, cap, (skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)). split; [exact Epbs|]. split; [reflexivity | exact CORE2]. }
eapply (K m2 a1' a2' a3' a4'); [| | exact PBC2].
- split; [| exact REST2]. unfold PE_CORE_A, ts; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [eapply pbufc_pbuf; exact PBC2|]. split; [exact Hpb|]. split; [exact TSK | exact FR2].
- exists buf, 0, cap, [], (skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)). unfold ts; cbn [t_pbs t_pb t_co]. split; [exact Epbs|]. split; [reflexivity|]. split; [exact CORE2 | lia].
Qed.

Hypothesis SHRINK : jo_array_shrink_A2 HIx.

Hypothesis AADD : jo_array_add_A2 HIx.

Lemma pe_free_null_c :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> BOK pf pa ts B (S (Z.to_nat 512 + nB)) ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 (r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts cb nb pj sv errv ->
PBOKat m2 ts kP -> BOK pf pa ts B2 nB ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 r w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x632c4) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK BK RA K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
pose proof REST1 as (HP1 & LV1 & OBJ1 & ST1 & ERR1 & _).
assert (SPF : lo <= pf_spf pf - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf < hiA_top A4L HIx + 64 /\ 0 <= pf_spf pf < 2^62).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4).
assert (COST : 512 <= bB B).
{ pose proof (BOK_ledger_nonneg _ _ _ _ _ BK) as L0. pose proof BK as (H1 & _ & H3 & _). unfold bneed in H1.
pose proof (K_ev_pos pf). pose proof (Zle_0_nat (length (tstate_blocks ts))).
replace (K_ev pf * Z.of_nat (S (Z.to_nat 512 + nB))) with (K_ev pf * Z.of_nat nB + 513) in H1 by (unfold K_ev; lia).
pose proof (Z.mul_nonneg_nonneg (K_ev pf) (Z.of_nat nB) ltac:(lia) ltac:(lia)). unfold K_free, K_exit in *. lia. }
eapply (hiA_free A4L HIx) with (p := 0) (u := UWpaid) (lo := lo) (errv := errv);
[ exact HP1 | left; reflexivity | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; cbn [hl_stack_A A4L]; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | reflexivity
| split; cbn; exact I  | exact COST | cbn; pose proof (proj2 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)); lia | ].
intros ms2 m2 md2 A2 r RS2 VM2 ST2 HPR2 ERR2 HP2.
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & ->).
cbn [hl_segs hl_tp hla_base A4L A4H Z.eqb] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (Enot : forall n, ~ In (0, n) (pe_blocksA pf q LB0 ts)).
{ intros n Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ 0 n HP1 (in_or_app _ LM _ (or_introl Hin))) as (_ & _ & H0 & _). lia. }
rewrite (lb_remove_notinS 0 _ Enot) in HPR2, HP2.
set (B2 := charge B 512 0) in *.
assert (BK2 : BOK pf pa ts B2 nB) by (eapply (BOK_pay pf pa ts B B2 nB 512); [exact BK | pose proof (K_ev_pos pf); lia | cbn; lia | cbn; lia]).
set (RB := (tstate_blocks ts ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0)).
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB; intros b Hb; apply in_or_app; right; right; right; exact Hb).
change (pe_blocksA pf q LB0 ts) with RB in HPR2, HP2.
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR2 | lia | exact GEO | | | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl INq))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (PBKa : PBOKat m2 ts kP).
{ eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts errv).
{ eapply (PE_REST_A_callG HIx GA GA_pres) with (ts := ts) (LBc := RB); [exact STC | exact REST1 | exact VM2 | exact HPR2 | exact LB0R | exact HP2 | | | exact ST2 | exact ERR2 | exact (BOK_weak _ _ _ _ _ BK2)].
- intros i li Hli. eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG |].
intros b Hb. unfold RB, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- destruct (zin (cur_st ts) [ST_array_add; ST_ovadd]); [| exact OBJ1].
eapply (jopt_agree asegs A4F); [exact OBJ1 | exact AG |]. unfold RB, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb. }
eapply (K m2 md2 A2 B2 r); [| exact PBKa | exact BK2].
split; [| exact REST2]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOKat_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR2].
Qed.

Hypothesis PUT : put_stmt_A HIx.

Lemma pe_put_null_c :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts kP -> BOK pf pa ts B nB ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 (r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts cb nb pj sv errv ->
PBOKat m2 ts kP -> BOK pf pa ts B2 nB ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 r w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9a78c) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC INV PBK BK RA K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
pose proof REST1 as (HP1 & LV1 & OBJ1 & ST1 & ERR1 & _).
assert (SPF : lo <= pf_spf pf - put_stk_A /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62).
{ unfold put_stk_A. clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF as (SPF1 & SPF2 & SPF3 & SPF4).
set (RB := pe_blocksA pf q LB0 ts) in *.
eapply PUT with (LB := RB) (BS := []) (s := None) (p := 0) (rc := 1) (lo := lo) (errv := errv);
[ exact HP1 | split; reflexivity | reflexivity | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2 | rewrite unsigned_lit by lia; exact SPF3 | exact ERR1 | reflexivity | exact RA
| cbn [put_costA]; exact (proj1 (heapA_budget A4L HIx _ _ _ _ _ _ _ HP1)) | ].
intros ms2 md2 A2 (m2 & r & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H put_costA] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
assert (HP2 : HEAPA A4L HIx A2 RB LM ((pa_F pa, 2) :: FRS) B2 m2 md2).
{ destruct OUT2 as [(_ & H) | (s' & E & _)]; [exact H | discriminate E]. }
assert (BK2 : BOK pf pa ts B2 nB) by (eapply BOK_mono; [| | exact BK]; lia).
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR2 | lia | exact GEO | | | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl INq))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (PBKa : PBOKat m2 ts kP).
{ eapply PBOKat_agree; [exact PBK | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts errv).
{ eapply (PE_REST_A_callG HIx GA GA_pres) with (ts := ts) (LBc := RB); [exact STC | exact REST1 | exact VM2 | exact HPR2 | exact LB0R | exact HP2 | | | exact ST2 | exact ERR2 | exact (BOK_weak _ _ _ _ _ BK2)].
- intros i li Hli. eapply (lvl_cur_agree asegs A4F); [exact (LV1 i li Hli) | exact AG |].
intros b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- destruct (zin (cur_st ts) [ST_array_add; ST_ovadd]); [| exact OBJ1].
eapply (jopt_agree asegs A4F); [exact OBJ1 | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb. }
eapply (K m2 md2 A2 B2 r); [| exact PBKa | exact BK2 | exact FS2 | exact FRM2].
split; [| exact REST2]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact (PBOKat_pbuf _ _ _ PBKa)|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR2].
Qed.
End PeSCallA.
End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QCcH Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QRUw.Mq0 QkMG. Import QG8z Qdyh.Mq2 QLbz.
Import Q7UD QlKV.Mq2 QrQv.Mq2 QEUF.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Pins2.
Variable segs : list Segment.
Variable fn : fnaddrs.
Lemma jfresh_arr_new_jval : forall m BS p rc, jval segs fn (Sarr []) m BS p rc -> length BS = 3%nat -> jfresh (Sarr []) BS 24.
Proof.
intros m BS p rc J L. cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (a & ABS & ps & KBS & -> & _ & AL & _ & LK & _)).
destruct KBS as [|x KBS]; [| cbn in LK; lia]. destruct AL as (arr & size & junk & -> & _). subst BS. cbn [concat app] in L |- *.
destruct PBS as [|x PBS]; [| cbn in L; lia]. apply jtx_arr_new; reflexivity.
Qed.
Lemma jfresh_obj_new_jval : forall m BS p rc, jval segs fn (Sobj []) m BS p rc -> length BS = 3%nat -> jfresh (Sobj []) BS 24.
Proof.
intros m BS p rc J L. cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (t & TBS & kvs & KBS & -> & _ & LH & LKV & LK & _)).
destruct KBS as [|x KBS]; [| cbn in LK; lia]. destruct LH as (tbl & size & es & svs & Ekv & -> & _).
destruct es as [|e es]; [| subst kvs; cbn in LKV; lia]. subst BS. unfold lh_blocks in *. cbn [map concat app] in L |- *.
destruct PBS as [|x PBS]; [| cbn in L; lia]. apply jtx_obj_new; reflexivity.
Qed.
End Pins2.

Lemma PBOKat_of_pbufc_nil : forall m ts, pbufc asegs m (t_pbs ts) (t_pb ts) [] -> PBOKat m ts 0.
Proof.
intros m ts (buf & bpos & size & post & E & L & C). exists buf, bpos, size, [], post. split; [exact E|]. split; [exact L|]. split; [exact C | cbn in L; lia].
Qed.
Lemma PBOK_at0 : forall m ts, PBOKat m ts 0 -> PBOK m ts (- t_co ts).
Proof. intros m ts H. unfold PBOK. replace (t_co ts + - t_co ts) with 0 by lia. exact H. Qed.
Lemma PBOK_to0 : forall m ts, PBOK m ts (- t_co ts) -> PBOKat m ts 0.
Proof. intros m ts H. unfold PBOK in H. replace (t_co ts + - t_co ts) with 0 in H by lia. exact H. Qed.

End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QCcH Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QkMG. Import QG8z Qdyh.Mq2 QLbz.
Import QlKV.Mq2 QrQv.Mq2 QEUF.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma jwl_nth_le : forall levels n i l W a, jwl levels n = Some W -> nth_error levels i = Some l -> (i < n)%nat -> lw l = Some a -> a <= W.
Proof.
induction levels as [|h t IH]; intros n i l W a H Hn Hi La; [destruct i; discriminate Hn|].
destruct n as [|n]; [lia|]. cbn [jwl] in H. destruct (lw h) as [ah|] eqn:E1; [| discriminate H]. destruct (jwl t n) as [b|] eqn:E2; [| discriminate H]. injection H as <-.
destruct i as [|i]; cbn [nth_error] in Hn.
- injection Hn as ->. rewrite La in E1. injection E1 as <-. pose proof (jwl_nonneg _ _ _ E2). lia.
- pose proof (IH n i l b a E2 Hn ltac:(lia) La). pose proof (lw_nonneg _ _ E1). lia.
Qed.

Lemma JOUT_level : forall len ts l s,
JOUT len ts -> bv_unsigned (sx32 (ts_err (t_x ts))) = 0 -> nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cs l = Some s ->
exists w, jtx s (tl_cbs l) = Some (w, []) /\ w <= 26 * len + 64.
Proof.
intros len ts l s J E Hl Hcs. destruct (J E) as (W & EW & LE). unfold jw in EW.
destruct (jwl (t_levels ts) (S (t_depth ts))) as [A|] eqn:EA; [| discriminate EW]. destruct (ow _ _ _) as [b|] eqn:Eb; [| discriminate EW]. injection EW as <-.
assert (B0 : 0 <= b) by (unfold ow in Eb; destruct (zin _ _); [exact (vw_nonneg _ _ _ Eb) | injection Eb as <-; lia]).
destruct (jwl_nth _ _ _ _ _ EA Hl ltac:(lia)) as (a & La). pose proof (jwl_nth_le _ _ _ _ _ _ EA Hl ltac:(lia) La) as LA.
unfold lw in La. rewrite Hcs in La. cbn [vw] in La. destruct (jtx s (tl_cbs l)) as [[w [|? ?]]|] eqn:EJ; try discriminate La. injection La as <-.
exists w. split; [reflexivity|]. pose proof (nw_nonneg (tl_nbs l)). unfold JC1, JC0 in LE. lia.
Qed.

End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QkMG. Import QG8z QLbz Q2Sr.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 Qiiq.Mq0 Q1Ey Q1Y6.Mq2 QrQv.Mq2 QEUF QlKV.Mq2 QEUF.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition PBS_dead : list Z :=
[ST_eatws; ST_start; ST_finish; ST_array; ST_array_add; ST_array_sep; ST_ofs; ST_ofend; ST_ovalue; ST_ovadd; ST_osep; ST_array_after_sep; ST_ofs_after_sep].
Definition PBSst (st : Z) : Z :=
if st =? ST_string_escape then -1
else if st =? ST_escape_unicode then -2
else if st =? ST_esc_need_escape then -3
else if st =? ST_esc_need_u then -4
else if zin st PBS_dead then 1 else 0.
Definition PBS (ts : tstate) : Z := PBSst (cur_st ts).

Definition BTOK (pf : pe_fix) : Z := 16 * Z.max 0 (pf_len pf) + 8192.
Definition BRX (pf : pe_fix) : Z := 16 * Z.max 0 (pf_len pf) + 11008.

Definition bcls0 (st : Z) : Z :=
if zin st [ST_array; ST_array_after_sep; ST_ovalue] then 5
else if zin st [ST_start; ST_null; ST_boolean; ST_inf; ST_number; ST_string] then 4
else if st =? ST_finish then 3
else if st =? ST_array_add then 2
else if zin st [ST_array_sep; ST_ofield; ST_ofend; ST_ovadd] then 1
else 0.
Definition bval (pf : pe_fix) (c : Z) : Z :=
if c =? 5 then 2 * BTOK pf + 2304 else if c =? 4 then 2 * BTOK pf + 1792 else if c =? 3 then BTOK pf + 1792 else if c =? 2 then BTOK pf + 1280 else if c =? 1 then BTOK pf else 0.
Definition bres0 (pf : pe_fix) (st : Z) : Z := bval pf (bcls0 st).

Definition bvia (st : Z) : bool := zin st [ST_eatws; ST_comment_start; ST_comment; ST_comment_eol; ST_comment_end; ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u].
Definition bres (pf : pe_fix) (st ss : Z) : Z := if bvia st then bres0 pf ss else bres0 pf st.
Lemma bval_5 : forall pf, bval pf 5 = 2 * BTOK pf + 2304. Proof. reflexivity. Qed.
Lemma bval_4 : forall pf, bval pf 4 = 2 * BTOK pf + 1792. Proof. reflexivity. Qed.
Lemma bval_3 : forall pf, bval pf 3 = BTOK pf + 1792. Proof. reflexivity. Qed.
Lemma bval_2 : forall pf, bval pf 2 = BTOK pf + 1280. Proof. reflexivity. Qed.
Lemma bval_1 : forall pf, bval pf 1 = BTOK pf. Proof. reflexivity. Qed.
Lemma bval_0 : forall pf, bval pf 0 = 0. Proof. reflexivity. Qed.
Definition bx (pf : pe_fix) (ts : tstate) : nat := Z.to_nat (BRX pf * (pf_len pf - t_co ts) + bres pf (cur_st ts) (cur_ss ts)).
Definition bxb (pf : pe_fix) (ts : tstate) : nat := Z.to_nat (BRX pf * (pf_len pf - t_co ts - 1) + bres pf (cur_st ts) (cur_ss ts)).
Definition bloop (pf : pe_fix) (ts : tstate) : nat := (mloop pf ts + bx pf ts)%nat.
Definition bredo (pf : pe_fix) (ts : tstate) : nat := (mredo pf ts + bx pf ts)%nat.
Definition bbrk (pf : pe_fix) (ts : tstate) : nat := (mbrk pf ts + bxb pf ts)%nat.
Lemma BTOK_ge : forall pf, 8192 <= BTOK pf. Proof. intros pf. unfold BTOK. lia. Qed.
Lemma BRX_eq : forall pf, BRX pf = BTOK pf + 2816. Proof. intros pf. unfold BRX, BTOK. lia. Qed.
Lemma bval_range : forall pf c, 0 <= bval pf c <= 2 * BTOK pf + 2304. Proof. intros pf c. pose proof (BTOK_ge pf). unfold bval. repeat (destruct (_ =? _)); lia. Qed.
Lemma bres0_nonneg : forall pf st, 0 <= bres0 pf st. Proof. intros pf st. unfold bres0. pose proof (bval_range pf (bcls0 st)). lia. Qed.
Lemma bres_nonneg : forall pf st ss, 0 <= bres pf st ss. Proof. intros pf st ss. unfold bres. destruct (bvia st); apply bres0_nonneg. Qed.
Lemma bres_self : forall pf s, bres pf s s = bres0 pf s. Proof. intros pf s. unfold bres. destruct (bvia s); reflexivity. Qed.

Lemma bx_ge : forall pf ts, t_co ts <= pf_len pf -> (Z.to_nat (bres pf (cur_st ts) (cur_ss ts)) <= bx pf ts)%nat.
Proof. intros pf ts H. unfold bx. pose proof (BTOK_ge pf). pose proof (BRX_eq pf). pose proof (bres_nonneg pf (cur_st ts) (cur_ss ts)). pose proof (Z.mul_nonneg_nonneg (BRX pf) (pf_len pf - t_co ts) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma bx_mono2 : forall pf r r' k k', r' <= r -> k' <= k -> (Z.to_nat (BRX pf * r' + k') <= Z.to_nat (BRX pf * r + k))%nat.
Proof. intros pf r r' k k' H1 H2. pose proof (BTOK_ge pf). pose proof (BRX_eq pf). assert (BRX pf * r' <= BRX pf * r) by (apply Z.mul_le_mono_nonneg_l; lia). lia. Qed.
Lemma bx_mono3 : forall pf r r' k k' C, r' <= r -> k' + Z.max 0 C <= k -> (Z.to_nat (BRX pf * r' + k') <= Z.to_nat (BRX pf * r + k) - Z.to_nat C)%nat.
Proof. intros pf r r' k k' C H1 H2. pose proof (BTOK_ge pf). pose proof (BRX_eq pf). assert (BRX pf * r' <= BRX pf * r) by (apply Z.mul_le_mono_nonneg_l; lia). lia. Qed.
Lemma bx_mono4 : forall pf r r' k k' C, r' + 1 <= r -> k' + Z.max 0 C <= k + BRX pf -> (Z.to_nat (BRX pf * r' + k') <= Z.to_nat (BRX pf * r + k) - Z.to_nat C)%nat.
Proof. intros pf r r' k k' C H1 H2. pose proof (BTOK_ge pf). pose proof (BRX_eq pf). assert (BRX pf * r' <= BRX pf * (r - 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. Qed.

Lemma bsplit_S : forall a b m x C : nat, (a <= S m)%nat -> (b <= x)%nat -> (C <= x)%nat -> (a + b <= S (C + (m + (x - C))))%nat.
Proof. intros. lia. Qed.

Definition EUS : list Z := [ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u].
Definition UCSV (x : tscal) : Z := bv_unsigned (ts_ucs x) mod 2^32.
Definition euok_b (x : tscal) : bool := (SPV x =? 0) && (UCSV x <? 65536).
Definition OBJW (pj : pe_junkA) (ts : tstate) : Prop :=
(zin (cur_st ts) [ST_array_add; ST_ovadd] = true -> pj_obj pj = Z_to_bv 64 (t_obj ts)) /\
(zin (cur_st ts) EUS = true -> SPV (t_x ts) = 0 /\ UCSV (t_x ts) < 65536).

Definition NAO (ts : tstate) : Prop := (zin (cur_st ts) [ST_array_add; ST_ovadd] || (zin (cur_st ts) EUS && negb (euok_b (t_x ts)))) = false.
Lemma OBJW_of_NAO : forall pj ts, NAO ts -> OBJW pj ts.
Proof.
intros pj ts H. unfold NAO in H. apply orb_false_iff in H as [H1 H2]. split.
- intros E. rewrite H1 in E. discriminate E.
- intros E. rewrite E in H2. cbn [andb] in H2. apply negb_false_iff in H2. unfold euok_b in H2. apply andb_true_iff in H2 as [HA HB].
split; [apply Z.eqb_eq; exact HA | apply Z.ltb_lt; exact HB].
Qed.
Lemma NAO_plain : forall ts, zin (cur_st ts) [ST_array_add; ST_ovadd] = false ->
zin (cur_st ts) [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false -> NAO ts.
Proof.
intros ts H1 H2. unfold NAO. rewrite H1. cbn [orb]. apply andb_false_iff. left.
cbn [zin] in H2. apply orb_false_iff in H2 as [_ H2]. unfold EUS. cbn [zin]. exact H2.
Qed.
Lemma NAO_eu : forall ts, zin (cur_st ts) [ST_array_add; ST_ovadd] = false -> SPV (t_x ts) = 0 -> UCSV (t_x ts) < 65536 -> NAO ts.
Proof.
intros ts H1 HS HU. unfold NAO. rewrite H1. cbn [orb]. apply andb_false_iff. right. apply negb_false_iff. unfold euok_b.
apply andb_true_iff. split; [apply Z.eqb_eq; exact HS | apply Z.ltb_lt; exact HU].
Qed.

Definition PBJ (m : word -> option byte) (ts : tstate) (k a : Z) : Prop := exists g, PBOKat m ts g /\ g <= t_co ts + k /\ JL ts g a.
Lemma PBJ_PBOK : forall m ts k a, PBJ m ts k a -> PBOK m ts k.
Proof. intros m ts k a (g & P & Hg & _). unfold PBOK. eapply PBOKat_weaken; [exact Hg | exact P]. Qed.
Lemma PBOKat_nonneg : forall m ts b, PBOKat m ts b -> 0 <= b.
Proof. intros m ts b (buf & bpos & size & pre & post & _ & L & _ & Hb). lia. Qed.

Lemma JOUT_of_PBJ : forall len m ts ts' k a, PBJ m ts k a -> a <= len -> t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts ->
(zin (cur_st ts) [ST_array_add; ST_ovadd] = true -> t_objs ts' = t_objs ts /\ t_objbs ts' = t_objbs ts) -> JOUT len ts'.
Proof. intros len m ts ts' k a (g & P & _ & J) Ha E1 E2 E3. eapply (JOUT_of_JL len ts ts' g a J (PBOKat_nonneg _ _ _ P) Ha). apply jw_same; assumption. Qed.

Section PeSKontA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Let tk56 := Z_to_bv 64 (pf_tk pf + 56).
Let cadr := Z_to_bv 64 (pa_F pa + 64).

Definition KLOOP_S (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t4 : word) (F : bvmap 5 word) (fc : bv 32),
(mloop pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv ->
cur_st ts <> ST_number -> SPOK ts 0 -> tdepth_ok ts ->
(pf_lenr pf <> pf_len pf -> t_co ts < pf_len pf) ->
PBJ m ts (PBS ts) (t_co ts) -> BOK pf pa ts B (bloop pf ts) -> NAO ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_LOOP (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 tk56 t4 F fc m).

Definition KREDO_S (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
(mredo pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
NUMC_A ts m -> SPOK ts 0 -> tdepth_ok ts ->
PBJ m ts (PBS ts) (t_co ts) -> BOK pf pa ts B (bredo pf ts) -> OBJW pj ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 tk56 cadr F fc m).

Definition KBRK_S (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
(mbrk pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
cur_st ts <> ST_number -> SPOK ts 1 -> tdepth_ok ts ->
PBJ m ts (PBS ts + 1) (t_co ts + 1) -> BOK pf pa ts B (bbrk pf ts) -> NAO ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 tk56 cadr F fc m).

Definition KADV_S (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word) (av : Z)
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
(mbrk pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
cur_st ts <> ST_number -> SPOK ts 1 -> tdepth_ok ts ->
0 <= av < 2^64 -> (av = 0 <-> bv_unsigned cb = 0) ->
PBJ m ts (PBS ts + 1) (t_co ts + 1) -> BOK pf pa ts B (bbrk pf ts) -> NAO ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_ADV (t_co ts) gp t0 t1 t2 (Z_to_bv 64 av) a1 a2 a3 a4 a5 a6 a7 s5 tk56 cadr F fc m).

Definition KALL_S (n : nat) : Prop := KLOOP_S n /\ KREDO_S n /\ KBRK_S n /\ KADV_S n.

Definition KOUT_S : Prop :=
forall (ts : tstate) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts -> JOUT (pf_len pf) ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msO asegs pf pa APE_OUT x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 tk56 s11 t4 t6 F fc m).
Definition KERR2_S : Prop :=
forall (ts : tstate) (LK : list blk) (e : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
0 < e < 2^31 ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1 gp t0 t1 t2 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 F fc m).

Definition CASE_S (st : Z) : Prop :=
forall (n : nat) (ts : tstate) (l : tlevel) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = st ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
NUMC_A ts m -> SPOK ts 0 -> tdepth_ok ts ->
PBJ m ts (PBS ts) (t_co ts) -> BOK pf pa ts B (bredo pf ts) -> OBJW pj ts ->
bytes_at asegs me UTF8REP_ADDR_A utf8rep ->
CSTR_OK pf payload ->
fsaved F0 F -> frm0 fc ->
(mredo pf ts <= n)%nat -> KALL_S n ->
KOUT_S -> KERR2_S ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA st) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) cadr F fc m).
End PeSKontA.

Lemma PBSst_plain_range : forall st, zin st [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false -> 0 <= PBSst st <= 1.
Proof.
intros st H. unfold PBSst. cbn [zin] in H. apply orb_false_iff in H as [H1 H]. apply orb_false_iff in H as [H2 H]. apply orb_false_iff in H as [H3 H]. apply orb_false_iff in H as [H4 _].
rewrite H1, H2, H3, H4. destruct (zin st PBS_dead); lia.
Qed.
End RC__1.

Ltac pbs_norm :=
repeat match goal with
| |- context [PBSst ?s] => let v := eval vm_compute in (PBSst s) in lazymatch v with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end; change (PBSst s) with v
end.
Ltac pbs_norm_in H :=
repeat match type of H with
| context [PBSst ?s] => let v := eval vm_compute in (PBSst s) in lazymatch v with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end; change (PBSst s) with v in H
end.

Ltac bres_norm :=
rewrite ?bres_self; unfold bres, bres0;
repeat match goal with |- context [bvia ?s] => let v := eval vm_compute in (bvia s) in (first [constr_eq v true | constr_eq v false]; change (bvia s) with v) end;
cbv iota;
repeat match goal with |- context [bcls0 ?s] => let v := eval vm_compute in (bcls0 s) in (lazymatch v with Z0 => idtac | Zpos _ => idtac end; change (bcls0 s) with v) end;
rewrite ?bval_5, ?bval_4, ?bval_3, ?bval_2, ?bval_1, ?bval_0.
Ltac bres_norm_in H :=
rewrite ?bres_self in H; unfold bres, bres0 in H;
repeat match type of H with context [bvia ?s] => let v := eval vm_compute in (bvia s) in (first [constr_eq v true | constr_eq v false]; change (bvia s) with v in H) end;
cbv iota in H;
repeat match type of H with context [bcls0 ?s] => let v := eval vm_compute in (bcls0 s) in (lazymatch v with Z0 => idtac | Zpos _ => idtac end; change (bcls0 s) with v in H) end;
rewrite ?bval_5, ?bval_4, ?bval_3, ?bval_2, ?bval_1, ?bval_0 in H.

Ltac bx_fin := match goal with |- context [BRX ?p] => pose proof (BTOK_ge p); pose proof (BRX_eq p) end; unfold BTOK in *; first [lia | (apply bx_mono2; lia) | (apply bx_mono3; lia) | (apply bx_mono4; lia)].
Ltac bx_tac Hl Hst :=
repeat match goal with x := _ : tlevel |- _ => subst x end;
unfold bx, bxb, cur_st, cur_ss;
cbn [ts_lvl ts_pbs ts_set_co ts_set_x ts_lvl_obj t_levels t_depth t_co];
rewrite ?nth_error_lupd_eq by (apply nth_error_Some; rewrite Hl; discriminate);
rewrite ?Hl; cbn [tl_st tl_ss]; rewrite ?Hst;
repeat match goal with
| H : ?x = _ \/ ?x = _ |- context [bres _ ?x _] => destruct H as [-> | ->]
| H : ?x = _ \/ ?x = _ |- context [bres _ _ ?x] => destruct H as [-> | ->]
| H : (_ /\ ?x = _) \/ (_ /\ ?x = _) |- context [bres _ ?x _] => destruct H as [[_ ->] | [_ ->]]
| H : (_ /\ ?x = _) \/ (_ /\ ?x = _) |- context [bres _ _ ?x] => destruct H as [[_ ->] | [_ ->]]
end;
bres_norm; bx_fin.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq7 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2 QEUF.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition tsF (ts : tstate) (BS : list blk) : tstate :=
TST (t_depth ts) (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) 0 None BS.

Definition lvl_bare (l : tlevel) : Prop :=
0 <= tl_st l <= 26 /\ 0 <= tl_ss l <= 26 /\ tl_cs l = None /\ tl_cbs l = [] /\ tl_name l = 0 /\ tl_nbs l = [].

Lemma lvl_mode_finish : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_finish ss = Some (c, hn) -> c = CAny /\ hn = false /\ ss = ST_finish.
Proof.
intros ss c hn R H. assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
do 27 (destruct k as [|k]; [vm_compute in H; first [discriminate H | injection H as <- <-; split; [reflexivity | split; reflexivity]] |]); exfalso; lia.
Qed.

Lemma BOK_pop : forall pf pa ts B n l dp,
BOK pf pa ts B n -> t_depth ts = S dp -> nth_error (t_levels ts) (S dp) = Some l -> tl_nbs l = [] -> t_objbs ts = [] ->
BOK pf pa (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) B n.
Proof.
intros pf pa ts B n l dp (H1 & H2 & H3 & H4 & H5) Ed Hl Hnbs Eobj.
set (lr := TL ST_eatws ST_start 0 None [] 0 []).
pose proof (H5 (S dp) l ltac:(lia) Hl) as [P0 _].
assert (Eled : ledger_open (lupd (t_levels ts) (S dp) lr) (S dp) = ledger_open (t_levels ts) (S dp)) by (apply ledger_open_lupd_out; lia).
assert (Eled2 : ledger_open (t_levels ts) (S (S dp)) = ledger_open (t_levels ts) (S dp) + phi_open l) by (apply ledger_open_S; exact Hl).
assert (Eblk : Z.of_nat (length (tstate_blocks (TST dp (lupd (t_levels ts) (S dp) lr) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)))) = Z.of_nat (length (tstate_blocks ts))).
{ unfold tstate_blocks; cbn [t_pbs t_objbs t_levels]. rewrite Eobj. cbn [app].
rewrite (lupd_split _ _ _ lr Hl), (concat_split _ _ _ Hl). change (lvl_blocks lr) with (@nil blk). unfold lvl_blocks. rewrite Hnbs, app_nil_r. rewrite !length_app. cbn [length app]. lia. }
split.
{ unfold bneed in *. rewrite Eblk. cbn [t_levels t_depth t_pbs]. rewrite Ed in H1. rewrite Eled. rewrite Eled2 in H1. lia. }
split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
cbn [t_levels t_depth]. intros i li Hi Hn. rewrite nth_error_lupd_neq in Hn by lia. exact (H5 i li ltac:(lia) Hn).
Qed.

Lemma BOK_attach : forall pf pa ts B B' n l st' ss' p s BS c {C},
BOK pf pa ts B (S (Z.to_nat C + n)) -> nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cs l = None -> lvl_blocks l = [] ->
0 <= phi_level (TL st' ss' p (Some s) BS 0 []) ->
c + K_free * Z.of_nat (length BS) + phi_level (TL st' ss' p (Some s) BS 0 []) <= C ->
(forall kids, s = Sarr kids -> arr_inv (arr_capA BS) (Z.of_nat (length kids))) ->
(forall kids, s = Sobj kids -> In (obj_capA BS) Q8tj.lf_sizes) ->
bB B - c <= bB B' -> bD B - 1 <= bD B' ->
BOK pf pa (ts_lvl ts (TL st' ss' p (Some s) BS 0 [])) B' n.
Proof.
intros pf pa ts B B' n l st' ss' p s BS c C (H1 & H2 & H3 & H4 & H5) Hl Ecs Eb P0 HC AI OI HB HD.
set (l' := TL st' ss' p (Some s) BS 0 []) in *.
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
assert (Ephi : phi_open l = 0) by (unfold phi_open, phi_level; rewrite Ecs; destruct (lvl_closed l); reflexivity).
assert (Hphi' : 0 <= phi_open l' <= phi_level l') by (unfold phi_open; destruct (lvl_closed l'); lia).
pose proof (tstate_blocks_lvl_length ts l l' Hl) as Hblk. rewrite Eb in Hblk. cbn [length] in Hblk.
assert (Elb : Z.of_nat (length (lvl_blocks l')) = Z.of_nat (length BS)) by (unfold lvl_blocks, l'; cbn [tl_cbs tl_nbs]; rewrite app_nil_r; reflexivity).
unfold BOK, bneed in *.
replace (K_ev pf * Z.of_nat (S (Z.to_nat C + n))) with (K_ev pf * Z.of_nat n + (Z.max 0 C + 1)) in H1 by (unfold K_ev; lia).
split.
{ rewrite Hblk, Elb. unfold ts_lvl; cbn [t_levels t_depth t_pbs]. rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)), Ephi.
unfold K_free in *. lia. }
split; [lia|]. split; [exact H3|]. split; [exact H4|].
unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [lia|].
split; [intros _ kids Hk; apply AI; unfold l' in Hk; cbn [tl_cs] in Hk; injection Hk as ->; reflexivity|].
split; [intros _ kids Hk; unfold l'; cbn [tl_cbs]; apply (OI kids); unfold l' in Hk; cbn [tl_cs] in Hk; injection Hk as ->; reflexivity | apply Forall_nil].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Definition PE_WIN (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (p : Z) (s : option jshape) (BS : list blk) (rc : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) : Prop :=
PE_CORE_A pf pa q m ts cb nb pj sv /\
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 (tsF ts BS)) errv /\
(forall i li, nth_error (t_levels ts) i = Some li -> i <> t_depth ts -> lvl_cur asegs A4F m (t_depth ts) i li) /\
(exists l, nth_error (t_levels ts) (t_depth ts) = Some l /\ lvl_bare l) /\
t_objbs ts = [] /\
put_pre A4H A4F s m BS p rc.

Lemma PE_BASE_A_private_write : forall pf pa q LB0 LM FRS payload me lo m m' md A B ts errv W,
PE_STATIC_A HIx pf pa lo ->
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 ts) errv ->
munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall (pe_privateA pf pa q (t_pbs ts)) W ->
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m' md A B (pe_blocksA pf q LB0 ts) errv /\
agree_on asegs (t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) m m'.
Proof.
intros pf pa q LB0 LM FRS payload me lo m m' md A B ts errv W STC (HP & ST & ERR & STR & PLEN & SBin & HPR & MDV & G) MU WM MI HW.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & _). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_hi A4L HIx) as HTH.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INtk) as (_ & _ & _ & Htkhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INq) as (_ & _ & _ & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INtk) as Himg_t. pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INq) as Himg_q.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & HFimg & _).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_t, Himg_q, HFimg. rewrite fr_size_2 in HFimg.
pose proof (own_frame_fresh HIx _ _ _ _ _ _ _ _ _ _ _ HP) as [OFF OFS].

assert (AG : agree_on asegs (t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) m m').
{ eapply agree_of_munch; [exact MU | exact WM |]. intros a n Hin.
assert (HinP : In (a, n) (tstate_blocks ts)) by (unfold tstate_blocks; apply in_or_app; right; exact Hin).
assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; left; exact HinP).
unfold pe_blocksA in ND.
eapply private_disjointA; [exact STC | exact HP | exact HinL | | | | exact HW].
- rewrite <- app_assoc in ND. eapply (nodup_app_ne _ _ _ _ _ _ ND HinP). left; reflexivity.
- rewrite <- app_assoc in ND. eapply (nodup_app_ne _ _ _ _ _ _ ND HinP). right; left; reflexivity.
- intros b k Hb. unfold tstate_blocks in ND. rewrite <- app_assoc in ND. exact (nd_pbs_ne _ _ _ _ _ _ _ _ ND Hb Hin). }

assert (HWF : Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hiA_top A4L HIx)
\/ (exists a n, In (a, n) (pe_blocksA pf q LB0 ts ++ LM) /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) ((pa_F pa, 2) :: FRS) /\ ((F <= fst iv /\ snd iv <= F + fr_size k - 8)
\/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))) W).
{ eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_privateA in Hiv. cbn [fst snd] in *.
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]].
- right; left. exists (pf_tk pf), 72. split; [exact INtk | lia].
- right; left. exists q, (32 * pf_mxd pf). split; [exact INq | lia].
- right; left. exists b, k. split; [| lia]. unfold pe_blocksA, tstate_blocks. apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb.
- left. lia.
- right; right; right. exists (pa_F pa), 2. split; [exact INF|]. left. rewrite fr_size_2. lia.
- right; right; right. exists (pa_F pa), 2. split; [exact INF|]. right. unfold shad, shA in H1 |- *. cbn [hl_sb hla_base A4L A4H]; rewrite ?fr_size_2, ?fr_shadow_len_2. unfold A_SB in H1 |- *. lia. }
assert (HIMG : Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W).
{ eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_privateA in Hiv. cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H] in *.
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]]; [lia | lia | | lia | lia |].
- pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ b k HP ltac:(unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb)) as Hbi.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbi. lia.
- unfold shA in H1. unfold A_SB in H1. pose proof (Z.div_pos (pa_F pa) 8 ltac:(lia) ltac:(lia)). lia. }
split; [| exact AG].
split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [exact MDV | exact (GA_outside _ _ _ G MU WM HIMG)]]]]]]]].
- eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx); [exact HP | exact MU | exact HWF].
- eapply (stk_transport_disjoint asegs); [exact ST | exact MU | exact WM |].
destruct ST as (ST0 & ST1 & _).
clear - HW LOS LO ST0 ST1 Htkhi Hqhi HP Gle GFc ACR. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold pe_privateA in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]]; try lia.
+ assert (INb : In (b, k) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INb) as (_ & _ & _ & Hbhi & _). lia.
+ unfold shA, A_SB in H1. Z.div_mod_to_equations. lia.
- eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat]. unfold A_ERRNO, A_TP.
clear - HW LOS LO Himg_t Himg_q Htkhi Hqhi HP SP0 HFimg Gle GFc GF0 ACR. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold pe_privateA in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]]; try lia.
+ assert (INb : In (b, k) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INb) as Hbi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbi.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INb) as (Hk0 & _ & _ & _ & _). lia.
+ unfold shA, A_SB in H1. Z.div_mod_to_equations. lia.
- eapply payload_privateA; [exact STC | exact HP | exact STR | exact PLEN | exact SBin | exact MU | exact HW].
- exact PLEN.
- eapply payload_locA_private; [exact STC | exact HP | exact SBin | exact MU | exact HW].
- eapply heap_presx_trans; [exact HPR|].
eapply (heap_presx_of_munch A4H a4_volatile); [exact MU | exact WM |].
eapply client_outsideF; [exact HP | | lia |].
{ intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb | Hb].
- left. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb | right; exact Hb].
- right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb. }
eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_privateA in Hiv. cbn [fst snd] in *.
assert (NB : forall a n, In (a, n) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)]) -> ~ In (a, n) (LB0 ++ LM ++ fr_ivs A4L FRS)).
{ intros a n Ha Hin. rewrite app_assoc in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_app_or in Hin as [Hin | Hin]; [exact (private_not_LB0A HIx _ _ _ _ _ _ _ _ _ _ _ _ n HP Ha Hin)|].
assert (HaX : In (a, n) (pe_blocksA pf q LB0 ts)).
{ unfold pe_blocksA. apply in_app_or in Ha. apply in_or_app. destruct Ha as [Ha | [Ha | [Ha | []]]]; [left; exact Ha | right; left; exact Ha | right; right; left; exact Ha]. }
exact (nodup_app_ne _ _ _ _ _ _ ND HaX Hin eq_refl).
- exact (blk_not_fr_iv HIx _ _ _ _ _ _ _ _ _ HP (private_in_blocksA _ _ _ LM _ _ _ Ha) ltac:(unfold fr_ivs in *; cbn [flat_map]; apply in_or_app; right; exact Hin)). }
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]].
+ right; left. exists (pf_tk pf), 72. split; [exact INtk|]. split; [| lia]. apply NB. apply in_or_app; right; left; reflexivity.
+ right; left. exists q, (32 * pf_mxd pf). split; [exact INq|]. split; [| lia]. apply NB. apply in_or_app; right; right; left; reflexivity.
+ right; left. exists b, k. split; [unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb|]. split; [| lia].
apply NB. apply in_or_app; left. unfold tstate_blocks; apply in_or_app; left; exact Hb.
+ left. lia.
+ right; right; right. exists (pa_F pa), 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. rewrite fr_size_2. lia.
+ right; right; right. exists (pa_F pa), 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right.
unfold shad, shA in H1 |- *. cbn [hl_sb hla_base A4L A4H]; rewrite ?fr_size_2, ?fr_shadow_len_2. unfold A_SB in H1 |- *. lia.
Qed.

Lemma PE_BASE_A_callG : forall pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 LBall LBall2 errv errv2 LBc,
PE_STATIC_A HIx pf pa lo ->
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m1 md A B LBall errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
incl LB0 LBc ->
HEAPA A4L HIx A2 LBall2 LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m2 md2 A2 B2 LBall2 errv2.
Proof.
intros pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 LBall LBall2 errv errv2 LBc STC
(HP & ST & ERR & STR & PLEN & SBin & HPR & MDV & G) VM12 HPRc Hincl HP2 ST2 ERR2.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
split; [exact HP2|]. split; [exact ST2|]. split; [exact ERR2|].
assert (SBin2 := payload_locA_pres HIx pf pa LB0 FRS _ _ _ _ _ _ _ LBc _ _ _ HP (incl_tl _ (incl_refl _)) HPRc SBin).
assert (FRI : incl (fr_ivs A4L FRS) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS))).
{ intros b Hb. apply in_or_app; right. apply in_or_app; right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb. }
split; [| split; [exact PLEN | split; [exact SBin2 | split; [| split]]]].
- eapply payload_presA; [exact HPRc | intros x Hx; apply in_or_app; left; apply Hincl; exact Hx | exact FRI | | exact STR | exact PLEN | exact SBin]. lia.
- eapply heap_presx_trans; [exact HPR|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPRc | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply Hincl; exact Hb|].
apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb.
- eapply model_vm_only_trans; [exact MDV | exact VM12].
- eapply GA_pres; [exact HPRc | exact G].
Qed.

Lemma pe_blocksA_tsF_lvl : forall pf q LB0 ts BS l l', nth_error (t_levels ts) (t_depth ts) = Some l -> lvl_blocks l' = lvl_blocks l ->
pe_blocksA pf q LB0 (tsF (ts_lvl ts l') BS) = pe_blocksA pf q LB0 (tsF ts BS).
Proof.
intros pf q LB0 ts BS l l' Hl E. unfold pe_blocksA, tstate_blocks, tsF, ts_lvl; cbn [t_pbs t_objbs t_levels t_depth].
rewrite (map_lupd_same lvl_blocks (t_levels ts) (t_depth ts) l' l Hl E). reflexivity.
Qed.

Lemma incl_blocks_tsF : forall pf q LB0 ts BS, t_objbs ts = [] -> incl (pe_blocksA pf q LB0 ts) (pe_blocksA pf q LB0 (tsF ts BS)).
Proof.
intros pf q LB0 ts BS E b Hb. unfold pe_blocksA, tstate_blocks, tsF in *; cbn [t_pbs t_objbs t_levels] in *. rewrite E in Hb. cbn [app] in Hb.
apply in_app_or in Hb as [Hb | Hb]; [| apply in_or_app; right; exact Hb]. apply in_or_app; left.
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb].
Qed.

Lemma perm_blocks_tsF : forall pf q LB0 ts BS, t_objbs ts = [] -> Permutation (pe_blocksA pf q LB0 (tsF ts BS)) (BS ++ pe_blocksA pf q LB0 ts).
Proof.
intros pf q LB0 ts BS E. unfold pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]. rewrite E. cbn [app]. rewrite <- !app_assoc.
apply Permutation_app_swap_app.
Qed.

Lemma lvl_cur_popA : forall m dp i li, i <> S dp -> lvl_cur asegs A4F m (S dp) i li -> lvl_cur asegs A4F m dp i li.
Proof.
intros m dp i li Hne (R1 & R2 & J & M). split; [exact R1|]. split; [exact R2|]. split; [exact J|].
destruct (Nat.lt_ge_cases i dp) as [Hlt | Hge].
- rewrite (proj2 (Nat.ltb_lt i dp) Hlt). rewrite (proj2 (Nat.ltb_lt i (S dp))) in M by lia. exact M.
- rewrite (proj2 (Nat.ltb_ge i dp) Hge). destruct (Nat.eq_dec i dp) as [-> | Hne2].
+ rewrite Nat.eqb_refl. rewrite (proj2 (Nat.ltb_lt dp (S dp))) in M by lia.
destruct M as [(E & C & N) | (E & C & N)]; rewrite E.
* exists CArr, false. split; [apply Qdyh.Mq0.lvl_mode_aadd | split; [exact C | exact N]].
* exists CObj, true. split; [apply Qdyh.Mq0.lvl_mode_ovadd | split; [exact C | exact N]].
+ rewrite (proj2 (Nat.eqb_neq i dp) Hne2). rewrite (proj2 (Nat.ltb_ge i (S dp))) in M by lia.
rewrite (proj2 (Nat.eqb_neq i (S dp)) Hne) in M. exact M.
Qed.

Lemma PE_WIN_open : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv l,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_name l = 0 -> tl_nbs l = [] -> t_objbs ts = [] ->
PE_WIN pf pa q LB0 LM FRS payload me lo m md A B (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) None [] 0 [])) (tl_cur l) (tl_cs l) (tl_cbs l) 1 cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv l [CORE REST] Hl Hn Hnbs Eobj.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply PE_REST_A_base in REST as (BASE & LV & OBJ & BUD).
set (lw := TL (tl_st l) (tl_ss l) (tl_cur l) None [] 0 []).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (LV _ _ Hl) as (R1 & R2 & JO & _).
split; [| split; [| split; [| split; [| split]]]].
- unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PB|]. split; [exact Hpb|]. split; [| exact FR].
eapply tstack_lupd_srec; [exact TSK | exact Hl |]. unfold srec_cells, lw; cbn [tl_st tl_ss tl_cur tl_name]. rewrite Hn. reflexivity.
- destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (pe_blocksA_cur_perm2 pf q LB0 ts l Hl)|]. apply Permutation_sym.
eapply Permutation_trans; [apply (pe_blocksA_lvl_obj_perm pf q LB0 ts l lw 0 None (tl_cbs l) Hl)|].
unfold lvl_blocks, lw; cbn [tl_cbs tl_nbs app]. rewrite Hnbs, Eobj, app_nil_r. cbn [app]. apply Permutation_refl.
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence. exact (LV i li Hli).
- exists lw. split; [unfold ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd|].
unfold lvl_bare, lw; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]. repeat split; try reflexivity; lia.
- exact Eobj.
- unfold put_pre. destruct (tl_cs l) as [s'|]; cbn [jopt] in JO; [| exact JO]. destruct JO as [Hp J]. split; [exact Hp|]. split; [lia | exact J].
Qed.

Lemma PE_WIN_write : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS rc cb nb pj sv errv W l' cb' nb' pj',
PE_STATIC_A HIx pf pa lo ->
PE_WIN pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc cb nb pj sv errv ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtqA pf pa q) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
tstack asegs mc q (lupd (t_levels ts) (t_depth ts) l') ->
pe_frameA asegs mc pf pa cb' nb' pj' sv ->
lvl_bare l' ->
PE_WIN pf pa q LB0 LM FRS payload me lo mc md A B (ts_lvl ts l') p s BS rc cb' nb' pj' sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_lvl ts l') b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS rc cb nb pj sv errv W l' cb' nb' pj' STC (CORE & BASE & LVo & (l & Hl & BARE) & Eobj & PP) MU WM MI HW TOKc TSKc FRc BARE'.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
destruct (PE_BASE_A_private_write pf pa q LB0 LM FRS payload me lo m mc md A B (tsF ts BS) errv W STC BASE MU WM MI (pe_wtqA_private _ _ _ _ _ HW)) as [BASEc AG].
unfold tsF in AG; cbn [t_objbs t_levels] in AG.
assert (Eb : lvl_blocks l' = lvl_blocks l).
{ destruct BARE as (_ & _ & _ & C1 & _ & C2). destruct BARE' as (_ & _ & _ & C1' & _ & C2'). unfold lvl_blocks. rewrite C1, C2, C1', C2'. reflexivity. }
split.
2:{ intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 (tsF ts BS) ++ LM)) by (unfold pe_blocksA, tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 BASE)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | right; left; reflexivity]. }
split; [| split; [| split; [| split; [| split]]]].
- unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [exact TSKc | exact FRc]]].
eapply (pbuf_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact PB | exact MU | exact WM | exact HW].
- rewrite (pe_blocksA_tsF_lvl pf q LB0 ts BS l l' Hl Eb). exact BASEc.
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- exists l'. split; [unfold ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd | exact BARE'].
- exact Eobj.
- unfold put_pre in *. destruct s as [s'|]; [| exact PP]. destruct PP as (Hp & Hrc & J). split; [exact Hp|]. split; [exact Hrc|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

Lemma PE_WIN_callG : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts p s BS rc rc2 cb nb pj sv errv errv2,
PE_STATIC_A HIx pf pa lo ->
PE_WIN pf pa q LB0 LM FRS payload me lo m1 md A B ts p s BS rc cb nb pj sv errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (pe_blocksA pf q LB0 ts ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 (tsF ts BS)) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) -> rw_cells asegs m2 A_ERRNO [C4 errv2] ->
put_pre A4H A4F s m2 BS p rc2 ->
PE_WIN pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts p s BS rc2 cb nb pj sv errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts p s BS rc rc2 cb nb pj sv errv errv2 STC (CORE & BASE & LVo & CUR & Eobj & PP) VM HPR HP2 ST2 ERR2 PP2.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m1 m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR (in_or_app _ _ _ (or_introl INq))) in TSK; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK.
split; [| split; [| split; [| split; [exact CUR | split; [exact Eobj | exact PP2]]]]].
- split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|]. split; [exact TOK|]. split; [| split; [exact Hpb | split; [exact TSK | exact FR2]]].
eapply pbuf_agree; [exact PB | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
- eapply (PE_BASE_A_callG pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 _ _ errv errv2 RB); [exact STC | exact BASE | exact VM | exact HPR | exact LB0R | exact HP2 | exact ST2 | exact ERR2].
- intros i li Hli Hne. eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
Qed.

Lemma PE_WIN_callG2 : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts p s BS rc p2 s2 BS2 rc2 cb nb pj sv errv errv2,
PE_STATIC_A HIx pf pa lo ->
PE_WIN pf pa q LB0 LM FRS payload me lo m1 md A B ts p s BS rc cb nb pj sv errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (pe_blocksA pf q LB0 ts ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 (tsF ts BS2)) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) -> rw_cells asegs m2 A_ERRNO [C4 errv2] ->
put_pre A4H A4F s2 m2 BS2 p2 rc2 ->
PE_WIN pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts p2 s2 BS2 rc2 cb nb pj sv errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts p s BS rc p2 s2 BS2 rc2 cb nb pj sv errv errv2 STC (CORE & BASE & LVo & CUR & Eobj & PP) VM HPR HP2 ST2 ERR2 PP2.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m1 m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR (in_or_app _ _ _ (or_introl INq))) in TSK; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK.
split; [| split; [| split; [| split; [exact CUR | split; [exact Eobj | exact PP2]]]]].
- split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|]. split; [exact TOK|]. split; [| split; [exact Hpb | split; [exact TSK | exact FR2]]].
eapply pbuf_agree; [exact PB | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
- eapply (PE_BASE_A_callG pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 _ _ errv errv2 RB); [exact STC | exact BASE | exact VM | exact HPR | exact LB0R | exact HP2 | exact ST2 | exact ERR2].
- intros i li Hli Hne. eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
Qed.

Lemma PE_WIN_close_cur : forall pf pa q LB0 LM FRS payload me lo m md A B ts p s BS cb nb pj sv errv l c,
PE_WIN pf pa q LB0 LM FRS payload me lo m md A B ts p (Some s) BS 1 cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cur l = p ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, false) -> cls_ok c (Some s) ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false ->
PE_BUD pf pa (ts_lvl ts (TL (tl_st l) (tl_ss l) p (Some s) BS 0 [])) B ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B (ts_lvl ts (TL (tl_st l) (tl_ss l) p (Some s) BS 0 [])) cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts p s BS cb nb pj sv errv l c (CORE & BASE & LVo & (l0 & Hl0 & BARE) & Eobj & PP) Hl Ecur Hm CLS Hz BUD.
rewrite Hl in Hl0. injection Hl0 as <-. destruct BARE as (R1 & R2 & Ecs & Ecbs & En & Enbs).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
set (l' := TL (tl_st l) (tl_ss l) p (Some s) BS 0 []).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
destruct PP as (Hp & _ & J).
split.
- unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PB|]. split; [exact Hpb|]. split; [| exact FR].
eapply tstack_lupd_srec; [exact TSK | exact Hl |]. unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name]. rewrite Ecur, En. reflexivity.
- apply PE_REST_A_of_base; [| | | exact BUD].
+ destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (perm_blocks_tsF pf q LB0 ts BS Eobj)|]. apply Permutation_sym.
eapply Permutation_trans; [apply (pe_blocksA_lvl_perm pf q LB0 ts l l' Hl)|].
unfold lvl_blocks at 1, l'; cbn [tl_cbs tl_nbs]. rewrite app_nil_r. apply Permutation_app_head.
apply Permutation_sym. eapply Permutation_trans; [apply (pe_blocksA_cur_perm pf q LB0 ts l Hl)|]. unfold lvl_blocks. rewrite Ecbs, Enbs. apply Permutation_refl.
+ unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | Hne].
* rewrite nth_error_lupd_eq in Hli by exact Hd. injection Hli as <-. split; [exact R1|]. split; [exact R2|]. split; [cbn [jopt l' tl_cs tl_cbs tl_cur]; split; [exact Hp | exact J]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists c, false. split; [exact Hm|]. split; [exact CLS|]. cbn. split; reflexivity.
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LVo i li Hli Hne).
+ unfold cur_st, ts_lvl; cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by exact Hd. cbn [tl_st l']. rewrite Hz. exact Eobj.
Qed.

Lemma PE_WIN_close_weak : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv rc,
PE_WIN pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] rc cb nb pj sv errv ->
(exists l, nth_error (t_levels ts) (t_depth ts) = Some l /\ tl_cur l = 0) ->
K_free * Z.of_nat (length (tstate_blocks ts)) + K_exit + pa_bslack pa <= bB B -> pa_dslack pa <= bD B ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts [] cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv rc (CORE & BASE & LVo & (l0 & Hl0 & BARE) & Eobj & PP) (l & Hl & Ecur) HB HD.
rewrite Hl in Hl0. injection Hl0 as <-. destruct BARE as (R1 & R2 & Ecs & Ecbs & En & Enbs).
split; [exact CORE|]. split; [| split; [| split; [exact HB | exact HD]]].
- rewrite app_nil_r. destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (perm_blocks_tsF pf q LB0 ts [] Eobj)|]. apply Permutation_refl.
- intros i li Hli. destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | Hne].
+ rewrite Hl in Hli. injection Hli as <-. split; [split; [exact R1 | exact R2]|]. split; [rewrite Ecs, Ecbs, Ecur; cbn; split; reflexivity|].
split; [left; cbn; split; [exact En | exact Enbs] | intros Hlt; exfalso; lia].
+ apply lvl_cur_weakA. exact (LVo i li Hli Hne).
Qed.

Lemma PE_WIN_close_pop : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS cb nb pj sv errv dp,
PE_STATIC_A HIx pf pa lo ->
PE_WIN pf pa q LB0 LM FRS payload me lo m md A B ts p s BS 1 cb nb pj sv errv ->
t_depth ts = S dp -> nth_error (t_levels ts) (S dp) = Some (TL ST_eatws ST_start 0 None [] 0 []) ->
munch [(pf_tk pf, pf_tk pf + 72)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat dp) q (t_x ts)) ->
PE_BUD pf pa (TST dp (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) p s BS) B ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (TST dp (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) p s BS) cb nb pj sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc (TST dp (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) p s BS) b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS cb nb pj sv errv dp STC (CORE & BASE & LVo & CUR & Eobj & PP) Ed Hrl MU WM MI TOKc BUD.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (HW : Forall (pe_wtfA pf pa) [(pf_tk pf, pf_tk pf + 72)]) by (apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]).
destruct (PE_BASE_A_private_write pf pa q LB0 LM FRS payload me lo m mc md A B (tsF ts BS) errv _ STC BASE MU WM MI (pe_wtfA_private _ _ _ _ _ HW)) as [BASEc AG].
unfold tsF in AG; cbn [t_objbs t_levels] in AG.
set (ts' := TST dp (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) p s BS).
assert (PBc : pbuf asegs mc (t_pbs ts) (t_pb ts)) by (eapply (pbuf_wtfA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact PB | exact MU | exact WM | exact HW]).

assert (Hdp : (dp < length (t_levels ts))%nat) by (rewrite LEN32; lia).
destruct (nth_error (t_levels ts) dp) as [lp|] eqn:Hlp; [| apply nth_error_None in Hlp; lia].
pose proof (LVo dp lp Hlp ltac:(lia)) as LVp. pose proof LVp as (_ & _ & _ & Mp). rewrite Ed in Mp.
replace (dp <? S dp)%nat with true in Mp by (symmetry; apply Nat.ltb_lt; lia).
assert (STp : zin (tl_st lp) [ST_array_add; ST_ovadd] = true) by (destruct Mp as [(E & _) | (E & _)]; rewrite E; reflexivity).
split.
- split.
+ unfold PE_CORE_A, ts'; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [lia|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [exact PBc|]. split; [exact Hpb|]. split; [| ].
* eapply (tstack_wtfA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
* eapply (pe_frameA_blkwriteG HIx) with (LBX := pe_blocksA pf q LB0 (tsF ts BS)); [exact STC | exact (proj1 BASE) | | exact FR | exact MU | exact WM].
apply Forall_cons; [| apply Forall_nil]. exists (pf_tk pf), 72. cbn [fst snd]. split; [| lia]. apply in_or_app; left. unfold pe_blocksA. apply in_or_app; right; left; reflexivity.
+ apply PE_REST_A_of_base; [exact BASEc | | | exact BUD].
* unfold ts'; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (S dp)) as [-> | Hne].
-- rewrite Hrl in Hli. injection Hli as <-. split; [unfold ST_eatws; cbn; lia|]. split; [unfold ST_start; cbn; lia|]. split; [cbn; split; reflexivity|].
replace (S dp <? dp)%nat with false by (symmetry; apply Nat.ltb_ge; lia). replace (S dp =? dp)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
repeat split.
-- apply lvl_cur_popA; [exact Hne|]. rewrite <- Ed.
eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli ltac:(rewrite Ed; exact Hne)) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
* unfold cur_st, ts'; cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite Hlp, STp.
unfold put_pre in PP. unfold jopt. destruct s as [s'|]; [| exact PP]. destruct PP as (Hp & _ & J). split; [exact Hp|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
- intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact MU | exact WM | apply pe_wtfA_wtqA; exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 (tsF ts BS) ++ LM)) by (unfold pe_blocksA, tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 BASE)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.

Lemma PE_WIN_munchG : forall pf pa q LB0 LM FRS payload me lo m m2 md A B ts p s BS rc rc2 cb nb pj sv errv W,
PE_STATIC_A HIx pf pa lo ->
PE_WIN pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc cb nb pj sv errv ->
munch W m m2 -> wmono asegs m m2 -> mem_inv asegs m2 ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= pf_spf pf) \/ (exists a n, In (a, n) BS /\ a <= fst iv /\ snd iv <= a + n)) W ->
stk asegs m2 lo (pf_spf pf) ->
put_pre A4H A4F s m2 BS p rc2 ->
PE_WIN pf pa q LB0 LM FRS payload me lo m2 md A B ts p s BS rc2 cb nb pj sv errv
/\ agree_on asegs (pe_blocksA pf q LB0 ts) m m2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m m2 md A B ts p s BS rc rc2 cb nb pj sv errv W STC WIN MU WM MI2 HW ST2 PP2.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof BASE as (HP & ST & ERR & _).
set (RB := pe_blocksA pf q LB0 ts) in *. set (LBall := pe_blocksA pf q LB0 (tsF ts BS)) in *.
pose proof (perm_blocks_tsF pf q LB0 ts BS Eobj) as PERM. fold RB LBall in PERM.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (NDp : List.NoDup (map blk_addr ((BS ++ RB) ++ LM))).
{ eapply Permutation_NoDup; [| exact ND]. apply Permutation_map. apply Permutation_app_tail. exact PERM. }
assert (INall : forall a n, In (a, n) BS -> In (a, n) (LBall ++ LM)).
{ intros a n Hin. apply in_or_app; left. eapply Permutation_in; [apply Permutation_sym; exact PERM | apply in_or_app; left; exact Hin]. }
assert (NBS : forall a n, In (a, n) BS -> ~ In (a, n) (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS))).
{ intros a n Hin Hx. rewrite app_assoc in Hx. apply in_app_or in Hx as [Hx | Hx].
- rewrite <- app_assoc in NDp. rewrite map_app in NDp. eapply (NoDup_app_in2 _ _ a NDp); [exact (in_map blk_addr _ _ Hin) | exact (in_map blk_addr _ _ Hx)].
- exact (blk_not_fr_iv HIx _ _ _ _ _ _ _ _ _ HP (INall a n Hin) Hx). }
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2).
{ eapply (heap_pres_of_munch A4H); [exact MU | exact WM |].
eapply (client_outsideF HIx); [exact HP | | lia |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb | Hb]; [left | right; exact Hb].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply (incl_blocks_tsF pf q LB0 ts BS Eobj); exact Hb | apply in_or_app; right; exact Hb].
- eapply Forall_impl; [| exact HW]. intros iv [H1 | (a & n & Hin & H1)]; [left; exact H1 | right; left].
exists a, n. split; [exact (INall a n Hin)|]. split; [exact (NBS a n Hin) | exact H1]. }
assert (HP2 : HEAPA A4L HIx A LBall LM ((pa_F pa, 2) :: FRS) B m2 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI2]. eapply (frame_writes_okF A4L HIx); [exact HP | exact MU |].
eapply Forall_impl; [| exact HW]. intros iv [H1 | (a & n & Hin & H1)]; [left; lia | right; left; exists a, n; split; [exact (INall a n Hin) | exact H1]]. }
assert (ERR2 : rw_cells asegs m2 A_ERRNO [C4 errv]).
{ eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat]. unfold A_ERRNO, A_TP.
pose proof alloc_ceiling_range as ACR.
clear - HW INall HP ACR LO. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [H1 | (a & n & Hin & H1)]; [lia|].
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP (INall a n Hin)) as Hbi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbi.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP (INall a n Hin)) as (Hk0 & _ & _ & _ & _). lia. }
split.
- eapply (PE_WIN_callG pf pa q LB0 LM FRS payload me lo m m2 md md A A B B ts p s BS rc rc2 cb nb pj sv errv errv);
[exact STC | exact WIN | apply model_vm_only_refl | exact HPRc | exact HP2 | exact ST2 | exact ERR2 | exact PP2].
- eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

Lemma pe_frameA_slotw : forall pf pa (LBX : list blk) LM FRS B A m m' md lo W cb nb pj pj' sv,
PE_STATIC_A HIx pf pa lo -> HEAPA A4L HIx A LBX LM ((pa_F pa, 2) :: FRS) B m md ->
Forall (fun iv => exists a n, In (a, n) (LBX ++ LM) /\ a <= fst iv /\ snd iv <= a + n) W ->
pe_frameA asegs m pf pa cb nb pj sv -> munch ((pf_spf pf, pf_spf pf + 312) :: W) m m' -> wmono asegs m m' ->
rw_cells asegs m' (pf_spf pf) (pe_slotsA pf pa nb pj') ->
pj_gap pj' = pj_gap pj -> pj_fhd pj' = pj_fhd pj -> pj_f1 pj' = pj_f1 pj -> pj_f2 pj' = pj_f2 pj ->
pe_frameA asegs m' pf pa cb nb pj' sv.
Proof.
intros pf pa LBX LM FRS B A m m' md lo W cb nb pj pj' sv STC HP HW (SL & GP & SV & FF & FSH) MU WM SLc E1 E2 E3 E4.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk). pose proof alloc_ceiling_range as ACR.
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
assert (BLO : forall a n, In (a, n) (LBX ++ LM) -> 0 <= n /\ a + n <= alloc_ceiling).
{ intros a n Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & _ & _ & Hhi & _). lia. }
split; [exact SLc | split; [| split; [| split]]].
- rewrite E1. eapply rw_cells_transport; [exact GP | exact MU | exact WM |]. cbn [cells_size csize Nat.add disjoint_from fst snd].
split; [lia|]. eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin; destruct (BLO a n Hin); lia].
- eapply rw_cells_transport; [exact SV | exact MU | exact WM |]. cbn [cells_size csize Nat.add pe_savedA_cells disjoint_from fst snd].
split; [lia|]. eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin; destruct (BLO a n Hin); lia].
- unfold ff_cellsA in *. rewrite E2, E3, E4. eapply rw_cells_transport; [exact FF | exact MU | exact WM |]. cbn [cells_size csize Nat.add disjoint_from fst snd].
split; [lia|]. eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin].
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hin). rewrite fr_size_2 in *. lia.
- eapply rw_cells_transport; [exact FSH | exact MU | exact WM |]. unfold ffsh_cells, FSH0. cbn [cells_size csize Nat.add map length disjoint_from fst snd].
split; [unfold shA, A_SB; clear - GF0 GFc LO LOS ACR; Z.div_mod_to_equations; lia|].
eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin].
assert (HF0' : 0 <= pa_F pa) by lia. assert (HFc' : pa_F pa < alloc_ceiling) by lia.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP Hin HF0' HFc' ltac:(lia)) as DD. unfold shA in DD |- *. lia.
Qed.

Lemma pe_uw_at : forall pf pa lo m cb nb pj sv v2 ra2,
PE_STATIC_A HIx pf pa lo -> pe_frameA asegs m pf pa cb nb pj sv ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) -> 0 <= v2 < 2^64 ->
uw_at (hiA_top A4L HIx) m (pf_spf pf) (pa_sp0 pa) (UWfp ra2 v2).
Proof.
intros pf pa lo m cb nb pj sv v2 ra2 STC (_ & _ & SV & _) S0V RAV HV HR.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
cbn [uw_at]. split; [lia|]. split; [clear - Gsp0; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [| split; [exact HV | exact HR]].
unfold pe_savedA_cells in SV. destruct SV as [[_ SVB] _].
cbn [cells_bytes cbytes app] in SVB. rewrite <- ?app_assoc in SVB.
do 11 (apply bytes_at_app in SVB as [_ SVB]; rewrite length_le8 in SVB).
rewrite S0V, RAV in SVB. eapply bytes_at_ext; [| reflexivity].
match type of SVB with bytes_at _ _ ?a _ => replace a with (pa_sp0 pa - 16) in SVB by lia end. exact SVB.
Qed.

End WithIface.
End RC__1.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QSHS Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ. Import QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq2. Import QJjn.Mq0. Import Q2Sr QLbz.
Import Q6WR.Mq0 QrPc.
Import QbFI QXUB. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh Q30W.Mq6 QlKV.Mqf QsKa.Mqd QlKV.Mqc Qiiq QSHS Ql4f.Mq4 Q1Y6.Mq4 QlKV.Mqe QrQv.
Import Qc5u.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section PeOutB.
Variable HIx : heap_iface_A A4L.

End PeOutB.
End RC__1.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ. Import QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq2. Import QJjn.Mq0. Import Q2Sr QLbz.
Import Q6WR.Mq0 QrPc.
Import QbFI QXUB. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh Q30W.Mq6 QlKV.Mqf QsKa.Mqd QlKV.Mqc Qiiq QSHS Ql4f.Mq4 Q1Y6.Mq4 QlKV.Mqe QrQv.
Import Qc5u.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section PeOutBJ.
Variable HIx : heap_iface_A A4L.

Ltac if_vm := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
first [ replace c with true by (vm_compute; reflexivity); cbv iota | replace c with false by (vm_compute; reflexivity); cbv iota ] end.

Lemma out_checksBJ :
forall (m : word -> option byte) (tk oldl newl len lenr sb spf : Z) (pmd : Model) (mxd fl : Z) (sp0 Ff oldloc newloc bsl dsl : Z) (depth : nat)
(isd stpos choff err ucs high : word) (quote : bv 8) (l : tlevel) (pb q : Z) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (K : machine_state -> Prop),
rw_cells asegs m tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stpos choff err ucs high quote)) ->
pe_frameA asegs m (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv ->
rw_cells asegs m (q + 32 * Z.of_nat depth) (srec_cells l) ->
ro_cells asegs m (tk / 8 + A_SB)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
ro_cells asegs m ((q + 32 * Z.of_nat depth) / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
(depth < Z.to_nat mxd)%nat -> 1 <= mxd <= 32 -> 0 <= fl < 2^32 ->
0 < tk -> tk + 72 <= alloc_ceiling -> tk mod 16 = 0 -> 0 < q -> q + 32 * mxd <= alloc_ceiling -> q mod 16 = 0 ->
(tk + 72 <= q \/ q + 32 * mxd <= tk) -> (Ff + 256 <= tk \/ tk + 72 <= Ff) ->
(tk + 72 + 8 <= 2147450880 \/ (2 ^ 47 - 1) / 8 + 2147450880 + 1 <= tk) ->
(q + 32 * mxd + 8 <= 2147450880 \/ (2 ^ 47 - 1) / 8 + 2147450880 + 1 <= q) ->
pe_geomA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) -> alloc_ceiling <= spf ->
0 <= tl_st l <= 26 -> 0 <= tl_ss l <= 26 ->
mem_inv asegs m ->
(forall mc (a0' a1' a2' a3' a4' a5' a6' a7' : word) (e' : word),
(e' = err \/ bv_unsigned (sx32 e') = 3 \/ bv_unsigned (sx32 e') = 4 \/ bv_unsigned (sx32 e') = 14) ->
rw_cells asegs mc tk (tok_cells_g mxd fl pb (Z.of_nat depth) q (TS isd stpos choff e' ucs high quote)) ->
munch [(tk + 36, tk + 40)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs K (pe_msO asegs (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) 0x999fc
gp t0 t1 t2 a0' a1' a2' a3' a4' a5' a6' a7' s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc mc)) ->
evt asegs K (pe_msO asegs (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) APE_OUT
gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until K. intros TOK FR LVL SHT SHL D32 MXB FLB Htlo Hthi Htal Hqlo Hqhi Hqal Dtq DFt APt APq GEO SPFlo ST26 SS26 MI TAIL.
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk). cbn [pf_spf pa_sp0 pa_F pf_tk] in Gspf, Gsp0, Gle, GF, GF0, GFc, Gtk.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. cbn [pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS, GAP, SAVED, FF, FSH.
unfold srec_cells in LVL. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse.
unfold pe_msO in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *. unfold APE_OUT.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
pose proof alloc_ceiling_range as ACR.
assert (Hbse32 : bse + 32 <= q + 32 * mxd) by nia || (assert (Hbse32 : bse + 32 <= q + 32 * mxd) by lia).
assert (Hbse0 : q <= bse) by lia.
assert (Hb8 : bse mod 8 = 0) by (rewrite Hbse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by lia.
unfold shA, SB2, SB4, SB7, SB8, A_SB, A_TP in *. unfold A_SB in *.
clear GAP SAVED.

assert (JOIN : forall mc (a0x a2x : word) (e1 : word),
(e1 = err \/ bv_unsigned (sx32 e1) = 14) ->
rw_cells asegs mc tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 choff; C4 e1; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(tk + 36, tk + 40)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
evt asegs K
(MS (mkR (Z_to_bv 64 (tk / 8 + 2147450882)) (Z_to_bv 64 spf) gp (Z_to_bv 64 6444320) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) a0x (Z_to_bv 64 fl) a2x a3 a4 a5 a6 a7
(Z_to_bv 64 (Ff / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x998f8) fc None mc (seg_rom asegs))).
{ intros mc a0x a2x e1 HE1 TOKc MUc WMc MIc.
assert (SLc : rw_cells asegs mc spf (pe_slotsA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) nb pj)).
{ eapply rw_cells_transport; [exact SLOTS | exact MUc | exact WMc | rewrite pe_slotsA_size; cbn [disjoint_from]; lia]. }
unfold pe_slotsA in SLc. cbn zeta in SLc. cbn [pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SLc. unfold A_SB in SLc.
assert (FFc : rw_cells asegs mc Ff (ff_cellsA cb pj)).
{ eapply rw_cells_transport; [exact FF | exact MUc | exact WMc | unfold ff_cellsA; cbn [disjoint_from cells_size csize Nat.add length]; lia]. }
unfold ff_cellsA in FFc.
assert (LVLc : rw_cells asegs mc bse [C4 (Z_to_bv 64 (tl_st l)); C4 (Z_to_bv 64 (tl_ss l)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (tl_cur l)); C8 (Z_to_bv 64 (tl_name l))]).
{ eapply rw_cells_transport; [exact LVL | exact MUc | exact WMc | cbn; lia]. }
assert (SHTc : ro_cells asegs mc (tk / 8 + 2147450880)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ eapply ro_cells_transport; [exact SHT | exact MUc | cbn; lia]. }
assert (SHLc : ro_cells asegs mc (bse / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ eapply ro_cells_transport; [exact SHL | exact MUc | cbn; Z.div_mod_to_equations; lia]. }
clear SLOTS FF LVL TOK MI SHT SHL. pose proof MUc as MU. pose proof WMc as WM. clear MUc WMc.
assert (GO : forall mf (a0' a1' a2' a3' a4' a5' a6' a7' : word) e',
(e' = e1 \/ bv_unsigned (sx32 e') = 3 \/ bv_unsigned (sx32 e') = 4) ->
rw_cells asegs mf tk
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 (Z.of_nat depth)); C4 isd; C4 stpos;
C4 choff; C4 e'; C4 ucs; C4 high; C1 quote; CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
munch [(tk + 36, tk + 40)] m mf -> wmono asegs m mf -> mem_inv asegs mf ->
evt asegs K
(MS (mkR (Z_to_bv 64 (tk / 8 + 2147450882)) (Z_to_bv 64 spf) gp (Z_to_bv 64 6444320) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (Ff / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x999fc) fc None mf (seg_rom asegs))).
{ intros mf a0' a1' a2' a3' a4' a5' a6' a7' e' HE' TOK' MU' WM' MI'. apply (TAIL mf a0' a1' a2' a3' a4' a5' a6' a7' e'); [| | exact MU' | exact WM' | exact MI'].
{ destruct HE' as [-> | [H | H]]; [destruct HE1 as [-> | H1]; [left; reflexivity | right; right; right; exact H1] | right; left; exact H | right; right; left; exact H]. }
unfold tok_cells_g. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote]. exact TOK'. }
clear TAIL.
step.
asan_rechkB.
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
asan_rechkMB 2.
step. step.
norm_sx32.
do 4 step.
ub_bse q bse (Z.of_nat depth).
do 6 step.
ub_lvl q bse (Z.of_nat depth).
step.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [CB0 | CBn].
-
rewrite CB0. if_vm.
step. ub_if_lit.
step. if_falsex.
step. ub_land Hb8. step. ub_if_lit.
asan_chkB.
step. norm_sx32.
step.
destruct (Z.eq_dec (tl_st l) 2) as [ST2 | STn].
+ rewrite ST2. step. if_vm. eapply GO; [left; reflexivity | exact TOKc | exact MU | exact WM | exact MIc].
+ step. if_falsex.
step.
asan_chkB.
step. norm_sx32. step.
destruct (Z.eq_dec (tl_ss l) 2) as [SS2 | SSn].
* rewrite SS2. step. if_vm. eapply GO; [left; reflexivity | exact TOKc | exact MU | exact WM | exact MIc].
* step. if_falsex.
step. step.
asan_rechkB.
step.
stepz.
eapply GO; [ | | exact MU | exact WM | ]; [ | eassumption | assumption]. first [right; left; vm_compute; reflexivity | right; right; vm_compute; reflexivity].
-
if_falsex.
step. ub_if_lit.
step. if_falsex.
step. ub_land Hb8. step. ub_if_lit.
asan_chkB.
step. rewrite (unsigned_lit fl) by lia. step.
step.
destruct (Z.eq_dec (Z.land fl 3) 1) as [F3 | F3].
+ rewrite F3. if_vm.
step.
destruct (PeanoNat.Nat.eq_dec depth 0) as [D0 | Dn].
* rewrite D0. cbn [Z.of_nat]. if_false.
step. norm_sx32. step.
destruct (Z.eq_dec (tl_st l) 2) as [ST2 | STn].
-- rewrite ST2. step. if_vm.
do 3 step.
asan_rechkB.
step.
stepz.
eapply GO; [ | | exact MU | exact WM | ]; [ | eassumption | assumption]. first [right; left; vm_compute; reflexivity | right; right; vm_compute; reflexivity].
-- step. if_truex. eapply GO; [left; reflexivity | exact TOKc | exact MU | exact WM | exact MIc].
* if_truex. eapply GO; [left; reflexivity | exact TOKc | exact MU | exact WM | exact MIc].
+ pose proof (land3_range fl). if_truex. eapply GO; [left; reflexivity | exact TOKc | exact MU | exact WM | exact MIc]. }

pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk + 36, tk + 40)] m) as MU.
step.
asan_rechkB.
step.
step. rewrite (zx32_small fl) by lia.
step. rewrite (unsigned_lit fl) by lia.
destruct (land16_cases fl) as [F16 | F16]; rewrite F16.
- step. if_true. eapply JOIN; [left; reflexivity | exact TOK | exact MU | exact WM | exact MI].
- step. if_false. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd; cbv iota end.
+ eapply JOIN; [left; reflexivity | exact TOK | exact MU | exact WM | exact MI].
+ step.
asan_rechkB.
step. step.
stepz.
eapply JOIN; [ | | exact MU | exact WM | ]; [ | eassumption | assumption]. right; vm_compute; reflexivity.
Qed.
End PeOutBJ.
End RC__1.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2. Import QPZI.Mq4. Import QkMG. Import QG8z QIsM.Mq2.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QugP QlKV.Mqf QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSCallA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

Lemma pe_memappend_g :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (xb xn bnd : Z) (src : list byte)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts bnd -> bnd + xn <= t_co ts + 1 -> 0 <= xn < 2^31 ->
forall kB : nat, BOK pf pa ts B kB -> bv_unsigned ra mod 2 = 0 ->
bytes_at asegs m xb src -> Z.of_nat (length src) = xn -> 0 <= xb ->
src_locA ((t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) ((pa_F pa, 2) :: FRS) xb xn ->
(0 < xn -> unpoisoned asegs m A_SB xb xn) ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2 ->
(r = xn /\ PBOKat m2 (ts_pbs ts pbs2) (bnd + xn) /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 xb) (Z_to_bv 64 xn) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9b4fc) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK Hbn Hn kB BK RA SRC SRCL Hb0 SLOC UNP K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST1].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK1 & FR1).
destruct PBK as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1 & Hbp).
pose proof (proj1 REST1) as HP1. unfold pe_blocksA, tstate_blocks in HP1. rewrite Epbs in HP1. cbn [app] in HP1.
pose proof REST1 as (_ & _ & _ & ST1 & ERR1 & _ & _ & _ & _ & _ & _ & BUD1).
assert (Hbp0 : 0 <= bpos) by (destruct CORE1 as (C1 & _); lia).
pose proof (BOK_memappend pf pa ts B kB (t_pb ts) buf cap bpos xn BK Epbs BSL Hbp0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BUDM.
assert (SPF1 : lo <= pf_spf pf - 112 - 4096 /\ pf_spf pf mod 16 = 0 /\ pf_spf pf <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62).
{ clear - LOS HT Gle Gspf SP0. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; lia. }
destruct SPF1 as (SPF1 & SPF2 & SPF3 & SPF4).
set (LBc := (t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) in *.
eapply MAPP with (lo := lo) (b := xb) (src := src) (n := xn) (pb := t_pb ts) (buf := buf) (bpos := bpos) (cap := cap);
[ exact HP1 | exact CORE1 | exact Hn | exact SRC | exact SRCL | exact Hb0 | exact SLOC | exact UNP
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; exact SPF1
| rewrite unsigned_lit by lia; exact SPF2
| rewrite unsigned_lit by lia; exact SPF3
| exact ERR1 | reflexivity | exact RA | reflexivity | reflexivity | reflexivity
| exact (proj1 BUDM) | ].
intros ms2 md2 A2 (m2 & r & errv2 & buf' & cap' & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & HB2 & HD2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp hla_base A4L A4H] in *. rewrite ?(unsigned_lit (pf_spf pf)) in ST2 by lia. rewrite ?(unsigned_lit (pf_spf pf)) in HPR2 by lia.
set (pbs2 := [(t_pb ts, 16); (buf', cap')]).
assert (INq2 : In (q, 32 * pf_mxd pf) LBc) by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (pf_tk pf, 72) LBc) by (apply in_or_app; right; left; reflexivity).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR2 | lia | exact GEO | | | exact FR1].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk2 | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR2 (in_or_app _ _ _ (or_introl INq2))) in TSK1; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK1.
assert (BUD2 : PE_BUD pf pa (ts_pbs ts pbs2) B2).
{ destruct OUT2 as [(_ & Ec & _) | (_ & Eb & Ec & _ & _)].
- subst cap'. exact (BOK_weak _ _ _ _ _ (proj2 BUDM buf' B2 HB2 HD2)).
- subst buf' cap'. unfold pbs2. change 16 with PB_SZ. rewrite <- Epbs. replace (ts_pbs ts (t_pbs ts)) with ts by (destruct ts; reflexivity).
exact (BOK_memappend_fail pf pa ts B B2 kB (t_pb ts) buf cap bpos xn BK Epbs Hbp0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HB2 HD2). }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) errv2).
{ eapply (PE_REST_A_call_pb HIx GA GA_pres) with (ts := ts) (LBc := LBc);
[exact STC | exact REST1 | exact VM2 | exact HPR2 | | | exact ST2 | exact ERR2 | exact BUD2].
- unfold LBc; intros b Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]].
- unfold pe_blocksA, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs]; exact HP2. }
assert (PBany : pbuf asegs m2 pbs2 (t_pb ts)).
{ destruct OUT2 as [(_ & _ & PBS) | (_ & -> & -> & _ & PC)]; [eapply pbufc_pbuf; exact PBS|].
exists buf, bpos, cap, pre, post. split; [reflexivity|]. split; [exact Lpre | exact PC]. }
assert (INV2 : PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2).
{ split; [| exact REST2]. unfold PE_CORE_A, ts_pbs; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK1 | exact FR2]. }
assert (Hbl : 0 <= bpos <= Z.of_nat (length (pre ++ [Z_to_bv 8 0] ++ post))) by (destruct CORE1 as (C1 & _ & C3 & _); lia).
eapply (K m2 md2 A2 B2 pbs2 errv2 r); [exact INV2 | | exact FS2 | exact FRM2].
destruct OUT2 as [(-> & Ec & PBS) | (-> & -> & -> & _ & _)].
- left. split; [reflexivity|]. split.
+ eapply (PBOKat_appended m2 _ (bnd + xn) (t_pb ts) buf' cap' bpos (pre ++ [Z_to_bv 8 0] ++ post) src); [reflexivity | reflexivity | exact PBS | exact Hbl |]. lia.
+ unfold pbs2. rewrite Ec. exact (proj2 BUDM buf' B2 HB2 HD2).
- right. split; [reflexivity|]. unfold pbs2. change 16 with PB_SZ. symmetry. exact Epbs.
Qed.

Lemma pe_memappend_c :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOK m ts 0 -> forall kB : nat, BOK pf pa ts B kB -> t_co ts < pf_len pf -> bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2 ->
(r = 1 /\ PBOK m2 (ts_pbs ts pbs2) 1 /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (pa_F pa + 64)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9b4fc) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK kB BK Hco RA K.
pose proof STC as (_ & _ & GEO & _). pose proof GEO as (_ & _ & _ & GF & GF0 & _).
pose proof INV as [(_ & _ & _ & _ & _ & _ & _ & _ & FR1) _].
eapply (pe_memappend_g pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T (pa_F pa + 64) 1 (t_co ts + 0) [cb]);
[exact STC | exact BSL | exact INV | exact PBK | lia | lia | exact BK | exact RA
| exact (pe_frameA_cbyte _ _ _ _ _ _ _ FR1) | reflexivity | lia
| right; first [left | idtac]; exists (pa_F pa), 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| intros _; exact (pe_frameA_c_unpoisoned _ _ _ _ _ _ _ GEO FR1) |].
intros m2 md2 A2 B2 pbs2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 INV2 OUT2 FS2 FRM2.
eapply (K m2 md2 A2 B2 pbs2 errv2 r); [exact INV2 | | exact FS2 | exact FRM2].
destruct OUT2 as [(-> & PBK2 & BK2) | [-> E]]; [left | right; split; [reflexivity | exact E]].
split; [reflexivity|]. split; [| exact BK2]. unfold PBOK, ts_pbs. cbn [t_co]. replace (t_co ts + 1) with (t_co ts + 0 + 1) by lia. exact PBK2.
Qed.

Lemma pe_memappend_p :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (co0 xn : Z)
(ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PBOKat m ts co0 -> 0 <= co0 -> 0 <= xn -> co0 + xn <= t_co ts + 1 -> co0 + xn <= pf_len pf -> 0 < pf_len pf ->
forall kB : nat, BOK pf pa ts B kB -> bv_unsigned ra mod 2 = 0 ->
(forall m2 md2 A2 B2 pbs2 errv2 r (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) F2 fc2,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 (ts_pbs ts pbs2) cb nb pj sv errv2 ->
(r = xn /\ PBOKat m2 (ts_pbs ts pbs2) (co0 + xn) /\ BOK pf pa (ts_pbs ts pbs2) B2 kB) \/ (r = 2^64 - 1 /\ pbs2 = t_pbs ts) ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T md2
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) w0 w1 w2 s0 s1 (Z_to_bv 64 r) w3 w4 w5 w6 w7 w8 w9
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w10 w11 w12 w13) F2 (ret_pc ra) fc2 None m2 (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (pf_sb pf + co0)) (Z_to_bv 64 xn) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9b4fc) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC BSL INV PBK Hco0 Hxn Hle1 Hle2 Hlen0 kB BK RA K.
pose proof STC as (_ & _ & _ & _ & _ & LEN & SB0 & _).
pose proof INV as [(_ & _ & CO & _) REST]. pose proof REST as (HP & _ & _ & _ & _ & STR & PLEN & SBin & _).
destruct SBin as [L0 | PL]; [exfalso; lia|].
pose proof (bytes_at_sub A4H m (pf_sb pf) payload (Z.to_nat co0) (Z.to_nat xn) STR ltac:(lia)) as SRC. cbn [hl_segs hla_base A4L A4H] in SRC. rewrite Z2Nat.id in SRC by lia.
eapply (pe_memappend_g pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T (pf_sb pf + co0) xn co0 (firstn (Z.to_nat xn) (skipn (Z.to_nat co0) payload)));
[exact STC | exact BSL | exact INV | exact PBK | exact Hle1 | lia | exact BK | exact RA | exact SRC
| rewrite length_firstn, length_skipn; lia | lia | | | exact K].
- destruct PL as [([b0 n0] & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)]; cbn [blk_addr blk_size fst snd] in *.
+ left. exists b0, n0. split; [apply in_or_app; right; right; right; exact Hb | lia].
+ right. first [left | idtac]. exists Fh, kh. split; [right; exact HFh | lia].
- intros Hn0. destruct PL as [([b0 n0] & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & UPS)]; cbn [blk_addr blk_size fst snd] in *.
+ eapply (unpoisoned_of_blk HIx); [exact HP | unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb | lia | lia | exact Hn0].
+ eapply unpoisoned_sub2; [exact UPS | lia | lia | exact Hn0].
Qed.

Lemma pe_pbreset :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (Q : machine_state -> Prop)
(ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
bv_unsigned ra mod 2 = 0 ->
(forall m2 (a1' a2' a3' a4' : word),
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts cb nb pj sv errv ->
PBOK m2 ts 0 -> pbufc asegs m2 (t_pbs ts) (t_pb ts) [] ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts + 8)) a1' a2' a3' a4' a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 (t_pb ts)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9bc54) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC INV RA K.
destruct ts as [depth levels co pbx pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
destruct PB as (buf & bpos & cap & pre & post & Epbs & Lpre & CORE1).
pose proof HP as HP1. unfold pe_blocksA, tstate_blocks in HP1. rewrite Epbs in HP1. cbn [app] in HP1.
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
set (LBc := (objbs ++ concat (map lvl_blocks levels)) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0) in *.
eapply (printbuf_reset_A HIx) with (lo := lo); [exact HP1 | exact CORE1 | rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; lia | exact RA |].
intros a1' a2' a3' a4' m2 MU WM MI2 CORE2 ST2. rewrite unsigned_lit in MU, ST2 by lia.
set (pb := pbx) in *.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP1) as ND. cbn [map app blk_addr fst] in ND.
apply List.NoDup_cons_iff in ND as [NDpb ND]. apply List.NoDup_cons_iff in ND as [NDbuf ND].
assert (Npb : forall k, ~ In (pb, k) (LBc ++ LM)) by (intros k Hin; apply NDpb; right; exact (in_map blk_addr _ _ Hin)).
assert (Nbuf : forall k, ~ In (buf, k) (LBc ++ LM)) by (intros k Hin; apply NDbuf; exact (in_map blk_addr _ _ Hin)).
assert (INpb : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LBc) ++ LM)) by (left; reflexivity).
assert (INbuf : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LBc) ++ LM)) by (right; left; reflexivity).
pose proof (blk_not_fr_iv HIx _ _ _ _ _ _ _ _ _ HP1 INpb) as NFpb. pose proof (blk_not_fr_iv HIx _ _ _ _ _ _ _ _ _ HP1 INbuf) as NFbuf.
assert (Hcap0 : 0 < cap) by (destruct CORE1 as (_ & C2 & _); lia).
assert (HW : Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= pf_spf pf)
\/ (exists a n, In (a, n) (((pb, PB_SZ) :: (buf, cap) :: LBc) ++ LM) /\ ~ In (a, n) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) ((pa_F pa, 2) :: FRS) /\ ~ In (F, fr_size k - 8) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) /\ ~ In (shad A4L F, fr_shadow_len k) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) /\
((F <= fst iv /\ snd iv <= F + fr_size k) \/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k))))
[(buf, buf + 1); (pb + 8, pb + 12); (pf_spf pf - 16, pf_spf pf)]).
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd].
- right; left. exists buf, cap. split; [exact INbuf|]. split; [| lia].
intros Hin. rewrite app_assoc in Hin. apply in_app_or in Hin as [Hin | Hin]; [exact (Nbuf _ Hin) | exact (NFbuf Hin)].
- right; left. exists pb, PB_SZ. split; [exact INpb|]. split; [| lia].
intros Hin. rewrite app_assoc in Hin. apply in_app_or in Hin as [Hin | Hin]; [exact (Npb _ Hin) | exact (NFpb Hin)].
- left. lia. }
assert (HPRc : heap_pres A4H (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2).
{ eapply (heap_pres_of_munch A4H); [exact MU | exact WM |].
eapply (client_outsideF HIx); [exact HP1 | | lia | exact HW].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb | Hb]; [left | right; exact Hb].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; right; right; exact Hb | apply in_or_app; right; exact Hb]. }
set (ts := TST depth levels co pb pbs x obj objs objbs) in *.
assert (HP2 : HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m2 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI2]. eapply (frame_writes_okF A4L HIx); [exact HP | exact MU |].
unfold pe_blocksA, tstate_blocks, ts; cbn [t_pbs t_objbs t_levels]. rewrite Epbs. cbn [app].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd].
- right; left. exists buf, cap. split; [exact INbuf | lia].
- right; left. exists pb, PB_SZ. split; [exact INpb | lia].
- left. lia. }
assert (INq2 : In (q, 32 * pf_mxd pf) LBc) by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (pf_tk pf, 72) LBc) by (apply in_or_app; right; left; reflexivity).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPRc | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPRc) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk2 | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPRc (in_or_app _ _ _ (or_introl INq2))) in TSK; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK.
assert (ERR2 : rw_cells asegs m2 A_ERRNO [C4 errv]).
{ pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP1 INpb) as Ipb. pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP1 INbuf) as Ibuf.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Ipb, Ibuf. pose proof alloc_ceiling_range as ACR.
eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat disjoint_from fst snd]. unfold A_ERRNO, A_TP. repeat split; try lia. }
assert (REST2 : PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md A B ts errv).
{ eapply (PE_REST_A_call_pb HIx GA GA_pres) with (ts := ts) (LBc := LBc) (co2 := co) (pb2 := pb) (pbs2 := pbs) (x2 := x);
[exact STC | exact REST | apply model_vm_only_refl | exact HPRc | | exact HP2 | exact ST2 | exact ERR2 | exact BUD].
unfold LBc, ts; cbn [t_objbs t_levels]; intros b Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]]. }
assert (PBC2 : pbufc asegs m2 pbs pb []).
{ exists buf, 0, cap, (skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)). split; [exact Epbs|]. split; [reflexivity | exact CORE2]. }
eapply (K m2 a1' a2' a3' a4'); [| | exact PBC2].
- split; [| exact REST2]. unfold PE_CORE_A, ts; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [eapply pbufc_pbuf; exact PBC2|]. split; [exact Hpb|]. split; [exact TSK | exact FR2].
- exists buf, 0, cap, [], (skipn 1 (pre ++ [Z_to_bv 8 0] ++ post)). unfold ts; cbn [t_pbs t_pb t_co]. split; [exact Epbs|]. split; [reflexivity|]. split; [exact CORE2 | lia].
Qed.

Hypothesis SHRINK : jo_array_shrink_A2 HIx.

Hypothesis AADD : jo_array_add_A2 HIx.

Hypothesis PUT : put_stmt_A HIx.

End PeSCallA.
End RC__1.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QCcH Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QRUw.Mq0 QkMG. Import QG8z Qdyh.Mq2 QLbz.
Import QbFI. Import QlKV.Mq2. Import QrQv.Mq4 QEUF.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Pins2.
Variable segs : list Segment.
Variable fn : fnaddrs.
Lemma jfresh_arr_new_jval : forall m BS p rc, jval segs fn (Sarr []) m BS p rc -> length BS = 3%nat -> jfresh (Sarr []) BS 24.
Proof.
intros m BS p rc J L. cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (a & ABS & ps & KBS & -> & _ & AL & _ & LK & _)).
destruct KBS as [|x KBS]; [| cbn in LK; lia]. destruct AL as (arr & size & junk & -> & _). subst BS. cbn [concat app] in L |- *.
destruct PBS as [|x PBS]; [| cbn in L; lia]. apply jtx_arr_new; reflexivity.
Qed.
Lemma jfresh_obj_new_jval : forall m BS p rc, jval segs fn (Sobj []) m BS p rc -> length BS = 3%nat -> jfresh (Sobj []) BS 24.
Proof.
intros m BS p rc J L. cbn [jval] in J. destruct J as (pb & PBS & REST & E & OP & (t & TBS & kvs & KBS & -> & _ & LH & LKV & LK & _)).
destruct KBS as [|x KBS]; [| cbn in LK; lia]. destruct LH as (tbl & size & es & svs & Ekv & -> & _).
destruct es as [|e es]; [| subst kvs; cbn in LKV; lia]. subst BS. unfold lh_blocks in *. cbn [map concat app] in L |- *.
destruct PBS as [|x PBS]; [| cbn in L; lia]. apply jtx_obj_new; reflexivity.
Qed.
End Pins2.

Lemma PBOKat_of_pbufc_nil : forall m ts, pbufc asegs m (t_pbs ts) (t_pb ts) [] -> PBOKat m ts 0.
Proof.
intros m ts (buf & bpos & size & post & E & L & C). exists buf, bpos, size, [], post. split; [exact E|]. split; [exact L|]. split; [exact C | cbn in L; lia].
Qed.
Lemma PBOK_at0 : forall m ts, PBOKat m ts 0 -> PBOK m ts (- t_co ts).
Proof. intros m ts H. unfold PBOK. replace (t_co ts + - t_co ts) with 0 by lia. exact H. Qed.
Lemma PBOK_to0 : forall m ts, PBOK m ts (- t_co ts) -> PBOKat m ts 0.
Proof. intros m ts H. unfold PBOK in H. replace (t_co ts + - t_co ts) with 0 in H by lia. exact H. Qed.

End RC__1.
End Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2EX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QCcH Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QkMG. Import QG8z Qdyh.Mq2 QLbz.
Import QlKV.Mq2. Import QrQv.Mq4 Q2EX.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma jwl_nth_le : forall levels n i l W a, jwl levels n = Some W -> nth_error levels i = Some l -> (i < n)%nat -> lw l = Some a -> a <= W.
Proof.
induction levels as [|h t IH]; intros n i l W a H Hn Hi La; [destruct i; discriminate Hn|].
destruct n as [|n]; [lia|]. cbn [jwl] in H. destruct (lw h) as [ah|] eqn:E1; [| discriminate H]. destruct (jwl t n) as [b|] eqn:E2; [| discriminate H]. injection H as <-.
destruct i as [|i]; cbn [nth_error] in Hn.
- injection Hn as ->. rewrite La in E1. injection E1 as <-. pose proof (jwl_nonneg _ _ _ E2). lia.
- pose proof (IH n i l b a E2 Hn ltac:(lia) La). pose proof (lw_nonneg _ _ E1). lia.
Qed.

Lemma JOUT_level : forall len ts l s,
JOUT len ts -> bv_unsigned (sx32 (ts_err (t_x ts))) = 0 -> nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cs l = Some s ->
exists w, jtx s (tl_cbs l) = Some (w, []) /\ w <= 26 * len + 64.
Proof.
intros len ts l s J E Hl Hcs. destruct (J E) as (W & EW & LE). unfold jw in EW.
destruct (jwl (t_levels ts) (S (t_depth ts))) as [A|] eqn:EA; [| discriminate EW]. destruct (ow _ _ _) as [b|] eqn:Eb; [| discriminate EW]. injection EW as <-.
assert (B0 : 0 <= b) by (unfold ow in Eb; destruct (zin _ _); [exact (vw_nonneg _ _ _ Eb) | injection Eb as <-; lia]).
destruct (jwl_nth _ _ _ _ _ EA Hl ltac:(lia)) as (a & La). pose proof (jwl_nth_le _ _ _ _ _ _ EA Hl ltac:(lia) La) as LA.
unfold lw in La. rewrite Hcs in La. cbn [vw] in La. destruct (jtx s (tl_cbs l)) as [[w [|? ?]]|] eqn:EJ; try discriminate La. injection La as <-.
exists w. split; [reflexivity|]. pose proof (nw_nonneg (tl_nbs l)). unfold JC1, JC0 in LE. lia.
Qed.

End RC__1.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QkMG. Import QG8z QLbz Q2Sr.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd Qiiq QSHS Q1Y6.Mq4 QrQv.Mq4 QEUF.Mq2. Import QlKV.Mq2. Import Q2EX.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition PBS_dead : list Z :=
[ST_eatws; ST_start; ST_finish; ST_array; ST_array_add; ST_array_sep; ST_ofs; ST_ofend; ST_ovalue; ST_ovadd; ST_osep; ST_array_after_sep; ST_ofs_after_sep].
Definition PBSst (st : Z) : Z :=
if st =? ST_string_escape then -1
else if st =? ST_escape_unicode then -2
else if st =? ST_esc_need_escape then -3
else if st =? ST_esc_need_u then -4
else if zin st PBS_dead then 1 else 0.
Definition PBS (ts : tstate) : Z := PBSst (cur_st ts).

Definition BTOK (pf : pe_fix) : Z := 16 * Z.max 0 (pf_len pf) + 8192.
Definition BRX (pf : pe_fix) : Z := 16 * Z.max 0 (pf_len pf) + 11008.

Definition bcls0 (st : Z) : Z :=
if zin st [ST_array; ST_array_after_sep; ST_ovalue] then 5
else if zin st [ST_start; ST_null; ST_boolean; ST_inf; ST_number; ST_string] then 4
else if st =? ST_finish then 3
else if st =? ST_array_add then 2
else if zin st [ST_array_sep; ST_ofield; ST_ofend; ST_ovadd] then 1
else 0.
Definition bval (pf : pe_fix) (c : Z) : Z :=
if c =? 5 then 2 * BTOK pf + 2304 else if c =? 4 then 2 * BTOK pf + 1792 else if c =? 3 then BTOK pf + 1792 else if c =? 2 then BTOK pf + 1280 else if c =? 1 then BTOK pf else 0.
Definition bres0 (pf : pe_fix) (st : Z) : Z := bval pf (bcls0 st).

Definition bvia (st : Z) : bool := zin st [ST_eatws; ST_comment_start; ST_comment; ST_comment_eol; ST_comment_end; ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u].
Definition bres (pf : pe_fix) (st ss : Z) : Z := if bvia st then bres0 pf ss else bres0 pf st.
Lemma bval_5 : forall pf, bval pf 5 = 2 * BTOK pf + 2304. Proof. reflexivity. Qed.
Lemma bval_4 : forall pf, bval pf 4 = 2 * BTOK pf + 1792. Proof. reflexivity. Qed.
Lemma bval_3 : forall pf, bval pf 3 = BTOK pf + 1792. Proof. reflexivity. Qed.
Lemma bval_2 : forall pf, bval pf 2 = BTOK pf + 1280. Proof. reflexivity. Qed.
Lemma bval_1 : forall pf, bval pf 1 = BTOK pf. Proof. reflexivity. Qed.
Lemma bval_0 : forall pf, bval pf 0 = 0. Proof. reflexivity. Qed.
Definition bx (pf : pe_fix) (ts : tstate) : nat := Z.to_nat (BRX pf * (pf_len pf - t_co ts) + bres pf (cur_st ts) (cur_ss ts)).
Definition bxb (pf : pe_fix) (ts : tstate) : nat := Z.to_nat (BRX pf * (pf_len pf - t_co ts - 1) + bres pf (cur_st ts) (cur_ss ts)).
Definition bloop (pf : pe_fix) (ts : tstate) : nat := (mloop pf ts + bx pf ts)%nat.
Definition bredo (pf : pe_fix) (ts : tstate) : nat := (mredo pf ts + bx pf ts)%nat.
Definition bbrk (pf : pe_fix) (ts : tstate) : nat := (mbrk pf ts + bxb pf ts)%nat.
Lemma BTOK_ge : forall pf, 8192 <= BTOK pf. Proof. intros pf. unfold BTOK. lia. Qed.
Lemma BRX_eq : forall pf, BRX pf = BTOK pf + 2816. Proof. intros pf. unfold BRX, BTOK. lia. Qed.
Lemma bval_range : forall pf c, 0 <= bval pf c <= 2 * BTOK pf + 2304. Proof. intros pf c. pose proof (BTOK_ge pf). unfold bval. repeat (destruct (_ =? _)); lia. Qed.
Lemma bres0_nonneg : forall pf st, 0 <= bres0 pf st. Proof. intros pf st. unfold bres0. pose proof (bval_range pf (bcls0 st)). lia. Qed.
Lemma bres_nonneg : forall pf st ss, 0 <= bres pf st ss. Proof. intros pf st ss. unfold bres. destruct (bvia st); apply bres0_nonneg. Qed.
Lemma bres_self : forall pf s, bres pf s s = bres0 pf s. Proof. intros pf s. unfold bres. destruct (bvia s); reflexivity. Qed.

Lemma bx_ge : forall pf ts, t_co ts <= pf_len pf -> (Z.to_nat (bres pf (cur_st ts) (cur_ss ts)) <= bx pf ts)%nat.
Proof. intros pf ts H. unfold bx. pose proof (BTOK_ge pf). pose proof (BRX_eq pf). pose proof (bres_nonneg pf (cur_st ts) (cur_ss ts)). pose proof (Z.mul_nonneg_nonneg (BRX pf) (pf_len pf - t_co ts) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma bx_mono2 : forall pf r r' k k', r' <= r -> k' <= k -> (Z.to_nat (BRX pf * r' + k') <= Z.to_nat (BRX pf * r + k))%nat.
Proof. intros pf r r' k k' H1 H2. pose proof (BTOK_ge pf). pose proof (BRX_eq pf). assert (BRX pf * r' <= BRX pf * r) by (apply Z.mul_le_mono_nonneg_l; lia). lia. Qed.
Lemma bx_mono3 : forall pf r r' k k' C, r' <= r -> k' + Z.max 0 C <= k -> (Z.to_nat (BRX pf * r' + k') <= Z.to_nat (BRX pf * r + k) - Z.to_nat C)%nat.
Proof. intros pf r r' k k' C H1 H2. pose proof (BTOK_ge pf). pose proof (BRX_eq pf). assert (BRX pf * r' <= BRX pf * r) by (apply Z.mul_le_mono_nonneg_l; lia). lia. Qed.
Lemma bx_mono4 : forall pf r r' k k' C, r' + 1 <= r -> k' + Z.max 0 C <= k + BRX pf -> (Z.to_nat (BRX pf * r' + k') <= Z.to_nat (BRX pf * r + k) - Z.to_nat C)%nat.
Proof. intros pf r r' k k' C H1 H2. pose proof (BTOK_ge pf). pose proof (BRX_eq pf). assert (BRX pf * r' <= BRX pf * (r - 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. Qed.

Lemma bsplit_S : forall a b m x C : nat, (a <= S m)%nat -> (b <= x)%nat -> (C <= x)%nat -> (a + b <= S (C + (m + (x - C))))%nat.
Proof. intros. lia. Qed.

Definition EUS : list Z := [ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u].
Definition UCSV (x : tscal) : Z := bv_unsigned (ts_ucs x) mod 2^32.
Definition euok_b (x : tscal) : bool := (SPV x =? 0) && (UCSV x <? 65536).
Definition OBJW (pj : pe_junkA) (ts : tstate) : Prop :=
(zin (cur_st ts) [ST_array_add; ST_ovadd] = true -> pj_obj pj = Z_to_bv 64 (t_obj ts)) /\
(zin (cur_st ts) EUS = true -> SPV (t_x ts) = 0 /\ UCSV (t_x ts) < 65536).

Definition NAO (ts : tstate) : Prop := (zin (cur_st ts) [ST_array_add; ST_ovadd] || (zin (cur_st ts) EUS && negb (euok_b (t_x ts)))) = false.
Lemma OBJW_of_NAO : forall pj ts, NAO ts -> OBJW pj ts.
Proof.
intros pj ts H. unfold NAO in H. apply orb_false_iff in H as [H1 H2]. split.
- intros E. rewrite H1 in E. discriminate E.
- intros E. rewrite E in H2. cbn [andb] in H2. apply negb_false_iff in H2. unfold euok_b in H2. apply andb_true_iff in H2 as [HA HB].
split; [apply Z.eqb_eq; exact HA | apply Z.ltb_lt; exact HB].
Qed.
Lemma NAO_plain : forall ts, zin (cur_st ts) [ST_array_add; ST_ovadd] = false ->
zin (cur_st ts) [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false -> NAO ts.
Proof.
intros ts H1 H2. unfold NAO. rewrite H1. cbn [orb]. apply andb_false_iff. left.
cbn [zin] in H2. apply orb_false_iff in H2 as [_ H2]. unfold EUS. cbn [zin]. exact H2.
Qed.
Lemma NAO_eu : forall ts, zin (cur_st ts) [ST_array_add; ST_ovadd] = false -> SPV (t_x ts) = 0 -> UCSV (t_x ts) < 65536 -> NAO ts.
Proof.
intros ts H1 HS HU. unfold NAO. rewrite H1. cbn [orb]. apply andb_false_iff. right. apply negb_false_iff. unfold euok_b.
apply andb_true_iff. split; [apply Z.eqb_eq; exact HS | apply Z.ltb_lt; exact HU].
Qed.

Definition PBJ (m : word -> option byte) (ts : tstate) (k a : Z) : Prop := exists g, PBOKat m ts g /\ g <= t_co ts + k /\ JL ts g a.
Lemma PBJ_PBOK : forall m ts k a, PBJ m ts k a -> PBOK m ts k.
Proof. intros m ts k a (g & P & Hg & _). unfold PBOK. eapply PBOKat_weaken; [exact Hg | exact P]. Qed.
Lemma PBOKat_nonneg : forall m ts b, PBOKat m ts b -> 0 <= b.
Proof. intros m ts b (buf & bpos & size & pre & post & _ & L & _ & Hb). lia. Qed.

Lemma JOUT_of_PBJ : forall len m ts ts' k a, PBJ m ts k a -> a <= len -> t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts ->
(zin (cur_st ts) [ST_array_add; ST_ovadd] = true -> t_objs ts' = t_objs ts /\ t_objbs ts' = t_objbs ts) -> JOUT len ts'.
Proof. intros len m ts ts' k a (g & P & _ & J) Ha E1 E2 E3. eapply (JOUT_of_JL len ts ts' g a J (PBOKat_nonneg _ _ _ P) Ha). apply jw_same; assumption. Qed.

Section PeSKontA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Let tk36 := Z_to_bv 64 (pf_tk pf + 36).
Let two := Z_to_bv 64 2.

Definition KLOOP_S (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 a0 a1 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(mloop pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv ->
cur_st ts <> ST_number -> SPOK ts 0 -> tdepth_ok ts ->
(pf_lenr pf <> pf_len pf -> t_co ts < pf_len pf) ->
PBJ m ts (PBS ts) (t_co ts) -> BOK pf pa ts B (bloop pf ts) -> NAO ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_LOOP (t_co ts) gp t0 a0 a1 tk36 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).

Definition KREDO_S (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(mredo pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
NUMC_A ts m -> SPOK ts 0 -> tdepth_ok ts ->
PBJ m ts (PBS ts) (t_co ts) -> BOK pf pa ts B (bredo pf ts) -> OBJW pj ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).

Definition KBRK_S (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(mbrk pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
cur_st ts <> ST_number -> SPOK ts 1 -> tdepth_ok ts ->
PBJ m ts (PBS ts + 1) (t_co ts + 1) -> BOK pf pa ts B (bbrk pf ts) -> NAO ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 two s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).

Definition KADV_S (n : nat) : Prop := KBRK_S n.

Definition KALL_S (n : nat) : Prop := KLOOP_S n /\ KREDO_S n /\ KBRK_S n /\ KADV_S n.

Definition KOUT_S : Prop :=
forall (ts : tstate) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts -> JOUT (pf_len pf) ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msO asegs pf pa APE_OUT gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Definition KERR2_S : Prop :=
forall (ts : tstate) (LK : list blk) (e : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
0 < e < 2^31 ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (Q1Y6.Mq4.pe_msE pf pa APE_ERR2 gp t0 t1 t2 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).

Definition CASE_S (st : Z) : Prop :=
forall (n : nat) (ts : tstate) (l : tlevel) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = st ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
NUMC_A ts m -> SPOK ts 0 -> tdepth_ok ts ->
PBJ m ts (PBS ts) (t_co ts) -> BOK pf pa ts B (bredo pf ts) -> OBJW pj ts ->
bytes_at asegs me UTF8REP_ADDR_A utf8rep ->
CSTR_OK pf payload ->
fsaved F0 F -> frm0 fc ->
(mredo pf ts <= n)%nat -> KALL_S n ->
KOUT_S -> KERR2_S ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA st) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
End PeSKontA.

Lemma PBSst_plain_range : forall st, zin st [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false -> 0 <= PBSst st <= 1.
Proof.
intros st H. unfold PBSst. cbn [zin] in H. apply orb_false_iff in H as [H1 H]. apply orb_false_iff in H as [H2 H]. apply orb_false_iff in H as [H3 H]. apply orb_false_iff in H as [H4 _].
rewrite H1, H2, H3, H4. destruct (zin st PBS_dead); lia.
Qed.
End RC__1.

Ltac pbs_norm :=
repeat match goal with
| |- context [PBSst ?s] => let v := eval vm_compute in (PBSst s) in lazymatch v with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end; change (PBSst s) with v
end.
Ltac pbs_norm_in H :=
repeat match type of H with
| context [PBSst ?s] => let v := eval vm_compute in (PBSst s) in lazymatch v with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end; change (PBSst s) with v in H
end.

Ltac bres_norm :=
rewrite ?bres_self; unfold bres, bres0;
repeat match goal with |- context [bvia ?s] => let v := eval vm_compute in (bvia s) in (first [constr_eq v true | constr_eq v false]; change (bvia s) with v) end;
cbv iota;
repeat match goal with |- context [bcls0 ?s] => let v := eval vm_compute in (bcls0 s) in (lazymatch v with Z0 => idtac | Zpos _ => idtac end; change (bcls0 s) with v) end;
rewrite ?bval_5, ?bval_4, ?bval_3, ?bval_2, ?bval_1, ?bval_0.
Ltac bres_norm_in H :=
rewrite ?bres_self in H; unfold bres, bres0 in H;
repeat match type of H with context [bvia ?s] => let v := eval vm_compute in (bvia s) in (first [constr_eq v true | constr_eq v false]; change (bvia s) with v in H) end;
cbv iota in H;
repeat match type of H with context [bcls0 ?s] => let v := eval vm_compute in (bcls0 s) in (lazymatch v with Z0 => idtac | Zpos _ => idtac end; change (bcls0 s) with v in H) end;
rewrite ?bval_5, ?bval_4, ?bval_3, ?bval_2, ?bval_1, ?bval_0 in H.

Ltac bx_fin := match goal with |- context [BRX ?p] => pose proof (BTOK_ge p); pose proof (BRX_eq p) end; unfold BTOK in *; first [lia | (apply bx_mono2; lia) | (apply bx_mono3; lia) | (apply bx_mono4; lia)].
Ltac bx_tac Hl Hst :=
repeat match goal with x := _ : tlevel |- _ => subst x end;
unfold bx, bxb, cur_st, cur_ss;
cbn [ts_lvl ts_pbs ts_set_co ts_set_x ts_lvl_obj t_levels t_depth t_co];
rewrite ?nth_error_lupd_eq by (apply nth_error_Some; rewrite Hl; discriminate);
rewrite ?Hl; cbn [tl_st tl_ss]; rewrite ?Hst;
repeat match goal with
| H : ?x = _ \/ ?x = _ |- context [bres _ ?x _] => destruct H as [-> | ->]
| H : ?x = _ \/ ?x = _ |- context [bres _ _ ?x] => destruct H as [-> | ->]
| H : (_ /\ ?x = _) \/ (_ /\ ?x = _) |- context [bres _ ?x _] => destruct H as [[_ ->] | [_ ->]]
| H : (_ /\ ?x = _) \/ (_ /\ ?x = _) |- context [bres _ _ ?x] => destruct H as [[_ ->] | [_ ->]]
end;
bres_norm; bx_fin.
End Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Ki QZUC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki. Import QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq2 Q2Sr QLbz.
Import Q6WR.Mq0 QrPc.
Import QbFI QXUB. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh Q30W.Mq6 QlKV.Mqf QsKa.Mqd QlKV.Mqc Qiiq QSHS Ql4f.Mq4 Q1Y6.Mq4 QlKV.Mqe QrQv QGdd.Mq0.
Import Qc5u QZUC.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lb_remove_app_notin : forall p (L1 L2 : list blk), (forall n, ~ In (p, n) L1) -> lb_remove p (L1 ++ L2) = L1 ++ lb_remove p L2.
Proof.
induction L1 as [|[a n] L1 IH]; intros L2 H; [reflexivity|]. cbn [app lb_remove blk_addr fst].
destruct (Z.eqb_spec a p) as [->|NE]; [exfalso; apply (H n); left; reflexivity|]. f_equal. apply IH. intros k Hk. apply (H k). right; exact Hk.
Qed.

Section PeSOutTopB.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.

Definition po_top_postB (pf : pe_fix) (pa : pe_fixA) (gp s4 s6 s7 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : config) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (l : tlevel) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (B' : bud) F' fc' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (Z.of_nat i)) s4 (Z_to_bv 64 (-1)) s6 s7 (Z_to_bv 64 (pf_tk pf)) s9 (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x99af0) fc' None m' (seg_rom asegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only (cfg_model md) (cfg_model md') /\
HEAPAx A' (tl_cbs l ++ REST) LM ((pa_F pa, 2) :: FRS) B' m' md' /\
tstack asegs m' q (lupd levels i lvl_reset) /\
rw_cells asegs m' (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb depth q x) /\
pe_frameA asegs m' pf pa cb nb pj sv /\
stk asegs m' lo (pf_spf pf) /\
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) me m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
agree_on asegs P mpre m' /\
jopt asegs A4F (tl_cs l) m' (tl_cbs l) (tl_cur l) /\
bB B - 512 <= bB B' /\ bD B <= bD B'.

Lemma po_body_topB :
forall (pf : pe_fix) (pa : pe_fixA) (i : nat) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s9 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (l : tlevel) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved),
PE_STATIC_A HIx pf pa lo ->
nth_error levels i = Some l -> (i < Z.to_nat (pf_mxd pf))%nat -> length levels = Z.to_nat (pf_mxd pf) ->
HEAPAx A (lvl_blocks l ++ REST) LM ((pa_F pa, 2) :: FRS) B m md ->
REST = P ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0 ->
match tl_cs l with Some s => tl_cur l <> 0 /\ jval asegs A4F s m (tl_cbs l) (tl_cur l) 2 | None => tl_cur l = 0 /\ tl_cbs l = [] end ->
((tl_name l = 0 /\ tl_nbs l = []) \/ (tl_name l <> 0 /\ exists nn, tl_nbs l = [(tl_name l, nn)])) ->
tstack asegs m q levels ->
rw_cells asegs m (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb depth q x) ->
pe_frameA asegs m pf pa cb nb pj sv ->
stk asegs m lo (pf_spf pf) ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) me m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
512 <= bB B ->
(forall ms' md' A', po_top_postB pf pa gp s4 s6 s7 s9 s11 F fc md REST LB0 P LM FRS B me m lo errv q pb depth x levels i l cb nb pj sv ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md (MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (Z.of_nat i)) s4 (Z_to_bv 64 (-1)) s6 s7 (Z_to_bv 64 (pf_tk pf)) s9 (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x99ae4) fc None m (seg_rom asegs)).
Proof.
intros until sv. intros STC Hl Hi LEN HP EREST CUR NM TS BLK FR ST HPR ERR BB K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
evt_done5.
eapply (tok_reset_level_B_cps HIx PUT) with (i := i) (l := l) (levels := levels) (P := P) (LB0 := LB0) (LM := LM) (REST := REST)
(FRS := (pa_F pa, 2) :: FRS) (B := B) (lo := lo) (errv := errv) (q := q) (r := pf_tk pf) (pb := pb) (depth := depth) (mxd := pf_mxd pf) (fl := pf_fl pf)
(x := x) (rc := 2) (me := m);
[ exact Hl | lia | exact (proj1 (proj2 RR)) | exact LEN | exact HP | exact EREST
| unfold put_pre; destruct (tl_cs l) as [s'|]; [destruct CUR as [Hp J]; split; [exact Hp | split; [lia | exact J]] | exact CUR]
| exact NM | exact TS | exact BLK
| rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; unfold put_stk_A; clear - LOS; lia
| rewrite unsigned_lit by lia; clear - Gspf; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; clear - HT Gle; lia
| apply heap_pres_refl | exact ERR
| unfold put_costA; destruct (tl_cs l); cbn; lia
| rewrite unsigned_lit by lia; reflexivity | ].
intros ms2 md2 A2 (m2 & B2 & rv & RS2 & VM2 & OUT2 & TS2 & TOK2 & ST2 & HPR2 & ERR2 & AG2 & BB2 & BD2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
apply K. unfold po_top_postB.
exists m2, B2, F2, fc2. do 16 eexists.
split; [reflexivity|]. split; [exact FS2|]. split; [exact FRM2|]. split; [exact VM2|].
assert (HJ : HEAPAx A2 (tl_cbs l ++ REST) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 /\ jopt asegs A4F (tl_cs l) m2 (tl_cbs l) (tl_cur l)).
{ destruct OUT2 as [([Es | Erc] & H) | (s' & Es & _ & J' & H)]; [| exfalso; lia |].
- rewrite Es in CUR |- *. destruct CUR as [Ep EBS]. rewrite EBS. cbn [app jopt]. split; [exact H | split; [exact Ep | reflexivity]].
- rewrite Es in CUR |- *. destruct CUR as [Hp _]. cbn [jopt]. replace (2 - 1) with 1 in J' by lia. split; [exact H | split; [exact Hp | exact J']]. }
destruct HJ as [HP2 JO2].
split; [exact HP2|]. split; [exact TS2|]. split; [exact TOK2|].
split.
{ eapply pe_frameA_pres; [exact HPR2 | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
split; [exact ST2|]. split; [eapply heap_pres_trans; [exact HPR | exact HPR2]|]. split; [exact ERR2|]. split; [exact AG2|]. split; [exact JO2|].
unfold put_costA in BB2. destruct (tl_cs l); cbn in BB2; lia.
Qed.
End PeSOutTopB.
End RC__1.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QRUw.Mq2 QmZZ. Import QPZI.Mq4. Import QkMG. Import QG8z Qdyh.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QlKV.Mqh QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition tsF (ts : tstate) (BS : list blk) : tstate :=
TST (t_depth ts) (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) 0 None BS.

Definition lvl_bare (l : tlevel) : Prop :=
0 <= tl_st l <= 26 /\ 0 <= tl_ss l <= 26 /\ tl_cs l = None /\ tl_cbs l = [] /\ tl_name l = 0 /\ tl_nbs l = [].

Lemma lvl_mode_finish : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_finish ss = Some (c, hn) -> c = CAny /\ hn = false /\ ss = ST_finish.
Proof.
intros ss c hn R H. assert (CASES : exists k : nat, (k <= 26)%nat /\ ss = Z.of_nat k) by (exists (Z.to_nat ss); split; lia).
destruct CASES as (k & Hk & ->). clear R.
do 27 (destruct k as [|k]; [vm_compute in H; first [discriminate H | injection H as <- <-; split; [reflexivity | split; reflexivity]] |]); exfalso; lia.
Qed.

Lemma BOK_pop : forall pf pa ts B n l dp,
BOK pf pa ts B n -> t_depth ts = S dp -> nth_error (t_levels ts) (S dp) = Some l -> tl_nbs l = [] -> t_objbs ts = [] ->
BOK pf pa (TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) B n.
Proof.
intros pf pa ts B n l dp (H1 & H2 & H3 & H4 & H5) Ed Hl Hnbs Eobj.
set (lr := TL ST_eatws ST_start 0 None [] 0 []).
pose proof (H5 (S dp) l ltac:(lia) Hl) as [P0 _].
assert (Eled : ledger_open (lupd (t_levels ts) (S dp) lr) (S dp) = ledger_open (t_levels ts) (S dp)) by (apply ledger_open_lupd_out; lia).
assert (Eled2 : ledger_open (t_levels ts) (S (S dp)) = ledger_open (t_levels ts) (S dp) + phi_open l) by (apply ledger_open_S; exact Hl).
assert (Eblk : Z.of_nat (length (tstate_blocks (TST dp (lupd (t_levels ts) (S dp) lr) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)))) = Z.of_nat (length (tstate_blocks ts))).
{ unfold tstate_blocks; cbn [t_pbs t_objbs t_levels]. rewrite Eobj. cbn [app].
rewrite (lupd_split _ _ _ lr Hl), (concat_split _ _ _ Hl). change (lvl_blocks lr) with (@nil blk). unfold lvl_blocks. rewrite Hnbs, app_nil_r. rewrite !length_app. cbn [length app]. lia. }
split.
{ unfold bneed in *. rewrite Eblk. cbn [t_levels t_depth t_pbs]. rewrite Ed in H1. rewrite Eled. rewrite Eled2 in H1. lia. }
split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
cbn [t_levels t_depth]. intros i li Hi Hn. rewrite nth_error_lupd_neq in Hn by lia. exact (H5 i li ltac:(lia) Hn).
Qed.

Lemma BOK_attach : forall pf pa ts B B' n l st' ss' p s BS c {C},
BOK pf pa ts B (S (Z.to_nat C + n)) -> nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cs l = None -> lvl_blocks l = [] ->
0 <= phi_level (TL st' ss' p (Some s) BS 0 []) ->
c + K_free * Z.of_nat (length BS) + phi_level (TL st' ss' p (Some s) BS 0 []) <= C ->
(forall kids, s = Sarr kids -> arr_inv (arr_capA BS) (Z.of_nat (length kids))) ->
(forall kids, s = Sobj kids -> In (obj_capA BS) Q8tj.lf_sizes) ->
bB B - c <= bB B' -> bD B - 1 <= bD B' ->
BOK pf pa (ts_lvl ts (TL st' ss' p (Some s) BS 0 [])) B' n.
Proof.
intros pf pa ts B B' n l st' ss' p s BS c C (H1 & H2 & H3 & H4 & H5) Hl Ecs Eb P0 HC AI OI HB HD.
set (l' := TL st' ss' p (Some s) BS 0 []) in *.
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
assert (Ephi : phi_open l = 0) by (unfold phi_open, phi_level; rewrite Ecs; destruct (lvl_closed l); reflexivity).
assert (Hphi' : 0 <= phi_open l' <= phi_level l') by (unfold phi_open; destruct (lvl_closed l'); lia).
pose proof (tstate_blocks_lvl_length ts l l' Hl) as Hblk. rewrite Eb in Hblk. cbn [length] in Hblk.
assert (Elb : Z.of_nat (length (lvl_blocks l')) = Z.of_nat (length BS)) by (unfold lvl_blocks, l'; cbn [tl_cbs tl_nbs]; rewrite app_nil_r; reflexivity).
unfold BOK, bneed in *.
replace (K_ev pf * Z.of_nat (S (Z.to_nat C + n))) with (K_ev pf * Z.of_nat n + (Z.max 0 C + 1)) in H1 by (unfold K_ev; lia).
split.
{ rewrite Hblk, Elb. unfold ts_lvl; cbn [t_levels t_depth t_pbs]. rewrite (ledger_open_lupd (t_levels ts) (S (t_depth ts)) (t_depth ts) l l' Hl (Nat.lt_succ_diag_r _)), Ephi.
unfold K_free in *. lia. }
split; [lia|]. split; [exact H3|]. split; [exact H4|].
unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hi Hn.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | NE].
- rewrite nth_error_lupd_eq in Hn by exact Hd. injection Hn as <-. split; [lia|].
split; [intros _ kids Hk; apply AI; unfold l' in Hk; cbn [tl_cs] in Hk; injection Hk as ->; reflexivity|].
split; [intros _ kids Hk; unfold l'; cbn [tl_cbs]; apply (OI kids); unfold l' in Hk; cbn [tl_cs] in Hk; injection Hk as ->; reflexivity | apply Forall_nil].
- rewrite nth_error_lupd_neq in Hn by congruence. exact (H5 i li Hi Hn).
Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Definition PE_WIN (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (p : Z) (s : option jshape) (BS : list blk) (rc : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) : Prop :=
PE_CORE_A pf pa q m ts cb nb pj sv /\
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 (tsF ts BS)) errv /\
(forall i li, nth_error (t_levels ts) i = Some li -> i <> t_depth ts -> lvl_cur asegs A4F m (t_depth ts) i li) /\
(exists l, nth_error (t_levels ts) (t_depth ts) = Some l /\ lvl_bare l) /\
t_objbs ts = [] /\
put_pre A4H A4F s m BS p rc.

Lemma PE_BASE_A_private_write : forall pf pa q LB0 LM FRS payload me lo m m' md A B ts errv W,
PE_STATIC_A HIx pf pa lo ->
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 ts) errv ->
munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall (pe_privateA pf pa q (t_pbs ts)) W ->
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m' md A B (pe_blocksA pf q LB0 ts) errv /\
agree_on asegs (t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) m m'.
Proof.
intros pf pa q LB0 LM FRS payload me lo m m' md A B ts errv W STC (HP & ST & ERR & STR & PLEN & SBin & HPR & MDV & G) MU WM MI HW.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & _). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_hi A4L HIx) as HTH.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INtk) as (_ & _ & _ & Htkhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INq) as (_ & _ & _ & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INtk) as Himg_t. pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INq) as Himg_q.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & HFimg & _).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_t, Himg_q, HFimg. rewrite fr_size_2 in HFimg.
pose proof (own_frame_fresh HIx _ _ _ _ _ _ _ _ _ _ _ HP) as [OFF OFS].

assert (AG : agree_on asegs (t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) m m').
{ eapply agree_of_munch; [exact MU | exact WM |]. intros a n Hin.
assert (HinP : In (a, n) (tstate_blocks ts)) by (unfold tstate_blocks; apply in_or_app; right; exact Hin).
assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; left; exact HinP).
unfold pe_blocksA in ND.
eapply private_disjointA; [exact STC | exact HP | exact HinL | | | | exact HW].
- rewrite <- app_assoc in ND. eapply (nodup_app_ne _ _ _ _ _ _ ND HinP). left; reflexivity.
- rewrite <- app_assoc in ND. eapply (nodup_app_ne _ _ _ _ _ _ ND HinP). right; left; reflexivity.
- intros b k Hb. unfold tstate_blocks in ND. rewrite <- app_assoc in ND. exact (nd_pbs_ne _ _ _ _ _ _ _ _ ND Hb Hin). }

assert (HWF : Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hiA_top A4L HIx)
\/ (exists a n, In (a, n) (pe_blocksA pf q LB0 ts ++ LM) /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) ((pa_F pa, 2) :: FRS) /\ ((F <= fst iv /\ snd iv <= F + fr_size k - 8)
\/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))) W).
{ eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_privateA in Hiv. cbn [fst snd] in *.
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]].
- right; left. exists (pf_tk pf), 72. split; [exact INtk | lia].
- right; left. exists q, (32 * pf_mxd pf). split; [exact INq | lia].
- right; left. exists b, k. split; [| lia]. unfold pe_blocksA, tstate_blocks. apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb.
- left. lia.
- right; right; right. exists (pa_F pa), 2. split; [exact INF|]. left. rewrite fr_size_2. lia.
- right; right; right. exists (pa_F pa), 2. split; [exact INF|]. right. unfold shad, shA in H1 |- *. cbn [hl_sb hla_base A4L A4H]; rewrite ?fr_size_2, ?fr_shadow_len_2. unfold A_SB in H1 |- *. lia. }
assert (HIMG : Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W).
{ eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_privateA in Hiv. cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H] in *.
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]]; [lia | lia | | lia | lia |].
- pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ b k HP ltac:(unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb)) as Hbi.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbi. lia.
- unfold shA in H1. unfold A_SB in H1. pose proof (Z.div_pos (pa_F pa) 8 ltac:(lia) ltac:(lia)). lia. }
split; [| exact AG].
split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [exact MDV | exact (GA_outside _ _ _ G MU WM HIMG)]]]]]]]].
- eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx); [exact HP | exact MU | exact HWF].
- eapply (stk_transport_disjoint asegs); [exact ST | exact MU | exact WM |].
destruct ST as (ST0 & ST1 & _).
clear - HW LOS LO ST0 ST1 Htkhi Hqhi HP Gle GFc ACR. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold pe_privateA in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]]; try lia.
+ assert (INb : In (b, k) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INb) as (_ & _ & _ & Hbhi & _). lia.
+ unfold shA, A_SB in H1. Z.div_mod_to_equations. lia.
- eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat]. unfold A_ERRNO, A_TP.
clear - HW LOS LO Himg_t Himg_q Htkhi Hqhi HP SP0 HFimg Gle GFc GF0 ACR. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold pe_privateA in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]]; try lia.
+ assert (INb : In (b, k) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INb) as Hbi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbi.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INb) as (Hk0 & _ & _ & _ & _). lia.
+ unfold shA, A_SB in H1. Z.div_mod_to_equations. lia.
- eapply payload_privateA; [exact STC | exact HP | exact STR | exact PLEN | exact SBin | exact MU | exact HW].
- exact PLEN.
- eapply payload_locA_private; [exact STC | exact HP | exact SBin | exact MU | exact HW].
- eapply heap_presx_trans; [exact HPR|].
eapply (heap_presx_of_munch A4H a4_volatile); [exact MU | exact WM |].
eapply client_outsideF; [exact HP | | lia |].
{ intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb | Hb].
- left. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb | right; exact Hb].
- right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb. }
eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_privateA in Hiv. cbn [fst snd] in *.
assert (NB : forall a n, In (a, n) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)]) -> ~ In (a, n) (LB0 ++ LM ++ fr_ivs A4L FRS)).
{ intros a n Ha Hin. rewrite app_assoc in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_app_or in Hin as [Hin | Hin]; [exact (private_not_LB0A HIx _ _ _ _ _ _ _ _ _ _ _ _ n HP Ha Hin)|].
assert (HaX : In (a, n) (pe_blocksA pf q LB0 ts)).
{ unfold pe_blocksA. apply in_app_or in Ha. apply in_or_app. destruct Ha as [Ha | [Ha | [Ha | []]]]; [left; exact Ha | right; left; exact Ha | right; right; left; exact Ha]. }
exact (nodup_app_ne _ _ _ _ _ _ ND HaX Hin eq_refl).
- exact (blk_not_fr_iv HIx _ _ _ _ _ _ _ _ _ HP (private_in_blocksA _ _ _ LM _ _ _ Ha) ltac:(unfold fr_ivs in *; cbn [flat_map]; apply in_or_app; right; exact Hin)). }
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]].
+ right; left. exists (pf_tk pf), 72. split; [exact INtk|]. split; [| lia]. apply NB. apply in_or_app; right; left; reflexivity.
+ right; left. exists q, (32 * pf_mxd pf). split; [exact INq|]. split; [| lia]. apply NB. apply in_or_app; right; right; left; reflexivity.
+ right; left. exists b, k. split; [unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb|]. split; [| lia].
apply NB. apply in_or_app; left. unfold tstate_blocks; apply in_or_app; left; exact Hb.
+ left. lia.
+ right; right; right. exists (pa_F pa), 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. rewrite fr_size_2. lia.
+ right; right; right. exists (pa_F pa), 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right.
unfold shad, shA in H1 |- *. cbn [hl_sb hla_base A4L A4H]; rewrite ?fr_size_2, ?fr_shadow_len_2. unfold A_SB in H1 |- *. lia.
Qed.

Lemma PE_BASE_A_callG : forall pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 LBall LBall2 errv errv2 LBc,
PE_STATIC_A HIx pf pa lo ->
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m1 md A B LBall errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
incl LB0 LBc ->
HEAPA A4L HIx A2 LBall2 LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m2 md2 A2 B2 LBall2 errv2.
Proof.
intros pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 LBall LBall2 errv errv2 LBc STC
(HP & ST & ERR & STR & PLEN & SBin & HPR & MDV & G) VM12 HPRc Hincl HP2 ST2 ERR2.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
split; [exact HP2|]. split; [exact ST2|]. split; [exact ERR2|].
assert (SBin2 := payload_locA_pres HIx pf pa LB0 FRS _ _ _ _ _ _ _ LBc _ _ _ HP (incl_tl _ (incl_refl _)) HPRc SBin).
assert (FRI : incl (fr_ivs A4L FRS) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS))).
{ intros b Hb. apply in_or_app; right. apply in_or_app; right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb. }
split; [| split; [exact PLEN | split; [exact SBin2 | split; [| split]]]].
- eapply payload_presA; [exact HPRc | intros x Hx; apply in_or_app; left; apply Hincl; exact Hx | exact FRI | | exact STR | exact PLEN | exact SBin]. lia.
- eapply heap_presx_trans; [exact HPR|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPRc | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply Hincl; exact Hb|].
apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb.
- eapply model_vm_only_trans; [exact MDV | exact VM12].
- eapply GA_pres; [exact HPRc | exact G].
Qed.

Lemma pe_blocksA_tsF_lvl : forall pf q LB0 ts BS l l', nth_error (t_levels ts) (t_depth ts) = Some l -> lvl_blocks l' = lvl_blocks l ->
pe_blocksA pf q LB0 (tsF (ts_lvl ts l') BS) = pe_blocksA pf q LB0 (tsF ts BS).
Proof.
intros pf q LB0 ts BS l l' Hl E. unfold pe_blocksA, tstate_blocks, tsF, ts_lvl; cbn [t_pbs t_objbs t_levels t_depth].
rewrite (map_lupd_same lvl_blocks (t_levels ts) (t_depth ts) l' l Hl E). reflexivity.
Qed.

Lemma incl_blocks_tsF : forall pf q LB0 ts BS, t_objbs ts = [] -> incl (pe_blocksA pf q LB0 ts) (pe_blocksA pf q LB0 (tsF ts BS)).
Proof.
intros pf q LB0 ts BS E b Hb. unfold pe_blocksA, tstate_blocks, tsF in *; cbn [t_pbs t_objbs t_levels] in *. rewrite E in Hb. cbn [app] in Hb.
apply in_app_or in Hb as [Hb | Hb]; [| apply in_or_app; right; exact Hb]. apply in_or_app; left.
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb].
Qed.

Lemma perm_blocks_tsF : forall pf q LB0 ts BS, t_objbs ts = [] -> Permutation (pe_blocksA pf q LB0 (tsF ts BS)) (BS ++ pe_blocksA pf q LB0 ts).
Proof.
intros pf q LB0 ts BS E. unfold pe_blocksA, tstate_blocks, tsF; cbn [t_pbs t_objbs t_levels]. rewrite E. cbn [app]. rewrite <- !app_assoc.
apply Permutation_app_swap_app.
Qed.

Lemma lvl_cur_popA : forall m dp i li, i <> S dp -> lvl_cur asegs A4F m (S dp) i li -> lvl_cur asegs A4F m dp i li.
Proof.
intros m dp i li Hne (R1 & R2 & J & M). split; [exact R1|]. split; [exact R2|]. split; [exact J|].
destruct (Nat.lt_ge_cases i dp) as [Hlt | Hge].
- rewrite (proj2 (Nat.ltb_lt i dp) Hlt). rewrite (proj2 (Nat.ltb_lt i (S dp))) in M by lia. exact M.
- rewrite (proj2 (Nat.ltb_ge i dp) Hge). destruct (Nat.eq_dec i dp) as [-> | Hne2].
+ rewrite Nat.eqb_refl. rewrite (proj2 (Nat.ltb_lt dp (S dp))) in M by lia.
destruct M as [(E & C & N) | (E & C & N)]; rewrite E.
* exists CArr, false. split; [apply Qdyh.Mq0.lvl_mode_aadd | split; [exact C | exact N]].
* exists CObj, true. split; [apply Qdyh.Mq0.lvl_mode_ovadd | split; [exact C | exact N]].
+ rewrite (proj2 (Nat.eqb_neq i dp) Hne2). rewrite (proj2 (Nat.ltb_ge i (S dp))) in M by lia.
rewrite (proj2 (Nat.eqb_neq i (S dp)) Hne) in M. exact M.
Qed.

Lemma PE_WIN_open : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv l,
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_name l = 0 -> tl_nbs l = [] -> t_objbs ts = [] ->
PE_WIN pf pa q LB0 LM FRS payload me lo m md A B (ts_lvl ts (TL (tl_st l) (tl_ss l) (tl_cur l) None [] 0 [])) (tl_cur l) (tl_cs l) (tl_cbs l) 1 cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv l [CORE REST] Hl Hn Hnbs Eobj.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply PE_REST_A_base in REST as (BASE & LV & OBJ & BUD).
set (lw := TL (tl_st l) (tl_ss l) (tl_cur l) None [] 0 []).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
pose proof (LV _ _ Hl) as (R1 & R2 & JO & _).
split; [| split; [| split; [| split; [| split]]]].
- unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PB|]. split; [exact Hpb|]. split; [| exact FR].
eapply tstack_lupd_srec; [exact TSK | exact Hl |]. unfold srec_cells, lw; cbn [tl_st tl_ss tl_cur tl_name]. rewrite Hn. reflexivity.
- destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (pe_blocksA_cur_perm2 pf q LB0 ts l Hl)|]. apply Permutation_sym.
eapply Permutation_trans; [apply (pe_blocksA_lvl_obj_perm pf q LB0 ts l lw 0 None (tl_cbs l) Hl)|].
unfold lvl_blocks, lw; cbn [tl_cbs tl_nbs app]. rewrite Hnbs, Eobj, app_nil_r. cbn [app]. apply Permutation_refl.
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence. exact (LV i li Hli).
- exists lw. split; [unfold ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd|].
unfold lvl_bare, lw; cbn [tl_st tl_ss tl_cs tl_cbs tl_name tl_nbs]. repeat split; try reflexivity; lia.
- exact Eobj.
- unfold put_pre. destruct (tl_cs l) as [s'|]; cbn [jopt] in JO; [| exact JO]. destruct JO as [Hp J]. split; [exact Hp|]. split; [lia | exact J].
Qed.

Lemma PE_WIN_write : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS rc cb nb pj sv errv W l' cb' nb' pj',
PE_STATIC_A HIx pf pa lo ->
PE_WIN pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc cb nb pj sv errv ->
munch W m mc -> wmono asegs m mc -> mem_inv asegs mc -> Forall (pe_wtqA pf pa q) W ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) ->
tstack asegs mc q (lupd (t_levels ts) (t_depth ts) l') ->
pe_frameA asegs mc pf pa cb' nb' pj' sv ->
lvl_bare l' ->
PE_WIN pf pa q LB0 LM FRS payload me lo mc md A B (ts_lvl ts l') p s BS rc cb' nb' pj' sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc (ts_lvl ts l') b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS rc cb nb pj sv errv W l' cb' nb' pj' STC (CORE & BASE & LVo & (l & Hl & BARE) & Eobj & PP) MU WM MI HW TOKc TSKc FRc BARE'.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
destruct (PE_BASE_A_private_write pf pa q LB0 LM FRS payload me lo m mc md A B (tsF ts BS) errv W STC BASE MU WM MI (pe_wtqA_private _ _ _ _ _ HW)) as [BASEc AG].
unfold tsF in AG; cbn [t_objbs t_levels] in AG.
assert (Eb : lvl_blocks l' = lvl_blocks l).
{ destruct BARE as (_ & _ & _ & C1 & _ & C2). destruct BARE' as (_ & _ & _ & C1' & _ & C2'). unfold lvl_blocks. rewrite C1, C2, C1', C2'. reflexivity. }
split.
2:{ intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 (tsF ts BS) ++ LM)) by (unfold pe_blocksA, tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 BASE)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | right; left; reflexivity]. }
split; [| split; [| split; [| split; [| split]]]].
- unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [| split; [exact Hpb | split; [exact TSKc | exact FRc]]].
eapply (pbuf_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact PB | exact MU | exact WM | exact HW].
- rewrite (pe_blocksA_tsF_lvl pf q LB0 ts BS l l' Hl Eb). exact BASEc.
- unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli Hne. rewrite nth_error_lupd_neq in Hli by congruence.
eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
- exists l'. split; [unfold ts_lvl; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd | exact BARE'].
- exact Eobj.
- unfold put_pre in *. destruct s as [s'|]; [| exact PP]. destruct PP as (Hp & Hrc & J). split; [exact Hp|]. split; [exact Hrc|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

Lemma PE_WIN_callG : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts p s BS rc rc2 cb nb pj sv errv errv2,
PE_STATIC_A HIx pf pa lo ->
PE_WIN pf pa q LB0 LM FRS payload me lo m1 md A B ts p s BS rc cb nb pj sv errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (pe_blocksA pf q LB0 ts ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 (tsF ts BS)) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) -> rw_cells asegs m2 A_ERRNO [C4 errv2] ->
put_pre A4H A4F s m2 BS p rc2 ->
PE_WIN pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts p s BS rc2 cb nb pj sv errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts p s BS rc rc2 cb nb pj sv errv errv2 STC (CORE & BASE & LVo & CUR & Eobj & PP) VM HPR HP2 ST2 ERR2 PP2.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m1 m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR (in_or_app _ _ _ (or_introl INq))) in TSK; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK.
split; [| split; [| split; [| split; [exact CUR | split; [exact Eobj | exact PP2]]]]].
- split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|]. split; [exact TOK|]. split; [| split; [exact Hpb | split; [exact TSK | exact FR2]]].
eapply pbuf_agree; [exact PB | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
- eapply (PE_BASE_A_callG pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 _ _ errv errv2 RB); [exact STC | exact BASE | exact VM | exact HPR | exact LB0R | exact HP2 | exact ST2 | exact ERR2].
- intros i li Hli Hne. eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
Qed.

Lemma PE_WIN_callG2 : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts p s BS rc p2 s2 BS2 rc2 cb nb pj sv errv errv2,
PE_STATIC_A HIx pf pa lo ->
PE_WIN pf pa q LB0 LM FRS payload me lo m1 md A B ts p s BS rc cb nb pj sv errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H (pe_blocksA pf q LB0 ts ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 (tsF ts BS2)) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) -> rw_cells asegs m2 A_ERRNO [C4 errv2] ->
put_pre A4H A4F s2 m2 BS2 p2 rc2 ->
PE_WIN pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts p2 s2 BS2 rc2 cb nb pj sv errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts p s BS rc p2 s2 BS2 rc2 cb nb pj sv errv errv2 STC (CORE & BASE & LVo & CUR & Eobj & PP) VM HPR HP2 ST2 ERR2 PP2.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR).
set (RB := pe_blocksA pf q LB0 ts) in *.
assert (INtk : In (pf_tk pf, 72) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) RB) by (unfold RB, pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (LB0R : incl LB0 RB) by (unfold RB, pe_blocksA; intros b Hb; apply in_or_app; right; right; right; exact Hb).
assert (AG : agree_on asegs RB m1 m2) by (eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]).
assert (FR2 : pe_frameA asegs m2 pf pa cb nb pj sv).
{ eapply pe_frameA_pres; [exact HPR | lia | exact GEO | | | exact FR].
- apply in_or_app; right. apply in_or_app; right. change 248 with (fr_size 2 - 8). apply fr_ivs_frame. left; reflexivity.
- apply in_or_app; right. apply in_or_app; right. rewrite <- fr_shadow_len_2. change (shA (pa_F pa)) with (shad A4L (pa_F pa)). apply fr_ivs_shadow. left; reflexivity. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtk | lia | unfold tok_cells_g; cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in TOK.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR (in_or_app _ _ _ (or_introl INq))) in TSK; [| exact LEN32]. cbn [hl_segs hla_base A4L A4H] in TSK.
split; [| split; [| split; [| split; [exact CUR | split; [exact Eobj | exact PP2]]]]].
- split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|]. split; [exact TOK|]. split; [| split; [exact Hpb | split; [exact TSK | exact FR2]]].
eapply pbuf_agree; [exact PB | exact AG |]. unfold RB, pe_blocksA, tstate_blocks. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb.
- eapply (PE_BASE_A_callG pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 _ _ errv errv2 RB); [exact STC | exact BASE | exact VM | exact HPR | exact LB0R | exact HP2 | exact ST2 | exact ERR2].
- intros i li Hli Hne. eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli Hne) | exact AG |].
intros b Hb. unfold RB, pe_blocksA, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
Qed.

Lemma PE_WIN_close_cur : forall pf pa q LB0 LM FRS payload me lo m md A B ts p s BS cb nb pj sv errv l c,
PE_WIN pf pa q LB0 LM FRS payload me lo m md A B ts p (Some s) BS 1 cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_cur l = p ->
lvl_mode (tl_st l) (tl_ss l) = Some (c, false) -> cls_ok c (Some s) ->
zin (tl_st l) [ST_array_add; ST_ovadd] = false ->
PE_BUD pf pa (ts_lvl ts (TL (tl_st l) (tl_ss l) p (Some s) BS 0 [])) B ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B (ts_lvl ts (TL (tl_st l) (tl_ss l) p (Some s) BS 0 [])) cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts p s BS cb nb pj sv errv l c (CORE & BASE & LVo & (l0 & Hl0 & BARE) & Eobj & PP) Hl Ecur Hm CLS Hz BUD.
rewrite Hl in Hl0. injection Hl0 as <-. destruct BARE as (R1 & R2 & Ecs & Ecbs & En & Enbs).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
set (l' := TL (tl_st l) (tl_ss l) p (Some s) BS 0 []).
assert (Hd : (t_depth ts < length (t_levels ts))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
destruct PP as (Hp & _ & J).
split.
- unfold PE_CORE_A, ts_lvl; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOK|]. split; [exact PB|]. split; [exact Hpb|]. split; [| exact FR].
eapply tstack_lupd_srec; [exact TSK | exact Hl |]. unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name]. rewrite Ecur, En. reflexivity.
- apply PE_REST_A_of_base; [| | | exact BUD].
+ destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (perm_blocks_tsF pf q LB0 ts BS Eobj)|]. apply Permutation_sym.
eapply Permutation_trans; [apply (pe_blocksA_lvl_perm pf q LB0 ts l l' Hl)|].
unfold lvl_blocks at 1, l'; cbn [tl_cbs tl_nbs]. rewrite app_nil_r. apply Permutation_app_head.
apply Permutation_sym. eapply Permutation_trans; [apply (pe_blocksA_cur_perm pf q LB0 ts l Hl)|]. unfold lvl_blocks. rewrite Ecbs, Enbs. apply Permutation_refl.
+ unfold ts_lvl; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | Hne].
* rewrite nth_error_lupd_eq in Hli by exact Hd. injection Hli as <-. split; [exact R1|]. split; [exact R2|]. split; [cbn [jopt l' tl_cs tl_cbs tl_cur]; split; [exact Hp | exact J]|].
rewrite Nat.ltb_irrefl, Nat.eqb_refl. exists c, false. split; [exact Hm|]. split; [exact CLS|]. cbn. split; reflexivity.
* rewrite nth_error_lupd_neq in Hli by congruence. exact (LVo i li Hli Hne).
+ unfold cur_st, ts_lvl; cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite nth_error_lupd_eq by exact Hd. cbn [tl_st l']. rewrite Hz. exact Eobj.
Qed.

Lemma PE_WIN_close_weak : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv rc,
PE_WIN pf pa q LB0 LM FRS payload me lo m md A B ts 0 None [] rc cb nb pj sv errv ->
(exists l, nth_error (t_levels ts) (t_depth ts) = Some l /\ tl_cur l = 0) ->
K_free * Z.of_nat (length (tstate_blocks ts)) + K_exit + pa_bslack pa <= bB B -> pa_dslack pa <= bD B ->
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts [] cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv rc (CORE & BASE & LVo & (l0 & Hl0 & BARE) & Eobj & PP) (l & Hl & Ecur) HB HD.
rewrite Hl in Hl0. injection Hl0 as <-. destruct BARE as (R1 & R2 & Ecs & Ecbs & En & Enbs).
split; [exact CORE|]. split; [| split; [| split; [exact HB | exact HD]]].
- rewrite app_nil_r. destruct BASE as (HP & BASE'). split; [| exact BASE'].
eapply (heapA_perm A4L HIx); [exact HP | | apply Permutation_refl | apply Permutation_refl].
eapply Permutation_trans; [apply (perm_blocks_tsF pf q LB0 ts [] Eobj)|]. apply Permutation_refl.
- intros i li Hli. destruct (PeanoNat.Nat.eq_dec i (t_depth ts)) as [-> | Hne].
+ rewrite Hl in Hli. injection Hli as <-. split; [split; [exact R1 | exact R2]|]. split; [rewrite Ecs, Ecbs, Ecur; cbn; split; reflexivity|].
split; [left; cbn; split; [exact En | exact Enbs] | intros Hlt; exfalso; lia].
+ apply lvl_cur_weakA. exact (LVo i li Hli Hne).
Qed.

Lemma PE_WIN_close_pop : forall pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS cb nb pj sv errv dp,
PE_STATIC_A HIx pf pa lo ->
PE_WIN pf pa q LB0 LM FRS payload me lo m md A B ts p s BS 1 cb nb pj sv errv ->
t_depth ts = S dp -> nth_error (t_levels ts) (S dp) = Some (TL ST_eatws ST_start 0 None [] 0 []) ->
munch [(pf_tk pf, pf_tk pf + 72)] m mc -> wmono asegs m mc -> mem_inv asegs mc ->
rw_cells asegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat dp) q (t_x ts)) ->
PE_BUD pf pa (TST dp (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) p s BS) B ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo mc md A B (TST dp (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) p s BS) cb nb pj sv errv
/\ (forall b, PBOKat m ts b -> PBOKat mc (TST dp (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) p s BS) b).
Proof.
intros pf pa q LB0 LM FRS payload me lo m mc md A B ts p s BS cb nb pj sv errv dp STC (CORE & BASE & LVo & CUR & Eobj & PP) Ed Hrl MU WM MI TOKc BUD.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (HW : Forall (pe_wtfA pf pa) [(pf_tk pf, pf_tk pf + 72)]) by (apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]).
destruct (PE_BASE_A_private_write pf pa q LB0 LM FRS payload me lo m mc md A B (tsF ts BS) errv _ STC BASE MU WM MI (pe_wtfA_private _ _ _ _ _ HW)) as [BASEc AG].
unfold tsF in AG; cbn [t_objbs t_levels] in AG.
set (ts' := TST dp (t_levels ts) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) p s BS).
assert (PBc : pbuf asegs mc (t_pbs ts) (t_pb ts)) by (eapply (pbuf_wtfA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact PB | exact MU | exact WM | exact HW]).

assert (Hdp : (dp < length (t_levels ts))%nat) by (rewrite LEN32; lia).
destruct (nth_error (t_levels ts) dp) as [lp|] eqn:Hlp; [| apply nth_error_None in Hlp; lia].
pose proof (LVo dp lp Hlp ltac:(lia)) as LVp. pose proof LVp as (_ & _ & _ & Mp). rewrite Ed in Mp.
replace (dp <? S dp)%nat with true in Mp by (symmetry; apply Nat.ltb_lt; lia).
assert (STp : zin (tl_st lp) [ST_array_add; ST_ovadd] = true) by (destruct Mp as [(E & _) | (E & _)]; rewrite E; reflexivity).
split.
- split.
+ unfold PE_CORE_A, ts'; cbn [t_levels t_depth t_co t_x t_pb t_pbs]. split; [exact LEN32|]. split; [lia|]. split; [exact CO|]. split; [exact CHOFF|].
split; [exact TOKc|]. split; [exact PBc|]. split; [exact Hpb|]. split; [| ].
* eapply (tstack_wtfA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
* eapply (pe_frameA_blkwriteG HIx) with (LBX := pe_blocksA pf q LB0 (tsF ts BS)); [exact STC | exact (proj1 BASE) | | exact FR | exact MU | exact WM].
apply Forall_cons; [| apply Forall_nil]. exists (pf_tk pf), 72. cbn [fst snd]. split; [| lia]. apply in_or_app; left. unfold pe_blocksA. apply in_or_app; right; left; reflexivity.
+ apply PE_REST_A_of_base; [exact BASEc | | | exact BUD].
* unfold ts'; cbn [t_levels t_depth]. intros i li Hli.
destruct (PeanoNat.Nat.eq_dec i (S dp)) as [-> | Hne].
-- rewrite Hrl in Hli. injection Hli as <-. split; [unfold ST_eatws; cbn; lia|]. split; [unfold ST_start; cbn; lia|]. split; [cbn; split; reflexivity|].
replace (S dp <? dp)%nat with false by (symmetry; apply Nat.ltb_ge; lia). replace (S dp =? dp)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
repeat split.
-- apply lvl_cur_popA; [exact Hne|]. rewrite <- Ed.
eapply (lvl_cur_agree asegs A4F); [exact (LVo i li Hli ltac:(rewrite Ed; exact Hne)) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hli.
* unfold cur_st, ts'; cbn [t_levels t_depth t_objs t_objbs t_obj]. rewrite Hlp, STp.
unfold put_pre in PP. unfold jopt. destruct s as [s'|]; [| exact PP]. destruct PP as (Hp & _ & J). split; [exact Hp|].
eapply jval_agree; [exact J | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
- intros b PBK. eapply PBOKat_same with (ts := ts); [reflexivity | reflexivity |].
eapply PBOKat_agree; [exact PBK | | apply incl_refl].
eapply (agree_wtqA HIx) with (ts := tsF ts BS); [exact STC | exact (proj1 BASE) | exact MU | exact WM | apply pe_wtfA_wtqA; exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 (tsF ts BS) ++ LM)) by (unfold pe_blocksA, tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ (proj1 BASE)) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | left; reflexivity].
+ intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks, tsF; cbn [t_pbs]; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.

Lemma PE_WIN_munchG : forall pf pa q LB0 LM FRS payload me lo m m2 md A B ts p s BS rc rc2 cb nb pj sv errv W,
PE_STATIC_A HIx pf pa lo ->
PE_WIN pf pa q LB0 LM FRS payload me lo m md A B ts p s BS rc cb nb pj sv errv ->
munch W m m2 -> wmono asegs m m2 -> mem_inv asegs m2 ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= pf_spf pf) \/ (exists a n, In (a, n) BS /\ a <= fst iv /\ snd iv <= a + n)) W ->
stk asegs m2 lo (pf_spf pf) ->
put_pre A4H A4F s m2 BS p rc2 ->
PE_WIN pf pa q LB0 LM FRS payload me lo m2 md A B ts p s BS rc2 cb nb pj sv errv
/\ agree_on asegs (pe_blocksA pf q LB0 ts) m m2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m m2 md A B ts p s BS rc rc2 cb nb pj sv errv W STC WIN MU WM MI2 HW ST2 PP2.
pose proof WIN as (CORE & BASE & LVo & CUR & Eobj & PP).
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof BASE as (HP & ST & ERR & _).
set (RB := pe_blocksA pf q LB0 ts) in *. set (LBall := pe_blocksA pf q LB0 (tsF ts BS)) in *.
pose proof (perm_blocks_tsF pf q LB0 ts BS Eobj) as PERM. fold RB LBall in PERM.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (NDp : List.NoDup (map blk_addr ((BS ++ RB) ++ LM))).
{ eapply Permutation_NoDup; [| exact ND]. apply Permutation_map. apply Permutation_app_tail. exact PERM. }
assert (INall : forall a n, In (a, n) BS -> In (a, n) (LBall ++ LM)).
{ intros a n Hin. apply in_or_app; left. eapply Permutation_in; [apply Permutation_sym; exact PERM | apply in_or_app; left; exact Hin]. }
assert (NBS : forall a n, In (a, n) BS -> ~ In (a, n) (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS))).
{ intros a n Hin Hx. rewrite app_assoc in Hx. apply in_app_or in Hx as [Hx | Hx].
- rewrite <- app_assoc in NDp. rewrite map_app in NDp. eapply (NoDup_app_in2 _ _ a NDp); [exact (in_map blk_addr _ _ Hin) | exact (in_map blk_addr _ _ Hx)].
- exact (blk_not_fr_iv HIx _ _ _ _ _ _ _ _ _ HP (INall a n Hin) Hx). }
assert (HPRc : heap_pres A4H (RB ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m m2).
{ eapply (heap_pres_of_munch A4H); [exact MU | exact WM |].
eapply (client_outsideF HIx); [exact HP | | lia |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb | Hb]; [left | right; exact Hb].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply (incl_blocks_tsF pf q LB0 ts BS Eobj); exact Hb | apply in_or_app; right; exact Hb].
- eapply Forall_impl; [| exact HW]. intros iv [H1 | (a & n & Hin & H1)]; [left; exact H1 | right; left].
exists a, n. split; [exact (INall a n Hin)|]. split; [exact (NBS a n Hin) | exact H1]. }
assert (HP2 : HEAPA A4L HIx A LBall LM ((pa_F pa, 2) :: FRS) B m2 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI2]. eapply (frame_writes_okF A4L HIx); [exact HP | exact MU |].
eapply Forall_impl; [| exact HW]. intros iv [H1 | (a & n & Hin & H1)]; [left; lia | right; left; exists a, n; split; [exact (INall a n Hin) | exact H1]]. }
assert (ERR2 : rw_cells asegs m2 A_ERRNO [C4 errv]).
{ eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat]. unfold A_ERRNO, A_TP.
pose proof alloc_ceiling_range as ACR.
clear - HW INall HP ACR LO. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [H1 | (a & n & Hin & H1)]; [lia|].
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP (INall a n Hin)) as Hbi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbi.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP (INall a n Hin)) as (Hk0 & _ & _ & _ & _). lia. }
split.
- eapply (PE_WIN_callG pf pa q LB0 LM FRS payload me lo m m2 md md A A B B ts p s BS rc rc2 cb nb pj sv errv errv);
[exact STC | exact WIN | apply model_vm_only_refl | exact HPRc | exact HP2 | exact ST2 | exact ERR2 | exact PP2].
- eapply (agree_of_heap_pres asegs A4H); [exact HPRc | reflexivity | intros b Hb; apply in_or_app; left; exact Hb].
Qed.

Lemma pe_frameA_slotw : forall pf pa (LBX : list blk) LM FRS B A m m' md lo W cb nb pj pj' sv,
PE_STATIC_A HIx pf pa lo -> HEAPA A4L HIx A LBX LM ((pa_F pa, 2) :: FRS) B m md ->
Forall (fun iv => exists a n, In (a, n) (LBX ++ LM) /\ a <= fst iv /\ snd iv <= a + n) W ->
pe_frameA asegs m pf pa cb nb pj sv -> munch ((pf_spf pf, pf_spf pf + 312) :: W) m m' -> wmono asegs m m' ->
rw_cells asegs m' (pf_spf pf) (pe_slotsA pf pa nb pj') ->
pj_gap pj' = pj_gap pj -> pj_fhd pj' = pj_fhd pj -> pj_f1 pj' = pj_f1 pj -> pj_f2 pj' = pj_f2 pj ->
pe_frameA asegs m' pf pa cb nb pj' sv.
Proof.
intros pf pa LBX LM FRS B A m m' md lo W cb nb pj pj' sv STC HP HW (SL & GP & SV & FF & FSH) MU WM SLc E1 E2 E3 E4.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk). pose proof alloc_ceiling_range as ACR.
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
assert (BLO : forall a n, In (a, n) (LBX ++ LM) -> 0 <= n /\ a + n <= alloc_ceiling).
{ intros a n Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & _ & _ & Hhi & _). lia. }
split; [exact SLc | split; [| split; [| split]]].
- rewrite E1. eapply rw_cells_transport; [exact GP | exact MU | exact WM |]. cbn [cells_size csize Nat.add disjoint_from fst snd].
split; [lia|]. eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin; destruct (BLO a n Hin); lia].
- eapply rw_cells_transport; [exact SV | exact MU | exact WM |]. cbn [cells_size csize Nat.add pe_savedA_cells disjoint_from fst snd].
split; [lia|]. eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin; destruct (BLO a n Hin); lia].
- unfold ff_cellsA in *. rewrite E2, E3, E4. eapply rw_cells_transport; [exact FF | exact MU | exact WM |]. cbn [cells_size csize Nat.add disjoint_from fst snd].
split; [lia|]. eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin].
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hin). rewrite fr_size_2 in *. lia.
- eapply rw_cells_transport; [exact FSH | exact MU | exact WM |]. unfold ffsh_cells, FSH0. cbn [cells_size csize Nat.add map length disjoint_from fst snd].
split; [unfold shA, A_SB; clear - GF0 GFc LO LOS ACR; Z.div_mod_to_equations; lia|].
eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin].
assert (HF0' : 0 <= pa_F pa) by lia. assert (HFc' : pa_F pa < alloc_ceiling) by lia.
pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP Hin HF0' HFc' ltac:(lia)) as DD. unfold shA in DD |- *. lia.
Qed.

Lemma pe_uw_at : forall pf pa lo m cb nb pj sv v2 ra2,
PE_STATIC_A HIx pf pa lo -> pe_frameA asegs m pf pa cb nb pj sv ->
pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) -> 0 <= v2 < 2^64 ->
uw_at (hiA_top A4L HIx) m (pf_spf pf) (pa_sp0 pa) (UWfp ra2 v2).
Proof.
intros pf pa lo m cb nb pj sv v2 ra2 STC (_ & _ & SV & _) S0V RAV HV HR.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
cbn [uw_at]. split; [lia|]. split; [clear - Gsp0; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [| split; [exact HV | exact HR]].
unfold pe_savedA_cells in SV. destruct SV as [[_ SVB] _].
cbn [cells_bytes cbytes app] in SVB. rewrite <- ?app_assoc in SVB.
do 11 (apply bytes_at_app in SVB as [_ SVB]; rewrite length_le8 in SVB).
rewrite S0V, RAV in SVB. eapply bytes_at_ext; [| reflexivity].
match type of SVB with bytes_at _ _ ?a _ => replace a with (pa_sp0 pa - 16) in SVB by lia end. exact SVB.
Qed.

End WithIface.
End RC__1.
End Mqe.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGdd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGdd.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma lb_remove_app_notin : forall p (L1 L2 : list blk), (forall n, ~ In (p, n) L1) -> lb_remove p (L1 ++ L2) = L1 ++ lb_remove p L2.
Proof.
induction L1 as [|[a n] L1 IH]; intros L2 H; [reflexivity|]. cbn [app lb_remove blk_addr fst].
destruct (Z.eqb_spec a p) as [->|NE]; [exfalso; apply (H n); left; reflexivity|]. f_equal. apply IH. intros k Hk. apply (H k). right; exact Hk.
Qed.

Section PeSOutTopA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.

Definition po_top_postA (pf : pe_fix) (pa : pe_fixA) (gp s3 s11 : word) (F : bvmap 5 word) (fc : bv 32)
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
HEAPAx A' (tl_cbs l ++ REST) LM ((pa_F pa, 2) :: FRS) B' m' md' /\
tstack asegs m' q (lupd levels i lvl_reset) /\
rw_cells asegs m' (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb depth q x) /\
pe_frameA asegs m' pf pa cb nb pj sv /\
stk asegs m' lo (pf_spf pf) /\
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
agree_on asegs P mpre m' /\
jopt asegs A4F (tl_cs l) m' (tl_cbs l) (tl_cur l) /\
bB B - 512 <= bB B' /\ bD B <= bD B'.

Lemma po_body_topA :
forall (pf : pe_fix) (pa : pe_fixA) (i : nat) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(q pb depth : Z) (x : tscal) (levels : list tlevel) (l : tlevel) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved),
PE_STATIC_A HIx pf pa lo ->
nth_error levels i = Some l -> (i < Z.to_nat (pf_mxd pf))%nat -> length levels = Z.to_nat (pf_mxd pf) ->
HEAPAx A (lvl_blocks l ++ REST) LM ((pa_F pa, 2) :: FRS) B m md ->
REST = P ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0 ->
match tl_cs l with Some s => tl_cur l <> 0 /\ jval asegs A4F s m (tl_cbs l) (tl_cur l) 2 | None => tl_cur l = 0 /\ tl_cbs l = [] end ->
((tl_name l = 0 /\ tl_nbs l = []) \/ (tl_name l <> 0 /\ exists nn, tl_nbs l = [(tl_name l, nn)])) ->
tstack asegs m q levels ->
rw_cells asegs m (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb depth q x) ->
pe_frameA asegs m pf pa cb nb pj sv ->
stk asegs m lo (pf_spf pf) ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
pe_s0 sv = Z_to_bv 64 (pf_tk pf) -> pe_ra sv = Z_to_bv 64 PE_RA2 ->
512 <= bB B ->
(forall ms' md' A', po_top_postA pf pa gp s3 s11 F fc md REST LB0 P LM FRS B me m lo errv q pb depth x levels i l cb nb pj sv ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 1) (Z_to_bv 64 (32 * Z.of_nat i + 16)) (Z_to_bv 64 (-16))
(Z_to_bv 64 (pf_tk pf / 8 + SB7)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (pf_tk pf + 56)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x981d4) fc None m (seg_rom asegs)).
Proof.
intros until sv. intros STC Hl Hi LEN HP EREST JO NM TS BLK FR ST HPR ERR S0V RAV BB K.
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
- pose proof (lvl_shadowAg HIx _ _ _ _ _ _ _ q mxd i HPc Iq ltac:(lia) ltac:(lia) Hi) as SH. unfold A_SB in SH. rewrite <- Hbse in SH. exact SH. }
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

unfold lvl_blocks in HP. rewrite <- app_assoc in HP.
assert (CDJ : forall a n, In (a, n) (tl_cbs l) -> a + n <= q \/ q + 32 * mxd <= a).
{ intros a n Hin.
assert (Haq : a <> q).
{ intros ->. refine (nodup_prefix_suffix (tl_cbs l) (tl_nbs l ++ REST) q n (32 * mxd) (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) Hin _).
apply in_or_app; right. exact INqR. }
exact (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n q (32 * mxd) HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact INqR) Haq). }
evt_done5.
assert (INq3 : In (q, 32 * mxd) (tl_cbs l ++ tl_nbs l ++ REST)) by (apply in_or_app; right; apply in_or_app; right; exact INqR).
assert (INq4 : In (q, 32 * mxd) ((tl_cbs l ++ tl_nbs l ++ REST) ++ LM)) by (apply in_or_app; left; exact INq3).
pose proof PUT as PUTx. unfold put_stmt_A, put_stmtA in PUTx.
eapply PUTx with (s := tl_cs l) (BS := tl_cbs l) (LB := tl_nbs l ++ REST) (p := tl_cur l) (rc := 2) (lo := lo) (errv := errv);
[ heap_nowA A4L HIx HP MU WM MI | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
{ lazymatch goal with |- put_pre _ _ _ ?mc _ _ _ => assert (AG : agree_on asegs (tl_cbs l) m mc) end.
{ eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a n Hin. cbn. split; [|exact I].
assert (Haq : a <> q).
{ intros ->. refine (nodup_prefix_suffix (tl_cbs l) (tl_nbs l ++ REST) q n (32 * mxd) (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) Hin _).
apply in_or_app; right. exact INqR. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n q (32 * mxd) HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact INqR) Haq). lia. }
unfold put_pre. revert JO. destruct (tl_cs l) as [s'|]; intros JO; [|exact JO].
destruct JO as [Hc J]. split; [exact Hc|]. split; [lia|]. eapply jval_agree; [exact J | exact AG | apply incl_refl]. }
all: try eassumption.
all: try (unfold put_stk_A; lia).
all: try (unfold put_costA; destruct (tl_cs l); [change (2 =? 1) with false; cbv iota|]; lia).
intros ms2 md2 A2 (m2 & r2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
assert (HPJ : HEAPAx A2 (tl_cbs l ++ tl_nbs l ++ REST) LM ((Ff, 2) :: FRS) B2 m2 md2 /\ jopt asegs A4F (tl_cs l) m2 (tl_cbs l) (tl_cur l)).
{ destruct OUT2 as [[[Hn | Habs] HPx] | (s2 & Es & _ & J2 & HPx)]; [ | exfalso; lia | ].
- rewrite Hn in JO |- *. destruct JO as [Hc0 Hnil]. rewrite Hnil. cbn [app jopt]. split; [exact HPx | split; [exact Hc0 | reflexivity]].
- rewrite Es in JO |- *. cbn [jopt]. destruct JO as [Hc _]. change (2 - 1) with 1 in J2. split; [exact HPx | split; [exact Hc | exact J2]]. }
destruct HPJ as [HP2 JOP2].
assert (INrN : In (r, 72) (tl_nbs l ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INqN : In (q, 32 * mxd) (tl_nbs l ++ REST)) by (apply in_or_app; right; exact INqR).
assert (INrN2 : In (r, 72) (tl_cbs l ++ tl_nbs l ++ REST)) by (apply in_or_app; right; exact INrN).
assert (INqN2 : In (q, 32 * mxd) (tl_cbs l ++ tl_nbs l ++ REST)) by (apply in_or_app; right; exact INqN).
assert (INrR3 : In (r, 72) (tl_cbs l ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INqR3 : In (q, 32 * mxd) (tl_cbs l ++ REST)) by (apply in_or_app; right; exact INqR).
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
destruct (SHAD _ _ _ _ m2 HP2 INrN2 INqN2) as [SHr SHl].
stash FR2.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. if_true.
step. step.
replace (q + (32 * Z.of_nat i + 16)) with (bse + 16) by lia.
asan_chkA.
stepz.
try clear SHr; try clear SHl.
destruct (SHAD _ _ _ _ _ ltac:(heap_nowA A4L HIx HP2 MU WM MI) INrN2 INqN2) as [SHr SHl].
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
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGC3 : agree_on asegs (tl_cbs l) m2 mc) by (eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (CDJ a n Hin); lia | exact I]]) end.
unstash FR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (FR3 : pe_frameA asegs mc (PEF r oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb pj sv)
by (eapply (pe_frameA_blkwriteG HIx _ _ _ _ _ _ _ m2 mc); [exact STC | exact HP2 | | exact FR2 | exact MU | exact WM];
apply Forall_cons; [| apply Forall_nil]; exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INqN2 | lia]) end.
clear FR2.
assert (UWB : bytes_at asegs m0 (sp0 - 16) (le8 (Z_to_bv 64 r) ++ le8 (Z_to_bv 64 602240))).
{ destruct FR3 as (_ & _ & SV & _). unfold pe_savedA_cells in SV. cbn [pa_sp0] in SV. destruct SV as [[_ SVB] _].
cbn [cells_bytes cbytes app] in SVB. rewrite <- ?app_assoc in SVB.
do 11 (apply bytes_at_app in SVB as [_ SVB]; rewrite length_le8 in SVB).
rewrite S0V, RAV in SVB. eapply bytes_at_ext; [| reflexivity].
match type of SVB with bytes_at _ _ ?a _ => replace a with (sp0 - 16) in SVB by lia end. exact SVB. }
alloc_callA (hiA_free A4L HIx) blk (tl_name l) uw (UWfp 602240 r) A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ destruct NM as [[Hn0 _] | [Hn0 [nn Hnbs]]]; [left; exact Hn0 | right; exists nn; rewrite Hnbs; apply in_or_app; right; left; reflexivity]. }
{ split; [lia|]. split; [clear - Gsp0; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact UWB | split; [left; lia | lia]]. }
{ clear - BB BB2 BD2 HB2 HD2. unfold put_costA in *; destruct (tl_cs l); [change (2 =? 1) with false in *; cbv iota in *|]; cbn [bB bD charge uw_cost] in *; lia. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPR3 by lia.
assert (ELB : lb_remove (tl_name l) (tl_cbs l ++ tl_nbs l ++ REST) = tl_cbs l ++ REST).
{ destruct NM as [[Hn0 Hnbs] | [Hn0 [nn Hnbs]]].
- rewrite Hn0, Hnbs. cbn [app]. apply lb_remove_notin. intros nn Hin.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ 0 nn HP2 ltac:(apply in_or_app; left; rewrite Hnbs; cbn [app]; exact Hin)) as (_ & _ & H0 & _). lia.
- rewrite Hnbs. rewrite lb_remove_app_notin; [cbn [app]; rewrite lb_remove_head; reflexivity |].
intros n Hin. refine (nodup_prefix_suffix (tl_cbs l) (tl_nbs l ++ REST) (tl_name l) n nn (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2)) Hin _). rewrite Hnbs. left; reflexivity. }
rewrite ELB in HPR3, HP3.
pose proof (pe_frameA_pres (PEF r oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ _ _ _ _ _ _ _ HPR3 ltac:(cbn [pf_spf]; lia) GEO
ltac:(apply in_or_app; right; apply in_or_app; right; cbn [pa_F fr_ivs flat_map app fr_base fr_class fst snd]; left; reflexivity)
ltac:(apply in_or_app; right; apply in_or_app; right; cbn [pa_F fr_ivs flat_map app fr_base fr_class fst snd]; right; left; unfold shad, shA, A_SB; cbn [hl_sb A4L]; reflexivity)
FR3) as FR4. clear FR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [apply in_or_app; left; exact INrR3 | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in LV1; [| eapply client_range_block; [apply in_or_app; left; exact INqR3 | lia | cbn; lia]]. a4l.
apply (tstack_pres_g A4H _ _ _ _ _ _ HPR3 ltac:(apply in_or_app; left; exact INqR3)) in TS2; [| rewrite lupd_length; exact LEN]. a4l.
assert (HPRb : heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) sp0 me m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB0 ++ LM ++ fr_ivs A4L FRS) sp0); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; cbn [fr_ivs flat_map app]; right; right; exact Hbb]] | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, (32 * mxd). split; [apply in_or_app; left; exact INqN2|]. split; [exact NQM | lia].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; cbn [fr_ivs flat_map app]; right; right; exact Hbb]]]. }
assert (AGP4 : agree_on asegs P m m3).
{ eapply agree_on_trans; [exact AGP3|]. eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity |].
intros b Hb. apply in_or_app; left. apply in_or_app; right. rewrite EREST. apply in_or_app; left; exact Hb. }
assert (AGC4 : agree_on asegs (tl_cbs l) m2 m3).
{ eapply agree_on_trans; [exact AGC3|]. eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity |].
intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
clear MU WM MI HPRa AGP3.

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. a4l.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(bse, bse + 32)] m3) as MU.
destruct (SHAD _ _ _ _ m3 HP3 INrR3 INqR3) as [SHr SHl].
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
apply Forall_cons; [| apply Forall_nil]; exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INqR3 | lia]) end.
clear FR4.
evt_done5. apply K. unfold po_top_postA. cbn [pf_spf pa_sp0 pa_F pf_tk pf_mxd pf_fl]. unfold shA, SB7, A_SB, A_TP, A_ERRNO.
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
eapply (client_outsideA A4L HIx); [exact HP3 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; exact Hbb | right; cbn [fr_ivs flat_map app]; right; right; exact Hbb]] | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, (32 * mxd). split; [apply in_or_app; left; exact INqR3|]. split; [exact NQM | lia]. }
split; [assumption|].
split; [eapply agree_on_trans; [exact AGP4|]; eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]] |].
split; [eapply (jopt_agree asegs A4F); [exact JOP2 | eapply agree_on_trans; [exact AGC4|]; eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (CDJ a n Hin); lia | exact I]] | apply incl_refl] |].
clear - BB BB2 BD2 HB2 HD2. unfold put_costA in BB2.
destruct (tl_cs l); [change (2 =? 1) with false in BB2; cbv iota in BB2|]; destruct (tl_name l =? 0); cbn [bB bD charge uw_cost] in *; lia.
Qed.

End PeSOutTopA.
End RC__1.
