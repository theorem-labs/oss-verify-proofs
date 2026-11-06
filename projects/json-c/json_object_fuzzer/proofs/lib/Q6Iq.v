(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3_c1 QWxq_c1 Qc3B Lib.GwApply QsjA QZAi QdBa QfYR QfcC Ql2m Lib.SepCache QnDM_c1 QDUx Q9Ay Qy5Y QPUx QhAd QVbl QQLG QQRC Q91D QCa8 QkTt Qy8Z Q8l1 QROt QZxv Q5m9 QXfH QzQg Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwFold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import QhAd.
Import QVbl.Mq3.
Import QQLG.Mq8.
Import QQRC.Mq0.
Import Q91D.
Import QCa8.
Import QVbl.
Import QQRC.
Import QkTt.Mq0.
Import QkTt.Mq1.
Import QVbl.Mq2.
Import QVbl.Mq1.
Import QQLG.Mq3.
Import QQLG.Mq4.
Import QQLG.Mq1.
Import Q91D.Mq4.
Import Qy8Z.Mq0.
Import QQRC.Mq3.
Import Q8l1.Mq3.
Import QROt.Mq2.
Import QQRC.Mq1.
Import QZxv.Mql.
Import QQRC.Mq2.
Import Q8l1.Mq0.
Import Q5m9.Mq1.
Import QXfH.

Import QzQg.Mq0.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 : Z).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.

Local Definition gw_tbl_0 := tt.

Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_0).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_1).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_2))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_3))).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_4))))).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_5).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_6).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_7).
Definition dfinv : ltac:(gw_rebind_ty (@QzQg.Mq0.dfinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QzQg.Mq0.dfinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.dfinv segs got_ssp RATP ssp_guard) dfinv gw_tbl_8).
Definition SN324 : ltac:(gw_rebind_ty (@QzQg.Mq0.SN324 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.SN324 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.SN324 segs base got_ssp RATP STRING_READ ssp_guard) SN324 gw_tbl_9).
Definition S_N324 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_N324 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_N324 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.S_N324 segs base got_ssp RATP STRING_READ ssp_guard) S_N324 gw_tbl_10).
Definition S_N2D4 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_N2D4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_N2D4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.S_N2D4 segs base got_ssp RATP STRING_READ ssp_guard) S_N2D4 gw_tbl_11).
Notation rfj := G.T_rfj.rfj.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Notation F_floatscan_common__S_N2D4 := S_N2D4 (only parsing).
Notation F_floatscan_common__S_N324 := S_N324 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER"] Lemma gw_all : True. Proof. exact I. Qed.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs_ ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs_ m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs_ m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs_ ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs_ m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs_ m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.

Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation S_N324 := (@F_floatscan_common__S_N324 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N2D4 := (@F_floatscan_common__S_N2D4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold F_floatscan_common__Wfs, FS_DEPTH, RERRNO in MU; unfold QzQg.Mq0.hi_cells in FRhi;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH in ST;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.

Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.

Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.

Hypothesis HS_N324 : S_N324.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE HS_N324"] Lemma L_N2D4 : S_N2D4.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE HS_N324 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SE_T; try gw_hide SPLO; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SPT; try gw_hide SG1; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros fo m; intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzf Rw Hfo Rrp Re2 HL HK. pose proof DI as DI0. dest_dfinv DI.
do 20 zs.
rewrite ?land2047. fix_idx.
stmt HS_N324. eapply NX; try eassumption; try lia.
- rewrite Z.shiftl_mul_pow2 by lia. lia.
- rewrite landW_mod2048. replace (z + -1)%Z with (z - 1)%Z by lia. reflexivity.
Qed.

End Floatscan.

End G.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import QhAd.
Import QVbl.Mq3.
Import QQLG.Mq8.
Import QQRC.Mq0.
Import Q91D.
Import QCa8.
Import QVbl.
Import QQRC.
Import QkTt.Mq0.
Import QkTt.Mq1.
Import QVbl.Mq2.
Import QVbl.Mq1.
Import QQLG.Mq3.
Import QQLG.Mq4.
Import QQLG.Mq1.
Import Q91D.Mq4.
Import Qy8Z.Mq0.
Import QQRC.Mq3.
Import Q8l1.Mq3.
Import QROt.Mq2.
Import QQRC.Mq1.
Import QZxv.Mql.
Import QQRC.Mq2.
Import Q8l1.Mq0.
Import Q5m9.Mq1.
Import QXfH.

Import QzQg.Mq0.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 : Z).
Variables (joff_556 joff_569 joff_573 joff_579 joff_586 joff_591 joff_595 joff_600 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_errno_loc e_extenddftf2 e_multf3 e_floatsitf e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_556 : decode_any (Z_to_bv 32 w_556) = Some (Jal 1 joff_556, 4%Z).
Hypothesis E_556 : is_ecall (Z_to_bv 32 w_556) = false.
Hypothesis D_569 : decode_any (Z_to_bv 32 w_569) = Some (Jal 1 joff_569, 4%Z).
Hypothesis E_569 : is_ecall (Z_to_bv 32 w_569) = false.
Hypothesis D_573 : decode_any (Z_to_bv 32 w_573) = Some (Jal 1 joff_573, 4%Z).
Hypothesis E_573 : is_ecall (Z_to_bv 32 w_573) = false.
Hypothesis D_579 : decode_any (Z_to_bv 32 w_579) = Some (Jal 1 joff_579, 4%Z).
Hypothesis E_579 : is_ecall (Z_to_bv 32 w_579) = false.
Hypothesis D_586 : decode_any (Z_to_bv 32 w_586) = Some (Jal 1 joff_586, 4%Z).
Hypothesis E_586 : is_ecall (Z_to_bv 32 w_586) = false.
Hypothesis D_591 : decode_any (Z_to_bv 32 w_591) = Some (Jal 1 joff_591, 4%Z).
Hypothesis E_591 : is_ecall (Z_to_bv 32 w_591) = false.
Hypothesis D_595 : decode_any (Z_to_bv 32 w_595) = Some (Jal 1 joff_595, 4%Z).
Hypothesis E_595 : is_ecall (Z_to_bv 32 w_595) = false.
Hypothesis D_600 : decode_any (Z_to_bv 32 w_600) = Some (Jal 1 joff_600, 4%Z).
Hypothesis E_600 : is_ecall (Z_to_bv 32 w_600) = false.
Hypothesis LINK_556 : gw_anch (base + 2224 + bv_signed joff_556)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_569 : gw_anch (base + 2276 + bv_signed joff_569)%Z (e_errno_loc + 0)%Z.
Hypothesis LINK_573 : gw_anch (base + 2292 + bv_signed joff_573)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_579 : gw_anch (base + 2316 + bv_signed joff_579)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_586 : gw_anch (base + 2344 + bv_signed joff_586)%Z (e_extenddftf2 + 0)%Z.
Hypothesis LINK_591 : gw_anch (base + 2364 + bv_signed joff_591)%Z (e_errno_loc + 0)%Z.
Hypothesis LINK_595 : gw_anch (base + 2380 + bv_signed joff_595)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_600 : gw_anch (base + 2400 + bv_signed joff_600)%Z (e_multf3 + 0)%Z.
Hypothesis CODE_e_errno_loc : code_at segs e_errno_loc errno_loc_code.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.
Hypothesis LAY_got_ssp_RERRNO : gw_le (got_ssp + 8) (RATP + -164).

Local Definition gw_tbl_0 := tt.

Definition getf2_post : ltac:(gw_rebind_ty (@QVbl.Mq1.getf2_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QVbl.Mq1.getf2_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QzQg.Mq0.getf2_post segs) getf2_post (gw_ent (@QVbl.Mq1.getf2_post segs) getf2_post gw_tbl_0)).
Definition scalbn_post : ltac:(gw_rebind_ty (@Q91D.Mq4.scalbn_post segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq4.scalbn_post segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QzQg.Mq0.scalbn_post segs) scalbn_post (gw_ent (@Q91D.Mq4.scalbn_post segs) scalbn_post gw_tbl_1)).
Definition SCALBNL := (e_extendsftf2 + 1132)%Z.
Local Definition gw_tbl_3 := (gw_ent (@QzQg.Mq0.SCALBNL e_extendsftf2) SCALBNL (gw_ent (@QQRC.Mq2.SCALBNL e_extendsftf2) SCALBNL gw_tbl_2)).
Definition COPYSIGNL := (e_extendsftf2 + 348)%Z.
Local Definition gw_tbl_4 := (gw_ent (@QzQg.Mq0.COPYSIGNL e_extendsftf2) COPYSIGNL (gw_ent (@QQRC.Mq2.COPYSIGNL e_extendsftf2) COPYSIGNL gw_tbl_3)).
Definition FABSL := (e_extendsftf2 + 1120)%Z.
Local Definition gw_tbl_5 := (gw_ent (@QzQg.Mq0.FABSL e_extendsftf2) FABSL (gw_ent (@QQRC.Mq2.FABSL e_extendsftf2) FABSL gw_tbl_4)).
Definition leafq_post : ltac:(gw_rebind_ty (@QQRC.Mq2.leafq_post segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QQRC.Mq2.leafq_post segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq0.leafq_post segs) leafq_post (gw_ent (@QQRC.Mq2.leafq_post segs) leafq_post gw_tbl_5)).
Definition scalbnl_post : ltac:(gw_rebind_ty (@QQRC.Mq2.scalbnl_post segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QQRC.Mq2.scalbnl_post segs) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.scalbnl_post segs) scalbnl_post (gw_ent (@QQRC.Mq2.scalbnl_post segs) scalbnl_post gw_tbl_6)).
Definition scalbnl_stmt : ltac:(gw_rebind_ty (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.scalbnl_stmt segs e_extendsftf2) scalbnl_stmt (gw_ent (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) scalbnl_stmt gw_tbl_7)).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@QzQg.Mq0.extenddftf2_post segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QzQg.Mq0.extenddftf2_post segs) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Q8l1.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@QQRC.Mq2.extenddftf2_post segs) extenddftf2_post gw_tbl_8)))).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@QzQg.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@QQRC.Mq2.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_9)))).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Q8l1.Mq0.leaf2_post segs) leaf2_post (gw_ent (@QQRC.Mq2.leaf2_post segs) leaf2_post gw_tbl_10)))).
Definition leaf1_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.leaf1_post segs) leaf1_post (gw_ent (@Qy8Z.Mq0.leaf1_post segs) leaf1_post (gw_ent (@Q8l1.Mq0.leaf1_post segs) leaf1_post gw_tbl_11))).
Definition call2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.call2_post segs) call2_post (gw_ent (@Qy8Z.Mq0.call2_post segs) call2_post (gw_ent (@Q8l1.Mq0.call2_post segs) call2_post (gw_ent (@QQRC.Mq2.call2_post segs) call2_post gw_tbl_12)))).
Definition FMODL := (e_extendsftf2 + 388)%Z.
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.FMODL e_extendsftf2) FMODL (gw_ent (@Q8l1.Mq0.FMODL e_extendsftf2) FMODL gw_tbl_13)).
Definition rfmodl_post : ltac:(gw_rebind_ty (@Q8l1.Mq0.rfmodl_post segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.rfmodl_post segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QzQg.Mq0.rfmodl_post segs) rfmodl_post (gw_ent (@Q8l1.Mq0.rfmodl_post segs) rfmodl_post gw_tbl_14)).
Definition rfmodl_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QzQg.Mq0.rfmodl_stmt segs e_extendsftf2) rfmodl_stmt (gw_ent (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) rfmodl_stmt gw_tbl_15)).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_16))))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_17))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_18))).
Definition fixunstfsi_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fixunstfsi_post segs) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fixunstfsi_post segs) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QzQg.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Q8l1.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@QQRC.Mq2.fixunstfsi_post segs) fixunstfsi_post gw_tbl_19)))).
Definition floatsitf_post : ltac:(gw_rebind_ty (@QzQg.Mq0.floatsitf_post segs) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QzQg.Mq0.floatsitf_post segs) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@QzQg.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Q8l1.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@QQRC.Mq2.floatsitf_post segs) floatsitf_post gw_tbl_20)))).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@QzQg.Mq0.floatunsitf_post segs) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QzQg.Mq0.floatunsitf_post segs) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@QzQg.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Q8l1.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@QQRC.Mq2.floatunsitf_post segs) floatunsitf_post gw_tbl_21)))).
Definition addtf3_post : ltac:(gw_rebind_ty (@QzQg.Mq0.addtf3_post segs) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QzQg.Mq0.addtf3_post segs) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@QzQg.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Q8l1.Mq0.addtf3_post segs) addtf3_post (gw_ent (@QQRC.Mq2.addtf3_post segs) addtf3_post gw_tbl_22)))).
Definition multf3_post : ltac:(gw_rebind_ty (@QzQg.Mq0.multf3_post segs) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QzQg.Mq0.multf3_post segs) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@QzQg.Mq0.multf3_post segs) multf3_post (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post (gw_ent (@Q8l1.Mq0.multf3_post segs) multf3_post (gw_ent (@QQRC.Mq2.multf3_post segs) multf3_post gw_tbl_23)))).
Definition multf3_stmt : ltac:(gw_rebind_ty (@QzQg.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QzQg.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_24)).
Local Definition gw_tbl_25 := (gw_ent (@QzQg.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Q8l1.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@QQRC.Mq2.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_24)))).
Definition divtf3_post : ltac:(gw_rebind_ty (@QzQg.Mq0.divtf3_post segs) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@QzQg.Mq0.divtf3_post segs) constr:(gw_tbl_25)).
Local Definition gw_tbl_26 := (gw_ent (@QzQg.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Q8l1.Mq0.divtf3_post segs) divtf3_post (gw_ent (@QQRC.Mq2.divtf3_post segs) divtf3_post gw_tbl_25)))).
Definition letf2_post : ltac:(gw_rebind_ty (@QzQg.Mq0.letf2_post segs) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@QzQg.Mq0.letf2_post segs) constr:(gw_tbl_26)).
Local Definition gw_tbl_27 := (gw_ent (@QzQg.Mq0.letf2_post segs) letf2_post (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post (gw_ent (@Q8l1.Mq0.letf2_post segs) letf2_post (gw_ent (@QQRC.Mq2.letf2_post segs) letf2_post gw_tbl_26)))).
Definition frexpl_post : ltac:(gw_rebind_ty (@QzQg.Mq0.frexpl_post segs) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@QzQg.Mq0.frexpl_post segs) constr:(gw_tbl_27)).
Local Definition gw_tbl_28 := (gw_ent (@QzQg.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Q8l1.Mq0.frexpl_post segs) frexpl_post (gw_ent (@QQRC.Mq2.frexpl_post segs) frexpl_post gw_tbl_27)))).
Definition signbitl_post : ltac:(gw_rebind_ty (@QzQg.Mq0.signbitl_post segs) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QzQg.Mq0.signbitl_post segs) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QzQg.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Q8l1.Mq0.signbitl_post segs) signbitl_post (gw_ent (@QQRC.Mq2.signbitl_post segs) signbitl_post gw_tbl_28)))).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fpclassifyl_post segs) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fpclassifyl_post segs) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QzQg.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Q8l1.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@QQRC.Mq2.fpclassifyl_post segs) fpclassifyl_post gw_tbl_29)))).
Definition calla_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.calla_post segs) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.calla_post segs) constr:(gw_tbl_30)).
Local Definition gw_tbl_31 := (gw_ent (@QzQg.Mq0.calla_post segs) calla_post (gw_ent (@Qy8Z.Mq0.calla_post segs) calla_post gw_tbl_30)).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_31)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_31)).
Local Definition gw_tbl_32 := (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_31).
Definition ERRNO_LOC : ltac:(gw_rebind_ty (@QzQg.Mq0.ERRNO_LOC e_errno_loc) constr:(gw_tbl_32)) := ltac:(gw_rebind_tm (@QzQg.Mq0.ERRNO_LOC e_errno_loc) constr:(gw_tbl_32)).
Local Definition gw_tbl_33 := (gw_ent (@QzQg.Mq0.ERRNO_LOC e_errno_loc) ERRNO_LOC gw_tbl_32).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_33)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_33)).
Local Definition gw_tbl_34 := (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_33).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_34)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_34)).
Local Definition gw_tbl_35 := (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_34).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_35)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_35)).
Local Definition gw_tbl_36 := (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_35).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_36)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_36)).
Local Definition gw_tbl_37 := (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_36).
Definition dfinv : ltac:(gw_rebind_ty (@QzQg.Mq0.dfinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_37)) := ltac:(gw_rebind_tm (@QzQg.Mq0.dfinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_37)).
Local Definition gw_tbl_38 := (gw_ent (@QzQg.Mq0.dfinv segs got_ssp RATP ssp_guard) dfinv gw_tbl_37).
Definition dfinvG : ltac:(gw_rebind_ty (@QzQg.Mq0.dfinvG segs got_ssp RATP ssp_guard) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QzQg.Mq0.dfinvG segs got_ssp RATP ssp_guard) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QzQg.Mq0.dfinvG segs got_ssp RATP ssp_guard) dfinvG gw_tbl_38).
Definition S_DD0 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_DD0 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_39)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_DD0 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_39)).
Local Definition gw_tbl_40 := (gw_ent (@QzQg.Mq0.S_DD0 segs base got_ssp RATP STRING_READ ssp_guard) S_DD0 gw_tbl_39).
Definition S_DD24 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_DD24 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_40)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_DD24 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_40)).
Local Definition gw_tbl_41 := (gw_ent (@QzQg.Mq0.S_DD24 segs base got_ssp RATP STRING_READ ssp_guard) S_DD24 gw_tbl_40).
Definition S_P : ltac:(gw_rebind_ty (@QzQg.Mq0.S_P segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_41)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_P segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_41)).
Local Definition gw_tbl_42 := (gw_ent (@QzQg.Mq0.S_P segs base got_ssp RATP STRING_READ ssp_guard) S_P gw_tbl_41).
Definition S_R : ltac:(gw_rebind_ty (@QzQg.Mq0.S_R segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_42)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_R segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_42)).
Local Definition gw_tbl_43 := (gw_ent (@QzQg.Mq0.S_R segs base got_ssp RATP STRING_READ ssp_guard) S_R gw_tbl_42).
Hypothesis extenddftf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq1.extenddftf2_spec segs e_extenddftf2) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_43))) in exact T).  Arguments extenddftf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis multf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QCa8.multf3_spec segs e_multf3) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).
Notation rfj := G.T_rfj.rfj.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.
Ltac mlia := Z.div_mod_to_equations; lia.

Ltac brs K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac]; try (exfalso; lia).

Definition errno_loc_spec : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.errno_loc_spec) constr:(gw_tbl_43)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.errno_loc_spec)).
Definition mul_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.mul_callE) constr:(gw_tbl_43)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.mul_callE)).
Definition L_RET1 : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.L_RET1) constr:(gw_tbl_43)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.L_RET1)).
Definition dfinvG_dfinv : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.dfinvG_dfinv) constr:(gw_tbl_43)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.dfinvG_dfinv)).
Definition extenddftf2_callF : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.extenddftf2_callF) constr:(gw_tbl_43)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.extenddftf2_callF)).
Definition floatsitf_callsg : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.floatsitf_callsg) constr:(gw_tbl_43)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.floatsitf_callsg)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Definition F_floatscan_common__Fok_refl : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_refl) constr:(gw_tbl_43)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_refl)).
Definition F_floatscan_common__Fok_set : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_set) constr:(gw_tbl_43)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_set)).
Notation F_floatscan_common__L_RET1 := L_RET1 (only parsing).
Notation F_floatscan_common__S_DD0 := S_DD0 (only parsing).
Notation F_floatscan_common__S_DD24 := S_DD24 (only parsing).
Notation F_floatscan_common__S_P := S_P (only parsing).
Notation F_floatscan_common__S_R := S_R (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__dfinvG_dfinv := dfinvG_dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_43)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard e_errno_loc e_extenddftf2 e_multf3 e_floatsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_556 E_556 D_569 E_569 D_573 E_573 D_579 E_579 D_586 E_586 D_591 E_591 D_595 E_595 D_600 E_600 LINK_556 LINK_569 LINK_573 LINK_579 LINK_586 LINK_591 LINK_595 LINK_600 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO extenddftf2_spec floatsitf_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_556 joff_569 joff_573 joff_579 joff_586 joff_591 joff_595 joff_600 got_ssp RATP STRING_READ ssp_guard e_errno_loc e_extenddftf2 e_multf3 e_floatsitf e_divtf3 e_extendsftf2 CODE BASE4 BASER D_556 E_556 D_569 E_569 D_573 E_573 D_579 E_579 D_586 E_586 D_591 E_591 D_595 E_595 D_600 E_600 LINK_556 LINK_569 LINK_573 LINK_579 LINK_586 LINK_591 LINK_595 LINK_600 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO extenddftf2_spec floatsitf_spec multf3_spec.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs_ ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs_ m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs_ m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs_ ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs_ m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs_ m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation XA := (q + -8312)%Z.

Local Notation Fok_refl := (@F_floatscan_common__Fok_refl F).
Local Notation Fok_set := (@F_floatscan_common__Fok_set F).

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation L_RET1 := (@F_floatscan_common__L_RET1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).

Local Notation dfinvG_dfinv := (@F_floatscan_common__dfinvG_dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_DD0 := (@F_floatscan_common__S_DD0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_DD24 := (@F_floatscan_common__S_DD24 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_P := (@F_floatscan_common__S_P ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_R := (@F_floatscan_common__S_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold F_floatscan_common__Wfs, FS_DEPTH, RERRNO in MU; unfold QzQg.Mq0.hi_cells in FRhi;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH in ST;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac mk_finv := gw_expose got_ssp; gw_expose ssp_guard; unfold F_floatscan_common__finv, F_floatscan_common__Wfs, QzQg.Mq0.hi_cells, FS_DEPTH, RERRNO;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac mk_framL := unfold F_floatscan_common__framL, RERRNO; split; hyp.

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.

Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.

Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.

Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold F_floatscan_common__dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].

Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

Notation POST := (fs_post m0).

Hypothesis HS_P : S_P.
Hypothesis HS_DD24 : S_DD24.
Hypothesis HS_DD0 : S_DD0.

Ltac some_snd H := apply (f_equal (fun o : option (shfile * Z) => match o with Some pr => snd pr | None => 0%Z end)) in H; cbv beta iota delta [snd] in H.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_556 joff_569 joff_573 joff_579 joff_586 joff_591 joff_595 joff_600 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_556 E_556 D_569 E_569 D_573 E_573 D_579 E_579 D_586 E_586 D_591 E_591 D_595 E_595 D_600 E_600 LINK_556 LINK_569 LINK_573 LINK_579 LINK_586 LINK_591 LINK_595 LINK_600 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO extenddftf2_spec floatsitf_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_P HS_DD24 HS_DD0"] Lemma L_R : S_R.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_556 joff_569 joff_573 joff_579 joff_586 joff_591 joff_595 joff_600 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_556 E_556 D_569 E_569 D_573 E_573 D_579 E_579 D_586 E_586 D_591 E_591 D_595 E_595 D_600 E_600 LINK_556 LINK_569 LINK_573 LINK_579 LINK_586 LINK_591 LINK_595 LINK_600 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO extenddftf2_spec floatsitf_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_P HS_DD24 HS_DD0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rj Rk Rdc Rlnz Hlnz Hxk Hkj Hkj45 Rrp Hw80 HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_rng in HK.
change (Z.quot (- (-1074)) 2) with 537%Z in HK. change (-1074 - 2 * LDBL_MANT_DIG_)%Z with (-1300)%Z in HK.
change (30 <? 53)%Z with true in HK. cbn [orb] in HK.
pose proof (X31H 0%Z) as Rt0. pose proof (REL 0%Z ltac:(lia) ltac:(unfold digz; right; left; reflexivity)) as Et0.
pose proof (u32arr_read segs _ _ _ 0%Z _ _ XW (nth_error_wnth ws 0%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD0.
replace (XA + 4 * 0)%Z with XA in RD0 by lia.
zs. rewrite (sx32_wval ws 0%Z (znth x 0) (eq_sym Et0) Rt0). set (x0 := znth x 0) in *. clear RD0.
zs. brf K1; rewrite ?land_W64 in K1.
{
assert (E0 : x0 = 0%Z) by (clear - K1 Rt0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_556 joff_569 joff_573 joff_579 joff_586 joff_591 joff_595 joff_600 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_556 E_556 D_569 E_569 D_573 E_573 D_579 E_579 D_586 E_586 D_591 E_591 D_595 E_595 D_600 E_600 LINK_556 LINK_569 LINK_573 LINK_579 LINK_586 LINK_591 LINK_595 LINK_600 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO extenddftf2_spec floatsitf_spec multf3_spec; mlia).
rewrite E0, Z.eqb_refl in HK. some_snd HK.
assert (Rs : (-1 <= sign <= 1)%Z) by lia.
zs. zs. zs. zs. zs.
callx (eapply extenddftf2_callF; [eassumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity]).
zs. eapply L_RET1; try eassumption; try lia; try mk_finv; try mk_framL; try fok.
unfold D_ZERO in HK. symmetry. exact HK. }
assert (Hne0 : x0 <> 0%Z) by (clear - K1 Rt0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_556 joff_569 joff_573 joff_579 joff_586 joff_591 joff_595 joff_600 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_556 E_556 D_569 E_569 D_573 E_573 D_579 E_579 D_586 E_586 D_591 E_591 D_595 E_595 D_600 E_600 LINK_556 LINK_569 LINK_573 LINK_579 LINK_586 LINK_591 LINK_595 LINK_600 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO extenddftf2_spec floatsitf_spec multf3_spec; mlia). clear K1.
replace (x0 =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne0).
specialize (Hlnz Hne0). specialize (Hw80 Hne0). subst w80. rewrite dfinvG_dfinv in DI0.

assert (G3C : forall (x10' : word),
((lrp =? dc) && (dc <? 10) = false)%Z ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10' x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 x0) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x8d8)) fct None m (seg_rom segs))).
{ intros x10' Hc. rewrite Hc in HK. cbv iota in HK.
zs. zs. zs. brs K5.
-
replace (537 <? lrp)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
zs. zs.
try replace (Z_to_bv 64 18446744073709550316) with (Z_to_bv 64 (-1300)) by (apply Z_to_bv_eqm; reflexivity).
try replace (Z_to_bv 64 (18446744073709550542 + -226)) with (Z_to_bv 64 (-1300)) by (apply Z_to_bv_eqm; reflexivity).
try replace (Z_to_bv 64 (-1074 + -226)) with (Z_to_bv 64 (-1300)) by (apply Z_to_bv_eqm; reflexivity).
zs. brs K6.
+
replace (lrp <? -1300)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
stmt HS_P. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)).
+
replace (lrp <? -1300)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). some_snd HK.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. zs. zs. zs.
zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := C_LDBL_MIN); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul SF C_LDBL_MIN) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
zs. zs.
stmt HS_DD0. eapply NX with (Y := C_LDBL_MIN); try eassumption; try lia; try mk_dfinv. symmetry; exact HK.
-
replace (537 <? lrp)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). some_snd HK.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. zs. zs. zs. zs.
try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := C_LDBL_MAX); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul SF C_LDBL_MAX) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
zs. try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity). zs. zs.
stmt HS_DD0. eapply NX with (Y := C_LDBL_MAX); try eassumption; try lia; try mk_dfinv. symmetry; exact HK. }
zs. zs. brs K2.
{  apply G3C. replace (dc <? 10)%Z with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
zs. brf K3; rewrite ?land_W64 in K3.
{  assert (Hne : lrp <> dc) by (clear - K3 Rrp Rdc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_556 joff_569 joff_573 joff_579 joff_586 joff_591 joff_595 joff_600 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_556 E_556 D_569 E_569 D_573 E_573 D_579 E_579 D_586 E_586 D_591 E_591 D_595 E_595 D_600 E_600 LINK_556 LINK_569 LINK_573 LINK_579 LINK_586 LINK_591 LINK_595 LINK_600 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO extenddftf2_spec floatsitf_spec multf3_spec; mlia).
apply G3C. replace (lrp =? dc)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity. }
assert (Heq : lrp = dc) by (clear - K3 Rrp Rdc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_556 joff_569 joff_573 joff_579 joff_586 joff_591 joff_595 joff_600 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_556 E_556 D_569 E_569 D_573 E_573 D_579 E_579 D_586 E_586 D_591 E_591 D_595 E_595 D_600 E_600 LINK_556 LINK_569 LINK_573 LINK_579 LINK_586 LINK_591 LINK_595 LINK_600 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO extenddftf2_spec floatsitf_spec multf3_spec; mlia). clear K3.
replace (lrp =? dc)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia).
replace (dc <? 10)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in HK. some_snd HK.

zs. zs. zs. zs. zs. zs. brf K4.
{ exfalso. clear - K4 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_556 joff_569 joff_573 joff_579 joff_586 joff_591 joff_595 joff_600 e_errno_loc e_extenddftf2 e_multf3 e_floatsitf CODE BASE4 BASER D_556 E_556 D_569 E_569 D_573 E_573 D_579 E_579 D_586 E_586 D_591 E_591 D_595 E_595 D_600 E_600 LINK_556 LINK_569 LINK_573 LINK_579 LINK_586 LINK_591 LINK_595 LINK_600 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO extenddftf2_spec floatsitf_spec multf3_spec. rewrite ?land_W64 in K4.
match type of K4 with (?a = 0)%Z => idtac end.
revert K4. match goal with |- context [Z.lor 1 ?b] => destruct (Z.lor_eq_0_iff 1 b) as [F _]; intros K4; try (specialize (F K4); lia) end.
all: try (Z.div_mod_to_equations; lia). }
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. zs. zs.
stmt HS_DD24. eapply NX; try eassumption; try lia; try mk_dfinv; try (symmetry; exact HK).
Qed.

End Floatscan.

End G.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import QhAd.
Import QVbl.Mq3.
Import QQLG.Mq8.
Import QQRC.Mq0.
Import Q91D.
Import QCa8.
Import QVbl.
Import QQRC.
Import QkTt.Mq0.
Import QkTt.Mq1.
Import QVbl.Mq2.
Import QVbl.Mq1.
Import QQLG.Mq3.
Import QQLG.Mq4.
Import QQLG.Mq1.
Import Q91D.Mq4.
Import Qy8Z.Mq0.
Import QQRC.Mq3.
Import Q8l1.Mq3.
Import QROt.Mq2.
Import QQRC.Mq1.
Import QZxv.Mql.
Import QQRC.Mq2.
Import Q8l1.Mq0.
Import Q5m9.Mq1.
Import QXfH.

Import QzQg.Mq0.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 : Z).
Variables (hi_22 : bv 20).
Variables (lo_23 : bv 12).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_22 : decode_any (Z_to_bv 32 w_22) = Some (Auipc 10 hi_22, 4%Z).
Hypothesis E_22 : is_ecall (Z_to_bv 32 w_22) = false.
Hypothesis D_23 : decode_any (Z_to_bv 32 w_23) = Some (Load SZ8 true 20 10 lo_23, 4%Z).
Hypothesis E_23 : is_ecall (Z_to_bv 32 w_23) = false.
Hypothesis ANCH_23 : gw_anch (Z.shiftl (bv_signed hi_22) 12 + (base + 88) + bv_signed lo_23)%Z got_ssp.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.
Hypothesis LAY_got_ssp_RERRNO : gw_le (got_ssp + 8) (RATP + -164).

Local Definition gw_tbl_0 := tt.

Definition SHGETC := (base + -488)%Z.
Local Definition gw_tbl_1 := (gw_ent (@Q5m9.Mq1.SHGETC (base + 7584)%Z) SHGETC (gw_ent (@QZxv.Mql.SHGETC (base + -544)%Z) SHGETC (gw_ent (@QROt.Mq2.SHGETC (base + -544)%Z) SHGETC (gw_ent (@QQRC.Mq3.SHGETC (base + -544)%Z) SHGETC gw_tbl_0)))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_1))))).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@Q5m9.Mq1.RFI STRING_READ) RFI (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_2))).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_3))))).
Definition shgetc_post : ltac:(gw_rebind_ty (@QROt.Mq2.shgetc_post segs got_ssp STRING_READ ssp_guard) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QROt.Mq2.shgetc_post segs got_ssp STRING_READ ssp_guard) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@Q5m9.Mq1.shgetc_post segs STRING_READ got_ssp ssp_guard) shgetc_post (gw_ent (@QZxv.Mql.shgetc_post segs got_ssp STRING_READ ssp_guard) shgetc_post (gw_ent (@QROt.Mq2.shgetc_post segs got_ssp STRING_READ ssp_guard) shgetc_post gw_tbl_4))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_5))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_6).
Definition FLOATSCAN := (base + 0)%Z.
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.FLOATSCAN base) FLOATSCAN gw_tbl_7).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_8).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_9).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_10).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_11).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_12).
Definition S_618 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_618 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_618 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.S_618 segs base got_ssp RATP STRING_READ ssp_guard) S_618 gw_tbl_13).

Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast_lt) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast_lt _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_getc : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_getc) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_getc _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis shgetc_callJ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.shgetc_callJ) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments shgetc_callJ _%_bv_scope _%_Z_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope _%_Z_scope _%_Z_scope _ _%_Z_scope _%_Z_scope _ _%_list_scope _%_list_scope _%_list_scope _%_bv_scope.
Notation rfj := G.T_rfj.rfj.
Notation j_flags := G.T_rfj.j_flags.
Notation j_pad0 := G.T_rfj.j_pad0.
Notation j_close := G.T_rfj.j_close.
Notation j_wend := G.T_rfj.j_wend.
Notation j_wpos := G.T_rfj.j_wpos.
Notation j_mbz1 := G.T_rfj.j_mbz1.
Notation j_wbase := G.T_rfj.j_wbase.
Notation j_read := G.T_rfj.j_read.
Notation j_write := G.T_rfj.j_write.
Notation j_seek := G.T_rfj.j_seek.
Notation j_bufsize := G.T_rfj.j_bufsize.
Notation j_prev := G.T_rfj.j_prev.
Notation j_next := G.T_rfj.j_next.
Notation j_fd := G.T_rfj.j_fd.
Notation j_ppid := G.T_rfj.j_ppid.
Notation j_lockcount := G.T_rfj.j_lockcount.
Notation j_mode := G.T_rfj.j_mode.
Notation j_lock := G.T_rfj.j_lock.
Notation j_lbf := G.T_rfj.j_lbf.
Notation j_pad1 := G.T_rfj.j_pad1.
Notation j_cookie := G.T_rfj.j_cookie.
Notation j_off := G.T_rfj.j_off.
Notation j_getln := G.T_rfj.j_getln.
Notation j_mbz2 := G.T_rfj.j_mbz2.
Notation j_pl := G.T_rfj.j_pl.
Notation j_nl := G.T_rfj.j_nl.
Notation j_locale := G.T_rfj.j_locale.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.cb8_c8_in) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.cb8_c8_in)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Definition F_floatscan_common__Fok_refl : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_refl) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_refl)).
Notation F_floatscan_common__S_618 := S_618 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__txt_char : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.txt_char) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.txt_char)).
Notation F_floatscan_common__winv := winv (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER D_22 E_22 D_23 E_23 ANCH_23 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_22 lo_23 got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER D_22 E_22 D_23 E_23 ANCH_23 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs_ ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs_ m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs_ m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs_ ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs_ m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs_ m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).

Notation RFJ' := (RFJ T txt p true J).

Local Notation ctx_all := (@QzQg.Mq0.ctx_all ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation Wfs := (@F_floatscan_common__Wfs q Fp).

Local Notation Fok_refl := (@F_floatscan_common__Fok_refl F).

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).
Local Notation txt_char := (@F_floatscan_common__txt_char txt BYT).

Local Notation winv := (@F_floatscan_common__winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

Local Notation FS_tail := (@QzQg.Mq0.FS_tail pok fuelc).
Local Notation S_618 := (@F_floatscan_common__S_618 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold F_floatscan_common__Wfs, FS_DEPTH, RERRNO in MU; unfold QzQg.Mq0.hi_cells in FRhi;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH in ST;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac mk_finv := gw_expose got_ssp; gw_expose ssp_guard; unfold F_floatscan_common__finv, F_floatscan_common__Wfs, QzQg.Mq0.hi_cells, FS_DEPTH, RERRNO;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac mk_framL := unfold F_floatscan_common__framL, RERRNO; split; hyp.

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.

Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.

Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.

Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).

Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.

Notation POST := (fs_post m0).

Hypothesis HS_618 : S_618.

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

Ltac eplia := gw_expose got_ssp; gw_expose ssp_guard; unfold zlength in *; unfold hide2 in *; lia.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
Ltac mk_winv2 := norm_m1074; unfold F_floatscan_common__winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|];
split; [first [assumption | rewrite ?upd_length; assumption]|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
#[using="Type"] Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_618 | gw_hide HS_618 | idtac]. clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma getc_rpos2 : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide BYT; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_618 | gw_hide HS_618 | idtac].
clear - BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.
Ltac call_shgetc FC0 RJ SLOW Hst :=
let STD := fresh "STD" in let EJ := fresh "EJ" in let Hn := fresh "Hn" in let Hrpe := fresh "Hrpe" in let Hc00 := fresh "Hc00" in
let STD0 := fresh "STD0" in let TXT := fresh "TXT" in let Hpre := fresh "Hpre" in
lazymatch type of RJ with RFJ _ _ _ _ _ ?kmin ?c ?f =>
destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & EJ & Hn & Hrpe & Hc00);
assert (STD0 : sh_stdio f0 = true) by (first [rewrite <- Hst; exact STD | exact STD]); destruct (ST0 STD0) as [TXT Hpre];
call_split 160%Z (eapply (gw_unhyp shgetc_callJ) with (pre := pre) (post := post);
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | hyp | gw_expose got_ssp; gw_expose ssp_guard; unfold ssp_cells; split; hyp
| eplia | eplia | exact SEP | replace (q + -8416 - 160)%Z with (q + -8416 - 160)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption ]);
match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H end;
match goal with H : ssp_cells ?m' _ |- _ => let S1 := fresh "SSP1'" in let S2 := fresh "SSP2'" in destruct H as [S1 S2]; gw_expose got_ssp; gw_expose ssp_guard end
end.
Ltac read_char f :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia; clear RDb end.

#[using="Hnul Hnum"] Lemma getc_fch : forall kmin c f, RFJ' kmin c f -> c <> 0%Z -> fch (fst (sh_getc f)).
Proof. clear - Hnul Hnum ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_618 | gw_hide HS_618 | idtac].
intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold fch, sh_getc. rewrite Hbuf.
destruct (sh_stdio f) eqn:ES; cbn [negb].
- destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & N5). rewrite N1. destruct (Z.eqb_spec (sh_rpos f) p) as [E|NE]; cbn [negb fst].
+ right; right; reflexivity.
+ left. apply Hnum. lia.
- destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). cbn [fst].
destruct (Z.eq_dec (sh_rpos f) p) as [E|NE]; [right; left; rewrite E; exact Hnul | left; apply Hnum; lia].
Qed.
Definition fch_ok (c : Z) : bool :=
(negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 73) &&
negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 78) &&
negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 88) &&
negb (Z.land c 18446744073709551583 =? 73) && negb (Z.land c 18446744073709551583 =? 78) && negb (Z.land c 18446744073709551583 =? 88) &&
negb (Z.lor c 32 =? 105) && negb (Z.lor c 32 =? 110) && negb (Z.lor c 32 =? 120) &&
negb (m_isspace c) && negb (c =? 32) && (5 <=? (c + -9) mod 2 ^ 64))%Z.
#[using="Type"] Lemma forallb_range : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, (0 <= c < Z.of_nat n)%Z -> P c = true.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_618 | gw_hide HS_618 | idtac].
clear. intros P n H c Hc. apply (proj1 (forallb_forall P _) H). apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
#[using="Type"] Lemma numch_range : forall c, is_numch c = true -> (0 <= c < 256)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_618 | gw_hide HS_618 | idtac].
clear. intros c N. unfold is_numch in N.
repeat (apply Bool.orb_true_iff in N; destruct N as [N|N]); try (apply Z.eqb_eq in N; lia).
apply andb_true_iff in N. destruct N as [N1 N2]. apply Z.leb_le in N1. apply Z.leb_le in N2. lia.
Qed.
#[using="Type"] Lemma fch_ok_true : forall c, fch c -> fch_ok c = true.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_618 | gw_hide HS_618 | idtac].
clear. intros c [N | [-> | ->]]; [| reflexivity | reflexivity].
pose proof (numch_range c N) as Rc.
pose proof (forallb_range (fun c => implb (is_numch c) (fch_ok c)) 256 ltac:(vm_compute; reflexivity) c Rc) as E.
cbv beta in E. rewrite N in E. exact E.
Qed.
#[using="Type"] Lemma fch_facts : forall c, fch c ->
(Z.land (Z.land c 18446744073709551615) 18446744073709551583 <> 73 /\ Z.land (Z.land c 18446744073709551615) 18446744073709551583 <> 78 /\
Z.land (Z.land c 18446744073709551615) 18446744073709551583 <> 88 /\
Z.land c 18446744073709551583 <> 73 /\ Z.land c 18446744073709551583 <> 78 /\ Z.land c 18446744073709551583 <> 88 /\
Z.lor c 32 <> 105 /\ Z.lor c 32 <> 110 /\ Z.lor c 32 <> 120 /\ m_isspace c = false /\ c <> 32 /\ 5 <= (c + -9) mod 2 ^ 64)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_618 | gw_hide HS_618 | idtac].
clear. intros c H. pose proof (fch_ok_true c H) as E. unfold fch_ok in E.
repeat (apply andb_true_iff in E; destruct E as [E ?X]).
repeat match goal with H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H end.
repeat match goal with H : (_ =? _)%Z = false |- _ => apply Z.eqb_neq in H end.
apply Z.leb_le in X.
repeat split; assumption.
Qed.
#[using="Type"] Lemma fch_range : forall c, fch c -> (-1 <= c < 256)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_618 | gw_hide HS_618 | idtac]. clear. intros c [N | [-> | ->]]; [pose proof (numch_range c N); lia | lia | lia]. Qed.

#[using="Type"] Lemma floatscan_front : forall (n : nat) (f : shfile) (sg c2 : Z) (f2 : shfile),
m_isspace (fst (sh_getc f)) = false ->
(if ((fst (sh_getc f) =? 43) || (fst (sh_getc f) =? 45))%Z
then ((1 - 2 * b2z (fst (sh_getc f) =? 45))%Z, fst (sh_getc (snd (sh_getc f))), snd (sh_getc (snd (sh_getc f))))
else (1%Z, fst (sh_getc f), snd (sh_getc f))) = (sg, c2, f2) ->
(Z.lor c2 32 <> 105)%Z -> (Z.lor c2 32 <> 110)%Z ->
floatscan (S n) f 1 pok =
(if (c2 =? 48)%Z then let '(c3, f3) := sh_getc f2 in if (Z.lor c3 32 =? 120)%Z then None else decfloat (S n) (sh_unget f3) 48 53 (-1074) sg pok
else decfloat (S n) f2 c2 53 (-1074) sg pok).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_618 | gw_hide HS_618 | idtac].
clear. intros n f sg c2 f2 Hsp Hsg L105 L110.
unfold floatscan. change (1 =? 0)%Z with false. change (1 =? 1)%Z with true. cbv beta iota.
change (fs_ws_loop (S n) f) with (let '(c, f') := sh_getc f in if m_isspace c then fs_ws_loop n f' else Some (c, f')).
rewrite (surjective_pairing (sh_getc f)). rewrite Hsp. cbv beta iota.
rewrite (surjective_pairing (sh_getc (snd (sh_getc f)))). cbv beta iota.
replace (if ((fst (sh_getc f) =? 43) || (fst (sh_getc f) =? 45))%Z
then ((1 - 2 * b2z (fst (sh_getc f) =? 45))%Z, fst (sh_getc (snd (sh_getc f))), snd (sh_getc (snd (sh_getc f))))
else (1%Z, fst (sh_getc f), snd (sh_getc f))) with (sg, c2, f2).
cbv beta iota.
change (fs_inf_loop 9 (0%Z, c2, f2)) with (if fs_inf_cond (0%Z, c2, f2) then fs_inf_loop 8 (fs_inf_body (0%Z, c2, f2)) else Some (0%Z, c2, f2)).
unfold fs_inf_cond at 1. change (znth str_infinity 0) with 105%Z.
replace (Z.lor c2 32 =? 105)%Z with false by (symmetry; apply Z.eqb_neq; exact L105).
rewrite Bool.andb_false_r. cbv iota beta.
cbn [Z.ltb Z.eqb Z.compare Pos.compare Pos.compare_cont andb orb].
change (fs_nan_loop 4 (0%Z, c2, f2)) with (if fs_nan_cond (0%Z, c2, f2) then fs_nan_loop 3 (fs_nan_body (0%Z, c2, f2)) else Some (0%Z, c2, f2)).
unfold fs_nan_cond. change (znth str_nan 0) with 110%Z.
replace (Z.lor c2 32 =? 110)%Z with false by (symmetry; apply Z.eqb_neq; exact L110).
rewrite Bool.andb_false_r. cbv iota beta.
cbn [Z.ltb Z.eqb Z.compare Pos.compare Pos.compare_cont andb orb nz negb].
reflexivity.
Qed.

Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let rec go pre l := lazymatch l with
| [CB 8 _] => fail
| CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
| ?c :: ?l' => go constr:(pre ++ [c]) l' end in
lazymatch cs with ?c0 :: ?l => go constr:([c0]) l end end.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard Hp SE_T SPF SPT SG1 SG3 FRM HS_618"] Lemma L_5D0 : forall m3 (x1' x5' x6' x7' x8' x12' x13' x14' x15' x16' x17' x19' x25' x26' x27' x28' x29' x30' x31' : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws (av sg c : Z) (f : shfile) (kmin : Z),
let _ := ctx_all in
winv m3 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> (sg = 1 \/ sg = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (0 <= av < 2^64)%Z -> av <> 78%Z ->
FS_tail sg c f = Some (fR, yR) ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 sg) (Z_to_bv 64 c) (Z_to_bv 64 av) x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19' (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25' x26' x27' x28' x29' x30' x31')
F (Z_to_bv 64 (base + 0x16c)) fc None m3 (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard Hp SE_T SPF SPT SG1 SG3 FRM HS_618 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPLO SPF2 SG2 Q1. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SPLO; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac].
intros until kmin. intros _ WI3 RJ3 Hk3 Hsg3 Hst3 Hr3 Rav Hav HK3.
pose proof WI3 as WI4. dest_winv WI4.
zs. zs. (brf K; [ | exfalso; lia ]).
stmt HS_618. eapply NX; try eassumption; try lia. apply Fok_refl.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618"] Lemma L_564 : forall m2 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x19' x25' x26' x27' x28' x29' x30' x31' : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws (c1 : Z) (f1 : shfile) (k1 : Z),
let _ := ctx_all in
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f1 ->
RFJ' k1 c1 f1 -> (1 <= k1)%Z -> sh_stdio f1 = sh_stdio f0 -> (c1 = 43%Z \/ c1 = 45%Z) ->
FS_tail (1 - 2 * b2z (c1 =? 45))%Z (fst (sh_getc f1)) (snd (sh_getc f1)) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 32) (Z_to_bv 64 c1) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19' (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25' x26' x27' x28' x29' x30' x31')
F (Z_to_bv 64 (base + 0x100)) fc None m2 (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok.
intros until k1. intros _ WI2 RK Hk2 Hst2 Hc1 HK2.
dest_winv WI2. bury_disj.
site_facts FC RK k1 c1 f1.
assert (Hc10 : c1 <> 0%Z) by lia.
pose proof (RFI_getc T txt p J BYT Hp Hnul k1 c1 f1 RK Hc10) as RJ3.
pose proof (getc_fch k1 c1 f1 RK Hc10) as FCH.
pose proof (getc_stdio f1) as Hst3. rewrite Hst2 in Hst3.
assert (Rc3 : (-1 <= fst (sh_getc f1) < 256)%Z) by (destruct RJ3 as (_ & R & _); exact R).
pose proof (getc_rpos2 f1 Hbuf) as [Rrp3 Rrp4].
set (sg := (1 - 2 * b2z (c1 =? 45))%Z) in HK2.
assert (Hsg : (sg = 1 \/ sg = -1)%Z) by (subst sg; destruct (c1 =? 45)%Z; cbn; lia).
destruct (Z.eq_dec (T + sh_rpos f1)%Z (rf_rend T p true f1)) as [SLOW|FAST].
- pose proof FC as FC0. ufc2 FC.
zs. zs. zs. zs. zs. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 sg) by (subst sg; destruct Hc1 as [-> | ->]; apply Z_to_bv_eqm; reflexivity).
clearbody sg.
zs. (brf K1; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RK SLOW Hst2.
set (c2 := fst (sh_getc f1)) in *.
zs. zs. zs. brf K2.
+ exfalso. clear - K2 FCH w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base ssp_guard. destruct (fch_facts _ FCH) as (A73 & A78 & A88 & B73 & B78 & B88 & _). first [exact (A73 K2) | exact (B73 K2)].
+ zs. eapply L_5D0; try eassumption; try lia.
* mk_winv2.
* pose proof (land_mask_range (Z.land c2 18446744073709551615) 18446744073709551583 ltac:(lia)). try pose proof (land_mask_range c2 18446744073709551583 ltac:(lia)). lia.
* clear - FCH w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base ssp_guard. destruct (fch_facts _ FCH) as (A73 & A78 & A88 & B73 & B78 & B88 & _). first [exact A78 | exact B78].
- pose proof (rf_getc_fast_lt T txt p J Hp k1 c1 f1 RK Hc10 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k1 c1 f1 RK FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f1) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. zs. zs. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 sg) by (subst sg; destruct Hc1 as [-> | ->]; apply Z_to_bv_eqm; reflexivity).
clearbody sg.
zs. (brf K1; [ exfalso; lia | ]).
zs. zs0. read_char f1.
set (c2 := znth txt (sh_rpos f1)) in *.
zs. zs. zs. brf K2.
+ eapply L_5D0; try eassumption; try lia.
* mk_winv2.
* pose proof (land_mask_range (Z.land c2 18446744073709551615) 18446744073709551583 ltac:(lia)). try pose proof (land_mask_range c2 18446744073709551583 ltac:(lia)). lia.
* clear - FCH w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base ssp_guard. destruct (fch_facts _ FCH) as (A73 & A78 & A88 & B73 & B78 & B88 & _). first [exact A78 | exact B78].
+ exfalso. clear - K2 FCH w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base ssp_guard. destruct (fch_facts _ FCH) as (A73 & A78 & A88 & B73 & B78 & B88 & _). first [exact (A73 K2) | exact (B73 K2)].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618"] Lemma L_554 : forall m2 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x19' x25' x26' x27' x28' x29' x30' x31' : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws (c1 : Z) (f1 : shfile) (k1 : Z),
let _ := ctx_all in
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f1 ->
RFJ' k1 c1 f1 -> (1 <= k1)%Z -> sh_stdio f1 = sh_stdio f0 -> fch c1 -> (c1 <> (-1)%Z -> 1 <= sh_rpos f1)%Z ->
(forall sg c2 f2,
(if ((c1 =? 43) || (c1 =? 45))%Z then ((1 - 2 * b2z (c1 =? 45))%Z, fst (sh_getc f1), snd (sh_getc f1)) else (1%Z, c1, f1)) = (sg, c2, f2) ->
FS_tail sg c2 f2 = Some (fR, yR)) ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 32) (Z_to_bv 64 c1) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19' (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25' x26' x27' x28' x29' x30' x31')
F (Z_to_bv 64 (base + 0xf0)) fc None m2 (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok.
intros until k1. intros _ WI2 RK Hk2 Hst2 FCH1 Hr1 HT.
pose proof WI2 as WI3. dest_winv WI3. bury_disj.
assert (Rc1 : (-1 <= c1 < 256)%Z) by (destruct RK as (_ & R & _); exact R).
zs. zs. brf Ka.
- assert (E45 : c1 = 45%Z) by (clear - Ka Rc1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base ssp_guard; rewrite ?land_W64 in Ka; Z.div_mod_to_equations; lia).
eapply L_564; try eassumption; try lia.
apply HT. rewrite E45. reflexivity.
- assert (N45 : c1 <> 45%Z) by (clear - Ka Rc1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base ssp_guard; rewrite ?land_W64 in Ka; Z.div_mod_to_equations; lia).
zs. zs. brf Kb.
+
assert (N43 : c1 <> 43%Z) by (clear - Kb Rc1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base ssp_guard; rewrite ?land_W64 in Kb; Z.div_mod_to_equations; lia).
specialize (HT 1%Z c1 f1).
replace ((c1 =? 43) || (c1 =? 45))%Z with false in HT by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) N43), (proj2 (Z.eqb_neq _ _) N45); reflexivity).
specialize (HT eq_refl).
zs. zs. zs. zs. brf Kc.
* exfalso. clear - Kc FCH1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base ssp_guard. destruct (fch_facts _ FCH1) as (A73 & A78 & A88 & B73 & B78 & B88 & _). first [exact (A73 Kc) | exact (B73 Kc)].
* eapply L_5D0; try eassumption; try lia.
-- pose proof (land_mask_range (Z.land c1 18446744073709551615) 18446744073709551583 ltac:(lia)). try pose proof (land_mask_range c1 18446744073709551583 ltac:(lia)). lia.
-- clear - FCH1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base ssp_guard. destruct (fch_facts _ FCH1) as (A73 & A78 & A88 & B73 & B78 & B88 & _). first [exact A78 | exact B78].
+ assert (E43 : c1 = 43%Z) by (clear - Kb Rc1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base ssp_guard; rewrite ?land_W64 in Kb; Z.div_mod_to_equations; lia).
eapply L_564; try eassumption; try lia.
apply HT. rewrite E43. reflexivity.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_22 lo_23 CODE BASE4 BASER D_22 E_22 D_23 E_23 ANCH_23 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ HM ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618"] Lemma L_ENTRY : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ev : word),
let _ := ctx_all in
stk segs m0 (q - FS_DEPTH) q -> mem_inv segs m0 ->
rw_cells segs m0 Fp (rf_cells T p true f0 J) -> RFJ' kmin0 c0 f0 -> (0 <= kmin0)%Z -> c0 <> 0%Z -> sh_stdio f0 = sh_stdio f0 ->
bytes_at segs m0 T (zbytes txt) -> ssp_cells m0 canary -> rw_cells segs m0 RERRNO [C4 ev] ->
evt segs POST
(MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 Fp) (Z_to_bv 64 1) (Z_to_bv 64 pok) a3 a4 a5 a6 a7
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F (Z_to_bv 64 FLOATSCAN) fc None m0 (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_22 lo_23 CODE BASE4 BASER D_22 E_22 D_23 E_23 ANCH_23 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ HM ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618 segs ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok. try gw_hide Hpok.
intros until ev. intros _ ST MI FC RJ Hk0 Hc0 Hst BY [SSP1 SSP2] ERR.
pose proof (munch_refl Wfs m0) as MU. pose proof (wmono_refl segs m0) as WM. unfold F_floatscan_common__Wfs, FS_DEPTH, RERRNO in MU. unfold FS_DEPTH in ST.
gw_expose got_ssp; gw_expose ssp_guard. unfold RERRNO in ERR.
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T.
pose proof zbytes_len as LTX. unfold zlength in *. bury_disj.
site_facts FC RJ kmin0 c0 f0.

pose proof HM as HM'. destruct fuelc as [|fu] eqn:Efu in HM'; [discriminate HM'|].
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin0 c0 f0 RJ Hc0) as RJ1.
pose proof (getc_fch kmin0 c0 f0 RJ Hc0) as FCH1.
pose proof (getc_stdio f0) as Hst1.
assert (Rc1 : (-1 <= fst (sh_getc f0) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f0 Hbuf) as [Rrp1 Rrp2].
unfold FLOATSCAN.

zs.
carve_frame 120%nat ST. rename FR into FRhi.
do 14 zs.
lazymatch type of FRhi with rw_cells _ _ _ (CB 8 ?b :: _) => set (jc := b) in FRhi; clearbody jc end.
zs. zs.
replace (Z_to_bv 64 (q + -2032 - 4096))%Z with (Z_to_bv 64 (q + -6128))%Z by (f_equal; lia).

assert (Hcv1 : (q - 8656 <= q + -120 - Z.of_nat (Z.to_nat 6000))%Z) by lia;
destruct (stk_carve segs _ _ _ (Z.to_nat 6000) ST Hcv1) as [ST' [junka XBa]]; clear ST Hcv1; rename ST' into ST;
replace (q + -120 - Z.of_nat (Z.to_nat 6000))%Z with (q + -6120)%Z in ST, XBa by lia.
assert (Hcv2 : (q - 8656 <= q + -6120 - Z.of_nat 8)%Z) by lia;
destruct (stk_carve segs _ _ _ 8%nat ST Hcv2) as [ST' [junkb XBb]]; clear ST Hcv2; rename ST' into ST;
replace (q + -6120 - Z.of_nat 8)%Z with (q + -6128)%Z in ST, XBb by lia.
assert (Hcv3 : (q - 8656 <= q + -6128 - Z.of_nat (Z.to_nat 2184))%Z) by lia;
destruct (stk_carve segs _ _ _ (Z.to_nat 2184) ST Hcv3) as [ST' [junkc XBc]]; clear ST Hcv3; rename ST' into ST;
replace (q + -6128 - Z.of_nat (Z.to_nat 2184))%Z with (q + -8312)%Z in ST, XBc by lia.
zs.
release_frame XBc ST (q + -6128)%Z. release_frame XBb ST (q + -6120)%Z. release_frame XBa ST (q + -120)%Z.
clear junka junkb junkc.
let n := eval vm_compute in (Z.to_nat 8192) in
assert (Hcv : (q - 8656 <= q + -120 - Z.of_nat n)%Z) by (change (Z.of_nat n) with 8192%Z; lia);
destruct (stk_carve segs _ _ _ n ST Hcv) as [ST' [junkx XB2]]; clear ST Hcv; rename ST' into ST;
change (Z.of_nat n) with 8192%Z in ST, XB2.
replace (q + -120 - 8192)%Z with (q + -8312)%Z in ST, XB2 by lia.
pose proof XB2 as XB0. destruct XB0 as [[[LB _] _] _]. cbn in LB.
apply u8arr_of_rw_cells in XB2.
destruct (u32arr_of_u8arr segs _ _ _ 2048%nat XB2 ltac:(rewrite LB; reflexivity)) as (ws0 & LW0 & XW). clear XB2 LB junkx.
zs. zs.
replace (Z_to_bv 64 (q + -6128 + -2048 + -240))%Z with SPv by (f_equal; lia).
carve_frame 104%nat ST. rename FR into LOW.
apply (rw_cells_split_CB _ _ _ [] 104 _ [] [8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in LOW; [|reflexivity]. cbn [mk_CB_cells app] in LOW.
do 11 (c8ify LOW).
lazymatch type of LOW with rw_cells _ _ _ [CB 8 ?a; C8 ?b1; C8 ?b2; C8 ?b3; C8 ?b4; C8 ?b5; C8 ?b6; C8 ?b7; C8 ?b8; C8 ?b9; C8 ?b10; C8 ?b11; CB 8 ?c] =>
set (j0 := a) in LOW; set (w8 := b1) in LOW; set (w16 := b2) in LOW; set (w24 := b3) in LOW; set (w32 := b4) in LOW;
set (w40 := b5) in LOW; set (w48 := b6) in LOW; set (w56 := b7) in LOW; set (w64 := b8) in LOW; set (w72 := b9) in LOW;
set (w80 := b10) in LOW; set (w88 := b11) in LOW; set (b96 := c) in LOW;
clearbody j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 end.
match goal with H : list byte |- _ => try clear H end.

zs. zs. zs. zs. zs. zs. zs. zs.

zs. (brf K1; [ exfalso; lia | ]). zs. zs. (brf K2; [ exfalso; lia | ]). zs. zs. (brf K3; [ exfalso; lia | ]). zs. zs. zs. zs. zs. zs.
clear K1 K2 K3.

assert (HT : forall sg c2 f2,
(if ((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z then ((1 - 2 * b2z (fst (sh_getc f0) =? 45))%Z, fst (sh_getc (snd (sh_getc f0))), snd (sh_getc (snd (sh_getc f0)))) else (1%Z, fst (sh_getc f0), snd (sh_getc f0))) = (sg, c2, f2) ->
FS_tail sg c2 f2 = Some (fR, yR)).
{ intros sg c2 f2 E.
assert (FC2 : fch c2).
{ destruct ((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z eqn:Eb; injection E as E1 E2 E3; subst c2; [|exact FCH1].
apply (getc_fch (kmin0 + 1) (fst (sh_getc f0))); [exact RJ1|].
intros E0. rewrite E0 in Eb. discriminate Eb. }
destruct (fch_facts _ FCH1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NSP & _).
destruct (fch_facts _ FC2) as (_ & _ & _ & _ & _ & _ & M105 & M110 & _).
unfold QzQg.Mq0.FS_tail. rewrite Efu. rewrite <- (floatscan_front fu f0 sg c2 f2 NSP E M105 M110). exact HM'. }
clear HM'.
destruct (fch_facts _ FCH1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N32 & N9).

destruct (Z.eq_dec (T + sh_rpos f0)%Z (rf_rend T p true f0)) as [SLOW|FAST].
- pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
zs. zs.
destruct (rf_getc_slow T txt p J Hp T1 kmin0 c0 f0 RJ SLOW) as (STD & EJ & Hn & Hrpe & Hc00).
destruct (ST0 STD) as [TXT Hpre].
call_split 160%Z (eapply (gw_unhyp shgetc_callJ) with (pre := pre) (post := post);
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | hyp | gw_expose got_ssp; gw_expose ssp_guard; unfold ssp_cells; split; hyp
| eplia | eplia | exact SEP | replace (q + -8416 - 160)%Z with (q + -8416 - 160)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H end.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; gw_expose got_ssp; gw_expose ssp_guard end.
set (c1 := fst (sh_getc f0)) in *.
zs. zs. brf K2.
+ zs. brf K3.
* exfalso. clear - K3 N32 Rc1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_22 lo_23 CODE BASE4 BASER D_22 E_22 D_23 E_23 ANCH_23 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs. rewrite ?land_W64 in K3. Z.div_mod_to_equations; lia.
* eapply L_554; try eassumption; try lia. mk_winv2.
+ exfalso. clear - K2 N9 Rc1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_22 lo_23 CODE BASE4 BASER D_22 E_22 D_23 E_23 ANCH_23 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs. rewrite ?land_W64 in K2. Z.div_mod_to_equations; lia.
- pose proof (rf_getc_fast_lt T txt p J Hp kmin0 c0 f0 RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin0 c0 f0 RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f0) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0. read_char f0.
set (c1 := znth txt (sh_rpos f0)) in *.
zs. zs. brf K2.
+ exfalso. clear - K2 N9 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_22 lo_23 CODE BASE4 BASER D_22 E_22 D_23 E_23 ANCH_23 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs. rewrite ?land_W64 in K2. Z.div_mod_to_equations; lia.
+ zs. brf K3.
* exfalso. clear - K3 N32 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 hi_22 lo_23 CODE BASE4 BASER D_22 E_22 D_23 E_23 ANCH_23 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs. rewrite ?land_W64 in K3. Z.div_mod_to_equations; lia.
* eapply L_554; try eassumption; try lia. mk_winv2.
Qed.

End Floatscan.

End G.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx2n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0 Qx2n.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import QhAd.
Import QVbl.Mq3.
Import QQLG.Mq8.
Import QQRC.Mq0.
Import Q91D.
Import QCa8.
Import QVbl.
Import QQRC.
Import QkTt.Mq0.
Import QkTt.Mq1.
Import QVbl.Mq2.
Import QVbl.Mq1.
Import QQLG.Mq3.
Import QQLG.Mq4.
Import QQLG.Mq1.
Import Q91D.Mq4.
Import Qy8Z.Mq0.
Import QQRC.Mq3.
Import Q8l1.Mq3.
Import QROt.Mq2.
Import QQRC.Mq1.
Import QZxv.Mql.
Import QQRC.Mq2.
Import Q8l1.Mq0.
Import Q5m9.Mq1.
Import QXfH.

Import QzQg.Mq0.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 : Z).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.

Local Definition gw_tbl_0 := tt.

Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_0))))).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@Q5m9.Mq1.RFI STRING_READ) RFI (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_1))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_2))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_3).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_4).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_5))))).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_6).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_7).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_8).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_9).

Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_10))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Notation rfj := G.T_rfj.rfj.

Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Notation F_floatscan_common__winv := winv (only parsing).

#[using="got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard rf_getc_slow"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard rf_getc_slow.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis Hpok1 : pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs_ ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs_ m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs_ m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs_ ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs_ m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs_ m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).

Notation RFJ' := (RFJ T txt p true J).

Local Notation ctx_all := (@QzQg.Mq0.ctx_all ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation Wfs := (@F_floatscan_common__Wfs q Fp).
Local Notation FokR := (@QzQg.Mq0.FokR F).
Local Notation Fok := (@QzQg.Mq0.Fok F).

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).

Local Notation winv := (@F_floatscan_common__winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

Notation POST := (fs_post m0).

#[using="Type"] Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma getc_rpos2 : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide BYT; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.

#[using="rf_getc_slow Hp T1"] Lemma rf_slow_false : forall kmin c f, RFJ' kmin c f -> (T + sh_rpos f)%Z = rf_rend T p true f -> False.
Proof. clear - rf_getc_slow Hp T1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hnul HP30 T0 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros kmin c f RJ SLOW. destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & _).
destruct RJ as (_ & _ & _ & _ & _ & SS). destruct (SS STD) as (_ & _ & _ & _ & [_ FF]). exact FF.
Qed.

#[using="Type"] Lemma forallb_range : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, (0 <= c < Z.of_nat n)%Z -> P c = true.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros P n H c Hc. apply (proj1 (forallb_forall P _) H). apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Definition and33_okb (c : Z) : bool :=
forallb (fun U => implb ((65 <=? U) && (U <=? 90))%Z (Bool.eqb (Z.land c 18446744073709551583 =? U) (Z.lor c 32 =? U + 32)))%Z
(map Z.of_nat (seq 0 91)).
#[using="Type"] Lemma and33_lor : forall c U, (0 <= c < 256)%Z -> (65 <= U <= 90)%Z ->
(Z.land c 18446744073709551583 = U <-> Z.lor c 32 = U + 32)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros c U Hc HU.
pose proof (forallb_range and33_okb 256 ltac:(vm_compute; reflexivity) c Hc) as E. unfold and33_okb in E.
pose proof (forallb_range _ 91 E U ltac:(lia)) as E2. cbv beta in E2.
replace ((65 <=? U) && (U <=? 90))%Z with true in E2 by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia). cbn [implb] in E2.
apply Bool.eqb_prop in E2.
destruct (Z.eqb_spec (Z.land c 18446744073709551583) U); destruct (Z.eqb_spec (Z.lor c 32) (U + 32)); try discriminate E2; tauto.
Qed.
#[using="Type"] Lemma and33_range : forall c, (0 <= c < 256)%Z -> (0 <= Z.land c 18446744073709551583 < 256)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros c Hc.
pose proof (forallb_range (fun c => (0 <=? Z.land c 18446744073709551583) && (Z.land c 18446744073709551583 <? 256))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

#[using="Type"] Lemma isspace_iff : forall c, (0 <= c < 256)%Z -> (m_isspace c = true <-> (c = 32 \/ 9 <= c <= 13))%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear Hpok | gw_hide Hpok | idtac]; first [clear Hpok1 | gw_hide Hpok1 | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros c Hc. unfold m_isspace, u32.
destruct (Z.eqb_spec c 32) as [->|N]; cbn [orb]; [split; [intros _; left; reflexivity | reflexivity]|].
rewrite Z.ltb_lt. change (2 ^ 32)%Z with 4294967296%Z. Z.div_mod_to_equations. lia.
Qed.

Notation FS_infk' := (FS_infk fuelc 53 (-1074) pok).

Notation FS_nank' := (FS_nank fuelc 53 (-1074) pok).

Notation FS_tail_h' := (FS_tail_h fuelc 53 (-1074) pok).
Notation FS_sign' := (FS_sign fuelc 53 (-1074) pok).

Definition SWSn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile) (c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (0 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
fs_ws_loop n f = Some (c', f') -> FS_sign' c' f' = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 5) (Z_to_bv 64 32) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xcc)) fc None m (seg_rom segs)).
Definition S_WS : Prop := forall n, SWSn n.

Definition S_AWS : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
(0 <= c < 256)%Z -> m_isspace c = false ->
FS_sign' c f = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 32) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xf0)) fc None m (seg_rom segs)).

Definition S_I1 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
Z.lor c 32 = 105%Z ->
FS_infk' sign 1 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x134)) fc None m (seg_rom segs)).

Definition S_N1 : Prop := forall m (x1 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (0 <= c < 256)%Z -> Z.lor c 32 <> 105%Z ->
FS_nank' sign 0 c f = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) (Z_to_bv 64 (Z.land c 18446744073709551583)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x16c)) fc None m (seg_rom segs)).

Definition S_Z : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
FS_tail_h' sign c f = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1b4)) fct None m (seg_rom segs)).

Definition S_ERR : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct -> sh_stdio f = sh_stdio f0 ->
fR = sh_lim0 (sh_unget f) -> yR = f128_of_i32 0 ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xa98)) fct None m (seg_rom segs)).

Definition sp_ok (v : word) (r : Z) : Prop :=
(v = Z_to_bv 64 0xffffffff7f800000 /\ r = C_INF) \/ (v = Z_to_bv 64 0xffffffffff800000 /\ r = C_NINF) \/ (v = Z_to_bv 64 0xffffffff7fc00000 /\ r = C_NAN).
Definition S_A38 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws k c (v : word),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws fR ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
sp_ok v yR -> (forall r : bv 5, bv_unsigned r = 10%Z -> reg_get Ft r = v) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xa90)) fct None m (seg_rom segs)).

Definition SPARn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile) (i i' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (i <= kmin)%Z -> Fok Ft -> frm0 fct -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
(1 <= i <= sh_rpos f)%Z ->
fs_par_loop n (i, f) = Some (i', c', f') ->
(fR, yR) = (if (c' =? 41)%Z then (f', C_NAN) else (fs_unget_loop (Z.to_nat i') (sh_unget f'), C_NAN)) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 i) (Z_to_bv 64 10) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 26) (Z_to_bv 64 95) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x470)) fct None m (seg_rom segs)).
Definition S_PAR : Prop := forall n, SPARn n.

Definition hinv (m : word -> option byte) (ev : word) (f : shfile) : Prop :=
mem_inv segs m /\ munch Wfs m0 m /\ wmono segs m0 m
/\ stk segs m (q - FS_DEPTH) q
/\ bytes_at segs m T (zbytes txt)
/\ rw_cells segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells segs m ssp_guard [C8 canary]
/\ rw_cells segs m RERRNO [C4 ev]
/\ rw_cells segs m Fp (rf_cells T p true f J).

Definition S_HEX : Prop := forall m (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) Ft fct ev sign kmin c (f : shfile),
let _ := ctx_all in
hinv m ev f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> FokR Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> Z.lor c 32 = 120%Z ->
hexfloat_m fuelc f 53 (-1074) sign pok = Some (fR, yR) ->
evt segs POST
(MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 Fp) (Z_to_bv 64 53) (Z_to_bv 64 (-1074)) (Z_to_bv 64 sign) (Z_to_bv 64 pok) a5 a6 a7
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
Ft (Z_to_bv 64 (base + 0x1688)) fct None m (seg_rom segs)).
End Floatscan.

End G.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 QqdR QYTG G.T_shp G.T_pe Qbz7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import QZAi.Mq1 Ql2m.Mq3 QZAi QqdR QYTG.Mq2.
Import QnDM_c1.
Import QVbl.Mq4.
Import QVbl.Mq3.
Import QQLG.Mq7.
Import Q91D.Mq2.
Import QQRC.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.
Import Q91D.Mq3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.
Import Qbz7.
Import Q8l1.Mq1.
Import Q5m9.Mq0.
Import QROt.Mq1.
Import Q8l1.Mq4.
Import QzQg.Mq1.
Import QzQg.Mq2.

Import Qfw3_c1.Mq1.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition vsnprintf_code (w_8 w_9 w_24 w_39 w_50 : Z) : list Z :=
[0xed010113; 0x12113423; 0x12813023; 0x10913c23; 0x11213823; 0x11313423; 0x00068413; 0x00060493; w_8; w_9; 0x00093603; 0x10c13023; 0x0fe10993; 0x00058463; 0x00050993; 0xfff58513; 0x00a5b5b3; 0xfff58593; 0x00a5f533; 0x0f313423; 0x0ea13823; 0x00010513; 0x0e800613; 0x00000593; w_24; 0x00000517; 0x0ff10593; 0xfff00613; 0x06850513; 0x04a13423; 0x04b13c23; 0x0e810513; 0x08c12623; 0x08c12823; 0x08a13c23; 0x00098023; 0x00010513; 0x00048593; 0x00040613; w_39; 0x00093583; 0x10013603; 0x02c59063; 0x12813083; 0x12013403; 0x11813483; 0x11013903; 0x10813983; 0x13010113; 0x00008067; w_50]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_8 w_9 w_24 w_39 w_50 : Z).
Variables (hi_8 : bv 20).
Variables (lo_9 : bv 12).
Variables (joff_24 joff_39 : bv 21).
Variables (got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_197bc e_fwritex e_towrite e_sn_write e_memset e_vfprintf : Z).
Hypothesis CODE : code_at segs base (vsnprintf_code w_8 w_9 w_24 w_39 w_50).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 204.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Auipc 12 hi_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_9 : decode_any (Z_to_bv 32 w_9) = Some (Load SZ8 true 18 12 lo_9, 4%Z).
Hypothesis E_9 : is_ecall (Z_to_bv 32 w_9) = false.
Hypothesis D_24 : decode_any (Z_to_bv 32 w_24) = Some (Jal 1 joff_24, 4%Z).
Hypothesis E_24 : is_ecall (Z_to_bv 32 w_24) = false.
Hypothesis D_39 : decode_any (Z_to_bv 32 w_39) = Some (Jal 1 joff_39, 4%Z).
Hypothesis E_39 : is_ecall (Z_to_bv 32 w_39) = false.
Hypothesis ANCH_9 : gw_anch (Z.shiftl (bv_signed hi_8) 12 + (base + 32) + bv_signed lo_9)%Z got_ssp.
Hypothesis LINK_24 : gw_anch (base + 96 + bv_signed joff_24)%Z (e_memset + 0)%Z.
Hypothesis LINK_39 : gw_anch (base + 156 + bv_signed joff_39)%Z (e_vfprintf + 0)%Z.
Hypothesis RNG_STATIC_SPLIT : gw_br STATIC_SPLIT 8.
Hypothesis LAY_lo_STATIC_SPLIT : gw_le 65536 STATIC_SPLIT.
Hypothesis AL_STATIC_SPLIT : gw_al STATIC_SPLIT 8.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_lo_GLOBALS_TOP : gw_le 65536 GLOBALS_TOP.
Hypothesis AL_GLOBALS_TOP : gw_al GLOBALS_TOP 8.
Hypothesis LAY_STATIC_SPLIT_got_ssp : gw_le (STATIC_SPLIT + 8) got_ssp.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.
Hypothesis LAY_snw_link : gw_anch (base + 204)%Z (e_sn_write + 0)%Z.

Local Definition gw_tbl_0 := tt.

Definition memset_post : ltac:(gw_rebind_ty (@QVbl.Mq4.memset_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QVbl.Mq4.memset_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@Q91D.Mq2.memset_post segs) memset_post (gw_ent (@QVbl.Mq4.memset_post segs) memset_post gw_tbl_0)).
Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QZxv.Mqi.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqh.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq7.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqg.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqf.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqe.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqj.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq9.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq8.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq5.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq4.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq0.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq2.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq3.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq1.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq1.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq0.arg_ok segs) arg_ok (gw_ent (@QK0e.arg_ok segs) arg_ok (gw_ent (@QEN3.arg_ok segs) arg_ok (gw_ent (@QzQg.Mq1.arg_ok segs) arg_ok (gw_ent (@Q5m9.Mq0.arg_ok segs) arg_ok (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_1))))))))))))))))))))))).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QZxv.Mqi.args_ok segs) args_ok (gw_ent (@QZxv.Mqh.args_ok segs) args_ok (gw_ent (@QEN3.Mq7.args_ok segs) args_ok (gw_ent (@QZxv.Mqg.args_ok segs) args_ok (gw_ent (@QZxv.Mqf.args_ok segs) args_ok (gw_ent (@QZxv.Mqe.args_ok segs) args_ok (gw_ent (@QZxv.Mqj.args_ok segs) args_ok (gw_ent (@QZxv.Mq9.args_ok segs) args_ok (gw_ent (@QZxv.Mq8.args_ok segs) args_ok (gw_ent (@QEN3.Mq5.args_ok segs) args_ok (gw_ent (@QEN3.Mq4.args_ok segs) args_ok (gw_ent (@QEN3.Mq0.args_ok segs) args_ok (gw_ent (@QZxv.Mq2.args_ok segs) args_ok (gw_ent (@QZxv.Mq3.args_ok segs) args_ok (gw_ent (@QEN3.Mq1.args_ok segs) args_ok (gw_ent (@QZxv.Mq1.args_ok segs) args_ok (gw_ent (@QZxv.Mq0.args_ok segs) args_ok (gw_ent (@QK0e.args_ok segs) args_ok (gw_ent (@QEN3.args_ok segs) args_ok (gw_ent (@QzQg.Mq1.args_ok segs) args_ok (gw_ent (@Q5m9.Mq0.args_ok segs) args_ok (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_2))))))))))))))))))))))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QZxv.Mq6.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq5.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq7.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqc.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqk.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqb.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqd.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqi.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqh.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq7.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqg.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqf.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqe.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqj.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq9.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq8.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq5.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq8.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QK0e.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqa.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq6.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QzQg.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_3)))))))))))))))))))))))))))))))))))))).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QZxv.Mq6.va_area segs) va_area (gw_ent (@QZxv.Mq5.va_area segs) va_area (gw_ent (@QZxv.Mq7.va_area segs) va_area (gw_ent (@QZxv.Mqc.va_area segs) va_area (gw_ent (@QEN3.Mq3.va_area segs) va_area (gw_ent (@QZxv.Mqk.va_area segs) va_area (gw_ent (@QZxv.Mqb.va_area segs) va_area (gw_ent (@QZxv.Mqd.va_area segs) va_area (gw_ent (@QZxv.Mq4.va_area segs) va_area (gw_ent (@QZxv.Mqi.va_area segs) va_area (gw_ent (@QZxv.Mqh.va_area segs) va_area (gw_ent (@QEN3.Mq7.va_area segs) va_area (gw_ent (@QZxv.Mqg.va_area segs) va_area (gw_ent (@QZxv.Mqf.va_area segs) va_area (gw_ent (@QZxv.Mqe.va_area segs) va_area (gw_ent (@QZxv.Mqj.va_area segs) va_area (gw_ent (@QZxv.Mq9.va_area segs) va_area (gw_ent (@QZxv.Mq8.va_area segs) va_area (gw_ent (@QEN3.Mq2.va_area segs) va_area (gw_ent (@QEN3.Mq5.va_area segs) va_area (gw_ent (@QEN3.Mq4.va_area segs) va_area (gw_ent (@QEN3.Mq0.va_area segs) va_area (gw_ent (@QZxv.Mq2.va_area segs) va_area (gw_ent (@QEN3.Mq8.va_area segs) va_area (gw_ent (@QZxv.Mq3.va_area segs) va_area (gw_ent (@QEN3.Mq1.va_area segs) va_area (gw_ent (@QZxv.Mq1.va_area segs) va_area (gw_ent (@QZxv.Mq0.va_area segs) va_area (gw_ent (@QK0e.va_area segs) va_area (gw_ent (@QEN3.va_area segs) va_area (gw_ent (@QZxv.Mqa.va_area segs) va_area (gw_ent (@QEN3.Mq6.va_area segs) va_area (gw_ent (@QzQg.Mq1.va_area segs) va_area (gw_ent (@QROt.Mq1.va_area segs) va_area (gw_ent (@Q5m9.Mq0.va_area segs) va_area (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_4)))))))))))))))))))))))))))))))))))))).
Definition snfile_head : ltac:(gw_rebind_ty (@QzQg.Mq1.snfile_head e_sn_write) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QzQg.Mq1.snfile_head e_sn_write) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq1.snfile_head e_sn_write) snfile_head gw_tbl_5).
Definition vfprintf_sn_post : ltac:(gw_rebind_ty (@QzQg.Mq1.vfprintf_sn_post segs got_ssp ssp_guard) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QzQg.Mq1.vfprintf_sn_post segs got_ssp ssp_guard) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq1.vfprintf_sn_post segs got_ssp ssp_guard) vfprintf_sn_post gw_tbl_6).
Definition vfprintf_sn_stmt := ltac:(let t := constr:(ltac:(gw_rebind (@QzQg.Mq1.vfprintf_sn_stmt segs e_vfprintf got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_sn_write) constr:(gw_tbl_7))) in exact t).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq1.vfprintf_sn_stmt segs e_vfprintf got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_sn_write) vfprintf_sn_stmt gw_tbl_7).

Hypothesis memset_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq4.memset_spec segs e_memset) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_8))) in exact T).

Hypothesis rw_CB_length : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8l1.Mq4.gw_all) (@Q8l1.Mq4.rw_CB_length) e_sn_write)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_8))) in exact T).

Hypothesis rwc_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QzQg.Mq1.gw_all) (@QzQg.Mq1.rwc_eq) e_vfprintf)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_8))) in exact T).
Hypothesis vfprintf_sn_proof : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QzQg.Mq1.gw_all) (@QzQg.Mq1.vfprintf_sn_proof) e_vfprintf)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_8))) in exact T).
Notation mem := (word -> option byte).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Notation parg := G.T_printf.parg.
Notation PA_s := G.T_printf.PA_s.

#[using="got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_197bc e_fwritex e_towrite e_sn_write e_memset e_vfprintf CODE BASE4 BASER D_8 E_8 D_9 E_9 D_24 E_24 D_39 E_39 ANCH_9 LINK_24 LINK_39 RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT AL_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP AL_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP LAY_snw_link memset_spec rw_CB_length rwc_eq vfprintf_sn_proof"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_8 w_9 w_24 w_39 w_50 hi_8 lo_9 joff_24 joff_39 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_197bc e_fwritex e_towrite e_sn_write e_memset e_vfprintf CODE BASE4 BASER D_8 E_8 D_9 E_9 D_24 E_24 D_39 E_39 ANCH_9 LINK_24 LINK_39 RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT AL_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP AL_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP LAY_snw_link memset_spec rw_CB_length rwc_eq vfprintf_sn_proof.

Local Ltac transport_chunks segs_ m a bs ::= transport_chunks_fast segs_ m a bs.
Local Ltac footprint_after_store segs_ m a bs ::= footprint_after_store_fast segs_ m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs_ m m' MU WM ::= transport_after_call_fast segs_ m m' MU WM.
Local Ltac lia ::= lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
(try g_ret_pc) end.

#[using="Type"] Lemma rw_cells_recast : forall m A cs cs', rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof. clear - segs.
intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

#[using="Type"] Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells segs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells segs m A (pre ++ C4 v' :: post).
Proof. clear - segs.
intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
- destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 [_ W2]]. apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
- rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.

Ltac c4_eqv H k v' :=
lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
let H' := fresh in
pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
end end.

Definition no_s (a : parg) : Prop := match a with PA_s _ => False | _ => True end.
#[using="Type"] Lemma args_ok_nos : forall Fp B BS Fp' B' BS' m m' lo sp ap lo' sp' ap' ws args,
Forall no_s args -> args_ok Fp B BS m lo sp ap ws args -> args_ok Fp' B' BS' m' lo' sp' ap' ws args.
Proof.
intros Fp B BS Fp' B' BS' m m' lo sp ap lo' sp' ap' ws args NS. revert ws.
induction NS as [|a args Ha _ IH]; intros ws H; [destruct ws; exact I|].
cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
split; [|apply IH; exact H2]. destruct a; cbn in Ha, H1 |- *; [contradiction|exact H1|exact H1|exact H1|exact H1|exact H1].
Qed.

Definition VSN_FRAME : Z := 304.
Definition VSN_DEPTH : Z := 5856.

Definition vsnprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(D : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom segs)
/\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk segs m' lo (bv_unsigned sp)
/\ ssp_cells m' canary
/\ rw_cells segs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)].

Definition vsnprintf_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(D n A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
(lo : Z) (canary : word) (r : Z) (o : list Z),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
rw_cells segs m D [CB dn junkd] ->
bytes_at segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> Forall no_s args -> args_ok 0 0 0 m lo q 0 slots args ->
printf_model OUT_sn OUTFP_sn fmt args [] = QlEo_c1.Mq0.Ret (Ok (r, o)) ->
Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
(length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
stk segs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
ssp_cells m canary -> mem_inv segs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D \/ (STATIC_SPLIT <= D /\ D + Z.of_nat dn <= got_ssp) \/ (got_ssp + 8 <= D /\ D + Z.of_nat dn <= ssp_guard) \/ (ssp_guard + 8 <= D /\ D + Z.of_nat dn <= GLOBALS_TOP)) ->
evt segs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).

#[using="w_8 w_9 w_24 w_39 w_50 hi_8 lo_9 joff_24 joff_39 e_sn_write e_memset e_vfprintf CODE BASE4 BASER D_8 E_8 D_9 E_9 D_24 E_24 D_39 E_39 ANCH_9 LINK_24 LINK_39 RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP LAY_snw_link memset_spec rw_CB_length rwc_eq vfprintf_sn_proof"] Theorem vsnprintf_proof : vsnprintf_stmt.
Proof. clear - w_8 w_9 w_24 w_39 w_50 hi_8 lo_9 joff_24 joff_39 e_sn_write e_memset e_vfprintf CODE BASE4 BASER D_8 E_8 D_9 E_9 D_24 E_24 D_39 E_39 ANCH_9 LINK_24 LINK_39 RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP LAY_snw_link memset_spec rw_CB_length rwc_eq vfprintf_sn_proof.
unfold vsnprintf_stmt. intros until o. cbv zeta.
intros -> -> -> -> DST BY HF P1 VAA NOS AOK MODEL FPF ROOM Hn Hn1 ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI DD1 DVA GD. gw_expose got_ssp; gw_expose ssp_guard.
gw_expose GLOBALS_TOP; gw_expose STATIC_SPLIT; unfold VSN_DEPTH in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
destruct SSP as [SSP1 SSP2]. gw_expose got_ssp; gw_expose ssp_guard. idtac. idtac.
pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
carve_frame 304%nat ST.
do 12 zs.
zs. zs. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
zs. zs. zs. zs. zs.

replace (n <? n + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615.
replace (Z.land 18446744073709551615 (n + -1)) with (n + -1)
by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
zs. zs. zs. zs. zs.
match goal with H : rw_cells _ _ (bv_unsigned sp + -304)%Z (CB 232 ?j :: _) |- _ => rename H into FRv; set (j0 := j) in FRv; clearbody j0 end.
match type of FRv with rw_cells _ _ _ [_; _; _; CB 8 ?j; _; _; _; _; _; _] => set (j8 := j) in FRv; clearbody j8 end.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in FRv. destruct FRv as [FZ FRv]. cbn [cells_size csize Nat.add app] in FRv.
replace (bv_unsigned sp + -304 + Z.of_nat 232)%Z with (bv_unsigned sp + -72)%Z in FRv by lia.

zs. eapply evt_cut.
{ eapply memset_spec; rewrite ?unsigned_lit by lia; [ | eassumption ]. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact FZ. }
cbv beta. intros ms' P. unfold memset_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m2 & -> & MUc & WMc & MI2 & FZ').
clear FZ.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call segs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.

pose proof (rw_cells_recast _ _ _ (gfile_cells (Z_to_bv 64 0) 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) 0 ++ snfile_rest 0) FZ'
ltac:(cbn [cells_wf cell_wf gfile_cells snfile_rest app]; repeat split) ltac:(vm_compute; reflexivity)) as FC. clear FZ'.
unfold gfile_cells, snfile_rest in FC. cbn [app] in FC.
do 10 zs.
c4_eqv FC 20%nat (Z_to_bv 64 4294967295). c4_eqv FC 21%nat (Z_to_bv 64 4294967295).

pose proof (rw_CB_length _ _ _ _ DST) as LJ.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
pose proof (u8arr_store_ok segs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
pose proof (u8arr_write segs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJ in DST. clear DA2.
zs. zs. zs. zs.

apply (proj1 (rw_cells_app segs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in FC. destruct FC as [FH FR]. cbn [cells_size csize Nat.add app] in FR.
replace (bv_unsigned sp + -304 + Z.of_nat 148)%Z with (bv_unsigned sp + -304 + 148)%Z in FR by lia.
apply (proj1 (rw_cells_app segs _ _ [_;_] _)) in FRv. destruct FRv as [CKC FRv]. cbn [cells_size csize Nat.add app] in FRv.
replace (bv_unsigned sp + -72 + Z.of_nat 16)%Z with (bv_unsigned sp + -56)%Z in FRv by lia.
pose proof (gw_unhyp vfprintf_sn_proof) as VF. unfold vfprintf_sn_stmt in VF.
eapply evt_cut.
pose proof LAY_snw_link as LK_snw_; unfold gw_anch in LK_snw_; repeat match goal with H : context [(0 + (base + 100) + 104)%Z] |- _ => replace (0 + (base + 100) + 104)%Z with (e_sn_write + 0)%Z in H by lia end; try replace (0 + (base + 100) + 104)%Z with (e_sn_write + 0)%Z by lia; clear LK_snw_.
{ eapply VF with (Fp := bv_unsigned sp + -304) (CK := bv_unsigned sp + -72) (D := D) (n := n + -1) (bufp := bv_unsigned sp + -49) (A := A) (VA := VA)
(dn := dn) (junkd := upd junkd (Z.to_nat 0) (Z_to_bv 8 0)) (fmt := fmt) (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
clear VF; rewrite ?unsigned_lit by lia; gw_expose GLOBALS_TOP; gw_expose STATIC_SPLIT; gw_expose got_ssp; gw_expose ssp_guard; unfold VF_FRAME, PC_DEPTH, zlength.
all: try reflexivity.
all: try lia.
- unfold snfile_head, gfile_cells. exact FH.
- unfold snfile_rest. exact FR.
- exact CKC.
- exact DST.
- exact BY.
- exact HF.
- exact P1.
- exact VAA.
- eapply args_ok_nos; [exact NOS | exact AOK].
- exact MODEL.
- exact FPF.
- exact ST.
- split; [exact SSP1 | exact SSP2].
- exact MI2.
- exact FRM. }
cbv beta. intros ms' P. clear VF.
unfold vfprintf_sn_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & fjunk & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SSP3 & DST3 & CK3 & FJ3).
lazymatch type of MUc with munch _ ?mm _ => transport_after_call segs mm m3 MUc WMc; clear MUc WMc; try clear MI2 end.
fix_ret.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. gw_expose got_ssp; gw_expose ssp_guard.
change segs with segs in SSP1, SSP2.

zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear - Kc w_8 w_9 w_24 w_39 w_50 hi_8 lo_9 joff_24 joff_39 e_sn_write e_memset e_vfprintf CODE BASE4 BASER D_8 E_8 D_9 E_9 D_24 E_24 D_39 E_39 ANCH_9 LINK_24 LINK_39 RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP LAY_snw_link memset_spec rw_CB_length rwc_eq vfprintf_sn_proof. apply Kc. reflexivity. }
do 7 zs.
lazymatch goal with FJ : rw_cells _ ?mm (bv_unsigned sp + -304)%Z _, CK : rw_cells _ ?mm (bv_unsigned sp + -72)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -56)%Z _ |- _ =>
assert (FALL : rw_cells segs mm (bv_unsigned sp + -304) ([CB 232 fjunk] ++ [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n + -1 - zlength o))] ++ [CB 8 j8; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
[ apply (proj2 (rw_cells_app segs _ _ _ _)); split; [exact FJ|];
apply (proj2 (rw_cells_app segs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact CK | lia] |];
cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
| clear FJ CK FR ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|].
split; [split; [exact SSP1 | exact SSP2]|].
rewrite upd_firstn_skipn in DST3 by (rewrite LJ; lia). change (Z.to_nat 0) with 0%nat in DST3.
change (firstn 0 junkd) with (@nil byte) in DST3. rewrite app_nil_l in DST3.
change (skipn (S (length o)) (Z_to_bv 8 0 :: skipn 1 junkd)) with (skipn (length o) (skipn 1 junkd)) in DST3.
rewrite skipn_skipn, Nat.add_1_r in DST3. exact DST3.
Qed.

#[using="Type"] Lemma fmt_bytes_at : forall m A f, mem_inv segs m -> ro_bytes_b segs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
bytes_at segs m A (zb f).
Proof. clear - segs.
intros m A f MI RB H0 H1.
pose proof (ro_cells_bytes_at segs m A _ (ro_cells_image segs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

End G.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPUx.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhAd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhAd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVbl.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q91D.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVbl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVbl.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVbl.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q91D.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8l1.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QROt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QROt.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZxv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZxv.Mql.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8l1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5m9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5m9.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXfH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXfH.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzQg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzQg.Mq0.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwFold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 : Z).
Variables (joff_1192 joff_1197 joff_1218 joff_1219 joff_1222 joff_1228 joff_1229 joff_1234 joff_1241 joff_1244 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_extenddftf2 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_1192 : decode_any (Z_to_bv 32 w_1192) = Some (Jal 1 joff_1192, 4%Z).
Hypothesis E_1192 : is_ecall (Z_to_bv 32 w_1192) = false.
Hypothesis D_1197 : decode_any (Z_to_bv 32 w_1197) = Some (Jal 1 joff_1197, 4%Z).
Hypothesis E_1197 : is_ecall (Z_to_bv 32 w_1197) = false.
Hypothesis D_1218 : decode_any (Z_to_bv 32 w_1218) = Some (Jal 1 joff_1218, 4%Z).
Hypothesis E_1218 : is_ecall (Z_to_bv 32 w_1218) = false.
Hypothesis D_1219 : decode_any (Z_to_bv 32 w_1219) = Some (Jal 1 joff_1219, 4%Z).
Hypothesis E_1219 : is_ecall (Z_to_bv 32 w_1219) = false.
Hypothesis D_1222 : decode_any (Z_to_bv 32 w_1222) = Some (Jal 1 joff_1222, 4%Z).
Hypothesis E_1222 : is_ecall (Z_to_bv 32 w_1222) = false.
Hypothesis D_1228 : decode_any (Z_to_bv 32 w_1228) = Some (Jal 1 joff_1228, 4%Z).
Hypothesis E_1228 : is_ecall (Z_to_bv 32 w_1228) = false.
Hypothesis D_1229 : decode_any (Z_to_bv 32 w_1229) = Some (Jal 1 joff_1229, 4%Z).
Hypothesis E_1229 : is_ecall (Z_to_bv 32 w_1229) = false.
Hypothesis D_1234 : decode_any (Z_to_bv 32 w_1234) = Some (Jal 1 joff_1234, 4%Z).
Hypothesis E_1234 : is_ecall (Z_to_bv 32 w_1234) = false.
Hypothesis D_1241 : decode_any (Z_to_bv 32 w_1241) = Some (Jal 1 joff_1241, 4%Z).
Hypothesis E_1241 : is_ecall (Z_to_bv 32 w_1241) = false.
Hypothesis D_1244 : decode_any (Z_to_bv 32 w_1244) = Some (Jal 1 joff_1244, 4%Z).
Hypothesis E_1244 : is_ecall (Z_to_bv 32 w_1244) = false.
Hypothesis LINK_1192 : gw_anch (base + 4768 + bv_signed joff_1192)%Z (e_floatsitf + 0)%Z.
Hypothesis LINK_1197 : gw_anch (base + 4788 + bv_signed joff_1197)%Z (e_multf3 + 0)%Z.
Hypothesis LINK_1218 : gw_anch (base + 4872 + bv_signed joff_1218)%Z (e_scalbn + 0)%Z.
Hypothesis LINK_1219 : gw_anch (base + 4876 + bv_signed joff_1219)%Z (e_extenddftf2 + 0)%Z.
Hypothesis LINK_1222 : gw_anch (base + 4888 + bv_signed joff_1222)%Z (e_extendsftf2 + 348)%Z.
Hypothesis LINK_1228 : gw_anch (base + 4912 + bv_signed joff_1228)%Z (e_scalbn + 0)%Z.
Hypothesis LINK_1229 : gw_anch (base + 4916 + bv_signed joff_1229)%Z (e_extenddftf2 + 0)%Z.
Hypothesis LINK_1234 : gw_anch (base + 4936 + bv_signed joff_1234)%Z (e_extendsftf2 + 388)%Z.
Hypothesis LINK_1241 : gw_anch (base + 4964 + bv_signed joff_1241)%Z (e_subtf3 + 0)%Z.
Hypothesis LINK_1244 : gw_anch (base + 4976 + bv_signed joff_1244)%Z (e_addtf3 + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.
Hypothesis LAY_got_ssp_RERRNO : gw_le (got_ssp + 8) (RATP + -164).

Local Definition gw_tbl_0 := tt.

Definition getf2_post : ltac:(gw_rebind_ty (@QVbl.Mq1.getf2_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QVbl.Mq1.getf2_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QzQg.Mq0.getf2_post segs) getf2_post (gw_ent (@QVbl.Mq1.getf2_post segs) getf2_post gw_tbl_0)).
Definition scalbn_post : ltac:(gw_rebind_ty (@Q91D.Mq4.scalbn_post segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq4.scalbn_post segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QzQg.Mq0.scalbn_post segs) scalbn_post (gw_ent (@Q91D.Mq4.scalbn_post segs) scalbn_post gw_tbl_1)).
Definition SCALBNL := (e_extendsftf2 + 1132)%Z.
Local Definition gw_tbl_3 := (gw_ent (@QzQg.Mq0.SCALBNL e_extendsftf2) SCALBNL (gw_ent (@QQRC.Mq2.SCALBNL e_extendsftf2) SCALBNL gw_tbl_2)).
Definition COPYSIGNL := (e_extendsftf2 + 348)%Z.
Local Definition gw_tbl_4 := (gw_ent (@QzQg.Mq0.COPYSIGNL e_extendsftf2) COPYSIGNL (gw_ent (@QQRC.Mq2.COPYSIGNL e_extendsftf2) COPYSIGNL gw_tbl_3)).
Definition FABSL := (e_extendsftf2 + 1120)%Z.
Local Definition gw_tbl_5 := (gw_ent (@QzQg.Mq0.FABSL e_extendsftf2) FABSL (gw_ent (@QQRC.Mq2.FABSL e_extendsftf2) FABSL gw_tbl_4)).
Definition leafq_post : ltac:(gw_rebind_ty (@QQRC.Mq2.leafq_post segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QQRC.Mq2.leafq_post segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq0.leafq_post segs) leafq_post (gw_ent (@QQRC.Mq2.leafq_post segs) leafq_post gw_tbl_5)).
Definition scalbnl_post : ltac:(gw_rebind_ty (@QQRC.Mq2.scalbnl_post segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QQRC.Mq2.scalbnl_post segs) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.scalbnl_post segs) scalbnl_post (gw_ent (@QQRC.Mq2.scalbnl_post segs) scalbnl_post gw_tbl_6)).
Definition scalbnl_stmt : ltac:(gw_rebind_ty (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.scalbnl_stmt segs e_extendsftf2) scalbnl_stmt (gw_ent (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) scalbnl_stmt gw_tbl_7)).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@QzQg.Mq0.extenddftf2_post segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QzQg.Mq0.extenddftf2_post segs) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Q8l1.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@QQRC.Mq2.extenddftf2_post segs) extenddftf2_post gw_tbl_8)))).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@QzQg.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@QQRC.Mq2.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_9)))).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Q8l1.Mq0.leaf2_post segs) leaf2_post (gw_ent (@QQRC.Mq2.leaf2_post segs) leaf2_post gw_tbl_10)))).
Definition leaf1_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.leaf1_post segs) leaf1_post (gw_ent (@Qy8Z.Mq0.leaf1_post segs) leaf1_post (gw_ent (@Q8l1.Mq0.leaf1_post segs) leaf1_post gw_tbl_11))).
Definition call2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.call2_post segs) call2_post (gw_ent (@Qy8Z.Mq0.call2_post segs) call2_post (gw_ent (@Q8l1.Mq0.call2_post segs) call2_post (gw_ent (@QQRC.Mq2.call2_post segs) call2_post gw_tbl_12)))).
Definition FMODL := (e_extendsftf2 + 388)%Z.
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.FMODL e_extendsftf2) FMODL (gw_ent (@Q8l1.Mq0.FMODL e_extendsftf2) FMODL gw_tbl_13)).
Definition rfmodl_post : ltac:(gw_rebind_ty (@Q8l1.Mq0.rfmodl_post segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.rfmodl_post segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QzQg.Mq0.rfmodl_post segs) rfmodl_post (gw_ent (@Q8l1.Mq0.rfmodl_post segs) rfmodl_post gw_tbl_14)).
Definition rfmodl_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QzQg.Mq0.rfmodl_stmt segs e_extendsftf2) rfmodl_stmt (gw_ent (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) rfmodl_stmt gw_tbl_15)).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_16))))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_17))))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_18))).
Definition fixunstfsi_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fixunstfsi_post segs) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fixunstfsi_post segs) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QzQg.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Q8l1.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@QQRC.Mq2.fixunstfsi_post segs) fixunstfsi_post gw_tbl_19)))).
Definition floatsitf_post : ltac:(gw_rebind_ty (@QzQg.Mq0.floatsitf_post segs) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QzQg.Mq0.floatsitf_post segs) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@QzQg.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Q8l1.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@QQRC.Mq2.floatsitf_post segs) floatsitf_post gw_tbl_20)))).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@QzQg.Mq0.floatunsitf_post segs) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QzQg.Mq0.floatunsitf_post segs) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@QzQg.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Q8l1.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@QQRC.Mq2.floatunsitf_post segs) floatunsitf_post gw_tbl_21)))).
Definition addtf3_post : ltac:(gw_rebind_ty (@QzQg.Mq0.addtf3_post segs) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QzQg.Mq0.addtf3_post segs) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@QzQg.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Q8l1.Mq0.addtf3_post segs) addtf3_post (gw_ent (@QQRC.Mq2.addtf3_post segs) addtf3_post gw_tbl_22)))).
Definition multf3_post : ltac:(gw_rebind_ty (@QzQg.Mq0.multf3_post segs) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QzQg.Mq0.multf3_post segs) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@QzQg.Mq0.multf3_post segs) multf3_post (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post (gw_ent (@Q8l1.Mq0.multf3_post segs) multf3_post (gw_ent (@QQRC.Mq2.multf3_post segs) multf3_post gw_tbl_23)))).
Definition multf3_stmt : ltac:(gw_rebind_ty (@QzQg.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QzQg.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_24)).
Local Definition gw_tbl_25 := (gw_ent (@QzQg.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Q8l1.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@QQRC.Mq2.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_24)))).
Definition divtf3_post : ltac:(gw_rebind_ty (@QzQg.Mq0.divtf3_post segs) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@QzQg.Mq0.divtf3_post segs) constr:(gw_tbl_25)).
Local Definition gw_tbl_26 := (gw_ent (@QzQg.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Q8l1.Mq0.divtf3_post segs) divtf3_post (gw_ent (@QQRC.Mq2.divtf3_post segs) divtf3_post gw_tbl_25)))).
Definition letf2_post : ltac:(gw_rebind_ty (@QzQg.Mq0.letf2_post segs) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@QzQg.Mq0.letf2_post segs) constr:(gw_tbl_26)).
Local Definition gw_tbl_27 := (gw_ent (@QzQg.Mq0.letf2_post segs) letf2_post (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post (gw_ent (@Q8l1.Mq0.letf2_post segs) letf2_post (gw_ent (@QQRC.Mq2.letf2_post segs) letf2_post gw_tbl_26)))).
Definition frexpl_post : ltac:(gw_rebind_ty (@QzQg.Mq0.frexpl_post segs) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@QzQg.Mq0.frexpl_post segs) constr:(gw_tbl_27)).
Local Definition gw_tbl_28 := (gw_ent (@QzQg.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Q8l1.Mq0.frexpl_post segs) frexpl_post (gw_ent (@QQRC.Mq2.frexpl_post segs) frexpl_post gw_tbl_27)))).
Definition signbitl_post : ltac:(gw_rebind_ty (@QzQg.Mq0.signbitl_post segs) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QzQg.Mq0.signbitl_post segs) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QzQg.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Q8l1.Mq0.signbitl_post segs) signbitl_post (gw_ent (@QQRC.Mq2.signbitl_post segs) signbitl_post gw_tbl_28)))).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fpclassifyl_post segs) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fpclassifyl_post segs) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QzQg.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Q8l1.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@QQRC.Mq2.fpclassifyl_post segs) fpclassifyl_post gw_tbl_29)))).
Definition calla_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.calla_post segs) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.calla_post segs) constr:(gw_tbl_30)).
Local Definition gw_tbl_31 := (gw_ent (@QzQg.Mq0.calla_post segs) calla_post (gw_ent (@Qy8Z.Mq0.calla_post segs) calla_post gw_tbl_30)).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_31)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_31)).
Local Definition gw_tbl_32 := (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_31).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_32)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_32)).
Local Definition gw_tbl_33 := (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_32).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_33)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_33)).
Local Definition gw_tbl_34 := (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_33).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_34)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_34)).
Local Definition gw_tbl_35 := (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_34).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_35)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_35)).
Local Definition gw_tbl_36 := (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_35).
Definition dfinv : ltac:(gw_rebind_ty (@QzQg.Mq0.dfinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_36)) := ltac:(gw_rebind_tm (@QzQg.Mq0.dfinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_36)).
Local Definition gw_tbl_37 := (gw_ent (@QzQg.Mq0.dfinv segs got_ssp RATP ssp_guard) dfinv gw_tbl_36).
Definition S_F2 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_F2 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_F2 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_37)).
Local Definition gw_tbl_38 := (gw_ent (@QzQg.Mq0.S_F2 segs base got_ssp RATP STRING_READ ssp_guard) S_F2 gw_tbl_37).
Definition S_F1 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_F1 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_F1 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_38)).
Local Definition gw_tbl_39 := (gw_ent (@QzQg.Mq0.S_F1 segs base got_ssp RATP STRING_READ ssp_guard) S_F1 gw_tbl_38).
Hypothesis extenddftf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq1.extenddftf2_spec segs e_extenddftf2) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_39))) in exact T).  Arguments extenddftf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis scalbn_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq4.gw_all) (@Q91D.Mq4.scalbn_spec) e_scalbn)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_39))) in exact T).  Arguments scalbn_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis copysignl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq2.gw_all) (@QQRC.Mq2.copysignl_spec) e_extendsftf2)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_39))) in exact T).  Arguments copysignl_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope _%_Z_scope.
Hypothesis rfmodl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8l1.Mq0.gw_all) (@Q8l1.Mq0.rfmodl_spec) e_extendsftf2)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_39))) in exact T).
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis addtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QDXD.Mq0.addtf3_spec segs e_addtf3) 5%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in let T := gw_subst T (@QDXD.Mq0.addtf3_post segs) addtf3_post in exact T).  Arguments addtf3_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis subtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QkTt.Mq1.subtf3_spec segs e_subtf3) 4%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments subtf3_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis multf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QCa8.multf3_spec segs e_multf3) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).
Notation rfj := G.T_rfj.rfj.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Ltac brs K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac]; try (exfalso; lia).
Ltac fixw2 := rewrite ?swrap32_landW, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
Ltac fixw :=
try match goal with |- context [bv_swrap 32 (?x + ?k)] =>
lazymatch isZcst k with true => idtac end;
first [ assert_succeeds (assert (2^63 <= k)%Z by lia);
let k' := eval vm_compute in (k - 2^64)%Z in rewrite (swrap32_shift x k k') by reflexivity
| idtac ] end;
try match goal with |- context [bv_swrap 32 (?x - ?k)] =>
lazymatch isZcst k with true => idtac end;
first [ assert_succeeds (assert (2^63 <= k)%Z by lia);
let k' := eval vm_compute in (2^64 - k)%Z in rewrite (swrap32_shift_sub x k k') by reflexivity
| idtac ] end;
try rewrite swrap32_land64_add by lia; try rewrite swrap32_land64_small by lia; try rewrite swrap32_small by lia.

Definition mul_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.mul_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.mul_callE)).
Definition add_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.add_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.add_callE)).
Definition sub_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.sub_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.sub_callE)).
Definition scalbn_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.scalbn_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.scalbn_callE)).
Definition copysignl_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.copysignl_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.copysignl_callE)).
Definition fmodl_callE : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.fmodl_callE) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.fmodl_callE)).
Definition extenddftf2_callF : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.extenddftf2_callF) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.extenddftf2_callF)).
Definition floatsitf_callsg : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.floatsitf_callsg) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.floatsitf_callsg)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Definition F_floatscan_common__Fok_refl : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_refl) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_refl)).
Definition F_floatscan_common__Fok_set : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_set) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_set)).
Definition F_floatscan_common__Fok_trans10 : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.Fok_trans10) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.Fok_trans10)).
Notation F_floatscan_common__S_F1 := S_F1 (only parsing).
Notation F_floatscan_common__S_F2 := S_F2 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_39)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard e_extenddftf2 e_fpclassifyl e_letf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1192 E_1192 D_1197 E_1197 D_1218 E_1218 D_1219 E_1219 D_1222 E_1222 D_1228 E_1228 D_1229 E_1229 D_1234 E_1234 D_1241 E_1241 D_1244 E_1244 LINK_1192 LINK_1197 LINK_1218 LINK_1219 LINK_1222 LINK_1228 LINK_1229 LINK_1234 LINK_1241 LINK_1244 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO extenddftf2_spec scalbn_spec copysignl_spec rfmodl_spec floatsitf_spec addtf3_spec subtf3_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs_ ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs_ m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs_ m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs_ ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs_ m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs_ m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs_ m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs_ m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).

Local Notation Fok := (@QzQg.Mq0.Fok F).
Local Notation Fok_refl := (@F_floatscan_common__Fok_refl F).
Local Notation Fok_set := (@F_floatscan_common__Fok_set F).
Local Notation Fok_trans10 := (@F_floatscan_common__Fok_trans10 F).
Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation dfinv := (@F_floatscan_common__dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_F2 := (@F_floatscan_common__S_F2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_F1 := (@F_floatscan_common__S_F1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold F_floatscan_common__Wfs, FS_DEPTH, RERRNO in MU; unfold QzQg.Mq0.hi_cells in FRhi;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH in ST;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac mk_finv := gw_expose got_ssp; gw_expose ssp_guard; unfold F_floatscan_common__finv, F_floatscan_common__Wfs, QzQg.Mq0.hi_cells, FS_DEPTH, RERRNO;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac mk_framL := unfold F_floatscan_common__framL, RERRNO; split; hyp.

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.

Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold F_floatscan_common__dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].

Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].

Notation POST := (fs_post m0).

Hypothesis HS_F2 : S_F2.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1192 joff_1197 joff_1218 joff_1219 joff_1222 joff_1228 joff_1229 joff_1234 joff_1241 joff_1244 e_extenddftf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_extendsftf2 CODE BASE4 BASER D_1192 E_1192 D_1197 E_1197 D_1218 E_1218 D_1219 E_1219 D_1222 E_1222 D_1228 E_1228 D_1229 E_1229 D_1234 E_1234 D_1241 E_1241 D_1244 E_1244 LINK_1192 LINK_1197 LINK_1218 LINK_1219 LINK_1222 LINK_1228 LINK_1229 LINK_1234 LINK_1241 LINK_1244 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO extenddftf2_spec scalbn_spec copysignl_spec rfmodl_spec floatsitf_spec addtf3_spec subtf3_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F2"] Lemma L_F1 : S_F1.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1192 joff_1197 joff_1218 joff_1219 joff_1222 joff_1228 joff_1229 joff_1234 joff_1241 joff_1244 e_extenddftf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_extendsftf2 CODE BASE4 BASER D_1192 E_1192 D_1197 E_1197 D_1218 E_1218 D_1219 E_1219 D_1222 E_1222 D_1228 E_1228 D_1229 E_1229 D_1234 E_1234 D_1241 E_1241 D_1244 E_1244 LINK_1192 LINK_1197 LINK_1218 LINK_1219 LINK_1222 LINK_1228 LINK_1229 LINK_1234 LINK_1241 LINK_1244 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO extenddftf2_spec scalbn_spec copysignl_spec rfmodl_spec floatsitf_spec addtf3_spec subtf3_spec multf3_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until e2. intros _ DI RJ Hk FOK FRM' Hsg He2 XR X31H Ra Rz Hin HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range zero0) as Rz0l. pose proof (hi64_range zero0) as Rz0h.
assert (Rsg : (-1 <= sign <= 1)%Z) by lia.
unfold fin_K1 in HK. change LDBL_MANT_DIG_ with 113%Z in HK.
replace (113 + e2 - -1074)%Z with (e2 + 1187)%Z in HK by lia. change (2 * 113)%Z with 226%Z in HK.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF). pose proof (hi64_range SF).
zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := Y) (Y := SF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y1 := f128_mul Y SF) in *. pose proof (lo64_range Y1). pose proof (hi64_range Y1).

assert (G74C : forall bits' m' (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x23' x24' x28' x29' x30' x31' : word) Ft' fct',
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft' -> frm0 fct' ->
(0 <= bits' <= 53)%Z ->
(let d := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (226 - bits' - 1) in
let t := f128_of_d (bv_unsigned d) in
let bias := m_copysignl t Y1 in
let d0 := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (113 - bits') in
let t0 := f128_of_d (bv_unsigned d0) in
match match m_fmodl Y1 t0 with
| Some frac => Some (f128_add (f128_sub Y1 frac) bias, frac, bias)
| None => None
end with
| Some (y, frac, bias) => fin_K2 sign 1024 a z x 4 bits' y frac bias e2
| None => None
end = Some yR) ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (a + 4)) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 z) (Z_to_bv 64 a) (Z_to_bv 64 (hi64 Y1)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y1)) x23' x24'
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') (Z_to_bv 64 53) x28' x29' x30' x31')
Ft' (Z_to_bv 64 (base + 0x12e8)) fct' None m' (seg_rom segs))).
{ intros until fct'. intros DI2 FOK2 FRM2 Hb HK2. clear HK. dest_dfinv DI2. cbv zeta in HK2.
zs. zs. zs. (brf K3; [ exfalso; lia | ]).
zs. zs. zs. zs. fixw2. zs. simpF.
zs. callx (eapply scalbn_callE; [eassumption | eassumption | lia]). match goal with H : frm0 _ |- evt _ _ (MS _ _ _ ?f _ _ _) => idtac end; lazymatch goal with |- evt _ _ (MS _ _ _ ?f _ _ _) => match goal with H : frm0 f |- _ => rename H into FRM3 end end. simpF.
set (D1 := scalbn_model (fcvt_d_w RNE (Z_to_bv 64 1)) (225 - bits')) in *.
change (m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (226 - bits' - 1)) with (scalbn_model (fcvt_d_w RNE (Z_to_bv 64 1)) (226 - bits' - 1)) in HK2.
replace (226 - bits' - 1)%Z with (225 - bits')%Z in HK2 by lia. fold D1 in HK2.
zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D1); [eassumption | simpF; reflexivity]).
set (TBv := f128_of_d (bv_unsigned D1)) in *. pose proof (lo64_range TBv). pose proof (hi64_range TBv).
zs. zs. zs. callx (eapply copysignl_callE with (X := TBv) (Y := Y1); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
set (BI := m_copysignl TBv Y1) in *. pose proof (lo64_range BI). pose proof (hi64_range BI).
zs. zs. zs. zs. fixw2. zs. simpF.
zs. callx (eapply scalbn_callE; [eassumption | eassumption | lia]). lazymatch goal with |- evt _ _ (MS _ _ _ ?f _ _ _) => match goal with H : frm0 f |- _ => rename H into FRM4 end end. simpF.
set (D2 := scalbn_model (fcvt_d_w RNE (Z_to_bv 64 1)) (113 - bits')) in *.
change (m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (113 - bits')) with D2 in HK2.
zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D2); [eassumption | simpF; reflexivity]).
set (TFv := f128_of_d (bv_unsigned D2)) in *. pose proof (lo64_range TFv). pose proof (hi64_range TFv).
destruct (m_fmodl Y1 TFv) as [frac|] eqn:HFM; [|discriminate HK2]. cbv beta iota in HK2.
zs. zs. zs. zs. zs.
callx (eapply fmodl_callE with (X := Y1) (Y := TFv) (r := frac); [eassumption | eassumption | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity | exact HFM]).
match goal with H : forall k : bv 5, _ -> reg_get _ k = reg_get _ k |- _ => rename H into FOK5 end.
pose proof (lo64_range frac). pose proof (hi64_range frac).
zs. zs. zs. zs. zs. zs. zs.
call_split 48%Z (eapply sub_callE with (X := Y1) (Y := frac); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y2 := f128_sub Y1 frac) in *. pose proof (lo64_range Y2). pose proof (hi64_range Y2).
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := Y2) (Y := BI); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y3 := f128_add Y2 BI) in *. pose proof (lo64_range Y3). pose proof (hi64_range Y3).
zs. zs. zs.
stmt HS_F2. eapply NX; try eassumption; try lia; try mk_dfinv.
eapply Fok_trans10; [|exact FOK5]. fok. }
zs. zs. zs. zs. fixw.
match goal with |- context [Z_to_bv 64 (e2 + 113 + 1074)%Z] => replace (Z_to_bv 64 (e2 + 113 + 1074)%Z) with (Z_to_bv 64 (e2 + 1187)%Z) by (f_equal; lia) end.
zs. zs. zs. brs K1.
-
replace (e2 + 1187 <? 53)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
zs. zs. zs. rewrite clamp0_idiom by lia.
set (bits' := (if e2 + 1187 <? 0 then 0 else e2 + 1187)%Z) in *.
assert (Hb : (0 <= bits' < 53)%Z) by (subst bits'; destruct (Z.ltb_spec (e2 + 1187) 0); lia).
replace (bits' <? 113)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
eapply G74C; try eassumption; try lia; try mk_dfinv; try (cbv zeta; exact HK).
- replace (e2 + 1187 <? 53)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). change (53 <? 113)%Z with true in HK. cbv beta iota in HK.
zs. zs.
eapply G74C; try eassumption; try lia; try mk_dfinv; try (cbv zeta; exact HK).
Qed.

End Floatscan.

End G.
