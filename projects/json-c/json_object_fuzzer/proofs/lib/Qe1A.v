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
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_7).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_8).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_9).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_10).
Definition dfinv : ltac:(gw_rebind_ty (@QzQg.Mq0.dfinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QzQg.Mq0.dfinv segs got_ssp RATP ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.dfinv segs got_ssp RATP ssp_guard) dfinv gw_tbl_11).
Definition dfinvG : ltac:(gw_rebind_ty (@QzQg.Mq0.dfinvG segs got_ssp RATP ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QzQg.Mq0.dfinvG segs got_ssp RATP ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.dfinvG segs got_ssp RATP ssp_guard) dfinvG gw_tbl_12).
Definition S_C38 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_C38 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_C38 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.S_C38 segs base got_ssp RATP STRING_READ ssp_guard) S_C38 gw_tbl_13).
Definition S_C2C : ltac:(gw_rebind_ty (@QzQg.Mq0.S_C2C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_C2C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QzQg.Mq0.S_C2C segs base got_ssp RATP STRING_READ ssp_guard) S_C2C gw_tbl_14).
Definition S_E : ltac:(gw_rebind_ty (@QzQg.Mq0.S_E segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_E segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QzQg.Mq0.S_E segs base got_ssp RATP STRING_READ ssp_guard) S_E gw_tbl_15).
Definition SDn : ltac:(gw_rebind_ty (@QzQg.Mq0.SDn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QzQg.Mq0.SDn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QzQg.Mq0.SDn segs base got_ssp RATP STRING_READ ssp_guard) SDn gw_tbl_16).
Definition S_D : ltac:(gw_rebind_ty (@QzQg.Mq0.S_D segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_D segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QzQg.Mq0.S_D segs base got_ssp RATP STRING_READ ssp_guard) S_D gw_tbl_17).

Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_18))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_18))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast_lt) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_18))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast_lt _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_18))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_getc : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_getc) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_18))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_getc _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_nop : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_nop) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_18))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).
Hypothesis shgetc_callJ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.shgetc_callJ) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_18))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments shgetc_callJ _%_bv_scope _%_Z_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope _%_Z_scope _%_Z_scope _ _%_Z_scope _%_Z_scope _ _%_list_scope _%_list_scope _%_list_scope _%_bv_scope.
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

Ltac brs K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac]; try (exfalso; lia).
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

Definition rw_cells_C8_CB8 : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.rw_cells_C8_CB8) constr:(gw_tbl_18)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.rw_cells_C8_CB8)).
Definition dfinvG_dfinv : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.dfinvG_dfinv) constr:(gw_tbl_18)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.dfinvG_dfinv)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Notation F_floatscan_common__SDn := SDn (only parsing).
Notation F_floatscan_common__S_C2C := S_C2C (only parsing).
Notation F_floatscan_common__S_C38 := S_C38 (only parsing).
Notation F_floatscan_common__S_D := S_D (only parsing).
Notation F_floatscan_common__S_E := S_E (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__dfinvG_dfinv := dfinvG_dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_18)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc rf_unget_nop shgetc_callJ"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 got_ssp RATP STRING_READ ssp_guard e_197bc CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc rf_unget_nop shgetc_callJ.

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
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QzQg.Mq0.Fok F).

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation dfinv := (@F_floatscan_common__dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation dfinvG_dfinv := (@F_floatscan_common__dfinvG_dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_C38 := (@F_floatscan_common__S_C38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_C2C := (@F_floatscan_common__S_C2C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_E := (@F_floatscan_common__S_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation SDn := (@F_floatscan_common__SDn ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_D := (@F_floatscan_common__S_D ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Ltac lo96b H := apply (proj1 (rw_cells_C8_CB8 _ _ [_; _; _; _; _; _; _; _; _; _; _; _] _ [])) in H; cbn [app] in H.
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.
Ltac store_done' := stash_mods; stash_disj; unfold hide in SPT; store_done; unstash.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
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

Hypothesis HS_E : S_E.
Hypothesis HS_C2C : S_C2C.
Hypothesis HS_C38 : S_C38.

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.
Ltac eplia := gw_expose got_ssp; gw_expose ssp_guard; unfold zlength in *; unfold hide2 in *; lia.
Ltac splits := lazymatch goal with |- _ /\ _ => split; [|splits] | |- _ => idtac end.
Ltac mk_facts := unfold digI, dig_facts; splits; try assumption; try lia.
#[using="Type"] Lemma stdio_getc : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_E HS_C2C HS_C38. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_E | gw_hide HS_E | idtac]; first [clear HS_C2C | gw_hide HS_C2C | idtac]; first [clear HS_C38 | gw_hide HS_C38 | idtac]. clear. intros f. exact (proj1 (sh_getc_stdio f)). Qed.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_E HS_C2C HS_C38. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_E | gw_hide HS_E | idtac]; first [clear HS_C2C | gw_hide HS_C2C | idtac]; first [clear HS_C38 | gw_hide HS_C38 | idtac]. clear. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
#[using="Type"] Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_E HS_C2C HS_C38. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_E | gw_hide HS_E | idtac]; first [clear HS_C2C | gw_hide HS_C2C | idtac]; first [clear HS_C38 | gw_hide HS_C38 | idtac]. clear. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
#[using="Type"] Lemma seqz46 : forall c, (-2^62 < c < 2^62)%Z -> Z.b2z (Z.land (c + -46) 18446744073709551615 <? 1)%Z = Z.b2z (c =? 46)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_E HS_C2C HS_C38. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_E | gw_hide HS_E | idtac]; first [clear HS_C2C | gw_hide HS_C2C | idtac]; first [clear HS_C38 | gw_hide HS_C38 | idtac].
clear. intros c Hc. rewrite land_W64. destruct (Z.eqb_spec c 46) as [->|Hne]; [reflexivity|].
destruct (Z.ltb_spec ((c + -46) mod 2 ^ 64) 1) as [Hl|Hg]; [|reflexivity]. exfalso. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma b2z_land1 : forall b, Z.land (Z.b2z b) 1 = Z.b2z b.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_E HS_C2C HS_C38. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_E | gw_hide HS_E | idtac]; first [clear HS_C2C | gw_hide HS_C2C | idtac]; first [clear HS_C38 | gw_hide HS_C38 | idtac]. clear. destruct b; reflexivity. Qed.
#[using="Type"] Lemma Eng : forall g, (0 <= g <= 1)%Z -> Z.b2z (g <? 1)%Z = Z.b2z (g =? 0)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_E HS_C2C HS_C38. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_E | gw_hide HS_E | idtac]; first [clear HS_C2C | gw_hide HS_C2C | idtac]; first [clear HS_C38 | gw_hide HS_C38 | idtac]. clear. intros g Hg. destruct (Z.ltb_spec g 1); destruct (Z.eqb_spec g 0); cbn; lia. Qed.

#[using="Type"] Lemma sh_getc_rpos : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_E HS_C2C HS_C38. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide BYT; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_E | gw_hide HS_E | idtac]; first [clear HS_C2C | gw_hide HS_C2C | idtac]; first [clear HS_C38 | gw_hide HS_C38 | idtac].
clear - BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_E"] Lemma L_LATCH : forall n, SDn n ->
forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
j0 ev ws sign kmin c (x : list Z) (f : shfile) (j k lrp dc lnz gotdig gotrad : Z) (s' : st_dig),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> c <> 0%Z -> c <> (-1)%Z ->
xrel ws x (digz k j) -> X31 x -> (0 <= j <= 8)%Z -> (0 <= k)%Z -> (9 * k + j <= dc)%Z -> (0 <= dc <= sh_rpos f)%Z ->
(0 <= lnz <= dc)%Z -> (znth x 0 <> 0%Z -> 1 <= lnz)%Z -> (j <> 0%Z -> znth x k < 10 ^ j)%Z -> (k = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) ->
(- 2^31 <= lrp < 2^31)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z -> (k <= 2045)%Z -> (k = 2045%Z -> j = 0%Z) ->
df_dig_loop n (mkDL (snd (sh_getc f)) (fst (sh_getc f)) j k lrp dc lnz gotdig gotrad x) = Some s' ->
dfK_exp fuelc 53 (-1074) sign pok s' = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 dc) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x78c)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_E segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok Hnum SE_T FRM HS_C2C HS_C38. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear Hnum | gw_hide Hnum | idtac]; try gw_hide SE_T; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_C2C | gw_hide HS_C2C | idtac]; first [clear HS_C38 | gw_hide HS_C38 | idtac].
intros n IH. intros until s'. intros DI RJ Hk FOK FRM' Hsg Hst Hc0 Hcn1 XR X31H Rj Rk Hkj9 Rdc Rlnz Hlnz Hxk Hkj Rlrp Rg Rgr Rk45 Hkj45 HL HK.
pose proof DI as DI0. dest_dfinv DI. bury_disj.
site_facts FC RJ kmin c f.
assert (Rrpp : (sh_rpos f <= p)%Z).
{ clear - RJ Hc0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base. destruct RJ as (R0 & R1 & R2 & R3 & NS0 & SS0). destruct (sh_stdio f) eqn:Es; [destruct (SS0 eq_refl) as (Qa & Qb & Qc); exact Qb | exact (proj2 (proj2 (NS0 eq_refl)) Hc0)]. }
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (sh_getc_rpos f Hbuf) as [Rrp1 Rrp2].

assert (NEXT : forall m2 (x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign (snd (sh_getc f)) ->
(evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) + -48)) (Z_to_bv 64 (Z.b2z (fst (sh_getc f) =? 46)%Z)) x13' x14' x15' x16' x17'
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28' x29' x30' x31')
Ft (Z_to_bv 64 (if (isdigitc (fst (sh_getc f)) || (fst (sh_getc f) =? 46))%Z then (base + 0x708) else (base + 0x650))) fct None m2 (seg_rom segs)))).
{ intros m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2.
destruct (isdigitc (fst (sh_getc f)) || (fst (sh_getc f) =? 46))%Z eqn:Hcond.
- eapply (IH m2); try eassumption; try lia. mk_facts.
- destruct n as [|n']; [discriminate HL|]. rewrite df_dig_loop_step in HL. unfold df_dig_cond in HL. cbn [dl_c] in HL. rewrite Hcond in HL.
injection HL as <-.
stmt HS_E. eapply NX with (gotdig := gotdig) (gotrad := gotrad); try eassumption; try lia.
all: try (rewrite <- dfinvG_dfinv in DI2; exact DI2). all: try (intros _; reflexivity). all: mk_facts. }

assert (N68 : forall m2 (x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign (snd (sh_getc f)) ->
fst (sh_getc f) <> 46%Z ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) + -48)) (Z_to_bv 64 (Z.b2z (fst (sh_getc f) =? 46)%Z)) x13' x14' x15' x16' x17'
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28' x29' x30' x31')
Ft (Z_to_bv 64 (base + 0x704)) fct None m2 (seg_rom segs))).
{ intros m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2 Hne.
clear HL. pose proof DI2 as DI3. dest_dfinv DI3.
set (c' := fst (sh_getc f)) in *.
zs. brf K; rewrite ?land_W64 in K.
-
pose proof (NEXT m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2) as NX.
replace (isdigitc c' || (c' =? 46))%Z with false in NX; [exact NX|].
replace (c' =? 46)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne).
replace (isdigitc c') with false; [reflexivity|]. symmetry. apply Bool.not_true_iff_false. intros D. apply (proj1 (isdigitc_iff c' ltac:(lia))) in D.
clear - K D Rc' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base. Z.div_mod_to_equations. lia.
- pose proof (NEXT m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2) as NX.
replace (isdigitc c' || (c' =? 46))%Z with true in NX; [exact NX|].
replace (isdigitc c') with true; [reflexivity|]. symmetry. apply (proj2 (isdigitc_iff c' ltac:(lia))).
clear - K Rc' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base. Z.div_mod_to_equations. lia. }
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & EJ & Hn & Hrpe & Hc00).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. call_split 160%Z (eapply (gw_unhyp shgetc_callJ) with (pre := pre) (post := post);
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| eplia | eplia | exact SEP | replace (q + -8416 - 160)%Z with (q + -8416 - 160)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end. rewrite <- EJ in FC2.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; gw_expose got_ssp; gw_expose ssp_guard end.
set (c' := fst (sh_getc f)) in *.
zs. fixw3. fixw. zs. zs. rewrite (seqz46 c') by lia. zs. brf K2; rewrite ?land_W64 in K2.
+
assert (E46 : c' = 46%Z) by (clear - K2 Rc' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base; Z.div_mod_to_equations; lia).
pose proof NEXT as NX.
replace (c' =? 46)%Z with true in NX |- * by (symmetry; apply Z.eqb_eq; exact E46). rewrite Bool.orb_true_r in NX.
eapply NX. mk_dfinv.
+ assert (N46 : c' <> 46%Z) by (clear - K2 Rc' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base; Z.div_mod_to_equations; lia).
eapply N68; [mk_dfinv | exact N46].
-
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0.
pose proof (u8ro_read segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
set (c' := znth txt (sh_rpos f)) in *.
zs. fixw3. fixw. zs. zs. rewrite (seqz46 c') by lia. zs. brf K2; rewrite ?land_W64 in K2.
+
assert (N46 : c' <> 46%Z) by (clear - K2 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base; Z.div_mod_to_equations; lia).
eapply N68; [| exact N46]. unfold F_floatscan_common__dfinv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
+ assert (E46 : c' = 46%Z) by (clear - K2 Rch w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ segs base; Z.div_mod_to_equations; lia).
zs.
pose proof NEXT as NX.
replace (c' =? 46)%Z with true in NX |- * by (symmetry; apply Z.eqb_eq; exact E46). rewrite Bool.orb_true_r in NX.
eapply NX. unfold F_floatscan_common__dfinv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
Qed.

#[using="Type"] Lemma seqz_land : forall e, (-2^63 < e < 2^63)%Z -> (Z.land e 18446744073709551615 <? 1)%Z = (e =? 0)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_E HS_C2C HS_C38. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_E | gw_hide HS_E | idtac]; first [clear HS_C2C | gw_hide HS_C2C | idtac]; first [clear HS_C38 | gw_hide HS_C38 | idtac].
clear. intros e He. rewrite land_W64. destruct (Z.eqb_spec e 0) as [->|Hne]; [reflexivity|].
destruct (Z.ltb_spec (e mod 2 ^ 64) 1) as [Hl|Hg]; [|reflexivity]. exfalso. Z.div_mod_to_equations. lia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc rf_unget_nop shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_E HS_C2C HS_C38"] Lemma L_D : S_D.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc rf_unget_nop shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_E HS_C2C HS_C38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok Hnum SE_T FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear Hnum | gw_hide Hnum | idtac]; try gw_hide SE_T; first [clear FRM | gw_hide FRM | idtac].
unfold F_floatscan_common__S_D. induction n as [|n IH].
{ intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Hst DG Hcond HL HK. discriminate HL. }
pose proof (L_LATCH n IH) as LATCH.
intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Hst DG Hcond HL HK.
pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct DG as (XR & X31H & Rj & Rk & Hkj9 & Rdc & Hdc1 & Rlnz & Hlnz & Hxk & Hkj & Rlrp & Rg & Rgr & Rk45 & Hkj45).
destruct XR as (LW' & LX & REL).
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
assert (Rrp' : (sh_rpos f <= p)%Z).
{ destruct RJ as (R0 & R1 & R2 & R3 & NS0 & SS0). destruct (sh_stdio f) eqn:Es.
- destruct (SS0 eq_refl) as (Qa & Qb & Qc). exact Qb.
- apply (proj2 (proj2 (NS0 eq_refl))). intros E0. rewrite E0 in Hcond. cbv in Hcond. discriminate Hcond. }
rewrite df_dig_loop_step in HL. unfold df_dig_cond in HL. cbn [dl_c] in HL. rewrite Hcond in HL.
unfold df_dig_body in HL. cbn [dl_f dl_c dl_j dl_k dl_lrp dl_dc dl_lnz dl_gotdig dl_gotrad dl_x] in HL.
zs. rewrite b2z_land1. zs. brf K1.
-
replace (c =? 46)%Z with false in Hcond by (symmetry; apply Z.eqb_neq; exact K1). rewrite Bool.orb_false_r in Hcond.
replace (c =? 46)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact K1).
assert (Hd : (48 <= c <= 57)%Z) by (apply (proj1 (isdigitc_iff c ltac:(lia))); exact Hcond).
zs. zs. brs K2.
{
assert (Ek : k = 2045%Z) by lia. pose proof (Hkj45 Ek) as Ej.
replace (k <? KMAX - 3)%Z with false in HL by (symmetry; apply Z.ltb_ge; unfold KMAX; lia).
change ((KMAX - 4) * 9)%Z with 18396%Z in HL. change (KMAX - 4)%Z with 2044%Z in HL.
rewrite (surjective_pairing (sh_getc f)) in HL.
zs. brf K3.
-
replace (c =? 48)%Z with true in HL by (symmetry; apply Z.eqb_eq; exact K3). cbv beta iota in HL.
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev ws sign kmin c x f j k lrp (dc + 1)%Z lnz gotdig gotrad s').
all: try assumption; try lia.
exact (conj LW' (conj LX REL)).
-
replace (c =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact K3). cbv beta iota in HL.
pose proof (X31H 2044%Z) as Rt. pose proof (REL 2044%Z ltac:(lia) ltac:(unfold digz; left; lia)) as Et.
pose proof (u32arr_read segs _ _ _ 2044%Z _ _ XW (nth_error_wnth ws 2044%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws 2044%Z (znth x 2044) (eq_sym Et) Rt). set (t := znth x 2044) in *. clear RD.
zs.
pose proof (Z_lor_lt_pow2' t 1 31 Rt ltac:(lia)) as Rv.
set (v := Z.lor t 1) in *.
pose proof (u32arr_store_ok segs _ _ _ 2044%Z _ XW ltac:(lia) eq_refl) as SOK.
replace (XA + 4 * 2044)%Z with (q + -136)%Z in SOK by lia.
zs.
pose proof (u32arr_write segs _ _ _ 2044%Z (Z_to_bv 64 v) XW ltac:(lia)) as XW'. clear XW.
replace (XA + 4 * 2044)%Z with (q + -136)%Z in XW' by lia.
store_done'. rename XW' into XW.
zs. zs. lo96b LOW.
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat 2044) (Z_to_bv 64 v)) sign kmin c (zupd x 2044 v) f j k lrp (dc + 1)%Z 18396%Z gotdig gotrad s').
all: try assumption; try lia.
{ mk_dfinv. }
{ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hq Hr. destruct (Z.eq_dec i0 2044) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|]. exact Hr. }
{ intros i0. destruct (Z.eq_dec i0 2044) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. } }
assert (Hk7 : (k <= 2044)%Z) by lia.
replace (k <? KMAX - 3)%Z with true in HL by (symmetry; apply Z.ltb_lt; unfold KMAX; lia).
rewrite (s32_id (dc + 1)) in HL by lia.

assert (G94 : forall m2 (x12' : word) lnz2, lnz2 = (if (c =? 48)%Z then lnz else (dc + 1)%Z) ->
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz2)) ev ws sign f ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 (dc + 1)) (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12' x13 x14 x15 x16 x17
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x730)) fct None m2 (seg_rom segs))).
{ intros m2 x12' lnz2 Elnz2 DI2.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW FC FI FL.
pose proof DI2 as DI3. dest_dfinv DI3.
zs. zs. zs. fix_idx. zs. brf K4.
+
assert (Ej : j = 0%Z) by exact K4. rewrite Ej in HL |- *. unfold nz in HL. rewrite Z.eqb_refl in HL. cbn [negb] in HL.
replace (0 + 1 =? 9)%Z with false in HL by reflexivity. cbv beta iota in HL. replace (0 + 1)%Z with 1%Z in HL by reflexivity.
pose proof (u32arr_store_ok segs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ k (Z_to_bv 64 (c + -48)) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs. fixw3. zs. zs. change (Z.b2z (18446744073709551608 <? 1)) with 0%Z. zs. fixw3. try rewrite (Z.add_0_r k). zs. zs. zs. zs.
try rewrite !swrap32_small by lia. try rewrite (Z.add_0_r k).
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
replace (if negb (c =? 48) then (dc + 1)%Z else lnz) with lnz2 in HL by (rewrite Elnz2; destruct (c =? 48)%Z; reflexivity).
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat k) (Z_to_bv 64 (c + -48))) sign kmin c (zupd x k (c - 48)) f 1%Z k lrp (dc + 1)%Z lnz2 1%Z gotrad s').
all: try assumption; try lia.
{ mk_dfinv. }
{ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hq Hr. destruct (Z.eq_dec i0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|]. unfold digz in Hr |- *. lia. }
{ intros i0. destruct (Z.eq_dec i0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. }
{ rewrite Elnz2. destruct (c =? 48)%Z; lia. }
{ intros Hx0. rewrite Elnz2. destruct (Z.eqb_spec c 48) as [Ec|Hc48]; [|lia].
destruct (Z.eq_dec k 0) as [Ek|Hk0].
- exfalso. apply Hx0. rewrite Ek. rewrite znth_zupd_eq by (unfold zlength; lia). lia.
- rewrite znth_zupd_neq in Hx0 by lia. exact (Hlnz Hx0). }
{ intros _. rewrite znth_zupd_eq by (unfold zlength; lia). change (10 ^ 1)%Z with 10%Z. lia. }
+
assert (Hj : j <> 0%Z) by exact K4.
unfold nz in HL. replace (j =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact Hj). cbn [negb] in HL.
pose proof (X31H k) as Rt. pose proof (REL k ltac:(lia) ltac:(unfold digz; right; right; split; [reflexivity | exact Hj])) as Et.
specialize (Hxk Hj).
pose proof (Z.pow_le_mono_r 10 j 8 ltac:(lia) ltac:(lia)) as P10. change (10 ^ 8)%Z with 100000000%Z in P10.
pose proof (u32arr_read segs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws k (znth x k) (eq_sym Et) Rt). set (t := znth x k) in *. clear RD.
zs. zs. zs.
rewrite (u32_id (t * 10 + c - 48)) in HL by lia.
replace (t * 10 + c - 48)%Z with (c + t * 10 + -48)%Z in HL by lia.
set (v := (c + t * 10 + -48)%Z) in *.
assert (P10j : (10 ^ j * 10 = 10 ^ (j + 1))%Z) by (rewrite Z.pow_add_r, Z.pow_1_r by lia; reflexivity).
assert (Rv : (0 <= v < 10 ^ (j + 1))%Z) by (subst v; nia).
assert (Rv2 : (10 ^ (j + 1) <= 1000000000)%Z) by (change 1000000000%Z with (10 ^ 9)%Z; apply Z.pow_le_mono_r; lia).
pose proof (u32arr_store_ok segs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ k (Z_to_bv 64 v) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (XR' : forall Q : Z -> Prop, (forall i, (0 <= i < 2048)%Z -> Q i -> (i <= k)%Z) -> xrel (upd ws (Z.to_nat k) (Z_to_bv 64 v)) (zupd x k v) Q).
{ intros Q HQ. split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hq Hr. specialize (HQ i0 Hq Hr). destruct (Z.eq_dec i0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|]. unfold digz. lia. }
assert (X31' : X31 (zupd x k v)).
{ intros i0. destruct (Z.eq_dec i0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. }
assert (Hx0' : znth (zupd x k v) 0 <> 0%Z -> (1 <= lnz2)%Z).
{ intros Hx0. rewrite Elnz2. destruct (Z.eqb_spec c 48) as [Ec|Hc48]; [|lia].
destruct (Z.eq_dec k 0) as [Ek|Hk0].
- apply Hlnz. intros E0. apply Hx0. rewrite Ek. rewrite znth_zupd_eq by (unfold zlength; lia). subst v t. rewrite Ek, E0, Ec. reflexivity.
- rewrite znth_zupd_neq in Hx0 by lia. exact (Hlnz Hx0). }
zs. fixw3. zs. zs.
rewrite (seqz_land (j + -8)%Z) by lia.
destruct (Z.eq_dec j 8) as [Ej8|Hj8].
*
replace (j + -8 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia).
replace (j + 1 =? 9)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia). cbv beta iota in HL.
change (Z.b2z true) with 1%Z.
zs. fixw3. zs. zs. zs. zs.
rewrite (Z.land_0_l (j + 1)).
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
replace (if negb (c =? 48) then (dc + 1)%Z else lnz) with lnz2 in HL by (rewrite Elnz2; destruct (c =? 48)%Z; reflexivity).
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat k) (Z_to_bv 64 v)) sign kmin c (zupd x k v) f 0%Z (k + 1)%Z lrp (dc + 1)%Z lnz2 1%Z gotrad s').
all: try assumption; try lia.
{ mk_dfinv. }
{ apply XR'. unfold digz. intros; lia. }
{ rewrite Elnz2; destruct (c =? 48)%Z; lia. }
* replace (j + -8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
replace (j + 1 =? 9)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). cbv beta iota in HL.
change (Z.b2z false) with 0%Z.
zs. fixw3. zs. zs. zs. zs.
replace (Z.land 18446744073709551615 (j + 1)) with (j + 1)%Z by (rewrite Z.land_comm, land_W64; symmetry; apply Z.mod_small; lia).
try rewrite (Z.add_0_r k).
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
replace (if negb (c =? 48) then (dc + 1)%Z else lnz) with lnz2 in HL by (rewrite Elnz2; destruct (c =? 48)%Z; reflexivity).
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat k) (Z_to_bv 64 v)) sign kmin c (zupd x k v) f (j + 1)%Z k lrp (dc + 1)%Z lnz2 1%Z gotrad s').
all: try assumption; try lia.
{ mk_dfinv. }
{ apply XR'. unfold digz. intros; lia. }
{ rewrite Elnz2; destruct (c =? 48)%Z; lia. }
{ intros _. rewrite znth_zupd_eq by (unfold zlength; lia). exact (proj2 Rv). } }

zs. brf K3.
+ eapply (G94 m _ lnz); [rewrite K3, Z.eqb_refl; reflexivity | exact DI0].
+ zs. lo96b LOW.
eapply (G94 _ _ (dc + 1)%Z); [replace (c =? 48)%Z with false by (symmetry; apply Z.eqb_neq; exact K3); reflexivity | mk_dfinv].
-
rewrite K1 in HL. change (46 =? 46)%Z with true in HL. unfold nz in HL. cbv beta iota in HL.
zs. brf K2.
+
replace (gotrad =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact K2). cbn [negb] in HL. injection HL as <-.
pose proof FC as FC0. ufc2 FC.
zs. zs. zs.
rewrite (Eng gotdig Rg).
unfold dfK_exp in HK.
change (0 <=? 46)%Z with true in HK. replace (nz gotrad) with true in HK by (unfold nz; symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact K2).
cbn [negb Z.lor Pos.lor Z.eqb Pos.eqb andb] in HK. rewrite Bool.andb_false_r in HK. cbv beta iota in HK.
assert (DF : dig_facts ws x j k dc lnz) by (unfold dig_facts; splits; try assumption; try lia; exact (conj LW' (conj LX REL))).
destruct (sh_shlim_neg f) eqn:SN; unfold M64.
* rewrite (rf_unget_nop f SN) in HK.
zs. (brf K3; [ exfalso; lia | ]). zs.
stmt HS_C38. eapply NX with (gotdig := gotdig); try eassumption; try lia; try reflexivity.
* zs. (brf K3; [ | exfalso; lia ]).
stmt HS_C2C. eapply NX with (gotdig := gotdig); try eassumption; try lia; try reflexivity.
+
replace (gotrad =? 0)%Z with true in HL by (symmetry; apply Z.eqb_eq; exact K2). cbn [negb] in HL.
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
zs. zs. zs.
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev ws sign kmin c x f j k dc dc lnz gotdig 1%Z s').
all: try assumption; try lia.
exact (conj LW' (conj LX REL)).
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
Variables (joff_502 joff_509 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_errno_loc e_197bc e_multf3 e_floatsitf e_divtf3 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_502 : decode_any (Z_to_bv 32 w_502) = Some (Jal 1 joff_502, 4%Z).
Hypothesis E_502 : is_ecall (Z_to_bv 32 w_502) = false.
Hypothesis D_509 : decode_any (Z_to_bv 32 w_509) = Some (Jal 1 joff_509, 4%Z).
Hypothesis E_509 : is_ecall (Z_to_bv 32 w_509) = false.
Hypothesis LINK_502 : gw_anch (base + 2008 + bv_signed joff_502)%Z (e_errno_loc + 0)%Z.
Hypothesis LINK_509 : gw_anch (base + 2036 + bv_signed joff_509)%Z (e_floatsitf + 0)%Z.
Hypothesis CODE_e_errno_loc : code_at segs e_errno_loc errno_loc_code.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.
Hypothesis LAY_got_ssp_RERRNO : gw_le (got_ssp + 8) (RATP + -164).

Local Definition gw_tbl_0 := tt.

Definition SHLIM := (base + -544)%Z.
Local Definition gw_tbl_1 := (gw_ent (@QQRC.Mq3.SHLIM (base + -544)%Z) SHLIM gw_tbl_0).
Definition shlim_post : ltac:(gw_rebind_ty (@QQRC.Mq3.shlim_post segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QQRC.Mq3.shlim_post segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QQRC.Mq3.shlim_post segs) shlim_post gw_tbl_1).
Definition shlim_stmt := ltac:(let t := constr:(ltac:(gw_rebind (@QQRC.Mq3.shlim_stmt segs (base + -544)%Z) constr:(gw_tbl_2))) in let t := gw_fold_pcs t base (-544)%Z [0; 56; 256; 396]%Z in exact t).
Local Definition gw_tbl_3 := (gw_ent (@QQRC.Mq3.shlim_stmt segs (base + -544)%Z) shlim_stmt gw_tbl_2).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QzQg.Mq0.ssJ STRING_READ) ssJ (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_3))))).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@Q5m9.Mq1.RFI STRING_READ) RFI (gw_ent (@QZxv.Mql.RFI STRING_READ) RFI (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_4))).
Definition SCANEXP := (base + 7584)%Z.
Local Definition gw_tbl_6 := (gw_ent (@Q5m9.Mq1.SCANEXP (base + 7584)%Z) SCANEXP gw_tbl_5).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_6))).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_7))))).
Definition scanexp_rpost : ltac:(gw_rebind_ty (@Q5m9.Mq1.scanexp_rpost segs STRING_READ got_ssp ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q5m9.Mq1.scanexp_rpost segs STRING_READ got_ssp ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@Q5m9.Mq1.scanexp_rpost segs STRING_READ got_ssp ssp_guard) scanexp_rpost gw_tbl_8).
Definition scanexp_rstmt := ltac:(let t := constr:(ltac:(gw_rebind (@Q5m9.Mq1.scanexp_rstmt segs (base + 7584)%Z STRING_READ got_ssp ssp_guard) constr:(gw_tbl_9))) in let t := gw_fold_pcs t base (7584)%Z [0; 104; 112; 192; 224; 232; 292; 372; 380; 400; 476; 484; 516; 548; 576]%Z in exact t).
Local Definition gw_tbl_10 := (gw_ent (@Q5m9.Mq1.scanexp_rstmt segs (base + 7584)%Z STRING_READ got_ssp ssp_guard) scanexp_rstmt gw_tbl_9).
Definition fixunstfsi_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Q8l1.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@QQRC.Mq2.fixunstfsi_post segs) fixunstfsi_post gw_tbl_10)))).
Definition floatsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Q8l1.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@QQRC.Mq2.floatsitf_post segs) floatsitf_post gw_tbl_11)))).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Q8l1.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@QQRC.Mq2.floatunsitf_post segs) floatunsitf_post gw_tbl_12)))).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Q8l1.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@QQRC.Mq2.extenddftf2_post segs) extenddftf2_post gw_tbl_13)))).
Definition addtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QzQg.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Q8l1.Mq0.addtf3_post segs) addtf3_post (gw_ent (@QQRC.Mq2.addtf3_post segs) addtf3_post gw_tbl_14)))).
Definition multf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QzQg.Mq0.multf3_post segs) multf3_post (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post (gw_ent (@Q8l1.Mq0.multf3_post segs) multf3_post (gw_ent (@QQRC.Mq2.multf3_post segs) multf3_post gw_tbl_15)))).
Definition multf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QzQg.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Q8l1.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@QQRC.Mq2.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_16)))).
Definition divtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QzQg.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Q8l1.Mq0.divtf3_post segs) divtf3_post (gw_ent (@QQRC.Mq2.divtf3_post segs) divtf3_post gw_tbl_17)))).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QzQg.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@QQRC.Mq2.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_18)))).
Definition letf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QzQg.Mq0.letf2_post segs) letf2_post (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post (gw_ent (@Q8l1.Mq0.letf2_post segs) letf2_post (gw_ent (@QQRC.Mq2.letf2_post segs) letf2_post gw_tbl_19)))).
Definition frexpl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@QzQg.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Q8l1.Mq0.frexpl_post segs) frexpl_post (gw_ent (@QQRC.Mq2.frexpl_post segs) frexpl_post gw_tbl_20)))).
Definition signbitl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@QzQg.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Q8l1.Mq0.signbitl_post segs) signbitl_post (gw_ent (@QQRC.Mq2.signbitl_post segs) signbitl_post gw_tbl_21)))).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@QzQg.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Q8l1.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@QQRC.Mq2.fpclassifyl_post segs) fpclassifyl_post gw_tbl_22)))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_23).
Definition ERRNO_LOC : ltac:(gw_rebind_ty (@QzQg.Mq0.ERRNO_LOC e_errno_loc) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QzQg.Mq0.ERRNO_LOC e_errno_loc) constr:(gw_tbl_24)).
Local Definition gw_tbl_25 := (gw_ent (@QzQg.Mq0.ERRNO_LOC e_errno_loc) ERRNO_LOC gw_tbl_24).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_25)).
Local Definition gw_tbl_26 := (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_25).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_26)).
Local Definition gw_tbl_27 := (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_26).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_27)).
Local Definition gw_tbl_28 := (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_27).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_28).
Definition dfinvG : ltac:(gw_rebind_ty (@QzQg.Mq0.dfinvG segs got_ssp RATP ssp_guard) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QzQg.Mq0.dfinvG segs got_ssp RATP ssp_guard) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QzQg.Mq0.dfinvG segs got_ssp RATP ssp_guard) dfinvG gw_tbl_29).
Definition S_R : ltac:(gw_rebind_ty (@QzQg.Mq0.S_R segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_R segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_30)).
Local Definition gw_tbl_31 := (gw_ent (@QzQg.Mq0.S_R segs base got_ssp RATP STRING_READ ssp_guard) S_R gw_tbl_30).
Definition S_C38 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_C38 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_31)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_C38 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_31)).
Local Definition gw_tbl_32 := (gw_ent (@QzQg.Mq0.S_C38 segs base got_ssp RATP STRING_READ ssp_guard) S_C38 gw_tbl_31).
Definition S_C2C : ltac:(gw_rebind_ty (@QzQg.Mq0.S_C2C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_32)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_C2C segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_32)).
Local Definition gw_tbl_33 := (gw_ent (@QzQg.Mq0.S_C2C segs base got_ssp RATP STRING_READ ssp_guard) S_C2C gw_tbl_32).
Definition S_E : ltac:(gw_rebind_ty (@QzQg.Mq0.S_E segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_33)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_E segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_33)).
Local Definition gw_tbl_34 := (gw_ent (@QzQg.Mq0.S_E segs base got_ssp RATP STRING_READ ssp_guard) S_E gw_tbl_33).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_34)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_34)).
Local Definition gw_tbl_35 := (gw_ent (@QzQg.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Q8l1.Mq0.leaf2_post segs) leaf2_post (gw_ent (@QQRC.Mq2.leaf2_post segs) leaf2_post gw_tbl_34)))).

Hypothesis shlim_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq3.gw_all) (@QQRC.Mq3.shlim_spec) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).

Hypothesis RFI_ok : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_ok) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_ok _%_Z_scope _%_list_scope _%_Z_scope _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_unget : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_unget) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_unget _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_eq) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).
Hypothesis rf_unget_nop : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_nop) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).

Hypothesis scanexp_rspec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q5m9.Mq1.gw_all) (@Q5m9.Mq1.scanexp_rspec) (base + 7584)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_35))) in let T := gw_fold_pcs T base (7584)%Z [0; 104; 112; 192; 224; 232; 292; 372; 380; 400; 476; 484; 516; 548; 576]%Z in exact T).
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
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
Ltac mlia := Z.div_mod_to_equations; lia.

Definition floatsitf_callp : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callp) constr:(gw_tbl_35)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callp)).

Ltac brs K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac]; try (exfalso; lia).

Definition errno_loc_spec : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.errno_loc_spec) constr:(gw_tbl_35)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.errno_loc_spec)).
Definition L_RET1 : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.L_RET1) constr:(gw_tbl_35)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.L_RET1)).
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Notation F_floatscan_common__L_RET1 := L_RET1 (only parsing).
Notation F_floatscan_common__S_C2C := S_C2C (only parsing).
Notation F_floatscan_common__S_C38 := S_C38 (only parsing).
Notation F_floatscan_common__S_E := S_E (only parsing).
Notation F_floatscan_common__S_R := S_R (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinvG := dfinvG (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_35)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard e_errno_loc e_197bc e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_502 E_502 D_509 E_509 LINK_502 LINK_509 CODE_e_errno_loc RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos RFI_unget rf_unget_eq rf_unget_nop scanexp_rspec floatsitf_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_502 joff_509 got_ssp RATP STRING_READ ssp_guard e_errno_loc e_197bc e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_502 E_502 D_509 E_509 LINK_502 LINK_509 CODE_e_errno_loc RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos RFI_unget rf_unget_eq rf_unget_nop scanexp_rspec floatsitf_spec.

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

Local Notation Fok := (@QzQg.Mq0.Fok F).

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation L_RET1 := (@F_floatscan_common__L_RET1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).

Local Notation dfinvG := (@F_floatscan_common__dfinvG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).

Local Notation S_R := (@F_floatscan_common__S_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_C38 := (@F_floatscan_common__S_C38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_C2C := (@F_floatscan_common__S_C2C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_E := (@F_floatscan_common__S_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac lia_goal P := lazymatch P with
| (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
| (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
| @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
| ?A /\ ?B => lia_goal A; lia_goal B | ?A \/ ?B => lia_goal A; lia_goal B | ?A -> ?B => lia_goal B | ~ _ => idtac
| ?A <-> ?B => lia_goal A; lia_goal B | False => idtac | True => idtac | hide ?A => lia_goal A | hide2 ?A => lia_goal A
end.
Ltac flia := lazymatch goal with |- ?G => lia_goal G end; first [ solve [stash_mods; stash_disj; lia] | lia ].
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.

Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.

Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zs1 := hush; unfold hide in SEP, SE_T; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.

Ltac mk_dfinvG := unfold F_floatscan_common__dfinvG; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].

Notation POST := (fs_post m0).

Hypothesis HS_R : S_R.

Ltac ufc FC := unfold rf_cells, rf_rend in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; flia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac]. clear. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
#[using="Type"] Lemma stdio_lim0 : forall f, sh_stdio (sh_lim0 f) = sh_stdio f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac]. clear. intros f. reflexivity. Qed.

#[using="Type"] Lemma RFJ_lim0 : forall kmin c f, RFJ' kmin c f -> RFJ' 0 c (sh_lim0 f).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac].
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold RFJ, sh_ok, sh_lim0; cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
split. { split; [exact Hbuf|]. split; [exact Rl|]. split; [exact Rr|]. split; [flia|]. split; [exact Rn | exact Rst]. }
split; [exact Rc|]. split; [flia|]. split; [intros _; flia|]. split.
- intros E. destruct (NS E) as (N1 & N2 & N3). split; [reflexivity|]. split; [exact N2 | exact N3].
- intros E. destruct (SS E) as (N1 & N2 & N3 & N4 & N5). split; [exact N1|]. split; [exact N2|]. split; [intros X; discriminate X|]. split; [intros X; discriminate X | exact N5].
Qed.

#[using="Type"] Lemma dfK_dn_f : forall sg f rp a z e2 x f' y, dfK_dn 53 (-1074) sg f rp a z e2 x = Some (f', y) -> f' = f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac].
clear. intros until y. unfold dfK_dn. destruct (df_dn_loop _ _) as [[rp2 a2 z2 e22 x2 i2]|]; [|discriminate].
destruct (df_final _ _ _ _ _ _ _ _ _ _); [|discriminate]. intros H. injection H as <- _. reflexivity.
Qed.
#[using="Type"] Lemma dfK_up_f : forall sg f rp a z e2 x f' y, dfK_up 53 (-1074) sg f rp a z e2 x = Some (f', y) -> f' = f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac]. clear. intros until y. unfold dfK_up. destruct (df_up_loop _ _) as [[rp2 a2 z2 e22 x2]|]; [|discriminate]. apply dfK_dn_f. Qed.
#[using="Type"] Lemma dfK_al_f : forall sg f rp z x f' y, dfK_al 53 (-1074) sg f rp z x = Some (f', y) -> f' = f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac].
clear. intros until y. unfold dfK_al.
destruct (if nz (Z.rem rp 9) then _ else _) as [[[[a2 z2] rp2] x2]|]; [|discriminate]. apply dfK_up_f.
Qed.
#[using="Type"] Lemma dfK_tz_f : forall sg f rp k x f' y, dfK_tz 53 (-1074) sg f rp k x = Some (f', y) -> f' = f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac]. clear. intros until y. unfold dfK_tz. destruct (df_tz_loop _ _ _); [|discriminate]. apply dfK_al_f. Qed.
#[using="Type"] Lemma dfK_mid_f : forall sg f rp lnz k x f' y, dfK_mid 53 (-1074) sg f rp lnz k x = Some (f', y) -> f' = f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac].
clear. intros until y. unfold dfK_mid.
destruct (_ && _ && _)%Z; cbv beta iota zeta; [|apply dfK_tz_f].
destruct (rp =? 9)%Z; cbv beta iota. { intros H; injection H as <- _; reflexivity. }
destruct (rp <? 9)%Z; cbv beta iota. { intros H; injection H as <- _; reflexivity. }
destruct (_ || _); cbv beta iota. { intros H; injection H as <- _; reflexivity. }
apply dfK_tz_f.
Qed.
#[using="Type"] Lemma dfK_pad_f : forall sg f lrp lnz j k x f' y, dfK_pad 53 (-1074) sg f lrp lnz j k x = Some (f', y) -> f' = f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac].
clear. intros until y. unfold dfK_pad. destruct (if nz j then _ else _) as [[k2 x2]|]; [|discriminate]. apply dfK_mid_f.
Qed.
#[using="Type"] Lemma dfK_rng_f : forall sg f lrp dc lnz j k x f' y, dfK_rng 53 (-1074) sg f lrp dc lnz j k x = Some (f', y) -> f' = f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac].
clear. intros until y. unfold dfK_rng.
destruct (znth x 0 =? 0)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (_ && _ && _); [intros H; injection H as <- _; reflexivity|].
destruct (_ <? lrp)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (lrp <? _)%Z; [intros H; injection H as <- _; reflexivity|].
apply dfK_pad_f.
Qed.

#[using="Type"] Lemma forallb_range : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, (0 <= c < Z.of_nat n)%Z -> P c = true.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac].
clear. intros P n H c Hc. apply (proj1 (forallb_forall P _) H). apply in_map_iff. exists (Z.to_nat c). split; [flia|]. apply in_seq. flia.
Qed.
#[using="Type"] Lemma and33_iff : forall c, (-1 <= c < 256)%Z ->
(Z.land (Z.land c 18446744073709551615) 18446744073709551583 = 69 <-> Z.lor c 32 = 101)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac].
clear. intros c Hc. destruct (Z.eq_dec c (-1)) as [->|Hne].
{ cbn. split; intros H; discriminate H. }
rewrite (land_W64_small c) by flia.
pose proof (forallb_range (fun c => Bool.eqb (Z.land c 18446744073709551583 =? 69) (Z.lor c 32 =? 101))%Z 256 ltac:(vm_compute; reflexivity) c ltac:(flia)) as E.
cbv beta in E. destruct (Z.eqb_spec (Z.land c 18446744073709551583) 69); destruct (Z.eqb_spec (Z.lor c 32) 101); cbn in E; try discriminate E; tauto.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_509 e_floatsitf CODE BASE4 BASER D_509 E_509 LINK_509 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos floatsitf_spec fc pre post fuelc f0 kmin0 c0 Hpok Hp HP30 T0 T1 SEP SE_T SPF SPT SG1 SG2 SG3"] Lemma L_C48 : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) b96 ev ws sign kmin c (f : shfile),
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> Fok Ft -> frm0 fct ->
fR = sh_lim0 f -> yR = f128_of_i32 0 ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x7e4)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_509 e_floatsitf CODE BASE4 BASER D_509 E_509 LINK_509 RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos floatsitf_spec fc pre post fuelc f0 kmin0 c0 Hpok Hp HP30 T0 T1 SEP SE_T SPF SPT SG1 SG2 SG3 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR HM ST0 BYT Hnul Hnum SPLO SPF2 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; try gw_hide SPLO; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac].
intros until f. intros DI RJ FOK FRM' HfR Hy. pose proof DI as DI0. dest_dfinv DI.
site_facts FC RJ kmin c f.
assert (L0 : length (j_pad0 J) = 4%nat /\ length (j_pad1 J) = 4%nat).
{ destruct FC as [[Hwf _] _]. cbn in Hwf. tauto. }
destruct L0 as [L0 L1].
pose proof FC as FC0. rewrite rf_cells_raw_eq in FC0.
pose proof (gw_unhyp shlim_spec) as SL. unfold shlim_stmt in SL.
zs. zs. zs. callx (eapply SL with (Fp := Fp) (T := T) (p := p) (w := true) (txt := txt) (f := f) (J := J);
[exact FC0 | exact (RFI_ok T txt p J _ _ _ RJ) | exact L0 | exact L1 | flia | flia | unfold zlength in *; flia | assumption]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end. rewrite <- HfR in FC2.
zs. zs. callx (eapply floatsitf_callp; [eassumption | flia]).
zs. eapply L_RET1; try eassumption; try flia; try mk_finv; try mk_framL.
all: try (rewrite HfR; eapply RFJ_lim0; exact RJ). all: flia.
Qed.

#[using="scanexp_rspec Hpok BYT Hp Hnul T0 T1 SEP SPF2 SG2 SG3"] Lemma scanexp_callE : forall (ra' : word) (q' : Z) (gp' tp' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (f : shfile) (kmin c : Z) (fS : shfile) (e10 : Z),
scanexp fuelc f pok = Some (fS, e10) ->
rw_cells segs m Fp (rf_cells T p true f J) -> RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z ->
(sh_stdio f = true -> rtext T txt pre post /\ p = zlength pre) ->
bytes_at segs m T (zbytes txt) -> ssp_cells m canary ->
stk segs m (q' - 240) q' -> (4096 <= q' - 240)%Z -> (q' <= Fp)%Z ->
(T + zlength txt <= q' - 240 \/ q' <= T)%Z -> (ssp_guard + 8 <= q' - 240)%Z -> (0 <= q')%Z -> (q' < 2^63)%Z ->
mem_inv segs m ->
evt segs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' k' c',
ms' = MS (mkR ra' (Z_to_bv 64 q') gp' tp' t0' t1' t2' s0 s1 (Z_to_bv 64 e10) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra') fc' None m' (seg_rom segs)
/\ munch [(q' - 240, q'); (Fp, Fp + 232)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q' - 240) q'
/\ rw_cells segs m' Fp (rf_cells T p true fS J)
/\ RFJ' k' c' fS /\ (1 <= k')%Z
/\ bytes_at segs m' T (zbytes txt)
/\ ssp_cells m' canary)
(MS (mkR ra' (Z_to_bv 64 q') gp' tp' t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 SCANEXP) fc' None m (seg_rom segs)).
Proof. clear - scanexp_rspec Hpok BYT Hp Hnul T0 T1 SEP SPF2 SG2 SG3 segs ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM ST0 Hnum HP30 SE_T SPLO SPF SPT SG1 Q1 FRM HS_R. first [clear HM | gw_hide HM | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_R | gw_hide HS_R | idtac].
intros until e10. intros HS FC RJ Hk Hc STX BY SSP ST Q1' Q2 Q3 Q4 Q5 Q6 MI.
pose proof (gw_unhyp scanexp_rspec) as SX. unfold scanexp_rstmt in SX.
eapply evt_mono.
{ eapply SX with (pre := pre) (post := post); try eassumption; unfold SCANEXP_DEPTH; try flia; clear - Hpok scanexp_rspec segs ssp_guard; unfold hide2 in *; flia. }
intros ms' P. unfold scanexp_rpost, SCANEXP_DEPTH in P. exact P.
Qed.
Ltac eplia := gw_expose got_ssp; gw_expose ssp_guard; unfold SCANEXP_DEPTH, zlength in *; unfold hide2 in *; flia.
Ltac some_pair H := let E1 := fresh "Ef" in injection H as E1 H.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_502 joff_509 e_errno_loc e_floatsitf CODE BASE4 BASER D_502 E_502 D_509 E_509 LINK_502 LINK_509 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos floatsitf_spec Hpok Hp HP30 T0 T1 SEP SE_T SPF SPT SG1 SG2 SG3 HS_R"] Lemma L_C38 : S_C38.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_502 joff_509 e_errno_loc e_floatsitf CODE BASE4 BASER D_502 E_502 D_509 E_509 LINK_502 LINK_509 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos floatsitf_spec Hpok Hp HP30 T0 T1 SEP SE_T SPF SPT SG1 SG2 SG3 HS_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM ST0 BYT Hnul Hnum SPLO SPF2 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; try gw_hide SPLO; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until ng. intros _ DI RJ Hk FOK FRM' Hsg Hst DF Hw80 Rg Hng Rlrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct DF as (XR & X31H & Rj & Rk & Rdc & Rlnz & Hlnz & Hxk & Hkj & Hkj45).
unfold nz in HK.
destruct (Z.eqb_spec gotdig 0) as [Eg|Ng]; cbn [Z.b2z negb] in Hng, HK; subst ng.
-
some_pair HK.
zs. (brf K1; [ exfalso; lia | ]).
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
eapply L_C48; try eassumption; try (symmetry; assumption). mk_dfinvG.
- pose proof (dfK_rng_f _ _ _ _ _ _ _ _ _ _ HK) as Ef. symmetry in Ef. subst f.
zs. (brf K1; [ | exfalso; lia ]).
stmt HS_R. eapply NX; try eassumption; try flia.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_502 joff_509 e_errno_loc e_floatsitf CODE BASE4 BASER D_502 E_502 D_509 E_509 LINK_502 LINK_509 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos RFI_unget rf_unget_eq floatsitf_spec Hpok Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG2 SG3 HS_R"] Lemma L_C2C : S_C2C.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_502 joff_509 e_errno_loc e_floatsitf CODE BASE4 BASER D_502 E_502 D_509 E_509 LINK_502 LINK_509 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos RFI_unget rf_unget_eq floatsitf_spec Hpok Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG2 SG3 HS_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM ST0 BYT Hnul Hnum SPLO Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; try gw_hide SPLO; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until ng. intros _ DI RJ Hk FOK FRM' Hsg Hst Hsn DF Hw80 Rg Hng Rlrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
site_facts FC RJ kmin c f.
pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu.
rewrite (rf_unget_eq f Hsn) in HK, RJu.
ufc FC. rewrite Hsn in FC.
zs. zs. zs0.
pose proof L_C38 as NX. unfold F_floatscan_common__S_C38 in NX. eapply NX with (f := mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)); try eassumption; try flia.
unfold F_floatscan_common__dfinvG. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?Hsn; unfold M64; hyp_cells.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_502 joff_509 e_errno_loc e_floatsitf CODE BASE4 BASER D_502 E_502 D_509 E_509 LINK_502 LINK_509 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos RFI_unget rf_unget_eq rf_unget_nop scanexp_rspec floatsitf_spec Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_R"] Lemma L_E : S_E.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_502 joff_509 e_errno_loc e_floatsitf CODE BASE4 BASER D_502 E_502 D_509 E_509 LINK_502 LINK_509 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos RFI_unget rf_unget_eq rf_unget_nop scanexp_rspec floatsitf_spec Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hnum FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until gotrad. intros _ DI RJ Hk FOK FRM' Hsg Hst DF Hw80 Rg Rgr Rlrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof DF as DF0. destruct DF as (XR & X31H & Rj & Rk & Rdc & Rlnz & Hlnz & Hxk & Hkj & Hkj45).
site_facts FC RJ kmin c f.
unfold dfK_exp in HK. cbv beta iota zeta in HK.
set (lrp' := (if nz gotrad then lrp else dc)%Z) in HK.
assert (Rlrp' : (- 2^31 <= lrp' < 2^31)%Z) by (subst lrp'; destruct (nz gotrad); flia).

assert (GAC0 :
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp') (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x65c)) fct None m (seg_rom segs))).
2:{ zs. zs. brf K1.
- replace lrp' with dc in GAC0; [exact GAC0|]. subst lrp'. unfold nz. replace (gotrad =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia). reflexivity.
- zs. replace lrp' with lrp in GAC0; [exact GAC0|]. subst lrp'. unfold nz. replace (gotrad =? 0)%Z with false by (symmetry; apply Z.eqb_neq; flia). reflexivity. }
clearbody lrp'.

assert (GC1C : forall (x11' x12' : word),
(nz gotdig && (Z.lor c 32 =? 101))%Z = false ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11' x12' x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp') (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x7b8)) fct None m (seg_rom segs))).
{ intros x11' x12' Hne. rewrite Hne in HK.
assert (Eng : forall g, (0 <= g <= 1)%Z -> Z.b2z (g <? 1)%Z = Z.b2z (g =? 0)%Z).
{ clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_502 joff_509 e_errno_loc e_floatsitf CODE BASE4 BASER D_502 E_502 D_509 E_509 LINK_502 LINK_509 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos RFI_unget rf_unget_eq rf_unget_nop scanexp_rspec floatsitf_spec. intros g Hg. destruct (Z.ltb_spec g 1); destruct (Z.eqb_spec g 0); cbn; flia. }
zs. rewrite (Eng gotdig Rg). zs. brs K2.
-
replace (0 <=? c)%Z with false in HK by (symmetry; apply Z.leb_gt; flia).
pose proof L_C38 as NX. unfold F_floatscan_common__S_C38 in NX. eapply NX with (gotdig := gotdig); try eassumption; try flia; try reflexivity.
- replace (0 <=? c)%Z with true in HK by (symmetry; apply Z.leb_le; flia).
pose proof FC as FC0. ufc FC.
destruct (sh_shlim_neg f) eqn:SN; unfold M64 in FC.
+
rewrite (rf_unget_nop f SN) in HK.
zs. zs. (brf K3; [ | exfalso; lia ]).
pose proof L_C38 as NX. unfold F_floatscan_common__S_C38 in NX. eapply NX with (gotdig := gotdig); try eassumption; try flia; try reflexivity.
+ zs. zs. (brf K3; [ exfalso; lia | ]).
pose proof L_C2C as NX. unfold F_floatscan_common__S_C2C in NX. eapply NX with (gotdig := gotdig); try eassumption; try flia; try reflexivity. }

zs. brf K2.
{  apply GC1C. unfold nz. replace (gotdig =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia). reflexivity. }
zs. zs. zs. brf K3.
{  apply GC1C. replace (Z.lor c 32 =? 101)%Z with false; [apply Bool.andb_false_r|].
symmetry. apply Z.eqb_neq. intros E. apply K3. apply (proj2 (and33_iff c ltac:(flia))). exact E. }
assert (He : Z.lor c 32 = 101%Z) by (apply (proj1 (and33_iff c ltac:(flia))); exact K3).
unfold nz in HK at 1. replace (gotdig =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; flia).
rewrite He in HK. cbn [negb andb Z.eqb Pos.eqb] in HK.
destruct (scanexp fuelc f pok) as [[fS e10]|] eqn:HSX; [|discriminate HK].
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in He; discriminate He).
pose proof (scanexp_bound fuelc f pok fS e10 ltac:(rewrite Hbuf; exact BYT) HSX) as Re10.

zs. zs. zs. zs.
callx (eapply scanexp_callE with (f := f) (kmin := kmin) (c := c) (fS := fS) (e10 := e10);
[ exact HSX | exact FC | exact RJ | eplia | exact Hc0 | intros E; apply ST0; rewrite <- Hst; exact E | exact BY | exact (conj SSP1 SSP2)
| replace (q + -8416 - 240)%Z with (q - 8656)%Z by flia; exact ST
| eplia | eplia | eplia | eplia | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end.
match goal with H : RFJ _ _ _ _ _ ?k ?c fS |- _ => rename H into RJ2 end.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; gw_expose got_ssp; gw_expose ssp_guard end.
match goal with H : stk _ ?m' (q + -8416 - 240)%Z _ |- _ => replace (q + -8416 - 240)%Z with (q - 8656)%Z in H by flia end.
match goal with H : (1 <= ?k)%Z, H2 : RFJ _ _ _ _ _ ?k _ fS |- _ => rename H into Hk2 end.
pose proof RJ2 as RJ3. destruct RJ3 as (OK2 & Rc2 & CC2 & KM2 & NS2 & SS2). destruct OK2 as (Hbuf2 & Rl2 & Rr2 & Rc02 & Rn2 & Rst2).
assert (RR2 : (0 <= rf_rend T p true fS <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio fS); unfold zlength in *; flia). unfold M64 in RR2.
assert (Hst2 : sh_stdio fS = sh_stdio f0) by (rewrite <- Hst; exact (proj1 (scanexp_stdio _ _ _ _ _ HSX))).
unfold nz in HK. replace (gotdig =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; flia).

zs. zs. zs. brf K4; rewrite ?land_W64 in K4.
-
assert (Hne : e10 <> LLONG_MIN_).
{ intros E. apply K4. rewrite E. vm_compute. reflexivity. }
replace (e10 =? LLONG_MIN_)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne). cbn [negb] in HK. cbv beta iota in HK.
pose proof (dfK_rng_f _ _ _ _ _ _ _ _ _ _ HK) as Ef. subst fS.
assert (Re : (-2^60 <= e10 <= 2^60)%Z) by (destruct Re10 as [E|R]; [exfalso; exact (Hne E) | exact R]).
zs.
let v := getreg 23%Z in replace v with (Z_to_bv 64 (lrp' + e10)%Z) by (apply Z_to_bv_eqm; rewrite ?land_W64; Z.div_mod_to_equations; flia).
stmt HS_R. eapply NX with (lrp := (lrp' + e10)%Z); try eassumption; try flia. mk_dfinvG.
- assert (Ee : e10 = LLONG_MIN_) by (destruct Re10 as [E|R]; [exact E | exfalso; clear - K4 R w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_502 joff_509 e_errno_loc e_floatsitf CODE BASE4 BASER D_502 E_502 D_509 E_509 LINK_502 LINK_509 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos RFI_unget rf_unget_eq rf_unget_nop scanexp_rspec floatsitf_spec; unfold LLONG_MIN_ in *; Z.div_mod_to_equations; flia]).
rewrite Ee, Z.eqb_refl in HK.
zs. brf K5; rewrite ?land_W64 in K5.
+
assert (Ep : pok = 0%Z) by (clear - K5 Hpok w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_502 joff_509 e_errno_loc e_floatsitf CODE BASE4 BASER D_502 E_502 D_509 E_509 LINK_502 LINK_509 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos RFI_unget rf_unget_eq rf_unget_nop scanexp_rspec floatsitf_spec; unfold hide2 in *; mlia).
rewrite Ep in HK. cbn [Z.eqb negb] in HK. cbv beta iota in HK. some_pair HK.
eapply L_C48; try eassumption; try (symmetry; assumption). mk_dfinvG.
+ assert (Ep : pok <> 0%Z) by (clear - K5 Hpok w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_502 joff_509 e_errno_loc e_floatsitf CODE BASE4 BASER D_502 E_502 D_509 E_509 LINK_502 LINK_509 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO shlim_spec RFI_ok RFI_rpos RFI_unget rf_unget_eq rf_unget_nop scanexp_rspec floatsitf_spec; unfold hide2 in *; mlia).
replace (pok =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Ep). cbn [negb] in HK. cbv beta iota in HK.
pose proof (dfK_rng_f _ _ _ _ _ _ _ _ _ _ HK) as Ef.
pose proof (RFI_unget T txt p J Hp _ _ fS RJ2 ltac:(flia)) as RJu.
pose proof FC2 as FC3. ufc FC3.
destruct (sh_shlim_neg fS) eqn:SN; unfold M64 in FC3.
*
rewrite (rf_unget_nop fS SN) in HK, Ef, RJu. subst fS.
zs. zs. (brf K6; [ | exfalso; lia ]). zs. zs.
let v := getreg 23%Z in replace v with (Z_to_bv 64 (lrp' + 0)%Z) by (apply Z_to_bv_eqm; rewrite ?land_W64; Z.div_mod_to_equations; flia).
stmt HS_R. eapply NX with (lrp := (lrp' + 0)%Z); try eassumption; try flia. mk_dfinvG.
* rewrite (rf_unget_eq fS SN) in HK, Ef, RJu.
zs. zs. (brf K6; [ exfalso; lia | ]). zs. zs. zs. zs1. zs. zs.
let v := getreg 23%Z in replace v with (Z_to_bv 64 (lrp' + 0)%Z) by (apply Z_to_bv_eqm; rewrite ?land_W64; Z.div_mod_to_equations; flia).
rewrite <- Ef in RJu, HK.
assert (Hst3 : sh_stdio fR = sh_stdio f0) by (rewrite Ef; cbn [sh_stdio]; exact Hst2).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (FC4 : rw_cells segs mm Fp (rf_cells T p true fR J))
by (rewrite Ef; unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells) end.
stmt HS_R. eapply NX with (lrp := (lrp' + 0)%Z); try eassumption; try flia. mk_dfinvG.
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

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 : Z).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.

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
Definition S_A568 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A568 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A568 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.S_A568 segs base got_ssp RATP STRING_READ ssp_guard) S_A568 gw_tbl_9).
Definition S_A534 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A534 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A534 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.S_A534 segs base got_ssp RATP STRING_READ ssp_guard) S_A534 gw_tbl_10).
Definition SN324 : ltac:(gw_rebind_ty (@QzQg.Mq0.SN324 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QzQg.Mq0.SN324 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.SN324 segs base got_ssp RATP STRING_READ ssp_guard) SN324 gw_tbl_11).
Definition S_N324 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_N324 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_N324 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.S_N324 segs base got_ssp RATP STRING_READ ssp_guard) S_N324 gw_tbl_12).
Definition S_N3E8 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_N3E8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_N3E8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.S_N3E8 segs base got_ssp RATP STRING_READ ssp_guard) S_N3E8 gw_tbl_13).
Notation rfj := G.T_rfj.rfj.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Ltac mlia2 := rewrite ?land_W64 in *; Z.div_mod_to_equations; lia.
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

Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Notation F_floatscan_common__SN324 := SN324 (only parsing).
Notation F_floatscan_common__S_A534 := S_A534 (only parsing).
Notation F_floatscan_common__S_A568 := S_A568 (only parsing).
Notation F_floatscan_common__S_N324 := S_N324 (only parsing).
Notation F_floatscan_common__S_N3E8 := S_N3E8 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard.

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

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).

Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).

Local Notation S_A568 := (@F_floatscan_common__S_A568 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A534 := (@F_floatscan_common__S_A534 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N324 := (@F_floatscan_common__S_N324 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_N3E8 := (@F_floatscan_common__S_N3E8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac lia_goal P := lazymatch P with
| (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
| (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
| @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
| ?A /\ ?B => lia_goal A; lia_goal B | ?A \/ ?B => lia_goal A; lia_goal B | ?A -> ?B => lia_goal B | ~ _ => idtac
| ?A <-> ?B => lia_goal A; lia_goal B | False => idtac | True => idtac | hide ?A => lia_goal A | hide2 ?A => lia_goal A
end.
Ltac flia := lazymatch goal with |- ?G => lia_goal G end; first [ solve [stash_mods; stash_disj; lia] | lia ].
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.

Ltac hlia H := let E := fresh in intros E; specialize (H E); lia.

Notation POST := (fs_post m0).

Hypothesis HS_N3E8 : S_N3E8.
Hypothesis HS_A534 : S_A534.
Hypothesis HS_A568 : S_A568.

#[using="Type"] Lemma th0_val : znth th_list 0 = 10384593%Z. Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_N3E8 HS_A534 HS_A568. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_N3E8 | gw_hide HS_N3E8 | idtac]; first [clear HS_A534 | gw_hide HS_A534 | idtac]; first [clear HS_A568 | gw_hide HS_A568 | idtac]. reflexivity. Qed.
#[using="Type"] Lemma th1_val : znth th_list 1 = 717069655%Z. Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_N3E8 HS_A534 HS_A568. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_N3E8 | gw_hide HS_N3E8 | idtac]; first [clear HS_A534 | gw_hide HS_A534 | idtac]; first [clear HS_A568 | gw_hide HS_A568 | idtac]. reflexivity. Qed.
#[using="Type"] Lemma th2_val : znth th_list 2 = 257060992%Z. Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_N3E8 HS_A534 HS_A568. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_N3E8 | gw_hide HS_N3E8 | idtac]; first [clear HS_A534 | gw_hide HS_A534 | idtac]; first [clear HS_A568 | gw_hide HS_A568 | idtac]. reflexivity. Qed.
#[using="Type"] Lemma th3_val : znth th_list 3 = 658440191%Z. Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_N3E8 HS_A534 HS_A568. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_N3E8 | gw_hide HS_N3E8 | idtac]; first [clear HS_A534 | gw_hide HS_A534 | idtac]; first [clear HS_A568 | gw_hide HS_A568 | idtac]. reflexivity. Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard Hp SE_T SPF SPT SG1 SG3 HS_N3E8 HS_A534 HS_A568"] Lemma L_N324 : S_N324.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard Hp SE_T SPF SPT SG1 SG3 HS_N3E8 HS_A534 HS_A568 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPLO SPF2 SG2 Q1 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SPLO; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
unfold F_floatscan_common__S_N324, F_floatscan_common__SN324. induction fo as [|fo IH]; intros m; intros until s'; intros DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzf Rw Hfo Rrp Re2 HZ0 HS1 HA6 HL HK; [discriminate HL|].
pose proof DI as DI0. dest_dfinv DI. destruct XR as (LW' & LX & REL).
rewrite df_dn_loop_step in HL. unfold df_dn_body in HL. cbn [ds_a ds_z ds_x ds_rp ds_e2] in HL.
destruct (df_dni_loop 6 a z x 0) as [i1|] eqn:HI; [|discriminate HL].
change LD_B1B_DIG with 4%Z in HL. change (9 * 4)%Z with 36%Z in HL. change (9 + 36)%Z with 45%Z in HL. change MASK with 2047%Z in HL.
rewrite !land2047 in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs0.
assert (Naz_none : a = z -> rp <> 36%Z -> False).
{ intros Eaz Hrp. subst a. pose proof (dn_az_none (S fo) rp z e2 x i0 ltac:(flia) Hrp) as HN.
rewrite df_dn_loop_step in HN. unfold df_dn_body in HN. cbn [ds_a ds_z ds_x ds_rp ds_e2] in HN. rewrite HI in HN.
change LD_B1B_DIG with 4%Z in HN. change (9 * 4)%Z with 36%Z in HN. change (9 + 36)%Z with 45%Z in HN. change MASK with 2047%Z in HN.
rewrite !land2047 in HN. rewrite HN in HL. discriminate HL. }

assert (G358 : forall (x5' x17' : word), i1 = 4%Z -> a <> z ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5' x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17'
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 (znth x a)) (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xef4)) fct None m (seg_rom segs))).
{ intros x5' x17' -> Naz. change (4 =? 4)%Z with true in HL. cbn [andb] in HL.
zs. fixw2. fixw. zs. zs.
try (assert (HrpR__ : (0 <= rp < 2 ^ 64)%Z) by (clear - K1 Naz_none LTX Re2 Rrp Hfo Rzf Rz LX LW' LW SG3 SG1 SPT SPF SE_T Hp w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; lia)).
brf K7.
-
replace (rp =? 36)%Z with false in HL by (symmetry; apply Z.eqb_neq; first [ clear - H0 H K7 Naz Naz_none LTX Re2 Rrp Hfo Rzf LX LW' LW SG3 SG1 SPT SPF SE_T Hp w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; mlia2 | mlia2 ]).
stmt HS_N3E8. eapply (NX fo IH 4%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)).
-
replace (rp =? 36)%Z with true in HL by (symmetry; apply Z.eqb_eq; first [ clear - H K7 Naz Naz_none LTX Re2 Rrp Hfo Rzf LX LW' LW SG3 SG1 SPT SPF SE_T Hp w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; mlia2 | mlia2 ]). injection HL as <-. cbn [ds_a ds_z ds_x ds_e2] in HK.
zs. stmt HS_A568. eapply NX; try eassumption; try flia; try reflexivity.
split; [exact (conj LW' (conj LX REL)) | split; [exact X31H | split; [flia | split; [hlia Rzf | split; [flia | intros E; specialize (Rw E); mlia2]]]]]. }

stash HZ0. stash HA6. stash HS1.
unfold df_dni_body in HI.
rewrite df_dni_loop_step in HI. change (0 <? LD_B1B_DIG)%Z with true in HI. cbv beta iota in HI. unfold df_dni_body in HI at 1.
change MASK with 2047%Z in HI. change LD_B1B_DIG with 4%Z in HI. rewrite Z.add_0_r, land2047, (Z.mod_small a 2048), th0_val in HI by flia.
zs. rewrite land2047, (Z.mod_small a 2048) by flia. zs. brf K1.
-
replace (a =? z)%Z with false in HI by (symmetry; apply Z.eqb_neq; flia). cbn [orb] in HI.
assert (Kin0 : inring a z a) by (unfold inring; rewrite Z.sub_diag; change (0 mod 2048)%Z with 0%Z; clear - K1 Ra Rz Rrs0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; Z.div_mod_to_equations; flia).
pose proof (X31H a) as Rt0. pose proof (REL a ltac:(flia) (zone_in h _ _ _ _ Kin0)) as Et0. clear Kin0.
pose proof (u32arr_read segs _ _ _ a _ _ XW (nth_error_wnth ws a ltac:(clear - Ra w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; flia) ltac:(clear - Ra LW' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; flia)) ltac:(clear - Ra w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; flia) eq_refl) as RD0.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws a (znth x a) (eq_sym Et0) Rt0). set (t0v := znth x a) in *.
zs. zs. zs. brf K2.
+
replace (t0v <? 10384593)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]). cbv iota in HI.
zs. brf K3.
*
replace (10384593 <? t0v)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-.
replace (0 =? 4)%Z with false in HL by reflexivity. cbn [andb] in HL.
stmt HS_N3E8. eapply (NX fo IH 0%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)).
*
replace (10384593 <? t0v)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
clear RD0 Et0 K2 K3.
replace (0 + 1)%Z with 1%Z in HI by reflexivity.
rewrite df_dni_loop_step in HI. change (1 <? 4)%Z with true in HI. unfold df_dni_body in HI. cbv beta iota in HI.
change MASK with 2047%Z in HI. rewrite th1_val in HI. replace (1 + 1)%Z with 2%Z in HI by reflexivity.
pose proof (land_mask_range (a + 1) 2047 ltac:(flia)) as Rk1. set (k1 := Z.land (a + 1) 2047) in *.
zs. zs. zs. brf K4.
--
replace (k1 =? z)%Z with true in HI by (symmetry; apply Z.eqb_eq; exact K4). cbn [orb] in HI. injection HI as <-.
eapply G358; [reflexivity | flia].
-- replace (k1 =? z)%Z with false in HI by (symmetry; apply Z.eqb_neq; exact K4). cbn [orb] in HI.
assert (Hd1 : (1 <= (z - a) mod 2048)%Z) by (clear - K1 Ra Rz Rrs0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; Z.div_mod_to_equations; flia).
destruct (inring_plus a z 1 ltac:(flia) ltac:(flia) Hd1 K4) as [Kin1 Hd2]. fold k1 in Kin1.
pose proof (X31H k1) as Rt1. pose proof (REL k1 ltac:(flia) (zone_in h _ _ _ _ Kin1)) as Et1. clear Kin1.
pose proof (u32arr_read segs _ _ _ k1 _ _ XW (nth_error_wnth ws k1 ltac:(clear - Rk1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; flia) ltac:(clear - Rk1 LW' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; flia)) ltac:(clear - Rk1 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; flia) eq_refl) as RD1.
zs. zs. fix_idx. zs. rewrite (sx32_wval ws k1 _ (eq_sym Et1) Rt1). set (t1v := znth x k1) in *.
zs. zs. zs. brf K5.
++
replace (t1v <? 717069655)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-.
eapply G358; [reflexivity | flia].
++ replace (t1v <? 717069655)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]). cbv iota in HI.
zs. brf K6.
** replace (717069655 <? t1v)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-.
replace (1 =? 4)%Z with false in HL by reflexivity. cbn [andb] in HL. stmt HS_N3E8. eapply (NX fo IH 1%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)).
** replace (717069655 <? t1v)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
clear RD1 Et1 K5 K6.
rewrite df_dni_loop_step in HI. change (2 <? 4)%Z with true in HI. unfold df_dni_body in HI. cbv beta iota in HI.
change MASK with 2047%Z in HI. rewrite th2_val in HI. replace (2 + 1)%Z with 3%Z in HI by reflexivity.
pose proof (land_mask_range (a + 2) 2047 ltac:(flia)) as Rk2. set (k2 := Z.land (a + 2) 2047) in *.
zs. zs. zs. brf K7.
{ replace (k2 =? z)%Z with true in HI by (symmetry; apply Z.eqb_eq; exact K7). cbn [orb] in HI. injection HI as <-.
eapply G358; [reflexivity | flia]. }
replace (k2 =? z)%Z with false in HI by (symmetry; apply Z.eqb_neq; exact K7). cbn [orb] in HI.
destruct (inring_plus a z 2 ltac:(flia) ltac:(flia) Hd2 K7) as [Kin2 Hd3]. fold k2 in Kin2.
pose proof (X31H k2) as Rt2. pose proof (REL k2 ltac:(flia) (zone_in h _ _ _ _ Kin2)) as Et2. clear Kin2.
pose proof (u32arr_read segs _ _ _ k2 _ _ XW (nth_error_wnth ws k2 ltac:(clear - Rk2 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; flia) ltac:(clear - Rk2 LW' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; flia)) ltac:(clear - Rk2 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; flia) eq_refl) as RD2.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws k2 _ (eq_sym Et2) Rt2). set (t2v := znth x k2) in *.
zs. zs. zs. brf K8.
{ replace (t2v <? 257060992)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-. eapply G358; [reflexivity | flia]. }
replace (t2v <? 257060992)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]). cbv iota in HI.
zs. brf K9.
{ replace (257060992 <? t2v)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-.
replace (2 =? 4)%Z with false in HL by reflexivity. cbn [andb] in HL. stmt HS_N3E8. eapply (NX fo IH 2%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)). }
replace (257060992 <? t2v)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
clear RD2 Et2 K8 K9.
rewrite df_dni_loop_step in HI. change (3 <? 4)%Z with true in HI. unfold df_dni_body in HI. cbv beta iota in HI.
change MASK with 2047%Z in HI. rewrite th3_val in HI. replace (3 + 1)%Z with 4%Z in HI by reflexivity.
pose proof (land_mask_range (a + 3) 2047 ltac:(flia)) as Rk3. set (k3 := Z.land (a + 3) 2047) in *.
zs. zs. zs. brf K10.
{ replace (k3 =? z)%Z with true in HI by (symmetry; apply Z.eqb_eq; exact K10). cbn [orb] in HI. injection HI as <-. eapply G358; [reflexivity | flia]. }
replace (k3 =? z)%Z with false in HI by (symmetry; apply Z.eqb_neq; exact K10). cbn [orb] in HI.
destruct (inring_plus a z 3 ltac:(flia) ltac:(flia) Hd3 K10) as [Kin3 Hd4]. fold k3 in Kin3.
pose proof (X31H k3) as Rt3. pose proof (REL k3 ltac:(flia) (zone_in h _ _ _ _ Kin3)) as Et3. clear Kin3.
pose proof (u32arr_read segs _ _ _ k3 _ _ XW (nth_error_wnth ws k3 ltac:(clear - Rk3 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; flia) ltac:(clear - Rk3 LW' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; flia)) ltac:(clear - Rk3 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; flia) eq_refl) as RD3.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws k3 _ (eq_sym Et3) Rt3). set (t3v := znth x k3) in *.
zs. zs. zs. brf K11.
{
assert (Hi4 : i1 = 4%Z).
{ destruct (Z.ltb_spec t3v 658440191).
- cbv iota in HI. injection HI as <-. reflexivity.
- replace (658440191 <? t3v)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
rewrite df_dni_loop_step in HI. change (4 <? 4)%Z with false in HI. injection HI as <-. reflexivity. }
eapply G358; [exact Hi4 | flia]. }
replace (t3v <? 658440191)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
replace (658440191 <? t3v)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). cbv iota in HI. injection HI as <-.
replace (3 =? 4)%Z with false in HL by reflexivity. cbn [andb] in HL. stmt HS_N3E8. eapply (NX fo IH 3%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)).
+
replace (t0v <? 10384593)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). cbv iota in HI. injection HI as <-.
eapply G358; [reflexivity | flia].
-
replace (a =? z)%Z with true in HI by (symmetry; apply Z.eqb_eq; flia). cbn [orb] in HI. injection HI as <-.
change (4 =? 4)%Z with true in HL. cbn [andb] in HL.
zs. fixw2. fixw. zs. zs.
try (assert (HrpR__ : (0 <= rp < 2 ^ 64)%Z) by (clear - K1 Naz_none LTX Re2 Rrp Hfo Rzf Rz LX LW' LW SG3 SG1 SPT SPF SE_T Hp w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; lia)).
brf K7.
+  exfalso. exact (Naz_none ltac:(flia) ltac:(mlia2)).
+ replace (rp =? 36)%Z with true in HL by (symmetry; apply Z.eqb_eq; first [ clear - H K7 Naz Naz_none LTX Re2 Rrp Hfo Rzf LX LW' LW SG3 SG1 SPT SPF SE_T Hp w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_RATP_ssp_guard; mlia2 | mlia2 ]). injection HL as <-. cbn [ds_a ds_z ds_x ds_e2] in HK.
unstash. subst Z0 a. zs. stmt HS_A534. eapply NX; try eassumption; try flia.
split; [exact (conj LW' (conj LX REL)) | split; [exact X31H | split; [flia | split; [hlia Rzf | split; [flia | intros E; specialize (Rw E); mlia2]]]]].
Qed.

End Floatscan.

End G.
End Mq2.

Module Mq3.

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
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.
Hypothesis LAY_got_ssp_RERRNO : gw_le (got_ssp + 8) (RATP + -164).

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
Definition S_N484 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_N484 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_N484 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.S_N484 segs base got_ssp RATP STRING_READ ssp_guard) S_N484 gw_tbl_10).
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

Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Notation F_floatscan_common__S_N484 := S_N484 (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__dfinv := dfinv (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 got_ssp RATP STRING_READ ssp_guard CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO.

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

Local Notation S_N484 := (@F_floatscan_common__S_N484 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.
Ltac store_done' := stash_mods; stash_disj; unfold hide in SPT; store_done; unstash.

Ltac lia_goal P := lazymatch P with
| (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
| (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
| @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
| ?A /\ ?B => lia_goal A; lia_goal B | ?A \/ ?B => lia_goal A; lia_goal B | ?A -> ?B => lia_goal B | ~ _ => idtac
| ?A <-> ?B => lia_goal A; lia_goal B | False => idtac | True => idtac | hide ?A => lia_goal A | hide2 ?A => lia_goal A
end.
Ltac flia := lazymatch goal with |- ?G => lia_goal G end; first [ solve [stash_mods; stash_disj; lia] | lia ].
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.

Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold F_floatscan_common__dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].

Ltac hlia H := let E := fresh in intros E; specialize (H E); lia.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_N484 : S_N484.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO Hp T1 SE_T SPF SPF2 SPT SG1 SG3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 SEP SPLO SG2 Q1 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; try gw_hide SEP; try gw_hide SPLO; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros fo IH [kk carry a1 i rp1 xx] m'; intros until s'. intros _ DI2 RJ Hk FOK FRM' Hsg XR2 X312 Ra1 Rc1 Hkk Hsh Rz Rzf Rw Hfo Rrp Rrp1 Re2 HZ0 HS1 HA6 HL2 HK.
cbn [dk_x dk_a dk_carry dk_rp dk_k] in *. subst kk.

assert (Hshb : (1 <= sh <= 9)%Z) by (clear - Hsh w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; lia).
pose proof DI2 as DI'. dest_dfinv DI'. destruct XR2 as (LW2 & LX2 & REL2).
pose proof (Z.mod_pos_bound (z - a1) 2048 ltac:(flia)) as Rrs1.
zs. brf K1.
-
unfold nz in HL2. replace (negb (carry =? 0))%Z with false in HL2 by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; flia).
eapply IH with (h := h) (x := xx) (z := z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia; try mk_dfinv.
1: exact (conj LW2 (conj LX2 REL2)).
all: try hlia Rzf.
-
unfold nz in HL2. replace (negb (carry =? 0))%Z with true in HL2 by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; flia).

assert (HZ0R__ : (0 <= Z0 < 2 ^ 64)%Z) by (first [ clear - LTX LW HZ0 Re2 Rrp Hfo Rz LX2 LW2 SG3 SG1 SPT SPF SE_T Hp w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; lia | lia ]).
zs. brf K2.
+
replace ((z + 1) mod 2048 =? a1)%Z with false in HL2 by (symmetry; apply Z.eqb_neq; first [ clear - K2 K1 LTX LW HZ0 Re2 Rrp Hfo Rzf Rz Rc1 LX2 LW2 SG3 SG1 SPT SPF SE_T Hp w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO; flia | flia ]). cbn [negb] in HL2.
assert (Hrs : ((z - a1) mod 2048 < 2047)%Z).
{ clear - K2 Ra1 Rz HZ0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. subst Z0. Z.div_mod_to_equations. flia. }
zs. zs. zs. fix_idx.
pose proof (u32arr_store_ok segs _ _ _ z _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ z (Z_to_bv 64 carry) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs.
assert (X31' : X31 (zupd xx z carry)).
{ intros ii. destruct (Z.eq_dec ii z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X312]. }

stash_mods. stash_disj. do 20 zs. unstash. rewrite ?land2047. fix_idx.
destruct (Z.eq_dec z 2047) as [Ez|Hz47].
*
subst Z0. subst z. change ((2047 + 1) mod 2048)%Z with 0%Z in HL2 |- *.
eapply IH with (h := false) (x := zupd xx 2047 carry) (z := 0%Z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia; try mk_dfinv.
1:{ split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros ii Hq Hr.
destruct (Z.eq_dec ii 2047) as [->|Hne].
++ rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
++ rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia|].
destruct Hr as [Hr | [[Hr _] | Hr]]; [left | discriminate Hr | right; right; exact Hr].
unfold inring in Hr |- *. clear - Hr Hne Hq Ra1 K2 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. Z.div_mod_to_equations. flia. }
all: rewrite ?Z.shiftl_mul_pow2 by flia; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia.
* rewrite (Z.mod_small (z + 1) 2048) in HL2, HZ0 by flia. subst Z0.
eapply IH with (h := h) (x := zupd xx z carry) (z := (z + 1)%Z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia; try mk_dfinv.
1:{ split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros ii Hq Hr. destruct (Z.eq_dec ii z) as [->|Hne].
++ rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
++ rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia|].
destruct Hr as [Hr | [[Hh Hzq] | Hr]]; [| right; left; split; [exact Hh | flia] | right; right; exact Hr].
apply (proj1 (inring_grow a1 z ii ltac:(flia) Hrs)) in Hr.
destruct Hr as [Hr|Hr]; [left; exact Hr|]. exfalso. apply Hne. apply (mod_eq_idx a1 z ii); flia. }
all: try hlia Rzf.
all: rewrite ?Z.shiftl_mul_pow2 by flia; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia.
all: try (replace (z + 1 + -1)%Z with z by flia; rewrite (Z.mod_small z 2048) by flia; replace (z + 1 - 1)%Z with z by flia; rewrite (Z.mod_small z 2048) by flia; reflexivity).
+
replace ((z + 1) mod 2048 =? a1)%Z with true in HL2 by (symmetry; apply Z.eqb_eq; flia). cbn [negb] in HL2.
assert (Hrs : ((z - a1) mod 2048 = 2047)%Z).
{ clear - K2 Ra1 Rz HZ0 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. subst Z0. Z.div_mod_to_equations. flia. }
pose proof (Z.mod_pos_bound (z - 1) 2048 ltac:(flia)) as Rkm. set (km := ((z - 1) mod 2048)%Z) in *.
assert (Kin : inring a1 z km).
{ unfold inring. subst km. rewrite Zminus_mod_idemp_l. clear - Hrs Ra1 Rz w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO. Z.div_mod_to_equations. flia. }
pose proof (X312 km) as Rt. pose proof (REL2 km ltac:(flia) (zone_in h _ _ _ _ Kin)) as Et.
pose proof (u32arr_read segs _ _ _ km _ _ XW (nth_error_wnth ws km ltac:(flia) ltac:(flia)) ltac:(flia) ltac:(unfold wa; f_equal; flia)) as RD.
zs. rewrite (sx32_wval ws km (znth xx km) (eq_sym Et) Rt). set (t := znth xx km) in *.
zs.
assert (Rt1 : (0 <= Z.lor t 1 < 2^31)%Z).
{ split; [apply Z.lor_nonneg; flia|]. apply (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2 t 1 31); flia. }
pose proof (u32arr_store_ok segs _ _ _ km _ XW ltac:(flia) ltac:(unfold wa; f_equal; flia)) as SOK.
zs.
pose proof (u32arr_write segs _ _ _ km (Z_to_bv 64 (Z.lor t 1)) XW ltac:(flia)) as XW'. clear XW.
replace (A6 + 0)%Z with (q + -8312 + 4 * km)%Z by flia.
store_done'. rename XW' into XW.
zs.
eapply IH with (h := h) (x := zupd xx km (Z.lor t 1)) (z := z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia; try mk_dfinv.
1:{ split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros ii Hq Hr. destruct (Z.eq_dec ii km) as [->|Hne].
-- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
-- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia | exact Hr]. }
1:{ intros ii. destruct (Z.eq_dec ii km) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X312]. }
all: try hlia Rzf.
Qed.

End Floatscan.

End G.
End Mq3.

Module Mq4.

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
Variables (joff_256 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_197bc e_multf3 e_floatsitf e_divtf3 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_256 : decode_any (Z_to_bv 32 w_256) = Some (Jal 1 joff_256, 4%Z).
Hypothesis E_256 : is_ecall (Z_to_bv 32 w_256) = false.
Hypothesis LINK_256 : gw_anch (base + 1024 + bv_signed joff_256)%Z (e_floatsitf + 0)%Z.
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
Definition fixunstfsi_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Q8l1.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@QQRC.Mq2.fixunstfsi_post segs) fixunstfsi_post gw_tbl_5)))).
Definition floatsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Q8l1.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@QQRC.Mq2.floatsitf_post segs) floatsitf_post gw_tbl_6)))).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Q8l1.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@QQRC.Mq2.floatunsitf_post segs) floatunsitf_post gw_tbl_7)))).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Q8l1.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@QQRC.Mq2.extenddftf2_post segs) extenddftf2_post gw_tbl_8)))).
Definition addtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Q8l1.Mq0.addtf3_post segs) addtf3_post (gw_ent (@QQRC.Mq2.addtf3_post segs) addtf3_post gw_tbl_9)))).
Definition multf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.multf3_post segs) multf3_post (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post (gw_ent (@Q8l1.Mq0.multf3_post segs) multf3_post (gw_ent (@QQRC.Mq2.multf3_post segs) multf3_post gw_tbl_10)))).
Definition multf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Q8l1.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@QQRC.Mq2.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_11)))).
Definition divtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Q8l1.Mq0.divtf3_post segs) divtf3_post (gw_ent (@QQRC.Mq2.divtf3_post segs) divtf3_post gw_tbl_12)))).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@QQRC.Mq2.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_13)))).
Definition letf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QzQg.Mq0.letf2_post segs) letf2_post (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post (gw_ent (@Q8l1.Mq0.letf2_post segs) letf2_post (gw_ent (@QQRC.Mq2.letf2_post segs) letf2_post gw_tbl_14)))).
Definition frexpl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QzQg.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Q8l1.Mq0.frexpl_post segs) frexpl_post (gw_ent (@QQRC.Mq2.frexpl_post segs) frexpl_post gw_tbl_15)))).
Definition signbitl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QzQg.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Q8l1.Mq0.signbitl_post segs) signbitl_post (gw_ent (@QQRC.Mq2.signbitl_post segs) signbitl_post gw_tbl_16)))).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QzQg.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Q8l1.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@QQRC.Mq2.fpclassifyl_post segs) fpclassifyl_post gw_tbl_17)))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_18))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_19).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_20).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_21).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_22).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_23).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_24)).
Local Definition gw_tbl_25 := (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_24).
Definition S_9EC : ltac:(gw_rebind_ty (@QzQg.Mq0.S_9EC segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_9EC segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_25)).
Local Definition gw_tbl_26 := (gw_ent (@QzQg.Mq0.S_9EC segs base got_ssp RATP STRING_READ ssp_guard) S_9EC gw_tbl_25).
Definition S_A64 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_A64 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_A64 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_26)).
Local Definition gw_tbl_27 := (gw_ent (@QzQg.Mq0.S_A64 segs base got_ssp RATP STRING_READ ssp_guard) S_A64 gw_tbl_26).
Definition S_7F4 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_7F4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_7F4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_27)).
Local Definition gw_tbl_28 := (gw_ent (@QzQg.Mq0.S_7F4 segs base got_ssp RATP STRING_READ ssp_guard) S_7F4 gw_tbl_27).
Definition S_9C8 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_9C8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_9C8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QzQg.Mq0.S_9C8 segs base got_ssp RATP STRING_READ ssp_guard) S_9C8 gw_tbl_28).
Definition SLZn : ltac:(gw_rebind_ty (@QzQg.Mq0.SLZn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QzQg.Mq0.SLZn segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QzQg.Mq0.SLZn segs base got_ssp RATP STRING_READ ssp_guard) SLZn gw_tbl_29).
Definition S_LZ : ltac:(gw_rebind_ty (@QzQg.Mq0.S_LZ segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_LZ segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_30)).
Local Definition gw_tbl_31 := (gw_ent (@QzQg.Mq0.S_LZ segs base got_ssp RATP STRING_READ ssp_guard) S_LZ gw_tbl_30).
Definition S_990 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_990 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_31)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_990 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_31)).
Local Definition gw_tbl_32 := (gw_ent (@QzQg.Mq0.S_990 segs base got_ssp RATP STRING_READ ssp_guard) S_990 gw_tbl_31).
Definition S_848 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_848 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_32)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_848 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_32)).
Local Definition gw_tbl_33 := (gw_ent (@QzQg.Mq0.S_848 segs base got_ssp RATP STRING_READ ssp_guard) S_848 gw_tbl_32).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_33)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_33)).
Local Definition gw_tbl_34 := (gw_ent (@QzQg.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Q8l1.Mq0.leaf2_post segs) leaf2_post (gw_ent (@QQRC.Mq2.leaf2_post segs) leaf2_post gw_tbl_33)))).

Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_34))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_34))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast_lt) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_34))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast_lt _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_34))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_getc : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_getc) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_34))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_getc _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_unget : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_unget) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_34))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_unget _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_unget_eq : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_eq) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_34))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).
Hypothesis rf_unget_nop : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_unget_nop) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_34))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).
Hypothesis shgetc_callJ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.shgetc_callJ) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_34))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments shgetc_callJ _%_bv_scope _%_Z_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope _%_Z_scope _%_Z_scope _ _%_Z_scope _%_Z_scope _ _%_list_scope _%_list_scope _%_list_scope _%_bv_scope.
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
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

Definition floatsitf_callp : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callp) constr:(gw_tbl_34)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callp)).

Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Notation F_floatscan_common__SLZn := SLZn (only parsing).
Notation F_floatscan_common__S_7F4 := S_7F4 (only parsing).
Notation F_floatscan_common__S_848 := S_848 (only parsing).
Notation F_floatscan_common__S_990 := S_990 (only parsing).
Notation F_floatscan_common__S_9C8 := S_9C8 (only parsing).
Notation F_floatscan_common__S_9EC := S_9EC (only parsing).
Notation F_floatscan_common__S_A64 := S_A64 (only parsing).
Notation F_floatscan_common__S_LZ := S_LZ (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__txt_char : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.txt_char) constr:(gw_tbl_34)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.txt_char)).
Notation F_floatscan_common__winv := winv (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_34)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard e_197bc e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_256 E_256 LINK_256 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ floatsitf_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_256 got_ssp RATP STRING_READ ssp_guard e_197bc e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_256 E_256 LINK_256 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ floatsitf_spec.

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

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).
Local Notation txt_char := (@F_floatscan_common__txt_char txt BYT).

Local Notation winv := (@F_floatscan_common__winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

Local Notation S_9EC := (@F_floatscan_common__S_9EC ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A64 := (@F_floatscan_common__S_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_7F4 := (@F_floatscan_common__S_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_9C8 := (@F_floatscan_common__S_9C8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_LZ := (@F_floatscan_common__S_LZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_990 := (@F_floatscan_common__S_990 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_848 := (@F_floatscan_common__S_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_9EC : S_9EC.
Hypothesis HS_A64 : S_A64.
Hypothesis HS_7F4 : S_7F4.

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
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_9EC HS_A64 HS_7F4. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_9EC | gw_hide HS_9EC | idtac]; first [clear HS_A64 | gw_hide HS_A64 | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac]. clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma getc_rpos2 : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_9EC HS_A64 HS_7F4. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide BYT; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_9EC | gw_hide HS_9EC | idtac]; first [clear HS_A64 | gw_hide HS_A64 | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac].
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

#[using="Type"] Lemma RFJ_rechar : forall k c c' f, RFJ' k c f -> (-1 <= c' < 256)%Z -> (sh_stdio f = false -> sh_rpos f <= p)%Z -> RFJ' k c' f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_9EC HS_A64 HS_7F4. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_9EC | gw_hide HS_9EC | idtac]; first [clear HS_A64 | gw_hide HS_A64 | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac].
clear. intros k c c' f (OK & Rc & CC & KM & NS & SS) Hc' Hp'. unfold RFJ.
split; [exact OK|]. split; [exact Hc'|]. split; [exact CC|]. split; [exact KM|]. split; [|exact SS].
intros E. destruct (NS E) as (N1 & N2 & N3). split; [exact N1|]. split; [exact N2|]. intros _. exact (Hp' E).
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64"] Lemma L_9C8 : S_9C8.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok Hnum SE_T FRM HS_7F4. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear Hnum | gw_hide Hnum | idtac]; try gw_hide SE_T; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac].
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
-
assert (N46 : c <> 46%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ; Z.div_mod_to_equations; lia).
unfold dfK_rz in HK. replace (c =? 46)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N46). cbv beta iota in HK.
stmt HS_A64. eapply NX; try eassumption; try lia. mk_winv2.
- assert (E46 : c = 46%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ; Z.div_mod_to_equations; lia).
unfold dfK_rz in HK. rewrite E46, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK.
destruct (df_rz_loop fuelc _) as [[[[g2 l2] c3] f3]|] eqn:HRZ; [|discriminate HK]. cbv beta iota in HK.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ ltac:(lia)) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].

assert (JOIN : forall m2 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 sign) (Z_to_bv 64 (fst (sh_getc f))) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 1) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 (base + 0x588)) fct None m2 (seg_rom segs))).
{ intros until x31'. intros WI2.
stmt HS_9EC. eapply NX with (gotdig := 1%Z) (kmin := (kmin + 1)%Z); try eassumption; try lia. }
clear HK HRZ.
zs.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
+ pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs. call_shgetc FC0 RJ SLOW Hst.
eapply JOIN. mk_winv2.
+ pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K2; [ | exfalso; lia ]).
zs. zs0. read_char f. zs.
eapply JOIN. mk_winv2.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64"] Lemma L_LZ : S_LZ.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok Hnum SE_T FRM HS_7F4. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear Hnum | gw_hide Hnum | idtac]; try gw_hide SE_T; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac].
unfold F_floatscan_common__S_LZ. induction n as [|n IH].
{ intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst HL HK. discriminate HL. }
intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst HL HK.
dest_winv WI. bury_disj.
rewrite df_lz_loop_step in HL. rewrite Z.eqb_refl in HL.
site_facts FC RJ kmin 48%Z f.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
assert (HEAD : forall m2 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
fst (sh_getc f) = 48%Z ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 sign) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 (base + 0x548)) fct None m2 (seg_rom segs))).
{ intros until x31'. intros WI2 E48. rewrite E48 in RJ1, HL.
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 w8 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws sign (kmin + 1)%Z (snd (sh_getc f)) 1%Z g' c' f');
try eassumption; try lia. }
assert (EXIT : forall m2 (x1' x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
fst (sh_getc f) <> 48%Z ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 sign) (Z_to_bv 64 (fst (sh_getc f))) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 (base + 0x564)) fct None m2 (seg_rom segs))).
{ intros until x31'. intros WI2 N48.
assert (E : (g', c', f') = (1%Z, fst (sh_getc f), snd (sh_getc f))).
{ clear - HL N48 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ. destruct n as [|n2]; [discriminate HL|]. rewrite df_lz_loop_step in HL.
replace (fst (sh_getc f) =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <-. reflexivity. }
injection E as -> -> ->. clear HL.
stmt L_9C8. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try lia. }
clear HL HK IH.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
- pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RJ SLOW Hst.
set (c'' := fst (sh_getc f)) in *.
zs. brf K2; rewrite ?land_W64 in K2.
+ eapply EXIT; [mk_winv2 | clear - K2 Rc' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ; Z.div_mod_to_equations; lia].
+ eapply HEAD; [mk_winv2 | clear - K2 Rc' w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ; Z.div_mod_to_equations; lia].
- pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
zs. brf K2; rewrite ?land_W64 in K2.
+ eapply HEAD; [mk_winv2 | exact K2].
+ eapply EXIT; [mk_winv2 | exact K2].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64"] Lemma L_990 : S_990.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok Hnum SE_T FRM HS_7F4. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear Hnum | gw_hide Hnum | idtac]; try gw_hide SE_T; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac].
intros n m; intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 HL HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (E48 : c = 48%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ; Z.div_mod_to_equations; lia). rewrite E48 in RJ, HL.
pose proof L_LZ as NX. unfold F_floatscan_common__S_LZ, F_floatscan_common__SLZn in NX. eapply (NX n); try eassumption; try lia. mk_winv2.
- assert (N48 : c <> 48%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ; Z.div_mod_to_equations; lia).
assert (E : (g', c', f') = (1%Z, c, f)).
{ clear - HL N48 w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ. destruct n as [|n2]; [discriminate HL|]. rewrite df_lz_loop_step in HL.
replace (c =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <-. reflexivity. }
injection E as -> -> ->. clear HL.
zs. stmt L_9C8. eapply NX; try eassumption; try lia. mk_winv2.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_256 e_floatsitf CODE BASE4 BASER D_256 E_256 LINK_256 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ floatsitf_spec ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64"] Lemma L_848 : S_848.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_256 e_floatsitf CODE BASE4 BASER D_256 E_256 LINK_256 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc RFI_unget rf_unget_eq rf_unget_nop shgetc_callJ floatsitf_spec ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok Hnum SE_T FRM HS_7F4. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear Hnum | gw_hide Hnum | idtac]; try gw_hide SE_T; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac].
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
rewrite (decfloat_split fuelc 53 (-1074) sign pok) in HK.
destruct fuelc as [|fu] eqn:Efu in HK; [discriminate HK|]. rewrite df_lz_loop_step, Z.eqb_refl in HK.
set (g := sh_unget f) in *.
destruct (df_lz_loop fu _) as [[[g' c'] f']|] eqn:HL; [|discriminate HK].
assert (Hg : RFJ' (kmin - 1) 48 g /\ sh_stdio g = sh_stdio f0 /\ sh_buf g = txt).
{ subst g. split; [|split; [unfold sh_unget; destruct (sh_shlim_neg f); exact Hst | unfold sh_unget; destruct (sh_shlim_neg f); exact Hbuf]].
apply (RFJ_rechar (kmin - 1) c); [apply (RFI_unget T txt p J Hp kmin c f RJ); lia | lia |].
intros E. rewrite (rf_unget_eq f (proj1 (NS ltac:(unfold sh_unget in E; destruct (sh_shlim_neg f); exact E)))). cbn.
destruct (NS ltac:(unfold sh_unget in E; destruct (sh_shlim_neg f); exact E)) as (_ & N2 & _). lia. }
destruct Hg as (RJg & Hstg & Hbufg).

assert (CONT : forall m2 (x10' : word),
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws g ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (T + sh_rpos g)) (Z_to_bv 64 sign) x10' x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x3f8)) fct None m2 (seg_rom segs))).
{ intros m2 x10' WI2. clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW FC FI FL BFC.
pose proof WI2 as WI3. dest_winv WI3.
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC.
pose proof (RFI_rpos T txt p J Hp (kmin - 1) 48 g RJg) as Rrpg.
assert (RRg : (0 <= rf_rend T p true g <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio g); unfold zlength in *; lia). unfold M64 in RRg.
pose proof (RFI_getc T txt p J BYT Hp Hnul (kmin - 1) 48 g RJg ltac:(lia)) as RJ1.
pose proof (getc_stdio g) as Hst1. rewrite Hstg in Hst1.
assert (Rc' : (-1 <= fst (sh_getc g) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 g Hbufg) as [Rrp1 Rrp2].
zs. replace (Z_to_bv 64 (-18446744073709550542)) with (Z_to_bv 64 1074) by (apply Z_to_bv_eqm; reflexivity).
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]). fold zero0.
pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.

assert (JOIN : forall m3 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x19' x28' x29' x30' x31' : word),
winv m3 j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc g)) ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 sign) (Z_to_bv 64 (fst (sh_getc g))) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19' (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 (base + 0x52c)) fct None m3 (seg_rom segs))).
{ intros until x31'. intros WI4.
stmt L_990. eapply (NX fu) with (kmin := (kmin - 1 + 1)%Z); try eassumption; try lia.
all: try (intros Hn1; specialize (Rrp2 Hn1); lia). rewrite Efu. exact HK. }
zs.
destruct (Z.eq_dec (T + sh_rpos g)%Z (rf_rend T p true g)) as [SLOW|FAST].
+ pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RJg SLOW Hstg.
eapply JOIN. mk_winv2.
+ pose proof (rf_getc_fast_lt T txt p J Hp (kmin - 1) 48 g RJg ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp (kmin - 1) 48 g RJg FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos g) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0. read_char g. zs.
eapply JOIN. mk_winv2. }

pose proof FC as FC0. ufc2 FC.
destruct (sh_shlim_neg f) eqn:SN; unfold M64 in FC.
-
assert (Eg : g = f) by (subst g; apply rf_unget_nop; exact SN).
zs. zs. zs. (brf K0; [ | exfalso; lia ]).
replace (Z_to_bv 64 (T + sh_rpos f)) with (Z_to_bv 64 (T + sh_rpos g)) by (rewrite Eg; reflexivity).
eapply CONT. rewrite Eg. mk_winv2.
- assert (Eg : g = mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) by (subst g; apply rf_unget_eq; exact SN).
clear FC0.
zs. zs. zs. (brf K0; [ exfalso; lia | ]).
zs. zs0.
replace (Z_to_bv 64 (T + sh_rpos f + -1)) with (Z_to_bv 64 (T + sh_rpos g)) by (rewrite Eg; cbn [sh_rpos]; f_equal; lia).
eapply CONT. rewrite Eg. unfold F_floatscan_common__winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite SN. unfold rf_rend in FC. hyp_cells.
Qed.

End Floatscan.

End G.
End Mq4.

Module Mq5.

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
Variables (joff_170 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_197bc e_multf3 e_floatsitf e_divtf3 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_170 : decode_any (Z_to_bv 32 w_170) = Some (Jal 1 joff_170, 4%Z).
Hypothesis E_170 : is_ecall (Z_to_bv 32 w_170) = false.
Hypothesis LINK_170 : gw_anch (base + 680 + bv_signed joff_170)%Z (e_floatsitf + 0)%Z.
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
Definition fixunstfsi_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QzQg.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Q8l1.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@QQRC.Mq2.fixunstfsi_post segs) fixunstfsi_post gw_tbl_5)))).
Definition floatsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QzQg.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Q8l1.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@QQRC.Mq2.floatsitf_post segs) floatsitf_post gw_tbl_6)))).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QzQg.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Q8l1.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@QQRC.Mq2.floatunsitf_post segs) floatunsitf_post gw_tbl_7)))).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.extenddftf2_post segs) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QzQg.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Q8l1.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@QQRC.Mq2.extenddftf2_post segs) extenddftf2_post gw_tbl_8)))).
Definition addtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QzQg.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Q8l1.Mq0.addtf3_post segs) addtf3_post (gw_ent (@QQRC.Mq2.addtf3_post segs) addtf3_post gw_tbl_9)))).
Definition multf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QzQg.Mq0.multf3_post segs) multf3_post (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post (gw_ent (@Q8l1.Mq0.multf3_post segs) multf3_post (gw_ent (@QQRC.Mq2.multf3_post segs) multf3_post gw_tbl_10)))).
Definition multf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QzQg.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Q8l1.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@QQRC.Mq2.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_11)))).
Definition divtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QzQg.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Q8l1.Mq0.divtf3_post segs) divtf3_post (gw_ent (@QQRC.Mq2.divtf3_post segs) divtf3_post gw_tbl_12)))).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QzQg.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@QQRC.Mq2.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_13)))).
Definition letf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QzQg.Mq0.letf2_post segs) letf2_post (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post (gw_ent (@Q8l1.Mq0.letf2_post segs) letf2_post (gw_ent (@QQRC.Mq2.letf2_post segs) letf2_post gw_tbl_14)))).
Definition frexpl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QzQg.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Q8l1.Mq0.frexpl_post segs) frexpl_post (gw_ent (@QQRC.Mq2.frexpl_post segs) frexpl_post gw_tbl_15)))).
Definition signbitl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QzQg.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Q8l1.Mq0.signbitl_post segs) signbitl_post (gw_ent (@QQRC.Mq2.signbitl_post segs) signbitl_post gw_tbl_16)))).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QzQg.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Q8l1.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@QQRC.Mq2.fpclassifyl_post segs) fpclassifyl_post gw_tbl_17)))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QzQg.Mq0.RFJ STRING_READ) RFJ (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_18))).
Definition RERRNO : ltac:(gw_rebind_ty (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QzQg.Mq0.RERRNO RATP) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QzQg.Mq0.RERRNO RATP) RERRNO gw_tbl_19).
Definition Wfs : ltac:(gw_rebind_ty (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QzQg.Mq0.Wfs RATP) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@QzQg.Mq0.Wfs RATP) Wfs gw_tbl_20).
Definition fs_post : ltac:(gw_rebind_ty (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@QzQg.Mq0.fs_post segs got_ssp RATP STRING_READ ssp_guard) fs_post gw_tbl_21).
Definition finv : ltac:(gw_rebind_ty (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@QzQg.Mq0.finv segs got_ssp RATP ssp_guard) finv gw_tbl_22).
Definition framL : ltac:(gw_rebind_ty (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QzQg.Mq0.framL segs RATP) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@QzQg.Mq0.framL segs RATP) framL gw_tbl_23).
Definition winv : ltac:(gw_rebind_ty (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) constr:(gw_tbl_24)).
Local Definition gw_tbl_25 := (gw_ent (@QzQg.Mq0.winv segs got_ssp RATP ssp_guard) winv gw_tbl_24).
Definition S_9EC : ltac:(gw_rebind_ty (@QzQg.Mq0.S_9EC segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_9EC segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_25)).
Local Definition gw_tbl_26 := (gw_ent (@QzQg.Mq0.S_9EC segs base got_ssp RATP STRING_READ ssp_guard) S_9EC gw_tbl_25).
Definition S_7F4 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_7F4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_7F4 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_26)).
Local Definition gw_tbl_27 := (gw_ent (@QzQg.Mq0.S_7F4 segs base got_ssp RATP STRING_READ ssp_guard) S_7F4 gw_tbl_26).
Definition S_848 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_848 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_848 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_27)).
Local Definition gw_tbl_28 := (gw_ent (@QzQg.Mq0.S_848 segs base got_ssp RATP STRING_READ ssp_guard) S_848 gw_tbl_27).
Definition S_6F8 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_6F8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_6F8 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@QzQg.Mq0.S_6F8 segs base got_ssp RATP STRING_READ ssp_guard) S_6F8 gw_tbl_28).
Definition S_618 : ltac:(gw_rebind_ty (@QzQg.Mq0.S_618 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@QzQg.Mq0.S_618 segs base got_ssp RATP STRING_READ ssp_guard) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@QzQg.Mq0.S_618 segs base got_ssp RATP STRING_READ ssp_guard) S_618 gw_tbl_29).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_30)).
Local Definition gw_tbl_31 := (gw_ent (@QzQg.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Q8l1.Mq0.leaf2_post segs) leaf2_post (gw_ent (@QQRC.Mq2.leaf2_post segs) leaf2_post gw_tbl_30)))).

Hypothesis RFI_rpos : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_rpos) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_rpos _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_fast_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_fast_lt) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_fast_lt _%_Z_scope _%_list_scope _%_Z_scope _ _ _%_Z_scope _%_Z_scope.
Hypothesis rf_getc_slow : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.rf_getc_slow) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments rf_getc_slow _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis RFI_getc : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.RFI_getc) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments RFI_getc _%_Z_scope _%_list_scope _%_Z_scope _ _ _ _ _%_Z_scope _%_Z_scope.
Hypothesis shgetc_callJ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mql.gw_all) (@QZxv.Mql.shgetc_callJ) (base + -544)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in let T := gw_fold_pcs T base (-544)%Z [0; 56; 256; 396]%Z in exact T).  Arguments shgetc_callJ _%_bv_scope _%_Z_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope _%_Z_scope _%_Z_scope _ _%_Z_scope _%_Z_scope _ _%_list_scope _%_list_scope _%_list_scope _%_bv_scope.
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
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

Definition floatsitf_callp : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callp) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callp)).

Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Notation F_floatscan_common__S_618 := S_618 (only parsing).
Notation F_floatscan_common__S_6F8 := S_6F8 (only parsing).
Notation F_floatscan_common__S_7F4 := S_7F4 (only parsing).
Notation F_floatscan_common__S_848 := S_848 (only parsing).
Notation F_floatscan_common__S_9EC := S_9EC (only parsing).
Notation F_floatscan_common__Wfs := Wfs (only parsing).
Notation F_floatscan_common__finv := finv (only parsing).
Notation F_floatscan_common__framL := framL (only parsing).
Notation F_floatscan_common__fs_post := fs_post (only parsing).
Definition F_floatscan_common__txt_char : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.txt_char) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.txt_char)).
Notation F_floatscan_common__winv := winv (only parsing).
Definition F_floatscan_common__zbytes_len : ltac:(gw_ctx_fold_ty (@QzQg.Mq0.zbytes_len) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@QzQg.Mq0.zbytes_len)).

#[using="got_ssp RATP STRING_READ ssp_guard e_197bc e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_170 got_ssp RATP STRING_READ ssp_guard e_197bc e_multf3 e_floatsitf e_divtf3 CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec.

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

Local Notation fs_post := (@F_floatscan_common__fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@F_floatscan_common__zbytes_len txt).
Local Notation txt_char := (@F_floatscan_common__txt_char txt BYT).

Local Notation winv := (@F_floatscan_common__winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

Local Notation S_9EC := (@F_floatscan_common__S_9EC ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_7F4 := (@F_floatscan_common__S_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_848 := (@F_floatscan_common__S_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_6F8 := (@F_floatscan_common__S_6F8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
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

Hypothesis HS_9EC : S_9EC.
Hypothesis HS_7F4 : S_7F4.
Hypothesis HS_848 : S_848.

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
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_9EC HS_7F4 HS_848. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_9EC | gw_hide HS_9EC | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac]; first [clear HS_848 | gw_hide HS_848 | idtac]. clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma getc_rpos2 : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_9EC HS_7F4 HS_848. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; try gw_hide BYT; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_9EC | gw_hide HS_9EC | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac]; first [clear HS_848 | gw_hide HS_848 | idtac].
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

#[using="Type"] Lemma RFJ_rechar : forall k c c' f, RFJ' k c f -> (-1 <= c' < 256)%Z -> (sh_stdio f = false -> sh_rpos f <= p)%Z -> RFJ' k c' f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_9EC HS_7F4 HS_848. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_9EC | gw_hide HS_9EC | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac]; first [clear HS_848 | gw_hide HS_848 | idtac].
clear. intros k c c' f (OK & Rc & CC & KM & NS & SS) Hc' Hp'. unfold RFJ.
split; [exact OK|]. split; [exact Hc'|]. split; [exact CC|]. split; [exact KM|]. split; [|exact SS].
intros E. destruct (NS E) as (N1 & N2 & N3). split; [exact N1|]. split; [exact N2|]. intros _. exact (Hp' E).
Qed.

#[using="Hnul Hnum"] Lemma getc_fch : forall kmin c f, RFJ' kmin c f -> c <> 0%Z -> fch (fst (sh_getc f)).
Proof. clear - Hnul Hnum ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_9EC HS_7F4 HS_848. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_9EC | gw_hide HS_9EC | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac]; first [clear HS_848 | gw_hide HS_848 | idtac].
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
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_9EC HS_7F4 HS_848. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_9EC | gw_hide HS_9EC | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac]; first [clear HS_848 | gw_hide HS_848 | idtac].
clear. intros P n H c Hc. apply (proj1 (forallb_forall P _) H). apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
#[using="Type"] Lemma numch_range : forall c, is_numch c = true -> (0 <= c < 256)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_9EC HS_7F4 HS_848. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_9EC | gw_hide HS_9EC | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac]; first [clear HS_848 | gw_hide HS_848 | idtac].
clear. intros c N. unfold is_numch in N.
repeat (apply Bool.orb_true_iff in N; destruct N as [N|N]); try (apply Z.eqb_eq in N; lia).
apply andb_true_iff in N. destruct N as [N1 N2]. apply Z.leb_le in N1. apply Z.leb_le in N2. lia.
Qed.
#[using="Type"] Lemma fch_ok_true : forall c, fch c -> fch_ok c = true.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_9EC HS_7F4 HS_848. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_9EC | gw_hide HS_9EC | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac]; first [clear HS_848 | gw_hide HS_848 | idtac].
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
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_9EC HS_7F4 HS_848. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_9EC | gw_hide HS_9EC | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac]; first [clear HS_848 | gw_hide HS_848 | idtac].
clear. intros c H. pose proof (fch_ok_true c H) as E. unfold fch_ok in E.
repeat (apply andb_true_iff in E; destruct E as [E ?X]).
repeat match goal with H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H end.
repeat match goal with H : (_ =? _)%Z = false |- _ => apply Z.eqb_neq in H end.
apply Z.leb_le in X.
repeat split; assumption.
Qed.
#[using="Type"] Lemma fch_range : forall c, fch c -> (-1 <= c < 256)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_9EC HS_7F4 HS_848. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_9EC | gw_hide HS_9EC | idtac]; first [clear HS_7F4 | gw_hide HS_7F4 | idtac]; first [clear HS_848 | gw_hide HS_848 | idtac]. clear. intros c [N | [-> | ->]]; [pose proof (numch_range c N); lia | lia | lia]. Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_170 e_floatsitf CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_7F4"] Lemma L_6F8 : S_6F8.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_170 e_floatsitf CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok Hnum SE_T FRM HS_848. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear Hnum | gw_hide Hnum | idtac]; try gw_hide SE_T; first [clear FRM | gw_hide FRM | idtac]; first [clear HS_848 | gw_hide HS_848 | idtac].
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
rewrite (decfloat_split fuelc 53 (-1074) sign pok) in HK.
assert (HK' : dfK_rz fuelc 53 (-1074) sign pok 0 c f = Some (fR, yR)).
{ clear - HK Hne w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_170 e_floatsitf CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec. destruct fuelc as [|fu] eqn:Efu in HK; [discriminate HK|].
rewrite df_lz_loop_step in HK. replace (c =? 48)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne). cbv iota in HK.
rewrite <- Efu in HK. exact HK. }
clear HK. rename HK' into HK.
zs. replace (Z_to_bv 64 (-18446744073709550542)) with (Z_to_bv 64 1074) by (apply Z_to_bv_eqm; reflexivity).
zs. try replace (Z_to_bv 64 (1074 + -53)) with (Z_to_bv 64 1021) by reflexivity.
zs. zs. zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]). fold zero0.
pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
zs. zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (N46 : c <> 46%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_170 e_floatsitf CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec; Z.div_mod_to_equations; lia).
unfold dfK_rz in HK. replace (c =? 46)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N46). cbv beta iota in HK.
stmt HS_7F4. eapply NX; try eassumption; try lia. mk_winv2.
- assert (E46 : c = 46%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_170 e_floatsitf CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec; Z.div_mod_to_equations; lia).
unfold dfK_rz in HK. rewrite E46, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK.
destruct (df_rz_loop fuelc _) as [[[[g2 l2] c3] f3]|] eqn:HRZ; [|discriminate HK]. cbv beta iota in HK.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ ltac:(lia)) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
assert (JOIN : forall m2 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 sign) (Z_to_bv 64 (fst (sh_getc f))) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 (base + 0x588)) fct None m2 (seg_rom segs))).
{ intros until x31'. intros WI2.
stmt HS_9EC. eapply NX with (gotdig := 0%Z) (kmin := (kmin + 1)%Z); try eassumption; try lia.
all: try (intros Hn1; specialize (Rrp2 Hn1); lia). }
clear HK HRZ.
zs.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
+ pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K2; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RJ SLOW Hst.
eapply JOIN. mk_winv2.
+ pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs0. read_char f. zs.
eapply JOIN. mk_winv2.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_170 e_floatsitf CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_7F4 HS_848"] Lemma L_618 : S_618.
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_170 e_floatsitf CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_7F4 HS_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok SE_T FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; try gw_hide SE_T; first [clear FRM | gw_hide FRM | idtac].
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
unfold QzQg.Mq0.FS_tail in HK.
zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (N48 : c <> 48%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_170 e_floatsitf CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec; Z.div_mod_to_equations; lia).
replace (c =? 48)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N48).
stmt L_6F8. eapply NX; try eassumption; try lia. mk_winv2.
- assert (E48 : c = 48%Z) by (clear - K1 Rc w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_170 e_floatsitf CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec; Z.div_mod_to_equations; lia).
rewrite E48, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK. rewrite E48 in RJ.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
pose proof (getc_fch kmin 48 f RJ ltac:(lia)) as FCH.
replace (Z.lor (fst (sh_getc f)) 32 =? 120)%Z with false in HK
by (destruct (fch_facts _ FCH) as (_ & _ & _ & _ & _ & _ & _ & _ & L120 & _); symmetry; apply Z.eqb_neq; exact L120).
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
assert (JOIN : forall m2 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
evt segs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8 (Z_to_bv 64 sign) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 (base + 0x3e4)) fct None m2 (seg_rom segs))).
{ intros until x31'. intros WI2.
stmt HS_848. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try lia. }
clear HK.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
+ pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K2; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RJ SLOW Hst.
set (c'' := fst (sh_getc f)) in *.
zs. zs. zs. brf K3.
* exfalso. clear - K3 FCH w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_170 e_floatsitf CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec. destruct (fch_facts _ FCH) as (A73 & A78 & A88 & B73 & B78 & B88 & _). first [exact (A88 K3) | exact (B88 K3)].
* eapply JOIN. mk_winv2.
+ pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. zs. brf K3.
* eapply JOIN. mk_winv2.
* exfalso. clear - K3 FCH w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_170 e_floatsitf CODE BASE4 BASER D_170 E_170 LINK_170 RNG_got_ssp RNG_ssp_guard LAY_lo_ssp_guard LAY_RATP_ssp_guard LAY_got_ssp_RERRNO RFI_rpos rf_getc_fast rf_getc_fast_lt rf_getc_slow RFI_getc shgetc_callJ floatsitf_spec. destruct (fch_facts _ FCH) as (A73 & A78 & A88 & B73 & B78 & B88 & _). first [exact (A88 K3) | exact (B88 K3)].
Qed.

End Floatscan.

End G.
End Mq5.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QlEo_c1 Q2qa Q4J3 QytA Qnxq QJE4 QWTl QPjm QUZl Q7S0 QGeV QLsg QkQT QlkP QyjG QM7w QNAo Q8QT QDXD QULt Q6q3 G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QyjG QM7w QNAo.Mq0.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import QROt.Mq3.
Import QZxv.Mqo.
Import QzQg.
Import Q5m9.Mq2.
Import QZxv.Mqn.
Import QzQg.Mq3.

Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rvm_wait_entry : Z).
Variables (w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 : Z).
Variables (hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 : bv 20).
Variables (lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 : bv 12).
Variables (joff_427 joff_552 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (alloc_slot_code w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2212.
Let ralloc_meta_entry := (base + -1608)%Z.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 10 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Load SZ8 true 20 10 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (Auipc 11 hi_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (OpImm ALU_ADD 22 11 lo_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_114 : decode_any (Z_to_bv 32 w_114) = Some (Auipc 11 hi_114, 4%Z).
Hypothesis E_114 : is_ecall (Z_to_bv 32 w_114) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (OpImm ALU_ADD 11 11 lo_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_121 : decode_any (Z_to_bv 32 w_121) = Some (Auipc 10 hi_121, 4%Z).
Hypothesis E_121 : is_ecall (Z_to_bv 32 w_121) = false.
Hypothesis D_122 : decode_any (Z_to_bv 32 w_122) = Some (OpImm ALU_ADD 25 10 lo_122, 4%Z).
Hypothesis E_122 : is_ecall (Z_to_bv 32 w_122) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Auipc 11 hi_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_131 : decode_any (Z_to_bv 32 w_131) = Some (Load SZ8 true 11 11 lo_131, 4%Z).
Hypothesis E_131 : is_ecall (Z_to_bv 32 w_131) = false.
Hypothesis D_136 : decode_any (Z_to_bv 32 w_136) = Some (Auipc 13 hi_136, 4%Z).
Hypothesis E_136 : is_ecall (Z_to_bv 32 w_136) = false.
Hypothesis D_137 : decode_any (Z_to_bv 32 w_137) = Some (OpImm ALU_ADD 13 13 lo_137, 4%Z).
Hypothesis E_137 : is_ecall (Z_to_bv 32 w_137) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (Auipc 13 hi_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (OpImm ALU_ADD 13 13 lo_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Auipc 13 hi_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis D_220 : decode_any (Z_to_bv 32 w_220) = Some (OpImm ALU_ADD 13 13 lo_220, 4%Z).
Hypothesis E_220 : is_ecall (Z_to_bv 32 w_220) = false.
Hypothesis D_311 : decode_any (Z_to_bv 32 w_311) = Some (Auipc 14 hi_311, 4%Z).
Hypothesis E_311 : is_ecall (Z_to_bv 32 w_311) = false.
Hypothesis D_313 : decode_any (Z_to_bv 32 w_313) = Some (OpImm ALU_ADD 14 14 lo_313, 4%Z).
Hypothesis E_313 : is_ecall (Z_to_bv 32 w_313) = false.
Hypothesis D_427 : decode_any (Z_to_bv 32 w_427) = Some (Jal 1 joff_427, 4%Z).
Hypothesis E_427 : is_ecall (Z_to_bv 32 w_427) = false.
Hypothesis D_552 : decode_any (Z_to_bv 32 w_552) = Some (Jal 1 joff_552, 4%Z).
Hypothesis E_552 : is_ecall (Z_to_bv 32 w_552) = false.
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z RGOT_SSP.
Hypothesis ANCH_19 : gw_anch (Z.shiftl (bv_signed hi_18) 12 + (base + 72) + bv_signed lo_19)%Z (RATP + 131960).
Hypothesis ANCH_116 : gw_anch (Z.shiftl (bv_signed hi_114) 12 + (base + 456) + bv_signed lo_116)%Z RDEBRUIJN.
Hypothesis ANCH_122 : gw_anch (Z.shiftl (bv_signed hi_121) 12 + (base + 484) + bv_signed lo_122)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_131 : gw_anch (Z.shiftl (bv_signed hi_130) 12 + (base + 520) + bv_signed lo_131)%Z (RATP + 131776).
Hypothesis ANCH_137 : gw_anch (Z.shiftl (bv_signed hi_136) 12 + (base + 544) + bv_signed lo_137)%Z (RDEBRUIJN + 128).
Hypothesis ANCH_149 : gw_anch (Z.shiftl (bv_signed hi_148) 12 + (base + 592) + bv_signed lo_149)%Z (RDEBRUIJN + 155).
Hypothesis ANCH_220 : gw_anch (Z.shiftl (bv_signed hi_218) 12 + (base + 872) + bv_signed lo_220)%Z RDEBRUIJN.
Hypothesis ANCH_313 : gw_anch (Z.shiftl (bv_signed hi_311) 12 + (base + 1244) + bv_signed lo_313)%Z (RDEBRUIJN + 32).
Hypothesis LINK_427 : gw_anch (base + 1708 + bv_signed joff_427)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_552 : gw_anch (base + 2208 + bv_signed joff_552)%Z (e_197bc + 0)%Z.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QzQg.Mq3.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QQRC.Mq4.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_0))))).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QzQg.Mq3.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QQRC.Mq4.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_1))))).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QzQg.Mq3.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QQRC.Mq4.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_2)))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QzQg.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QZxv.Mqn.rarea_rep segs) (@rarea_rep) (gw_ent (@Q5m9.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QzQg.rarea_rep segs) (@rarea_rep) (gw_ent (@QZxv.Mqo.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_3))))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QzQg.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QZxv.Mqn.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q5m9.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QzQg.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QZxv.Mqo.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_4))))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QzQg.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QZxv.Mqn.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q5m9.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QzQg.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QZxv.Mqo.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_5))))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QzQg.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QZxv.Mqn.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q5m9.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QzQg.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QZxv.Mqo.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_6))))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QzQg.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QZxv.Mqn.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q5m9.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QzQg.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QZxv.Mqo.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_7))))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QzQg.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QZxv.Mqn.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q5m9.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QzQg.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QZxv.Mqo.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_8))))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QzQg.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QZxv.Mqn.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q5m9.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QzQg.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QZxv.Mqo.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_9))))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QzQg.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QZxv.Mqn.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q5m9.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QzQg.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QZxv.Mqo.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_10))))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QzQg.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QZxv.Mqn.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q5m9.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QzQg.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QZxv.Mqo.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_11))))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QzQg.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QZxv.Mqn.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q5m9.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QzQg.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QZxv.Mqo.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_12))))))))))))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QzQg.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QzQg.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq4.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_13))))))))).
Definition ras_post2 : ltac:(gw_rebind_ty (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) gw_tbl_14).
Definition ram_post : ltac:(gw_rebind_ty (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@QQRC.Mq4.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) (gw_ent (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) gw_tbl_15)).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_16)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_17 := (gw_ent (@QzQg.rimplT segs RC__) (@rimplT) (gw_ent (@QQRC.Mq4.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_16))))).
Definition ralloc_meta_stmt : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@QQRC.Mq4.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) (@ralloc_meta_stmt) (gw_ent (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) (@ralloc_meta_stmt) gw_tbl_17)).
Definition rta_fp : ltac:(gw_rebind_ty (@QzQg.rta_fp RATP) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QzQg.rta_fp RATP) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@QzQg.rta_fp RATP) (@rta_fp) gw_tbl_18).
Definition rt1_regs : ltac:(gw_rebind_ty (@QZxv.Mqo.rt1_regs RATP) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QZxv.Mqo.rt1_regs RATP) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@Q5m9.Mq2.rt1_regs RATP) (@rt1_regs) (gw_ent (@QzQg.rt1_regs RATP) (@rt1_regs) (gw_ent (@QZxv.Mqo.rt1_regs RATP) (@rt1_regs) gw_tbl_19))).
Definition rta_frame : ltac:(gw_rebind_ty (@QROt.Mq3.rta_frame RC__) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QROt.Mq3.rta_frame RC__) constr:(gw_tbl_20)).
Notation gw_tbl_21 := (gw_ent (@QZxv.Mqn.rta_frame RC__) (@rta_frame) (gw_ent (@QzQg.rta_frame RC__) (@rta_frame) (gw_ent (@QZxv.Mqo.rta_frame RC__) (@rta_frame) (gw_ent (@QROt.Mq3.rta_frame RC__) (@rta_frame) gw_tbl_20)))).

Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rauxv_ok_weaken : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rauxv_ok_weaken) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rauxv_ok_weaken)).
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).
Definition rpres_except_rw_cells : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_rw_cells) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_rw_cells)).
Definition rfresh_image : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rfresh_image) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rfresh_image)).
Ltac riprefixT := apply rimplT_from_evt.

Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).

Definition rauxv_ok_pres : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq1.rauxv_ok_pres) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq1.rauxv_ok_pres)).

Definition rmeta_chunk_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmeta_chunk_facts) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmeta_chunk_facts)).
Definition rregion_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rregion_facts) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rregion_facts)).

Definition ralloc_meta_stmtL : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq4.ralloc_meta_stmtL) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq4.ralloc_meta_stmtL)).
Notation RAREACH := (AREACH_from ref_reserved rc_secret).
Notation RISTF := (@ISTF_g ref_reserved).
Notation RAMP_AS := (AMP_AS_g ref_reserved rc_secret).

Definition rag_entry_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq2.rag_entry_walk) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq2.rag_entry_walk)).
Definition rag_ret_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq2.rag_ret_walk) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq2.rag_ret_walk)).

Definition ras_ret0 : ltac:(gw_ctx_fold_ty2 (@QZxv.Mqn.ras_ret0) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QZxv.Mqn.ras_ret0)).

Definition rauxv_ok_malloc_fp_ER : ltac:(gw_ctx_fold_ty2 (@QzQg.Mq3.rauxv_ok_malloc_fp_ER) constr:(gw_tbl_21)) := ltac:(gw_ctx_fold_tm2 (@QzQg.Mq3.rauxv_ok_malloc_fp_ER)).

#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ralloc_meta_entry rmmap_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk segs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells segs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv segs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := QULt.Mq1.ist_facts_proof st0 LB st AR IS.

Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : RAMP_AS ram_pre.

Definition rag_regs (x1 t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' s9' t3' t4' t5' t6' : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) s1' a0' a1' a2' a3' a4' a5' a6' a7' a1 s3'
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 ((RATP + 132048) + 8 * sc)) (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) s8' s9' s10 s11 t3' t4' t5' t6'.
Definition rFRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

Definition rHAG_stmt : Prop :=
forall st1 st2 mm m3 s' (errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte) oo,
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) ->
IST st0 st2 -> ENTRY_REL st0 st2 -> ALLC st2 ->
am_rel st1 st2 (Some mm) -> get_meta_rec st2 mm = meta0 -> meta_slot st2 mm ->
rmrep st2 m3 -> ticks_ok st2 -> unk_agree st2 o m3 -> mem_inv segs m3 -> stk segs m3 lo (bv_unsigned sp + -144) ->
rw_cells segs m3 (bv_unsigned sp + -144) (rFRM junk) ->
rw_cells segs m3 (errno_addr tp) [C4 errv'] -> rauxv_ok m3 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 ->
brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (ag_body f sc req k bail st2 mm) s' Q
(MS (rag_regs (Z_to_bv 64 (base + 0x1f8)) t0' t1' t2' (Z_to_bv 64 (conc st2 mm)) (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (sc * 2)) (wz (size_class sc)) (Z_to_bv 64 (RDEBRUIJN + 32)) t3' t4' t5' t6')
F (Z_to_bv 64 (base + 0x204)) fc None m3 (seg_rom segs)).
Hypothesis HAG : rHAG_stmt.

#[using="base rvm_wait_entry RNG_RATP ralloc_meta_entry rmmap_entry RC__ TP"] Lemma rerrno_lit2 : errno_addr tp = (RATP + -164).
Proof. clear - base rvm_wait_entry RNG_RATP ralloc_meta_entry rmmap_entry RC__ TP RATP R f k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st LB lo sc req errv AR IS ER AC SC RQ FIT MR TK UA BL AUX ST CLO LO ERR MI A0 A1 HK F0 ram_pre AM AMP HAG. gw_expose_fam RATP. first [clear HAG | gw_hide HAG | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear AM | gw_hide AM | idtac]; first [clear ram_pre | gw_hide ram_pre | idtac]; first [clear F0 | gw_hide F0 | idtac]; first [clear HK | gw_hide HK | idtac]; first [clear A1 | gw_hide A1 | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear CLO | gw_hide CLO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear UA | gw_hide UA | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear RQ | gw_hide RQ | idtac]; first [clear SC | gw_hide SC | idtac]; first [clear AC | gw_hide AC | idtac]; first [clear ER | gw_hide ER | idtac]; first [clear IS | gw_hide IS | idtac]; first [clear AR | gw_hide AR | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear req | gw_hide req | idtac]; first [clear sc | gw_hide sc | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear LB | gw_hide LB | idtac]; first [clear st | gw_hide st | idtac]; first [clear st0 | gw_hide st0 | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a7 | gw_hide a7 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear a0 | gw_hide a0 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear f | gw_hide f | idtac]. rewrite TP. gw_expose_fam RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

#[using="segs base RATP RGOT_SSP ref_reserved rvm_wait_entry ralloc_meta_entry rmmap_entry RC__ m MR"] Lemma rconc_meta_stable stE q : mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof. clear - segs base RATP RGOT_SSP ref_reserved rvm_wait_entry ralloc_meta_entry rmmap_entry RC__ m MR stE q R f k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc st0 st LB lo sc req errv AR IS ER AC SC RQ FIT TK UA BL AUX ST CLO LO ERR MI TP A0 A1 HK F0 ram_pre AM AMP HAG. first [clear HAG | gw_hide HAG | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear AM | gw_hide AM | idtac]; first [clear ram_pre | gw_hide ram_pre | idtac]; first [clear F0 | gw_hide F0 | idtac]; first [clear HK | gw_hide HK | idtac]; first [clear A1 | gw_hide A1 | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear CLO | gw_hide CLO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear UA | gw_hide UA | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear RQ | gw_hide RQ | idtac]; first [clear SC | gw_hide SC | idtac]; first [clear AC | gw_hide AC | idtac]; first [clear ER | gw_hide ER | idtac]; first [clear IS | gw_hide IS | idtac]; first [clear AR | gw_hide AR | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear req | gw_hide req | idtac]; first [clear sc | gw_hide sc | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear LB | gw_hide LB | idtac]; try gw_hide st; first [clear st0 | gw_hide st0 | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a7 | gw_hide a7 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear a0 | gw_hide a0 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear f | gw_hide f | idtac].
intros REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

#[using="base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved ralloc_meta_entry rmmap_entry m ER MR"] Lemma rta_fp_malloc_fp stE mE a :
rmrep stE mE -> mrel st stE -> (forall q, meta_slot st q -> meta_slot stE q) ->
rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 stE lo (bv_unsigned sp) a.
Proof. clear - base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved ralloc_meta_entry rmmap_entry m ER MR stE mE a R f k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc st0 st LB lo sc req errv AR IS AC SC RQ FIT TK UA BL AUX ST CLO LO ERR MI TP A0 A1 HK F0 ram_pre AM AMP HAG. first [clear HAG | gw_hide HAG | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear AM | gw_hide AM | idtac]; first [clear ram_pre | gw_hide ram_pre | idtac]; first [clear F0 | gw_hide F0 | idtac]; first [clear HK | gw_hide HK | idtac]; first [clear A1 | gw_hide A1 | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear CLO | gw_hide CLO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear UA | gw_hide UA | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear RQ | gw_hide RQ | idtac]; first [clear SC | gw_hide SC | idtac]; first [clear AC | gw_hide AC | idtac]; first [clear IS | gw_hide IS | idtac]; first [clear AR | gw_hide AR | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear req | gw_hide req | idtac]; first [clear sc | gw_hide sc | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear LB | gw_hide LB | idtac]; try gw_hide st; first [clear st0 | gw_hide st0 | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a7 | gw_hide a7 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear a0 | gw_hide a0 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear f | gw_hide f | idtac].
intros MRE REL AREAS [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- left. left. gw_exact X.
- left. right. right. left. gw_exact X.
- left. do 3 right.
pose proof (AREAS q MSq) as MSq'.
destruct (rmeta_chunk_facts stE mE q MRE MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
exists rid0, r0. split; [gw_exact H0|]. split; [gw_exact K0|].
rewrite (rconc_meta_stable stE q REL MSq) in L0, H0'. lia.
- do 3 right. left. pose proof MR as (WF & _).
destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct ER as [_ EG EGR _ _ _ _ _].
destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
exists bq, gh0, rb. split; [gw_exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); gw_exact Hrb|]. split; [gw_exact Kb|].
rewrite Cb in Xq. lia.
Qed.

#[using="segs base RGOT_SSP RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmmap_entry RC__ m MR CLO"] Lemma rta_fp_not_image a : 0x10000 <= a < RIMG_HI -> ~ ((RATP + 131968) <= a < (RATP + 132896)) -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof. clear - segs base RGOT_SSP RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmmap_entry RC__ m MR CLO RATP RIMG_HI a R f k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc st0 st LB lo sc req errv AR IS ER AC SC RQ FIT TK UA BL AUX ST LO ERR MI TP A0 A1 HK F0 ram_pre AM AMP HAG. gw_expose_fam RATP. first [clear HAG | gw_hide HAG | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear AM | gw_hide AM | idtac]; first [clear ram_pre | gw_hide ram_pre | idtac]; first [clear F0 | gw_hide F0 | idtac]; first [clear HK | gw_hide HK | idtac]; first [clear A1 | gw_hide A1 | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear UA | gw_hide UA | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear RQ | gw_hide RQ | idtac]; first [clear SC | gw_hide SC | idtac]; first [clear AC | gw_hide AC | idtac]; first [clear ER | gw_hide ER | idtac]; first [clear IS | gw_hide IS | idtac]; first [clear AR | gw_hide AR | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear req | gw_hide req | idtac]; first [clear sc | gw_hide sc | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear LB | gw_hide LB | idtac]; try gw_hide st; first [clear st0 | gw_hide st0 | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a7 | gw_hide a7 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear a0 | gw_hide a0 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear f | gw_hide f | idtac].
intros Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- unfold alloc_ceiling in CLO. lia.
- exact (Hc X).
- destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
- pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _).
destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
Qed.

#[using="segs base RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmmap_entry RC__ m sc MR CLO LO"] Lemma rta_fp_not_high a : bv_unsigned sp <= a -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof. clear - segs base RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmmap_entry RC__ m sc MR CLO LO a RATP R f k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc st0 st LB lo req errv AR IS ER AC SC RQ FIT TK UA BL AUX ST ERR MI TP A0 A1 HK F0 ram_pre AM AMP HAG. gw_expose_fam RATP. first [clear HAG | gw_hide HAG | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear AM | gw_hide AM | idtac]; first [clear ram_pre | gw_hide ram_pre | idtac]; first [clear F0 | gw_hide F0 | idtac]; first [clear HK | gw_hide HK | idtac]; first [clear A1 | gw_hide A1 | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear UA | gw_hide UA | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear RQ | gw_hide RQ | idtac]; first [clear SC | gw_hide SC | idtac]; first [clear AC | gw_hide AC | idtac]; first [clear ER | gw_hide ER | idtac]; first [clear IS | gw_hide IS | idtac]; first [clear AR | gw_hide AR | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear req | gw_hide req | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear LB | gw_hide LB | idtac]; try gw_hide st; first [clear st0 | gw_hide st0 | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a7 | gw_hide a7 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear a0 | gw_hide a0 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear f | gw_hide f | idtac].
pose proof (RAS_STACK_ge sc) as ASG. unfold alloc_ceiling in CLO.
intros Ha [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- lia.
- gw_expose_fam RATP. lia.
- destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). lia.
- pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). unfold alloc_ceiling in RC. lia.
Qed.

#[using="UA"] Lemma runk_agree_keep stE mE :
s_shadow stE = s_shadow st ->
(forall rid r, r_kind r = RKGroup -> (s_regions stE) !! rid = Some r -> (s_regions st) !! rid = Some r) ->
(forall b, is_Some ((s_groups stE) !! b) <-> is_Some ((s_groups st) !! b)) ->
(forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) off = Unknown h -> ~ grp_hdr_cov st rid off -> mE (wa (r_base r + off)) = m (wa (r_base r + off))) ->
unk_agree stE o mE.
Proof. clear - UA stE mE R f k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st LB lo sc req errv AR IS ER AC SC RQ FIT MR TK BL AUX ST CLO LO ERR MI TP A0 A1 HK F0 ram_pre AM AMP HAG. first [clear HAG | gw_hide HAG | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear AM | gw_hide AM | idtac]; first [clear ram_pre | gw_hide ram_pre | idtac]; first [clear F0 | gw_hide F0 | idtac]; first [clear HK | gw_hide HK | idtac]; first [clear A1 | gw_hide A1 | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear CLO | gw_hide CLO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear RQ | gw_hide RQ | idtac]; first [clear SC | gw_hide SC | idtac]; first [clear AC | gw_hide AC | idtac]; first [clear ER | gw_hide ER | idtac]; first [clear IS | gw_hide IS | idtac]; first [clear AR | gw_hide AR | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear req | gw_hide req | idtac]; first [clear sc | gw_hide sc | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear LB | gw_hide LB | idtac]; try gw_hide st; first [clear st0 | gw_hide st0 | idtac]; first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a7 | gw_hide a7 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear a0 | gw_hide a0 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear f | gw_hide f | idtac].
intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
pose proof (ERG rid r Hk Hr) as Hr0.
assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; gw_exact X).
assert (NG0 : ~ grp_hdr_cov st rid off).
{ intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

#[using="segs base RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved ralloc_meta_entry rmmap_entry RC__ m MR CLO"] Lemma rta_fp_not_inband rid r off :
(s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) -> ~ grp_hdr_cov st rid off ->
~ rta_fp st lo (bv_unsigned sp) (r_base r + off).
Proof. clear - segs base RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_reservedZ LAY_ref_reserved ralloc_meta_entry rmmap_entry RC__ m MR CLO rid r off RATP R f k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc st0 st LB lo sc req errv AR IS ER AC SC RQ FIT TK UA BL AUX ST LO ERR MI TP A0 A1 HK F0 ram_pre AM AMP HAG. gw_expose_fam RATP. first [clear HAG | gw_hide HAG | idtac]; first [clear AMP | gw_hide AMP | idtac]; first [clear AM | gw_hide AM | idtac]; first [clear ram_pre | gw_hide ram_pre | idtac]; first [clear F0 | gw_hide F0 | idtac]; first [clear HK | gw_hide HK | idtac]; first [clear A1 | gw_hide A1 | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear TP | gw_hide TP | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ERR | gw_hide ERR | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear AUX | gw_hide AUX | idtac]; first [clear BL | gw_hide BL | idtac]; first [clear UA | gw_hide UA | idtac]; first [clear TK | gw_hide TK | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear RQ | gw_hide RQ | idtac]; first [clear SC | gw_hide SC | idtac]; first [clear AC | gw_hide AC | idtac]; first [clear ER | gw_hide ER | idtac]; first [clear IS | gw_hide IS | idtac]; first [clear AR | gw_hide AR | idtac]; first [clear errv | gw_hide errv | idtac]; first [clear req | gw_hide req | idtac]; first [clear sc | gw_hide sc | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear LB | gw_hide LB | idtac]; try gw_hide st; first [clear st0 | gw_hide st0 | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a7 | gw_hide a7 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear a0 | gw_hide a0 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear k | gw_hide k | idtac]; first [clear f | gw_hide f | idtac].
intros Hr Hk Ho NG. pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). unfold alloc_ceiling in RC, CLO.
intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- lia.
- destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). gw_expose_fam RATP. lia.
- destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
- destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct (N.eq_dec (fst bq) rid) as [E|NE].
+ apply NG. exists bq, gh. split; [gw_exact Hbq|]. split; [gw_exact E|]. rewrite E, Hr in Hrb. inversion Hrb; subst rb. lia.
+ pose proof (lr_lo_group r Hk). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
Qed.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_121 lo_122 CODE BASE4 BASER D_121 E_121 D_122 E_122 ANCH_122 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved ralloc_meta_entry rmmap_entry st0 LB errv AR IS ER AC SC MR TK UA BL AUX CLO LO ERR TP HK F0 ram_pre AM AMP HAG"] Lemma rag_phase : forall st1 m1 (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
rmrep st1 m1 -> mem_inv segs m1 -> rw_cells segs m1 (bv_unsigned sp + -144) (rFRM junk) -> stk segs m1 lo (bv_unsigned sp + -144) ->
rpres_except (rta_fp st lo (bv_unsigned sp)) m m1 ->
rimplT o (as_grp full_lay f sc req k bail st1) s Q
(MS (rag_regs ra t0' t1' t2 s1 a0' a1' a2' a3' a4' a5' a6' a7' s3 s8 s9 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1e0)) fc None m1 (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_121 lo_122 CODE BASE4 BASER D_121 E_121 D_122 E_122 ANCH_122 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved ralloc_meta_entry rmmap_entry st0 LB errv AR IS ER AC SC MR TK UA BL AUX CLO LO ERR TP HK F0 ram_pre AM AMP HAG segs base RATP R f k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st lo sc req RQ FIT ST MI A0 A1. gw_expose_fam RATP. first [clear A1 | gw_hide A1 | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear MI | gw_hide MI | idtac]; first [clear ST | gw_hide ST | idtac]; first [clear FIT | gw_hide FIT | idtac]; first [clear RQ | gw_hide RQ | idtac]; try gw_hide req; try gw_hide sc; try gw_hide lo; try gw_hide st; try gw_hide m; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a7 | gw_hide a7 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear a0 | gw_hide a0 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; try gw_hide tp; try gw_hide gp; try gw_hide sp; first [clear ra | gw_hide ra | idtac]; first [clear Q | gw_hide Q | idtac]; try gw_hide s; try gw_hide o; try gw_hide bail; try gw_hide k; try gw_hide f.
intros until junk. intros TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
pose proof rerrno_lit2 as EA.
pose proof (isf_mf _ _ F0) as MF. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
rewrite (as_grp_eq f sc req k bail st1).
riprefixT. unfold rag_regs.
eapply evt_cut. { eapply (rag_entry_walk sc SC). gw_exact MI1. }
cbv beta. intros ms' ->. apply evt_done. unfold rt1_regs.

assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
assert (TK1 : ticks_ok st1) by (eapply ticks_ok_same; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)| gw_exact TK]).
assert (CONC1 : forall q, conc st1 q = conc st q) by (intros q; unfold conc, get_region; rewrite REG1; reflexivity).
assert (BL1 : brk_link_ps st1 s).
{ unfold brk_link_ps in *. unfold ctx in *. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONC1. gw_exact BL. }
assert (AUX2 : rauxv_ok m1 (bv_unsigned sp + -144)).
{ apply (rauxv_ok_weaken m1 (bv_unsigned sp)); [| unfold alloc_ceiling; lia]. eapply rauxv_ok_pres; [gw_exact AUX| gw_exact PE1| |].
- intros a Ha. apply rta_fp_not_high. gw_exact Ha.
- intros a Ha. apply rta_fp_not_image; gw_expose_fam RATP; lia. }
assert (ERR2 : rw_cells segs m1 (errno_addr tp) [C4 errv]).
{ eapply rpres_except_rw_cells; [gw_exact PE1| gw_exact ERR|]. rewrite EA. cbn. intros a Ha. apply rta_fp_not_image; [lia| gw_expose_fam RATP; lia]. }
eapply (ralloc_meta_stmtL ram_pre AM) with (lo := lo);
[ exact (AMP st0 LB st sc st1 AR IS SC TF) | gw_exact MR1 | gw_exact TK1 | gw_exact BL1 | rewrite unsigned_lit by lia; gw_exact AUX2
| rewrite unsigned_lit by lia; gw_exact ST1 | gw_exact CLO
| rewrite unsigned_lit by lia; unfold RAM_STACK; lia | gw_exact ERR2 | gw_exact MI1 | gw_exact TP |].
intros st2 mo s' ms' PO BL2 LF.
destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & PE3 & MR3 & TK3 & PSM & PSF & PSO & REL & E12).
rewrite unsigned_lit in ST3, AUX3, PE3 by lia.
try g_ret_pc_any.
pose proof MR3 as (WF3 & _). pose proof WF3 as (RS3 & WR3 & DJ3 & _).

assert (OUT3 : forall a, bv_unsigned sp - 144 <= a \/ (0x10000 <= a < RIMG_HI /\ ~ ((RATP + 131968) <= a < (RATP + 132896)) /\ ~ ((RATP + -164) <= a < (RATP + -164 + 4))) ->
~ (ralloc_fp (fun k => k <> RKGroup) st2 lo (bv_unsigned sp + -144) a \/ fresh_addr st1 a)).
{ intros a Ha [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
- lia.
- rewrite unsigned_lit in X by lia. lia.
- gw_expose_fam RATP. lia.
- destruct (WR3 _ _ Hq') as (B0 & _ & _ & BC & RF'). pose proof (lr_lo_ge rq2). unfold alloc_ceiling in BC.
pose proof (rreserved_disjoint _ _ RF') as (D1 & D2 & D3 & D4). pose proof (round_up_pg_ge (r_len rq2)). lia.
- destruct X as [XC XF]. unfold alloc_ceiling in XC.
pose proof (rfresh_image st1 a (conj XC XF) ltac:(rewrite (tr_reserved _ _ _ TR); gw_exact RS)). lia. }
assert (FR3 : rw_cells segs m3 (bv_unsigned sp + -144) (rFRM junk)).
{ eapply rpres_except_rw_cells; [gw_exact PE3| gw_exact FR1|]. intros a Ha. apply OUT3. left. unfold rFRM, rta_frame in Ha. cbn in Ha. lia. }

assert (REL02 : mrel st st2).
{ split; [| rewrite <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _). exists r'. auto. }
assert (AREAS2 : forall q, meta_slot st q -> meta_slot st2 q).
{ intros q (ar & arr & kk & Ha & Hk & E). destruct (amr_areas _ _ _ REL ar ltac:(rewrite (tr_areas _ _ _ TR), Ha; eexists; reflexivity)) as [arr' Ha'].
exists ar, arr', kk. auto. }
assert (PE03 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3).
{ eapply rpres_except_trans.
- eapply rpres_except_mono; [gw_exact PE1|]. intros a Ha. eapply (rta_fp_malloc_fp st2 m3); [gw_exact MR3| gw_exact REL02| gw_exact AREAS2| gw_exact Ha].
- eapply rpres_except_mono; [gw_exact PE3|]. intros a [[X|[X|[X|X]]]|X].
+ left. left. lia. + left. right. left. gw_exact X. + left. right. right. left. gw_exact X. + left. right. right. right. gw_exact X.
+ do 4 right. eapply (fresh_addr_anti st0 st1); [| | gw_exact X].
* rewrite (tr_reserved _ _ _ TR). destruct ER as [_ _ _ EM _ _ _ _]. apply (mrel_reserved _ _ EM).
* intros rid r Hr. destruct ER as [_ _ _ EM _ _ _ _]. destruct (mrel_regions _ _ EM rid r Hr) as (r' & H' & K' & B' & L'). exists r'. rewrite REG1. auto. }

assert (UA3 : unk_agree st2 o m3).
{ eapply (runk_agree_keep st2 m3).
- rewrite (amr_shadow _ _ _ REL). apply (tr_shadow _ _ _ TR).
- intros rid r Hk Hr. rewrite <- REG1. destruct ((s_regions st1) !! rid) as [r0|] eqn:E0.
+ destruct (amr_regions _ _ _ REL rid r0 E0) as (r' & H' & K' & _ & _ & G'). rewrite Hr in H'. inversion H'; subst r'. rewrite (G' ltac:(rewrite <- K'; gw_exact Hk)). reflexivity.
+ exfalso. exact (amr_new _ _ _ REL rid r Hr E0 Hk).
- intros b. rewrite (amr_groups _ _ _ REL). apply (tr_groups _ _ _ TR).
- intros rid r off h Hr Hk Ho Hc NG.
destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). unfold alloc_ceiling in RC.
transitivity (m1 (wa (r_base r + off))).
+ refine (proj1 (PE3 (r_base r + off) ltac:(lia) _)). intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
* lia.
* rewrite unsigned_lit in X by lia. destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2).
specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
* destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). gw_expose_fam RATP. lia.
* assert (Hr2 : (s_regions st2) !! rid = Some r).
{ rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & _ & _ & G'). rewrite H'. f_equal. apply G'. gw_exact Hk. }
assert (NE : q2 <> rid) by (intros ->; rewrite Hr2 in Hq'; inversion Hq'; subst; exact (Kq2 Hk)).
pose proof (lr_lo_group r Hk). destruct (DJ3 _ _ _ _ Hq' Hr2 NE); lia.
* rewrite <- REG1 in Hr. pose proof (fresh_live_region st1 _ rid r X Hr) as Y. pose proof (lr_lo_group r Hk). lia.
+ refine (proj1 (PE1 (r_base r + off) ltac:(lia) _)). apply (rta_fp_not_inband rid r off Hr Hk Ho NG). }
destruct mo as [mm|].
-
destruct (amr_result _ _ _ REL mm eq_refl) as [G0 MSL].
pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & _).
riprefixT. eapply evt_cut.
{ unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := conc st2 mm); [unfold alloc_ceiling in GC; lia| gw_exact MI3]. }
cbv beta. intros ms' ->. replace (conc st2 mm =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
apply evt_done.
eapply (HAG st1 st2 mm m3 s'); try eassumption.
+ eapply ist_am; [gw_exact IS| gw_exact SC| gw_exact TF| gw_exact LF].
+ eapply ER_am; [eapply ER_ta; [gw_exact ER| gw_exact TR]| gw_exact REL| gw_exact LF].
+ eapply ALLC_am; [gw_exact REL|]. eapply ALLC_ta; [gw_exact TR| gw_exact AC].
+ eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [gw_exact MR3| gw_exact AUX| gw_exact PE03| gw_exact CLO| lia].
-
cbn iota.
riprefixT. eapply evt_cut.
{ unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := 0); [lia| gw_exact MI3]. }
cbv beta. intros ms' ->. cbn [Z.eqb].
eapply evt_cut. { unfold rFRM in FR3. eapply (ras_ret0 sp gp tp); [gw_exact MR3| gw_exact MI3| gw_exact FR3| gw_exact ST3| gw_exact CLO| lia]. }
cbv beta. intros ms' (a1x & a2x & -> & ST4). apply evt_done.
apply HK. unfold ras_post2.
do 14 eexists. exists m3, errv3. split; [reflexivity|].
split; [gw_exact MI3|]. split; [gw_exact ST4|]. split; [gw_exact ERR3|].
split. { eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [gw_exact MR3| gw_exact AUX| gw_exact PE03| gw_exact CLO| lia]. }
split; [gw_exact MR3|]. split; [gw_exact TK3|]. split; [gw_exact UA3|]. split; [gw_exact PE03|].
split; [gw_exact REL02|]. split; [gw_exact BL2|]. split; [gw_exact PSM|]. split; [gw_exact PSF|]. split; [gw_exact PSO|].
split. { constructor.
- intros c Hc. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
- intros a Ha. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). gw_exact Ha.
- rewrite (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
- intros H; exfalso; lia.
- intros _ H; exfalso; lia. }
split. { rewrite (amr_counter _ _ _ REL). unfold ctx. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
pose proof (mf_ctx _ _ MF) as (X & _). gw_exact X. }
left. split; [reflexivity| exact (E12 eq_refl)].
Qed.
End LEVEL.

End RC__1.

End G.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8P7 QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import QytA Qnxq Q4J3.Mq3 QLsg QkQT QM7w QNAo.Mq0 Q8P7 QTyG.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QkTt.Mq5.
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import Q8l1.
Import Q5m9.Mq9.

Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (ralloc_meta_entry ralloc_slot_entry : Z).
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_ralloc_meta_entry : gw_al ralloc_meta_entry 4.
Hypothesis AL_ralloc_slot_entry : gw_al ralloc_slot_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QQRC.Mq4.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Q5m9.Mq9.ralloc_fp RATP) (@ralloc_fp) gw_tbl_0))))).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QQRC.Mq4.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Q5m9.Mq9.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_1)))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Q5m9.Mq9.rarea_rep segs) (@rarea_rep) gw_tbl_2)))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q5m9.Mq9.rmrep_areas segs) (@rmrep_areas) gw_tbl_3)))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q5m9.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4)))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q5m9.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5)))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q5m9.Mq9.rgroup_rep segs) (@rgroup_rep) gw_tbl_6)))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q5m9.Mq9.rmrep_groups segs) (@rmrep_groups) gw_tbl_7)))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q5m9.Mq9.rshadow_rep segs) (@rshadow_rep) gw_tbl_8)))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q5m9.Mq9.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9)))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q5m9.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10)))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q5m9.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11)))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QQRC.Mq4.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@Q5m9.Mq9.rpres_except segs) (@rpres_except) gw_tbl_12))))).
Definition ram_post : ltac:(gw_rebind_ty (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QQRC.Mq4.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) (gw_ent (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) (gw_ent (@Q5m9.Mq9.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) gw_tbl_13))).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_14)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_15 := (gw_ent (@QQRC.Mq4.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) (gw_ent (@Q5m9.Mq9.rimplT segs RC__) (@rimplT) gw_tbl_14)))).
Definition ralloc_meta_stmt : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@QQRC.Mq4.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) (@ralloc_meta_stmt) (gw_ent (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) (@ralloc_meta_stmt) (gw_ent (@Q5m9.Mq9.ralloc_meta_stmt segs ralloc_meta_entry RATP RGOT_SSP ref_reserved RC__) (@ralloc_meta_stmt) gw_tbl_15))).
Definition ras_pre2 : ltac:(gw_rebind_ty (@QQRC.Mq4.ras_pre2 ref_reserved RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QQRC.Mq4.ras_pre2 ref_reserved RC__) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@QQRC.Mq4.ras_pre2 ref_reserved RC__) (@ras_pre2) gw_tbl_16).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@QQRC.Mq4.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_17))).
Definition ras_post2 : ltac:(gw_rebind_ty (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@QQRC.Mq4.ras_post2 segs RATP RGOT_SSP ref_reserved RC__) (@ras_post2) gw_tbl_18).
Definition ralloc_slot_stmt2 : ltac:(gw_rebind_ty (@QQRC.Mq4.ralloc_slot_stmt2 segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QQRC.Mq4.ralloc_slot_stmt2 segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@QQRC.Mq4.ralloc_slot_stmt2 segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt2) gw_tbl_19).
Definition ras_post : ltac:(gw_rebind_ty (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_20)).
Notation gw_tbl_21 := (gw_ent (@QQRC.Mq4.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) (gw_ent (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) gw_tbl_20)).
Definition ralloc_slot_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_21)).
Notation gw_tbl_22 := (gw_ent (@QQRC.Mq4.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt) (gw_ent (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt) gw_tbl_21)).

Hypothesis ralloc_meta_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q5m9.Mq9.gw_all) (@Q5m9.Mq9.ralloc_meta_spec) ralloc_meta_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_22))) in exact T).
Hypothesis ralloc_slot_ok : gw_hyp (forall (ram_pre : QUZl.mstate -> Prop), ralloc_meta_stmt ram_pre -> QkQT.AMP_AS_g ref_reserved Q6q3.rc_secret ram_pre -> forall f, ralloc_slot_stmt2 f).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_22)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Notation RMFACTS := (@MFACTS_g ref_reserved).

Notation RAREACH := (AREACH_from ref_reserved rc_secret).

Notation ram_pre := (am_pre_g ref_reserved rc_secret).

#[using="ralloc_meta_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_ralloc_meta_entry AL_ralloc_slot_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ralloc_meta_spec ralloc_slot_ok"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

#[using="Type"] Lemma ras_pre2_intro : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> ras_pre2 st (set_tick t st) sc n FUEL.
Proof. clear - segs.
intros st LB t sc n AR MF TT SC N FIT. split; [| split; [| split; [| repeat split; lia]]].
- exists LB. split; [gw_exact AR| apply ist_top; gw_exact TT].
- apply ER_refl_tick.
- apply ALLC_tick; [| gw_exact TT]. exact (mf_cell_ticks _ _ MF).
Qed.

#[using="ralloc_meta_entry ralloc_meta_spec ralloc_slot_ok"] Theorem ralloc_slot_spec : ralloc_slot_stmt ras_pre2 as_inv2.
Proof. clear - ralloc_meta_entry ralloc_meta_spec ralloc_slot_ok.
unfold ralloc_slot_stmt. intros fuel.
exact (ralloc_slot_ok ram_pre ralloc_meta_spec QULt.Mq1.ist_ampre_proof fuel).
Qed.

End RC__1.

End G.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.

Import QnDM_c1.Mq0 QULt.Mq2 Q2qa.Mq1.
Import QVbl.Mq4.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Definition calloc_code (w_7 w_19 w_22 w_23 w_33 w_40 w_56 w_67 w_75 : Z) : list Z :=
[0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x02058a63; 0x02a5b633; 0x02060663; w_7; 0x00000413; 0x00c00593; 0x00b52023; 0x00040513; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0x00008067; 0x02a584b3; 0x00048513; w_19; 0x0c050063; 0x00050413; w_22; w_23; 0x0c050463; 0x00c4d513; 0x08050463; 0x009404b3; 0xfffff537; 0x03449613; 0x03465613; 0x00a4f533; 0x00000593; w_33; 0x408504b3; 0x00c4d593; 0x02059063; 0x05c0006f; 0x40c50533; 0x00000593; w_40; 0x408504b3; 0x00c4d593; 0x04058263; 0x80050593; 0x80058593; 0x00001637; 0xff053683; 0xff853703; 0x00e6e6b3; 0xfc0698e3; 0xff060613; 0xff050513; 0xfe0614e3; 0x40c58533; 0x00000593; w_56; 0x408504b3; 0x00c4d593; 0xfc0592e3; 0x00040513; 0x00000593; 0x00048613; 0x01813083; 0x01013403; 0x00813483; 0x02010113; w_67; 0x00000513; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0x00008067; 0x00040513; w_75; 0xee051ee3; 0xf31ff06f]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma zeros_app a b : zeros a ++ zeros b = zeros (a + b).
Proof. unfold zeros. rewrite repeat_app. reflexivity. Qed.

Lemma le8_zero_inv (w : word) : bv_unsigned w = 0 -> le8 w = zeros 8.
Proof. intros H. change (zeros 8) with (le8 (wz 0)). unfold le8, word_to_le_bytes. rewrite H. unfold wz. rewrite unsigned_lit by lia. reflexivity. Qed.

Ltac st1 := step; try rewrite ?unsigned_lit by lia.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry ris_allzero_entry : Z).
Variables (w_7 w_19 w_22 w_23 w_33 w_40 w_56 w_67 w_75 : Z).
Variables (hi_22 : bv 20).
Variables (lo_23 : bv 12).
Variables (joff_7 joff_33 joff_40 joff_56 joff_67 joff_75 : bv 21).
Variables (e_memset : Z).
Hypothesis CODE : code_at segs base (calloc_code w_7 w_19 w_22 w_23 w_33 w_40 w_56 w_67 w_75).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 312.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Jal 1 joff_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_22 : decode_any (Z_to_bv 32 w_22) = Some (Auipc 10 hi_22, 4%Z).
Hypothesis E_22 : is_ecall (Z_to_bv 32 w_22) = false.
Hypothesis D_23 : decode_any (Z_to_bv 32 w_23) = Some (Load SZ4 true 10 10 lo_23, 4%Z).
Hypothesis E_23 : is_ecall (Z_to_bv 32 w_23) = false.
Hypothesis D_33 : decode_any (Z_to_bv 32 w_33) = Some (Jal 1 joff_33, 4%Z).
Hypothesis E_33 : is_ecall (Z_to_bv 32 w_33) = false.
Hypothesis D_40 : decode_any (Z_to_bv 32 w_40) = Some (Jal 1 joff_40, 4%Z).
Hypothesis E_40 : is_ecall (Z_to_bv 32 w_40) = false.
Hypothesis D_56 : decode_any (Z_to_bv 32 w_56) = Some (Jal 1 joff_56, 4%Z).
Hypothesis E_56 : is_ecall (Z_to_bv 32 w_56) = false.
Hypothesis D_67 : decode_any (Z_to_bv 32 w_67) = Some (Jal 0 joff_67, 4%Z).
Hypothesis E_67 : is_ecall (Z_to_bv 32 w_67) = false.
Hypothesis D_75 : decode_any (Z_to_bv 32 w_75) = Some (Jal 1 joff_75, 4%Z).
Hypothesis E_75 : is_ecall (Z_to_bv 32 w_75) = false.
Hypothesis ANCH_23 : gw_anch (Z.shiftl (bv_signed hi_22) 12 + (base + 88) + bv_signed lo_23)%Z (RATP + 132896).
Hypothesis LINK_7 : gw_anch (base + 28 + bv_signed joff_7)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_33 : gw_anch (base + 132 + bv_signed joff_33)%Z (e_memset + 0)%Z.
Hypothesis LINK_40 : gw_anch (base + 160 + bv_signed joff_40)%Z (e_memset + 0)%Z.
Hypothesis LINK_56 : gw_anch (base + 224 + bv_signed joff_56)%Z (e_memset + 0)%Z.
Hypothesis LINK_67 : gw_anch (base + 268 + bv_signed joff_67)%Z (e_memset + 0)%Z.
Hypothesis LINK_75 : gw_anch (base + 300 + bv_signed joff_75)%Z (ris_allzero_entry + 0)%Z.
Hypothesis CODE_rerrno_loc_entry : code_at segs rerrno_loc_entry errno_loc_code.
Hypothesis AL_rerrno_loc_entry_b4 : gw_b4 rerrno_loc_entry.
Hypothesis RNG_rerrno_loc_entry_code : gw_br rerrno_loc_entry 12.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_ris_allzero_entry : gw_al ris_allzero_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.

Notation gw_tbl_0 := tt.

Definition memset_post : ltac:(gw_rebind_ty (@QVbl.Mq4.memset_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QVbl.Mq4.memset_post segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QVbl.Mq4.memset_post segs) (@memset_post) gw_tbl_0).

Hypothesis memset_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq4.memset_spec segs e_memset) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_1))) in exact T).
#[using="rerrno_loc_entry ris_allzero_entry e_memset RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_7 E_7 D_22 E_22 D_23 E_23 D_33 E_33 D_40 E_40 D_56 E_56 D_67 E_67 D_75 E_75 ANCH_23 LINK_7 LINK_33 LINK_40 LINK_56 LINK_67 LINK_75 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT LAY_ref_reserved AL_rerrno_loc_entry AL_ris_allzero_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay memset_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Local Abbreviation mem := (word -> option byte).

Definition ztail (m : mem) (p n k : Z) : Prop :=
exists junk, rw_cells segs m p [CB (Z.to_nat k) junk; CB (Z.to_nat (n - k)) (zeros (Z.to_nat (n - k)))].

#[using="Type"] Lemma ztail_bound m p n k : ztail m p n k -> 0 <= k <= n -> 0 <= p /\ p + n <= 2^64.
Proof. clear - m p n k.
intros [junk H] Hk. pose proof (rw_cells_bound _ _ _ _ H) as B. cbn [cells_size csize] in B. lia.
Qed.

#[using="Type"] Lemma ztail_init m p n junk : rw_cells segs m p [CB (Z.to_nat n) junk] -> 0 <= n -> ztail m p n n.
Proof. clear - segs m p n junk.
intros H Hn. exists junk. rewrite Z.sub_diag. change (Z.to_nat 0) with 0%nat. cbn [zeros repeat].
change [CB (Z.to_nat n) junk; CB 0 []] with ([CB (Z.to_nat n) junk] ++ [CB 0%nat []]).
apply (proj2 (rw_cells_app _ _ _ _ _)). split; [gw_exact H|].
pose proof (rw_cells_bound _ _ _ _ H) as B. cbn [cells_size csize Nat.add] in B |- *.
split; [split; [cbn; auto|]|].
- cbn. apply bytes_at_nil. lia.
- cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

#[using="Type"] Lemma ztail_all m p n : ztail m p n 0 -> 0 <= n -> rw_cells segs m p [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Proof. clear - segs m p n.
intros [junk H] Hn.
pose proof (rw_cells_merge segs m p [] [CB (Z.to_nat 0) junk; CB (Z.to_nat (n - 0)) (zeros (Z.to_nat (n - 0)))] [] ltac:(cbn [app]; gw_exact H)) as X.
pose proof (proj1 (proj1 H)) as WF. cbn in WF. destruct WF as (L0 & _ & _).
destruct junk; [| cbn in L0; lia]. cbn [app cells_size cells_bytes csize cbytes] in X.
rewrite Z.sub_0_r, app_nil_r in X. replace (Z.to_nat 0 + (Z.to_nat n + 0))%nat with (Z.to_nat n) in X by lia. gw_exact X.
Qed.

#[using="Type"] Lemma ztail_split m p n k len : ztail m p n k -> 0 <= len <= k -> k <= n ->
exists j1 j2, rw_cells segs m p [CB (Z.to_nat (k - len)) j1]
/\ rw_cells segs m (p + (k - len)) [CB (Z.to_nat len) j2]
/\ rw_cells segs m (p + k) [CB (Z.to_nat (n - k)) (zeros (Z.to_nat (n - k)))].
Proof. clear - segs m p n k len.
intros [junk H] Hl Hk.
pose proof (rw_cells_split_CB segs m p [] (Z.to_nat k) junk [CB (Z.to_nat (n - k)) (zeros (Z.to_nat (n - k)))]
[Z.to_nat (k - len); Z.to_nat len]%nat H ltac:(cbn; lia)) as X.
cbn [app mk_CB_cells] in X.
match type of X with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: nil) =>
change (rw_cells segs m p ([c1] ++ ([c2] ++ [c3]))) in X end.
apply rw_cells_app in X as [X1 X]. apply rw_cells_app in X as [X2 X3]. cbn [cells_size csize Nat.add] in X2, X3.
do 2 eexists. split; [gw_exact X1|]. split.
- replace (p + (k - len)) with (p + Z.of_nat (Z.to_nat (k - len) + 0)) by lia. gw_exact X2.
- replace (p + k) with (p + Z.of_nat (Z.to_nat (k - len) + 0) + Z.of_nat (Z.to_nat len + 0)) by lia. gw_exact X3.
Qed.

#[using="Type"] Lemma ztail_join m p n k len j1 :
rw_cells segs m p [CB (Z.to_nat (k - len)) j1] ->
rw_cells segs m (p + (k - len)) [CB (Z.to_nat len) (zeros (Z.to_nat len))] ->
rw_cells segs m (p + k) [CB (Z.to_nat (n - k)) (zeros (Z.to_nat (n - k)))] ->
0 <= len <= k -> k <= n -> ztail m p n (k - len).
Proof. clear - segs m p n k len j1.
intros X1 X2 X3 Hl Hk. exists j1.
assert (X23 : rw_cells segs m (p + (k - len)) ([CB (Z.to_nat len) (zeros (Z.to_nat len))] ++ [CB (Z.to_nat (n - k)) (zeros (Z.to_nat (n - k)))])).
{ apply (proj2 (rw_cells_app _ _ _ _ _)). split; [gw_exact X2|]. cbn [cells_size csize].
replace (p + (k - len) + Z.of_nat (Z.to_nat len + 0)) with (p + k) by lia. gw_exact X3. }
pose proof (rw_cells_merge segs m _ [] _ [] ltac:(rewrite app_nil_r; cbn [app]; gw_exact X23)) as M.
cbn [app cells_size cells_bytes csize cbytes Nat.add] in M. rewrite app_nil_r, zeros_app in M.
replace (Z.to_nat len + (Z.to_nat (n - k) + 0))%nat with (Z.to_nat (n - (k - len))) in M by lia.
replace (Z.to_nat len + Z.to_nat (n - k))%nat with (Z.to_nat (n - (k - len))) in M by lia.
change [CB (Z.to_nat (k - len)) j1; CB (Z.to_nat (n - (k - len))) (zeros (Z.to_nat (n - (k - len))))]
with ([CB (Z.to_nat (k - len)) j1] ++ [CB (Z.to_nat (n - (k - len))) (zeros (Z.to_nat (n - (k - len))))]).
apply (proj2 (rw_cells_app _ _ _ _ _)). split; [gw_exact X1|]. cbn [cells_size csize].
replace (p + Z.of_nat (Z.to_nat (k - len) + 0)) with (p + (k - len)) by lia. gw_exact M.
Qed.

Definition zms_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (p n k' : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(p, p + n)] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ ztail m' p n k'.

#[using="memset_spec"] Lemma zt_memset : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (p n k len : Z),
ztail m p n k -> 0 <= len <= k -> k <= n -> p + n < 2^64 -> mem_inv segs m ->
a0 = Z_to_bv 64 (p + (k - len)) -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 len ->
evt segs (zms_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc m p n (k - len))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_memset + 0x0)) fc None m (seg_rom segs)).
Proof. clear - memset_spec segs e_memset.
intros until len. intros ZT Hl Hk N64 MI -> -> ->.
pose proof (ztail_bound m p n k ZT ltac:(lia)) as [P0 PN].
destruct (ztail_split m p n k len ZT Hl Hk) as (j1 & j2 & X1 & X2 & X3).
eapply evt_mono.
{ eapply (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m j2); [|gw_exact MI].
rewrite !unsigned_lit by lia. gw_exact X2. }
cbv beta. intros ms' (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & m' & -> & MU & WM & MI' & DST).
rewrite !unsigned_lit in MU, DST by lia.
unfold zms_post. do 14 eexists. exists m'. split; [reflexivity|].
split. { eapply munch_weaken; [|gw_exact MU]. unfold sub_fp. cbn [outside]. intros; lia. }
split; [gw_exact WM|]. split; [gw_exact MI'|].
apply (ztail_join m' p n k len j1); [| | | lia| lia].
- eapply rw_cells_transport; [gw_exact X1| gw_exact MU| gw_exact WM|]. cbn. lia.
- change (0 mod 256) with 0 in DST. gw_exact DST.
- eapply rw_cells_transport; [gw_exact X3| gw_exact MU| gw_exact WM|]. cbn. lia.
Qed.

#[using="Type"] Lemma bytes_at_inj m a bs bs' : bytes_at segs m a bs -> bytes_at segs m a bs' -> length bs = length bs' -> bs = bs'.
Proof. clear - segs m a bs bs'.
intros (_ & _ & H) (_ & _ & H') L. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
- rewrite <- (H i Hi), <- (H' i ltac:(lia)). reflexivity.
- rewrite (proj2 (nth_error_None bs i)) by lia. rewrite (proj2 (nth_error_None bs' i)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma bytes_at_sub m a bs (k n : nat) : bytes_at segs m a bs -> (k + n <= length bs)%nat ->
bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof. clear - segs m a bs k n.
intros (A0 & AL & H) Hkn. split; [lia|]. rewrite length_firstn, length_skipn. split; [lia|].
intros i Hi. replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia. rewrite H by lia.
rewrite nth_error_firstn. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_error_skipn. reflexivity.
Qed.

#[using="Type"] Lemma ztail_read8 m p n k a : ztail m p n k -> 0 <= k <= n -> p <= a -> a + 8 <= p + n ->
exists w : word, bytes_at segs m a (le8 w) /\ ov_read_bytes segs m (wa a) 8 = Some (le8 w).
Proof. clear - segs m p n k a.
intros [junk H] Hk Ha Ha8.
pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
pose proof (proj1 (proj1 H)) as WF. cbn in WF. destruct WF as (L1 & L2 & _).
assert (LL : length (junk ++ zeros (Z.to_nat (n - k))) = Z.to_nat n) by (rewrite app_length; unfold zeros in *; rewrite repeat_length; lia).
pose proof (bytes_at_sub m p _ (Z.to_nat (a - p)) 8 B ltac:(lia)) as B8.
set (bs := firstn 8 (skipn (Z.to_nat (a - p)) (junk ++ zeros (Z.to_nat (n - k))))) in B8.
assert (L8 : length bs = 8%nat) by (subst bs; rewrite length_firstn, length_skipn; lia).
exists (le_bytes_to_word bs).
assert (E : le8 (le_bytes_to_word bs) = bs).
{ unfold le8, word_to_le_bytes, le_bytes_to_word.
assert (HR : 0 <= bytes_le_to_Z bs < 2^64).
{ rewrite bytes_le_to_Z_le_val. pose proof (le_val_range _ (bytes_ok_map bs)) as X. rewrite length_map, L8 in X. gw_exact X. }
rewrite unsigned_lit by lia. rewrite <- L8. apply Z_to_le_bytes_to_Z. }
rewrite E. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia. split; [gw_exact B8|].
rewrite <- (Z.add_0_r (p + Z.of_nat (Z.to_nat (a - p)))).
clearbody bs.
pose proof (bytes_at_read segs m _ _ 0 8 B8 ltac:(lia)) as R.
assert (R8 : (Z.to_nat 0 + 8 <= length bs)%nat) by (rewrite L8; apply Nat.le_refl). specialize (R R8). change (Z.to_nat 0) with 0%nat in R. change (drop 0 bs) with bs in R.
rewrite firstn_all2 in R by (rewrite L8; apply Nat.le_refl). gw_exact R.
Qed.

#[using="Type"] Lemma ztail_learn16 m p n k w1 w2 : ztail m p n k -> 16 <= k <= n ->
bytes_at segs m (p + k - 16) (le8 w1) -> bytes_at segs m (p + k - 8) (le8 w2) ->
bv_unsigned w1 = 0 -> bv_unsigned w2 = 0 -> ztail m p n (k - 16).
Proof. clear - segs m p n k w1 w2.
intros ZT Hk B1 B2 Z1 Z2.
destruct (ztail_split m p n k 16 ZT ltac:(lia) ltac:(lia)) as (j1 & j2 & X1 & X2 & X3).
apply (ztail_join m p n k 16 j1 X1); [| gw_exact X3| lia| lia].
pose proof (rw_cells_CB_length _ _ _ _ _ X2) as L2.
assert (E : j2 = zeros 16).
{ apply (bytes_at_inj m (p + (k - 16))); [| | unfold zeros; rewrite repeat_length; lia].
- pose proof (rw_cells_bytes_at _ _ _ _ X2) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. gw_exact B.
- change (zeros 16) with (zeros 8 ++ zeros 8). apply bytes_at_app. rewrite <- (le8_zero_inv w1 Z1) at 1. rewrite <- (le8_zero_inv w2 Z2).
split; [replace (p + (k - 16)) with (p + k - 16) by lia; gw_exact B1|].
rewrite length_le8. replace (p + (k - 16) + Z.of_nat 8) with (p + k - 8) by lia. gw_exact B2. }
rewrite <- E. gw_exact X2.
Qed.

Definition zx_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : mem) (p n g : Z) : machine_state -> Prop :=
fun ms' => exists ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 (g - p)) (Z_to_bv 64 g) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (if g - p <? 4096 then (base + 0xf0) else (base + 0xb0))) fc None m' (seg_rom segs)
/\ munch [(p, p + n)] m0 m' /\ wmono segs m0 m' /\ mem_inv segs m' /\ ztail m' p n (g - p).

#[using="w_7 w_19 w_22 w_23 w_33 w_40 w_56 w_67 w_75 joff_40 joff_56 e_memset CODE BASE4 BASER D_40 E_40 D_56 E_56 LINK_40 LINK_56 memset_spec"] Lemma zt_inner : forall (j : nat) ra sp gp tp t0 t1 t2 s1v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (p n g : Z),
let q := g + 16 * Z.of_nat j in
(1 <= j <= 256)%nat ->
ztail m p n (q - p) -> 0 < p -> p <= g -> q <= p + n -> p + n < 2^64 -> mem_inv segs m ->
evt segs (zx_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p n g)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 p) s1v (Z_to_bv 64 q) (Z_to_bv 64 g) (Z_to_bv 64 (16 * Z.of_nat j)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xbc)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_19 w_22 w_23 w_33 w_40 w_56 w_67 w_75 joff_40 joff_56 e_memset CODE BASE4 BASER D_40 E_40 D_56 E_56 LINK_40 LINK_56 memset_spec segs base.
induction j as [|j IH]; intros until g; intros q Hj ZT P0 PG QN N64 MI; [lia|].
subst q. set (q := g + 16 * Z.of_nat (S j)) in *.
assert (Q16 : p + 16 <= q) by (subst q; lia).
destruct (ztail_read8 m p n (q - p) (q - 16) ZT ltac:(lia) ltac:(lia) ltac:(lia)) as (wA & BA & RA).
destruct (ztail_read8 m p n (q - p) (q - 8) ZT ltac:(lia) ltac:(lia) ltac:(lia)) as (wB & BB & RB).
change (wa (q - 16)) with (Z_to_bv 64 (q + -16)) in RA. change (wa (q - 8)) with (Z_to_bv 64 (q + -8)) in RB.

st1. st1. st1. st1. if_cases K; zify_cond K.
-
st1. st1. st1.
replace (q + - (16 * Z.of_nat (S j))) with (p + ((q - p) - (q - g))) by lia.
eapply evt_cut.
{ eapply (zt_memset _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m p n (q - p) (q - g));
[gw_exact ZT| lia| lia| lia| gw_exact MI| reflexivity| reflexivity| f_equal; lia]. }
cbv beta. intros ms' (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & m' & -> & MU & WM & MI' & ZT').
try g_ret_pc_any.
replace (p + (q - p - (q - g))) with g by lia. replace (q - p - (q - g)) with (g - p) in ZT' by lia.

st1. st1. st1. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
+ apply evt_done. unfold zx_post. do 15 eexists. exists m'.
replace (g - p <? 4096) with true. 2:{ symmetry. apply Z.ltb_lt. rewrite Z.shiftr_div_pow2 in K1 by lia. Z.div_mod_to_equations; lia. }
split; [reflexivity|]. auto.
+ apply evt_done. unfold zx_post. do 15 eexists. exists m'.
replace (g - p <? 4096) with false. 2:{ symmetry. apply Z.ltb_ge. rewrite Z.shiftr_div_pow2 in K1 by lia. Z.div_mod_to_equations; lia. }
split; [reflexivity|]. auto.
-
apply zb_lor_eq0 in K as [KA KB].
assert (ZT2 : ztail m p n (q - 16 - p)).
{ replace (q - 16 - p) with ((q - p) - 16) by lia. apply (ztail_learn16 m p n (q - p) wA wB ZT ltac:(lia)); [| | gw_exact KA| gw_exact KB].
- replace (p + (q - p) - 16) with (q - 16) by lia. gw_exact BA.
- replace (p + (q - p) - 8) with (q - 8) by lia. gw_exact BB. }
st1. st1. st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
+
replace (16 * Z.of_nat (S j) + -16) with (16 * Z.of_nat j) by lia.
replace (q + -16) with (g + 16 * Z.of_nat j) by (subst q; lia).
apply IH; [lia| | lia| lia| subst q; lia| lia| gw_exact MI].
replace (g + 16 * Z.of_nat j - p) with (q - 16 - p) by (subst q; lia). gw_exact ZT2.
+
assert (J1 : j = 0%nat) by lia. subst j.
assert (QG : q - 16 = g) by (subst q; lia). rewrite QG in ZT2.
st1. st1. st1.
replace (g + - (16 * Z.of_nat 1 + -16)) with (p + ((g - p) - 0)) by lia.
eapply evt_cut.
{ eapply (zt_memset _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m p n (g - p) 0);
[gw_exact ZT2| lia| lia| lia| gw_exact MI| reflexivity| reflexivity| f_equal; lia]. }
cbv beta. intros ms' (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & m' & -> & MU & WM & MI' & ZT').
try g_ret_pc_any.
replace (p + (g - p - 0)) with g by lia. rewrite Z.sub_0_r in ZT'.

st1. st1. st1. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
* apply evt_done. unfold zx_post. do 15 eexists. exists m'.
replace (g - p <? 4096) with false. 2:{ symmetry. apply Z.ltb_ge. rewrite Z.shiftr_div_pow2 in K1 by lia. Z.div_mod_to_equations; lia. }
split; [reflexivity|]. auto.
* apply evt_done. unfold zx_post. do 15 eexists. exists m'.
replace (g - p <? 4096) with true. 2:{ symmetry. apply Z.ltb_lt. rewrite Z.shiftr_div_pow2 in K1 by lia. Z.div_mod_to_equations; lia. }
split; [reflexivity|]. auto.
Qed.

Definition zdone_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : mem) (p n : Z) : machine_state -> Prop :=
fun ms' => exists k ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 k) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xf0)) fc None m' (seg_rom segs)
/\ 0 <= k <= n /\ munch [(p, p + n)] m0 m' /\ wmono segs m0 m' /\ mem_inv segs m' /\ ztail m' p n k.

#[using="w_7 w_19 w_22 w_23 w_33 w_40 w_56 w_67 w_75 joff_40 joff_56 e_memset CODE BASE4 BASER D_40 E_40 D_56 E_56 LINK_40 LINK_56 memset_spec"] Lemma zt_outer : forall (N : nat) ra sp gp tp t0 t1 t2 s1v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (p n pp : Z),
pp - p <= 4096 * Z.of_nat N -> 4096 <= pp - p -> pp <= p + n ->
ztail m p n (pp - p) -> 0 < p -> p + n < 2^64 -> mem_inv segs m ->
evt segs (zdone_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p n)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 p) s1v (Z_to_bv 64 pp) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xb0)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_19 w_22 w_23 w_33 w_40 w_56 w_67 w_75 joff_40 joff_56 e_memset CODE BASE4 BASER D_40 E_40 D_56 E_56 LINK_40 LINK_56 memset_spec segs base.
induction N as [|N IH]; intros until pp; intros HN H4 HP ZT P0 N64 MI; [lia|].

st1. st1. st1.
replace (pp + -2048 + -2048) with (pp - 4096) by lia.
replace (Z_to_bv 64 pp) with (Z_to_bv 64 ((pp - 4096) + 16 * Z.of_nat 256)) by (f_equal; lia).
change (Z_to_bv 64 4096) with (Z_to_bv 64 (16 * Z.of_nat 256)).
eapply evt_cut.
{ eapply (zt_inner 256) with (n := n) (p := p) (g := pp - 4096); try lia; [| gw_exact MI].
replace (pp - 4096 + 16 * Z.of_nat 256 - p) with (pp - p) by lia. gw_exact ZT. }
cbv beta. intros ms' (ra' & w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & m' & -> & MU & WM & MI' & ZT').
destruct (Z.ltb_spec (pp - 4096 - p) 4096) as [LT|GE].
- apply evt_done. unfold zdone_post. exists (pp - 4096 - p). do 16 eexists. exists m'.
split; [reflexivity|]. split; [lia|]. auto.
- eapply evt_mono.
{ eapply IH with (n := n) (pp := pp - 4096); try lia; [gw_exact ZT'| gw_exact MI']. }
cbv beta. intros ms2 (k & rax & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & -> & HK & MU2 & WM2 & MI2 & ZT2).
unfold zdone_post. exists k. do 16 eexists. exists m2. split; [reflexivity|]. split; [gw_exact HK|].
split; [eapply munch_trans; [gw_exact MU| gw_exact MU2]|]. split; [eapply wmono_trans; [gw_exact WM| gw_exact WM2]|]. auto.
Qed.

#[using="w_7 w_19 w_22 w_23 w_33 w_40 w_56 w_67 w_75 joff_33 joff_40 joff_56 e_memset CODE BASE4 BASER D_33 E_33 D_40 E_40 D_56 E_56 LINK_33 LINK_40 LINK_56 memset_spec"] Lemma zt_clear : forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (p n : Z) junk,
rw_cells segs m p [CB (Z.to_nat n) junk] -> 0 <= n -> 0 < p -> p + n < 2^64 -> mem_inv segs m ->
evt segs (zdone_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p n)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x64)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_19 w_22 w_23 w_33 w_40 w_56 w_67 w_75 joff_33 joff_40 joff_56 e_memset CODE BASE4 BASER D_33 E_33 D_40 E_40 D_56 E_56 LINK_33 LINK_40 LINK_56 memset_spec segs base.
intros until junk. intros BLK N0 P0 N64 MI.
pose proof (ztail_init m p n junk BLK N0) as ZT.

st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{
apply evt_done. unfold zdone_post. exists n. do 16 eexists. exists m.
split; [reflexivity|]. split; [lia|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. auto. }
assert (N4 : 4096 <= n) by (rewrite Z.shiftr_div_pow2 in K by lia; Z.div_mod_to_equations; lia).

st1. st1. st1. st1. st1. st1. st1.
rewrite (unsigned_lit_wrap (Z.shiftl (p + n) 52)), zb_shl_shr by lia. change (2 ^ (64 - 52)) with 4096.
rewrite ?(unsigned_lit (p + n)) by lia. rewrite land_pgmask by lia.
set (i0 := (p + n) mod 4096). assert (I0 : 0 <= i0 < 4096) by (subst i0; apply Z.mod_pos_bound; lia).
replace (p + n - i0) with (p + (n - i0)) by lia.
eapply evt_cut.
{ eapply (zt_memset _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m p n n i0);
[gw_exact ZT| lia| lia| lia| gw_exact MI| reflexivity| reflexivity| reflexivity]. }
cbv beta. intros ms' (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & m' & -> & MU & WM & MI' & ZT').
try g_ret_pc_any.

st1. st1. st1. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
- replace (p + (n - i0) + - p) with (p + (n - i0) - p) by lia.
eapply evt_mono.
{ eapply (zt_outer (Z.to_nat n)) with (n := n); try lia; try gw_exact MI'.
- rewrite Z.shiftr_div_pow2 in K1 by lia. Z.div_mod_to_equations. lia.
- replace (p + (n - i0) - p) with (n - i0) by lia. gw_exact ZT'. }
cbv beta. intros ms2 (k & rax & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & -> & HK & MU2 & WM2 & MI2 & ZT2).
unfold zdone_post. exists k. do 16 eexists. exists m2. split; [reflexivity|]. split; [gw_exact HK|].
split; [eapply munch_trans; [gw_exact MU| gw_exact MU2]|]. split; [eapply wmono_trans; [gw_exact WM| gw_exact WM2]|]. auto.
- st1. apply evt_done. unfold zdone_post. exists (n - i0). do 16 eexists. exists m'.
replace (p + (n - i0) + - p) with (n - i0) by lia.
split; [reflexivity|]. split; [lia|]. auto.
Qed.

Definition zfin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m0 : mem) (p n : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(p, p + n)] m0 m' /\ wmono segs m0 m' /\ mem_inv segs m'
/\ rw_cells segs m' p [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].

#[using="w_7 w_19 w_22 w_23 w_33 w_40 w_56 w_67 w_75 joff_67 e_memset CODE D_67 E_67 LINK_67 memset_spec"] Lemma zt_tail : forall rax (sp : word) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (p n k : Z) (ra s0 s1 : word) (fr0 : list byte),
ztail m p n k -> 0 <= k <= n -> 0 < p -> p + n < 2^64 -> mem_inv segs m ->
rw_cells segs m (bv_unsigned sp) [CB 8 fr0; C8 s1; C8 s0; C8 ra] -> p + n <= bv_unsigned sp ->
evt segs (zfin_post ra (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p n)
(MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 k) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xf0)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_19 w_22 w_23 w_33 w_40 w_56 w_67 w_75 joff_67 e_memset CODE D_67 E_67 LINK_67 memset_spec segs base.
intros until fr0. intros ZT HK P0 N64 MI FR SPB.
pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn [cells_size csize Nat.add] in B.

st1. st1. st1. st1. st1. st1. st1. st1.
replace (Z_to_bv 64 p) with (Z_to_bv 64 (p + (k - k))) at 1 by (f_equal; lia).
eapply evt_mono.
{ eapply (zt_memset _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m p n k k);
[gw_exact ZT| lia| lia| lia| gw_exact MI| reflexivity| reflexivity| reflexivity]. }
cbv beta. intros ms' (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & m' & -> & MU & WM & MI' & ZT').
rewrite Z.sub_diag in ZT'. replace (p + (k - k)) with p by lia.
unfold zfin_post. do 14 eexists. exists m'. split; [reflexivity|]. split; [gw_exact MU|]. split; [gw_exact WM|]. split; [gw_exact MI'|].
apply ztail_all; [gw_exact ZT'| lia].
Qed.

End G.
End Mq8.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE QFkE Q6y7 Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import Q2qa.Mq1 Qy5Y.Mq4 Q4J3.Mq3 QlQE QPjm.Mq1 QPjm.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Qy5Y.Mq6 QPjm.Mq2 QFkE Q6y7 QJE4.Mq2 Q3o5.Mq0 QULt.Mq0.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QDXD.Mq3.
Import QkTt.Mq6.
Import QZxv.Mqp.
Import Qy8Z.Mq6.
Import Q5m9.Mqa.

Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rfree_sym rfree_entry rnontrivial_free_entry : Z).
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rfree_sym : gw_al rfree_sym 4.
Hypothesis AL_rfree_entry : gw_al rfree_entry 4.
Hypothesis AL_rnontrivial_free_entry : gw_al rnontrivial_free_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_0)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_1 := (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) (gw_ent (@Q5m9.Mqa.rimplT segs RC__) (@rimplT) (gw_ent (@QZxv.Mqp.rimplT segs RC__) (@rimplT) gw_tbl_0)))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@Q5m9.Mqa.rpres_except segs) (@rpres_except) (gw_ent (@QZxv.Mqp.rpres_except segs) (@rpres_except) gw_tbl_1))))).
Definition rfree_fp : ltac:(gw_rebind_ty (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qy8Z.Mq6.rfree_fp RATP) (@rfree_fp) (gw_ent (@QDXD.Mq2.rfree_fp RATP) (@rfree_fp) (gw_ent (@Q5m9.Mqa.rfree_fp RATP) (@rfree_fp) (gw_ent (@QZxv.Mqp.rfree_fp RATP) (@rfree_fp) gw_tbl_2)))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Qy8Z.Mq6.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq6.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Q5m9.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QZxv.Mqp.rarea_rep segs) (@rarea_rep) gw_tbl_3))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Qy8Z.Mq6.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq6.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q5m9.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QZxv.Mqp.rmrep_areas segs) (@rmrep_areas) gw_tbl_4))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Qy8Z.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q5m9.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QZxv.Mqp.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_5))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Qy8Z.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q5m9.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QZxv.Mqp.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_6))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Qy8Z.Mq6.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq6.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q5m9.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QZxv.Mqp.rgroup_rep segs) (@rgroup_rep) gw_tbl_7))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Qy8Z.Mq6.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq6.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q5m9.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QZxv.Mqp.rmrep_groups segs) (@rmrep_groups) gw_tbl_8))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Qy8Z.Mq6.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq6.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q5m9.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QZxv.Mqp.rshadow_rep segs) (@rshadow_rep) gw_tbl_9))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Qy8Z.Mq6.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq6.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q5m9.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QZxv.Mqp.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_10))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Qy8Z.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q5m9.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QZxv.Mqp.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_11))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Qy8Z.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q5m9.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QZxv.Mqp.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_12))))))))).
Definition rfree_end : ltac:(gw_rebind_ty (@Q5m9.Mqa.rfree_end segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q5m9.Mqa.rfree_end segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@Q5m9.Mqa.rfree_end segs RATP RGOT_SSP ref_reserved RC__) (@rfree_end) gw_tbl_13).
Definition RFREE_SYM : ltac:(gw_rebind_ty (@QDXD.Mq3.RFREE_SYM rfree_sym) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QDXD.Mq3.RFREE_SYM rfree_sym) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@QDXD.Mq3.RFREE_SYM rfree_sym) (@RFREE_SYM) gw_tbl_14).
Definition RHEAP : ltac:(gw_rebind_ty (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@QkTt.Mq6.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) (gw_ent (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) gw_tbl_15)).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@QkTt.Mq6.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq3.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_16))).
Definition ralloc_static : ltac:(gw_rebind_ty (@QDXD.Mq3.ralloc_static RATP) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QDXD.Mq3.ralloc_static RATP) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@QkTt.Mq6.ralloc_static RATP) (@ralloc_static) (gw_ent (@QDXD.Mq3.ralloc_static RATP) (@ralloc_static) gw_tbl_17)).
Definition rclient_addr : ltac:(gw_rebind_ty (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@QkTt.Mq6.rclient_addr RATP RIMG_HI RDATA_LO) (@rclient_addr) (gw_ent (@QDXD.Mq3.rclient_addr RATP RIMG_HI RDATA_LO) (@rclient_addr) gw_tbl_18)).
Definition rheap_pres : ltac:(gw_rebind_ty (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@QkTt.Mq6.rheap_pres segs RATP RIMG_HI RDATA_LO) (@rheap_pres) (gw_ent (@QDXD.Mq3.rheap_pres segs RATP RIMG_HI RDATA_LO) (@rheap_pres) gw_tbl_19)).
Definition rfree_post : ltac:(gw_rebind_ty (@QDXD.Mq3.rfree_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rfree_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) constr:(gw_tbl_20)).
Notation gw_tbl_21 := (gw_ent (@QkTt.Mq6.rfree_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rfree_post) (gw_ent (@QDXD.Mq3.rfree_post segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved RC__) (@rfree_post) gw_tbl_20)).
Definition rfree_stmt : ltac:(gw_rebind_ty (@QDXD.Mq3.rfree_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rfree_sym RC__) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rfree_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rfree_sym RC__) constr:(gw_tbl_21)).
Notation gw_tbl_22 := (gw_ent (@QDXD.Mq3.rfree_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rfree_sym RC__) (@rfree_stmt) gw_tbl_21).
Definition rfree_impl_stmt : ltac:(gw_rebind_ty (@QkTt.Mq6.rfree_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rfree_entry RC__) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QkTt.Mq6.rfree_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rfree_entry RC__) constr:(gw_tbl_22)).
Notation gw_tbl_23 := (gw_ent (@QkTt.Mq6.rfree_impl_stmt segs RATP RGOT_SSP RIMG_HI RDATA_LO ref_reserved rfree_entry RC__) (@rfree_impl_stmt) gw_tbl_22).

Hypothesis rfree_fp_lt : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QZxv.Mqp.gw_all) (@QZxv.Mqp.rfree_fp_lt) rnontrivial_free_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_23))) in exact T).

Hypothesis rlibc_free_implT : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q5m9.Mqa.gw_all) (@Q5m9.Mqa.rlibc_free_implT) rfree_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_23))) in exact T).
Hypothesis rfree_stmt_of_impl : gw_hyp (rfree_impl_stmt -> rfree_stmt).

Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_23)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_23)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_23)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rimplT_reach : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_reach) constr:(gw_tbl_23)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_reach)).
#[global] Arguments rimplT_reach {R}%_type_scope o t s Q%_function_scope ms _.
Definition rraw_free_bridge : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rraw_free_bridge) constr:(gw_tbl_23)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rraw_free_bridge)).
Definition rpres_except_bytes_at : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_bytes_at) constr:(gw_tbl_23)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_bytes_at)).
Definition rpres_except_rw_cells : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_rw_cells) constr:(gw_tbl_23)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_rw_cells)).

#[using="rfree_entry rnontrivial_free_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rfree_sym RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rfree_sym AL_rfree_entry AL_rnontrivial_free_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rfree_fp_lt rlibc_free_implT rfree_stmt_of_impl"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="Type"] Lemma rauxv_ok_pres_B : forall C m m' B,
rauxv_ok m B -> rpres_except C m m' ->
(forall a, B <= a -> ~ C a) -> (forall a, (RATP + 131736) <= a < (RATP + 131744) -> ~ C a) ->
rauxv_ok m' B.
Proof. clear - RATP. gw_expose_fam RATP.
intros C m m' B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) HP HB HC.
exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|gw_exact H]]].
- eapply rpres_except_rw_cells; [gw_exact HP| gw_exact C1|]. cbn. intros a Ha. apply HC. lia.
- eapply rpres_except_bytes_at; [gw_exact HP| gw_exact A1|]. intros a Ha. apply HB. lia.
- eapply rpres_except_bytes_at; [gw_exact HP| gw_exact A2|]. intros a Ha. apply HB. lia.
Qed.

Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ (RATP + -164) <= a < (RATP + -164 + 4)) m m'.

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ (RATP + -164) <= a < (RATP + -164 + 4).

#[using="segs RGOT_SSP RIMG_HI ref_reserved LAY_hi_RATP LAY_win_4 rfree_fp_lt RC__ m MR LO LS"] Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof. clear - segs RGOT_SSP RIMG_HI ref_reserved LAY_hi_RATP LAY_win_4 rfree_fp_lt RC__ m MR LO LS a RATP st st' LB0 blk lo sp m' C BLKR SHR PE FPT. gw_expose_fam RATP. first [clear FPT | gw_hide FPT | idtac]; first [clear PE | gw_hide PE | idtac]; first [clear SHR | gw_hide SHR | idtac]; first [clear BLKR | gw_hide BLKR | idtac]; first [clear C | gw_hide C | idtac]; first [clear m' | gw_hide m' | idtac]; try gw_hide sp; try gw_hide lo; first [clear blk | gw_hide blk | idtac]; first [clear LB0 | gw_hide LB0 | idtac]; first [clear st' | gw_hide st' | idtac]; try gw_hide st.
intros Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
intros [FP|[DR|ER]].
- pose proof (rfree_fp_lt st m lo sp a MR ltac:(unfold alloc_ceiling; lia) LS FP). lia.
- destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- lia.
Qed.

#[using="segs RGOT_SSP gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved RC__ m MR LO"] Lemma rfp_not_img a : RDATA_LO <= a < RIMG_HI -> ~ ((RATP + 131968) <= a < (RATP + 132896)) -> ~ ((RATP + -164) <= a < (RATP + -164 + 4)) -> ~ FPT a.
Proof. clear - segs RGOT_SSP gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved RC__ m MR LO RATP RIMG_HI RDATA_LO a st st' LB0 blk lo sp m' C LS BLKR SHR PE FPT. gw_expose_fam RATP. first [clear FPT | gw_hide FPT | idtac]; first [clear PE | gw_hide PE | idtac]; first [clear SHR | gw_hide SHR | idtac]; first [clear BLKR | gw_hide BLKR | idtac]; first [clear LS | gw_hide LS | idtac]; first [clear C | gw_hide C | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear blk | gw_hide blk | idtac]; first [clear LB0 | gw_hide LB0 | idtac]; first [clear st' | gw_hide st' | idtac]; try gw_hide st.
intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ exact (N1 X).
+ destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
+ destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
+ destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- exact (N2 ER).
Qed.

#[using="segs RGOT_SSP gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved RC__ m MR LO"] Lemma rfp_not_image a : RDATA_LO <= a < RIMG_HI -> ~ ralloc_static a -> ~ FPT a.
Proof. clear - segs RGOT_SSP gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved RC__ m MR LO RIMG_HI RDATA_LO a RATP st st' LB0 blk lo sp m' C LS BLKR SHR PE FPT. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. first [clear FPT | gw_hide FPT | idtac]; first [clear PE | gw_hide PE | idtac]; first [clear SHR | gw_hide SHR | idtac]; first [clear BLKR | gw_hide BLKR | idtac]; first [clear LS | gw_hide LS | idtac]; first [clear C | gw_hide C | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear blk | gw_hide blk | idtac]; first [clear LB0 | gw_hide LB0 | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear st | gw_hide st | idtac].
intros Ha NS. apply rfp_not_img; [gw_exact Ha| |]; intros X; apply NS; (gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold ralloc_static in *); lia.
Qed.

#[using="segs RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_ref_reserved RC__ m C MR LO BLKR SHR"] Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof. clear - segs RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_ref_reserved RC__ m C MR LO BLKR SHR blk' a RATP st st' LB0 blk lo sp m' LS PE FPT. gw_expose_fam RATP. first [clear FPT | gw_hide FPT | idtac]; first [clear PE | gw_hide PE | idtac]; first [clear LS | gw_hide LS | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear lo | gw_hide lo | idtac]; first [clear blk | gw_hide blk | idtac]; first [clear LB0 | gw_hide LB0 | idtac]; first [clear st' | gw_hide st' | idtac]; try gw_hide st.
intros Hb' Hab. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
destruct (UNK a Hab) as [h UNKa].
destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF). pose proof (rreserved_disjoint _ _ RGF) as (?&?&?&?). unfold alloc_ceiling in RGC.
pose proof (lr_lo_group rg Krg) as LRG.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ gw_expose_fam RATP. lia.
+ destruct X as (rid & r & Hr & NK & Hin).
assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
destruct (DJ _ _ _ _ Hr Hrg NE); lia.
+ destruct X as (b & gh & Hb & Hin). destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
* specialize (HD b gh Hb E). unfold IB in HD. lia.
* destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
+ destruct X as (rid & r & v & Hr & Kr & Hin & HC). destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
* rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
* pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
- destruct DR as (rid & r & Hr & Hr' & Kr & Hin).
destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
- lia.
Qed.

#[using="RGOT_SSP gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rfree_fp_lt RC__ st st' lo C MR LO LS BLKR SHR PE FPT"] Lemma rheap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> rheap_pres LB' sp m m'.
Proof. clear - RGOT_SSP gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rfree_fp_lt RC__ st st' lo C MR LO LS BLKR SHR PE FPT LB' LB0 blk sp m m'. first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear blk | gw_hide blk | idtac]; first [clear LB0 | gw_hide LB0 | idtac].
intros HLB a Ha CA. apply PE; [gw_exact Ha|].
destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
- apply rfp_not_high. gw_exact CA.
- apply rfp_not_image; assumption.
- apply (rfp_not_block blk' a); [apply HLB; gw_exact Hb'| gw_exact Hab].
Qed.

#[using="RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rfree_fp_lt st st' lo MR LO LS PE FPT"] Lemma rauxv_ok_free B : rauxv_ok m B -> sp <= B -> rauxv_ok m' B.
Proof. clear - RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rfree_fp_lt st st' lo MR LO LS PE FPT B RATP LB0 blk sp m m' C BLKR SHR. gw_expose_fam RATP. first [clear SHR | gw_hide SHR | idtac]; first [clear BLKR | gw_hide BLKR | idtac]; first [clear C | gw_hide C | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear blk | gw_hide blk | idtac]; first [clear LB0 | gw_hide LB0 | idtac].
intros AV HB. eapply rauxv_ok_pres_B; [gw_exact AV | gw_exact PE | |].
- intros a Ha. apply rfp_not_high. lia.
- intros a Ha. apply rfp_not_img; gw_expose_fam RATP; lia.
Qed.
End FP.

#[using="gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rfree_fp_lt rlibc_free_implT"] Theorem rfree_impl_spec_proof : rfree_impl_stmt.
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rfree_fp_lt rlibc_free_implT rfree_entry.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
HP Hin AV HB ST LO SLO ERR MI TP A0.
destruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]).
assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; gw_exact PERM| gw_exact Hin]).
pose proof (QNAo.Mq2.areach_cinv_proof _ _ AR) as C.
pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
cbn [blk_addr blk_slot fst snd] in OA.
pose proof (Q3o5.Mq1.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.
eapply (rraw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
(fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
/\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
- gw_exact Hst.
- gw_exact HOK.
- apply rimplT_reach.
replace (Z_to_bv 64 rfree_entry) with (Z_to_bv 64 (rfree_entry + 0)) by (rewrite Z.add_0_r; reflexivity).
apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
[unfold RFREE_STACK in SLO; lia | gw_exact ERR | gw_exact A0].
- intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR).
pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_STACK in SLO; lia).
unfold rfree_post. do 16 eexists. split; [reflexivity|].
split; [gw_exact MI'|]. split; [gw_exact ST'|]. split; [gw_exact ERR'|].
split; [exact (rauxv_ok_free st st' lo (bv_unsigned sp) m m' MR LO SLO' PE B AV HB)|].
split. { apply (rheap_pres_free st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO SLO' BLKR SHR PE).
intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; gw_exact PERM| gw_exact Hb']. }
split; [reflexivity|]. split; [reflexivity|].
exists st', (lbrm LB0 (p, A, n)). split; [rewrite ELB; apply lbrm_perm; gw_exact PERM|].
split; [reflexivity|]. split; [gw_exact MR'|]. split.
+  unfold brk_link. cbn [ps_brk set_m]. rewrite EB. unfold brk_link in BL.
destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [gw_exact Logic.I| gw_exact Logic.I|].
rewrite ?HB0 in BL. unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [gw_exact HB0 | reflexivity])). gw_exact BL.
+ destruct LEAF as (ans & o' & FO).
eapply (areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | gw_exact FO].
cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
cbn [fst]. rewrite <- FB. destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _). rewrite Hr. eexists; reflexivity.
Qed.

#[using="gw_RTEXT_LO gw_RDATA2_LO rfree_entry LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rfree_fp_lt rlibc_free_implT rfree_stmt_of_impl"] Theorem rfree_spec_proof : rfree_stmt.
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO rfree_entry LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rfree_fp_lt rlibc_free_implT rfree_stmt_of_impl. exact (rfree_stmt_of_impl rfree_impl_spec_proof). Qed.

End RC__1.

End G.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 Qy5Y.Mq4 Q4J3.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 Q9Ay.Mqa QXxF.Mq3 QDUx.Mq9 Q6y7.Mq2 QDUx.Mq7 Q3o5 Q8P7 QTyG.Mq1.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import Q8QT.Mq2.
Import QDXD.Mq1.
Import QkTt.Mq5.
Import QCa8.Mq3.
Import Qy8Z.Mq7.
Import Qy8Z.Mq1.
Import Qy8Z.Mq8.
Import QQRC.Mq8.
Import Q8l1.Mq8.
Import QROt.Mq5.
Import Qy8Z.Mqa.
Import QQRC.Mq7.

Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rsysret_entry rvm_wait_entry rlock_entry runlock_entry : Z).
Variables (w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 : Z).
Variables (hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 : bv 20).
Variables (lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 : bv 12).
Variables (joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 : bv 21).
Hypothesis CODE : code_at segs base (malloc_code w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 880.
Let ralloc_meta_entry := (base + -728)%Z.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Let rmunmap_entry := (rvm_wait_entry + 524)%Z.
Hypothesis D_11 : decode_any (Z_to_bv 32 w_11) = Some (Jal 1 joff_11, 4%Z).
Hypothesis E_11 : is_ecall (Z_to_bv 32 w_11) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 11 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 9 11 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_37 : decode_any (Z_to_bv 32 w_37) = Some (Jal 1 joff_37, 4%Z).
Hypothesis E_37 : is_ecall (Z_to_bv 32 w_37) = false.
Hypothesis D_40 : decode_any (Z_to_bv 32 w_40) = Some (Auipc 10 hi_40, 4%Z).
Hypothesis E_40 : is_ecall (Z_to_bv 32 w_40) = false.
Hypothesis D_41 : decode_any (Z_to_bv 32 w_41) = Some (Load SZ1 false 10 10 lo_41, 4%Z).
Hypothesis E_41 : is_ecall (Z_to_bv 32 w_41) = false.
Hypothesis D_43 : decode_any (Z_to_bv 32 w_43) = Some (Auipc 10 hi_43, 4%Z).
Hypothesis E_43 : is_ecall (Z_to_bv 32 w_43) = false.
Hypothesis D_44 : decode_any (Z_to_bv 32 w_44) = Some (OpImm ALU_ADD 10 10 lo_44, 4%Z).
Hypothesis E_44 : is_ecall (Z_to_bv 32 w_44) = false.
Hypothesis D_45 : decode_any (Z_to_bv 32 w_45) = Some (Jal 1 joff_45, 4%Z).
Hypothesis E_45 : is_ecall (Z_to_bv 32 w_45) = false.
Hypothesis D_57 : decode_any (Z_to_bv 32 w_57) = Some (Auipc 12 hi_57, 4%Z).
Hypothesis E_57 : is_ecall (Z_to_bv 32 w_57) = false.
Hypothesis D_59 : decode_any (Z_to_bv 32 w_59) = Some (OpImm ALU_ADD 19 12 lo_59, 4%Z).
Hypothesis E_59 : is_ecall (Z_to_bv 32 w_59) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 12 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_90 : decode_any (Z_to_bv 32 w_90) = Some (OpImm ALU_ADD 11 12 lo_90, 4%Z).
Hypothesis E_90 : is_ecall (Z_to_bv 32 w_90) = false.
Hypothesis D_125 : decode_any (Z_to_bv 32 w_125) = Some (Auipc 10 hi_125, 4%Z).
Hypothesis E_125 : is_ecall (Z_to_bv 32 w_125) = false.
Hypothesis D_126 : decode_any (Z_to_bv 32 w_126) = Some (Load SZ1 false 10 10 lo_126, 4%Z).
Hypothesis E_126 : is_ecall (Z_to_bv 32 w_126) = false.
Hypothesis D_128 : decode_any (Z_to_bv 32 w_128) = Some (Auipc 10 hi_128, 4%Z).
Hypothesis E_128 : is_ecall (Z_to_bv 32 w_128) = false.
Hypothesis D_129 : decode_any (Z_to_bv 32 w_129) = Some (OpImm ALU_ADD 10 10 lo_129, 4%Z).
Hypothesis E_129 : is_ecall (Z_to_bv 32 w_129) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Jal 1 joff_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_147 : decode_any (Z_to_bv 32 w_147) = Some (Auipc 10 hi_147, 4%Z).
Hypothesis E_147 : is_ecall (Z_to_bv 32 w_147) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (OpImm ALU_ADD 10 10 lo_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (Jal 1 joff_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_152 : decode_any (Z_to_bv 32 w_152) = Some (Jal 1 joff_152, 4%Z).
Hypothesis E_152 : is_ecall (Z_to_bv 32 w_152) = false.
Hypothesis D_203 : decode_any (Z_to_bv 32 w_203) = Some (Jal 1 joff_203, 4%Z).
Hypothesis E_203 : is_ecall (Z_to_bv 32 w_203) = false.
Hypothesis D_216 : decode_any (Z_to_bv 32 w_216) = Some (Auipc 10 hi_216, 4%Z).
Hypothesis E_216 : is_ecall (Z_to_bv 32 w_216) = false.
Hypothesis D_217 : decode_any (Z_to_bv 32 w_217) = Some (OpImm ALU_ADD 10 10 lo_217, 4%Z).
Hypothesis E_217 : is_ecall (Z_to_bv 32 w_217) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Jal 1 joff_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131960).
Hypothesis ANCH_41 : gw_anch (Z.shiftl (bv_signed hi_40) 12 + (base + 160) + bv_signed lo_41)%Z (RATP + 131731).
Hypothesis ANCH_44 : gw_anch (Z.shiftl (bv_signed hi_43) 12 + (base + 172) + bv_signed lo_44)%Z (RATP + 131960).
Hypothesis ANCH_59 : gw_anch (Z.shiftl (bv_signed hi_57) 12 + (base + 228) + bv_signed lo_59)%Z RDEBRUIJN.
Hypothesis ANCH_90 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_90)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_126 : gw_anch (Z.shiftl (bv_signed hi_125) 12 + (base + 500) + bv_signed lo_126)%Z (RATP + 131731).
Hypothesis ANCH_129 : gw_anch (Z.shiftl (bv_signed hi_128) 12 + (base + 512) + bv_signed lo_129)%Z (RATP + 131960).
Hypothesis ANCH_148 : gw_anch (Z.shiftl (bv_signed hi_147) 12 + (base + 588) + bv_signed lo_148)%Z (RATP + 131960).
Hypothesis ANCH_217 : gw_anch (Z.shiftl (bv_signed hi_216) 12 + (base + 864) + bv_signed lo_217)%Z (RATP + 131960).
Hypothesis LINK_11 : gw_anch (base + 44 + bv_signed joff_11)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_37 : gw_anch (base + 148 + bv_signed joff_37)%Z (rvm_wait_entry + 4)%Z.
Hypothesis LINK_45 : gw_anch (base + 180 + bv_signed joff_45)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_130 : gw_anch (base + 520 + bv_signed joff_130)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_149 : gw_anch (base + 596 + bv_signed joff_149)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_152 : gw_anch (base + 608 + bv_signed joff_152)%Z (rvm_wait_entry + 524)%Z.
Hypothesis LINK_203 : gw_anch (base + 812 + bv_signed joff_203)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_218 : gw_anch (base + 872 + bv_signed joff_218)%Z (runlock_entry + 0)%Z.
Hypothesis CODE_rerrno_loc_entry : code_at segs rerrno_loc_entry errno_loc_code.
Hypothesis AL_rerrno_loc_entry_b4 : gw_b4 rerrno_loc_entry.
Hypothesis RNG_rerrno_loc_entry_code : gw_br rerrno_loc_entry 12.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rsysret_entry : gw_al rsysret_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis AL_rlock_entry : gw_al rlock_entry 4.
Hypothesis AL_runlock_entry : gw_al runlock_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rmunmap_post : ltac:(gw_rebind_ty (@Q8QT.Mq2.rmunmap_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq2.rmunmap_post segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Q8QT.Mq2.rmunmap_post segs) (@rmunmap_post) gw_tbl_0).
Definition rmmap_anon_post : ltac:(gw_rebind_ty (@Q8QT.Mq2.rmmap_anon_post segs RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq2.rmmap_anon_post segs RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Q8QT.Mq2.rmmap_anon_post segs RC__) (@rmmap_anon_post) gw_tbl_1).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QROt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Q8l1.Mq8.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QQRC.Mq8.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_2)))))).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QROt.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Q8l1.Mq8.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QQRC.Mq8.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_3)))))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QQRC.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8l1.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_4))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QQRC.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8l1.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_5))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QQRC.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8l1.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_6))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QQRC.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8l1.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_7))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QQRC.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8l1.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_8))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QQRC.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8l1.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_9))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QQRC.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8l1.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_10))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QQRC.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8l1.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_11))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QQRC.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8l1.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_12))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QQRC.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8l1.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_13))))))))))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@QROt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@Q8l1.Mq8.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq8.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq7.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_14)))))))))).
Definition ram_post : ltac:(gw_rebind_ty (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@QCa8.Mq5.ram_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_post) gw_tbl_15).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_16)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_17 := (gw_ent (@QROt.Mq5.rimplT segs RC__) (@rimplT) (gw_ent (@Q8l1.Mq8.rimplT segs RC__) (@rimplT) (gw_ent (@QQRC.Mq8.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq7.rimplT segs RC__) (@rimplT) (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_16))))))).
Definition ralloc_meta_stmt : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@QCa8.Mq5.ralloc_meta_stmt segs RATP RGOT_SSP ref_reserved ralloc_meta_entry RC__) (@ralloc_meta_stmt) gw_tbl_17).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@QROt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Q8l1.Mq8.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QQRC.Mq8.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_18))))).
Definition rcoreQ : ltac:(gw_rebind_ty (@QROt.Mq5.rcoreQ segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QROt.Mq5.rcoreQ segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@QROt.Mq5.rcoreQ segs base RATP RGOT_SSP ref_reserved RC__) (@rcoreQ) gw_tbl_19).
Definition rbig_stmt : ltac:(gw_rebind_ty (@QROt.Mq5.rbig_stmt segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QROt.Mq5.rbig_stmt segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_20)).
Notation gw_tbl_21 := (gw_ent (@QROt.Mq5.rbig_stmt segs base RATP RGOT_SSP ref_reserved RC__) (@rbig_stmt) gw_tbl_20).
Definition rseq_post : ltac:(gw_rebind_ty (@QQRC.Mq7.rseq_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@QQRC.Mq7.rseq_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_21)).
Notation gw_tbl_22 := (gw_ent (@QQRC.Mq7.rseq_post segs base RATP RGOT_SSP ref_reserved RC__) (@rseq_post) gw_tbl_21).
Definition runlock_post : ltac:(gw_rebind_ty (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_22)).
Notation gw_tbl_23 := (gw_ent (@QQRC.Mq7.runlock_post segs) (@runlock_post) (gw_ent (@QROt.Mq5.runlock_post segs) (@runlock_post) (gw_ent (@Q8l1.Mq8.runlock_post segs) (@runlock_post) (gw_ent (@Qy8Z.Mq7.runlock_post segs) (@runlock_post) (gw_ent (@QCa8.Mq4.runlock_post segs) (@runlock_post) gw_tbl_22))))).
Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_23)).
Notation gw_tbl_24 := (gw_ent (@QQRC.Mq7.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QROt.Mq5.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QkTt.Mq4.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QkTt.Mq3.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_23))))).

Hypothesis rmunmap_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8QT.Mq2.gw_all) (@Q8QT.Mq2.rmunmap_spec) rvm_wait_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_24))) in exact T).
Hypothesis rmmap_anon_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8QT.Mq2.gw_all) (@Q8QT.Mq2.rmmap_anon_spec) rvm_wait_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_24))) in exact T).
Hypothesis runlock_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.runlock_spec) (base + -1984)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_24))) in let T := gw_fold_pcs T base (-1984)%Z [0; 244]%Z in exact T).
Hypothesis land_m4096 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq3.gw_all) (@QCa8.Mq3.land_m4096) (base + 3092)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_24))) in let T := gw_fold_pcs T base (3092)%Z [0; 36; 64; 124; 184; 220]%Z in exact T).

Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rreserved_disjoint1 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint1) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint1)).
Definition rmrep_ctx_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_ctx_ext) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_ctx_ext)).
Definition rarea_rep_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_rep_ext) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_rep_ext)).
Definition rgroup_rep_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_rep_ext) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_rep_ext)).
Definition rshadow_rep_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rshadow_rep_ext) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rshadow_rep_ext)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_ret : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_ret) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_ret)).
#[global] Arguments rimplT_ret {R}%_type_scope o r s Q%_function_scope ms _.
Definition rimplT_undef : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_undef) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_undef)).
#[global] Arguments rimplT_undef {R}%_type_scope o w k%_function_scope s Q%_function_scope ms.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rimplT_mmap_rw : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_mmap_rw) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_mmap_rw)).
#[global] Arguments rimplT_mmap_rw {R}%_type_scope o len%_Z_scope k%_function_scope s P%_function_scope Q%_function_scope ms _ _%_function_scope.
Definition rimplT_munmap : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_munmap) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_munmap)).
#[global] Arguments rimplT_munmap {R}%_type_scope o addr%_Z_scope len%_Z_scope k%_function_scope s P%_function_scope Q%_function_scope ms _ _%_function_scope.
Definition rauxv_ok_weaken : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rauxv_ok_weaken) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rauxv_ok_weaken)).
Definition rauxv_ok_frame : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rauxv_ok_frame) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rauxv_ok_frame)).
Definition rpres_except_refl : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_refl) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_refl)).
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).
Definition rpres_except_of_munch : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_of_munch) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_of_munch)).
Definition rpres_except_rw_cells : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_rw_cells) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_rw_cells)).
Ltac riprefixT := apply rimplT_from_evt.

Definition rmrep_transport_unowned : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_transport_unowned) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_transport_unowned)).

Definition rmeta_chunk_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmeta_chunk_facts) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmeta_chunk_facts)).
Definition rregion_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rregion_facts) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rregion_facts)).
Definition rmalloc_fp_mono : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmalloc_fp_mono) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmalloc_fp_mono)).

Definition rauxv_ok_malloc_fp : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq8.rauxv_ok_malloc_fp) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq8.rauxv_ok_malloc_fp)).

Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs_ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs_ m A ?cs0 |- _ =>
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs_ m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs_ m |- _ =>
apply (mem_inv_store_cbytes segs_ m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs_ m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs_ m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs_ m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs_ m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end.
Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs_ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs_ m A ?cs0 |- _ =>
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs_ m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs_ m |- _ =>
apply (mem_inv_store_cbytes segs_ m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs_ m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs_ m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs_ m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs_ m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.

Notation RAREACH := (AREACH_from ref_reserved rc_secret).

Definition rrw_cells_agree : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rrw_cells_agree) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rrw_cells_agree)).
Definition rnr_old_disjoint : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rnr_old_disjoint) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rnr_old_disjoint)).
Definition rmrep_new_region : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rmrep_new_region) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rmrep_new_region)).
Definition rmrep_drop_region : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mqa.rmrep_drop_region) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mqa.rmrep_drop_region)).

Definition rbig_fail1_walk : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq7.rbig_fail1_walk) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq7.rbig_fail1_walk)).
Definition rbig_fail2b_walk : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq7.rbig_fail2b_walk) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq7.rbig_fail2b_walk)).
Definition rbig_fail2a_walk : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq7.rbig_fail2a_walk) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq7.rbig_fail2a_walk)).
Definition rbig_seq_walk : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq7.rbig_seq_walk) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq7.rbig_seq_walk)).
Definition rbig_succ_walk : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq7.rbig_succ_walk) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq7.rbig_succ_walk)).

#[using="RDEBRUIJN rerrno_loc_entry rsysret_entry rvm_wait_entry rmmap_entry rmunmap_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rsysret_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ralloc_meta_entry rmmap_entry rmunmap_entry rmunmap_spec rmmap_anon_spec runlock_spec land_m4096"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 RDEBRUIJN rerrno_loc_entry rsysret_entry rvm_wait_entry rmmap_entry rmunmap_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rsysret_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ralloc_meta_entry rmunmap_spec rmmap_anon_spec runlock_spec land_m4096 | clear - hs segs base w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 RDEBRUIJN rerrno_loc_entry rsysret_entry rvm_wait_entry rmmap_entry rmunmap_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rsysret_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay ralloc_meta_entry rmunmap_spec rmmap_anon_spec runlock_spec land_m4096].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="Type"] Lemma rmrep_ext : forall st st' m,
rmrep st m ->
s_regions st' = s_regions st -> ctx st' = ctx st -> (forall q, get_meta_rec st' q = get_meta_rec st q) ->
s_areas st' = s_areas st -> s_groups st' = s_groups st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
s_reserved st' = s_reserved st ->
rmrep st' m.
Proof. clear - segs.
intros st st' m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [|split; [gw_exact GL|split; [|split]]]].
- unfold rregions_wf. rewrite ER, EA, EG, ERs. gw_exact WF.
- eapply rmrep_ctx_ext; [gw_exact EC| gw_exact Hconc| gw_exact CX].
- intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [gw_exact Hconc| intros; apply EM| exact (AR a ar Ha)].
- intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [gw_exact Hconc| exact (GR b gh Hb)].
- intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^63.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

#[using="G0"] Lemma rbf_meta : get_meta_rec stF g = big_meta rid n.
Proof. clear - G0 st3 g rid xa n c GN HC NR RR stF stM. first [clear stM | gw_hide stM | idtac]; try gw_hide stF; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac].
unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
rewrite G0. reflexivity.
Qed.

#[using="Type"] Lemma rbf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof. clear - q st3 g rid xa n c G0 GN HC NR RR stF stM. first [clear stM | gw_hide stM | idtac]; try gw_hide stF; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac].
intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma rbm_meta : get_meta_rec stM g = big_meta rid n.
Proof. clear - st3 g rid xa n c G0 GN HC NR RR stF stM. try gw_hide stM; first [clear stF | gw_hide stF | idtac]; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac]. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma rbm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof. clear - q st3 g rid xa n c G0 GN HC NR RR stF stM. try gw_hide stM; first [clear stF | gw_hide stF | idtac]; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac].
intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma rbf_regions : s_regions stF = s_regions st3. Proof. clear - st3 g rid xa n c G0 GN HC NR RR stF stM. first [clear stM | gw_hide stM | idtac]; first [clear stF | gw_hide stF | idtac]; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac]. reflexivity. Qed.
#[using="Type"] Lemma rbf_areas : s_areas stF = s_areas st3. Proof. clear - st3 g rid xa n c G0 GN HC NR RR stF stM. first [clear stM | gw_hide stM | idtac]; first [clear stF | gw_hide stF | idtac]; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac]. reflexivity. Qed.
#[using="Type"] Lemma rbf_reserved : s_reserved stF = s_reserved st3. Proof. clear - st3 g rid xa n c G0 GN HC NR RR stF stM. first [clear stM | gw_hide stM | idtac]; first [clear stF | gw_hide stF | idtac]; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac]. reflexivity. Qed.
#[using="Type"] Lemma rbf_next : s_next_rid stF = s_next_rid st3. Proof. clear - st3 g rid xa n c G0 GN HC NR RR stF stM. first [clear stM | gw_hide stM | idtac]; first [clear stF | gw_hide stF | idtac]; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac]. reflexivity. Qed.
#[using="GN"] Lemma rbf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. clear - GN st3 g rid xa n c G0 HC NR RR stF stM. first [clear stM | gw_hide stM | idtac]; try gw_hide stF; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac].
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
rewrite GN. reflexivity.
Qed.
#[using="Type"] Lemma rbm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. clear - st3 g rid xa n c G0 GN HC NR RR stF stM. first [clear stM | gw_hide stM | idtac]; first [clear stF | gw_hide stF | idtac]; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac]. reflexivity. Qed.
#[using="Type"] Lemma rbf_shadow q : get_shadow stF q = get_shadow stM q.
Proof. clear - q st3 g rid xa n c G0 GN HC NR RR stF stM. first [clear stM | gw_hide stM | idtac]; first [clear stF | gw_hide stF | idtac]; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac]. reflexivity. Qed.
#[using="Type"] Lemma rbf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof. clear - q st3 g rid xa n c G0 GN HC NR RR stF stM. first [clear stM | gw_hide stM | idtac]; try gw_hide stF; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac].
intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="HC"] Lemma rbf_ctx : ctx stF = ctx stM.
Proof. clear - HC st3 g rid xa n c G0 GN NR RR stF stM. try gw_hide stM; try gw_hide stF; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac]. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
#[using="HC stM"] Lemma rbf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof. clear - HC stM st3 g rid xa n c G0 GN NR RR stF. first [clear stF | gw_hide stF | idtac]; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac]. rewrite rbf_ctx. reflexivity. Qed.

#[using="G0 GN HC"] Lemma rmrep_big_final m : rmrep stM m -> rmrep stF m.
Proof. clear - G0 GN HC m st3 g rid xa n c NR RR stF stM. try gw_hide stM; try gw_hide stF; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; try gw_hide g; first [clear st3 | gw_hide st3 | idtac].
intros MR. eapply (rmrep_ext stM stF m MR); try reflexivity.
- gw_exact rbf_ctx.
- intros q. destruct (decide (q = g)) as [->|NE]; [rewrite rbf_meta, rbm_meta; reflexivity| rewrite rbf_meta_other, rbm_meta_other by gw_exact NE; reflexivity].
- rewrite rbf_groups, rbm_groups. reflexivity.
Qed.

#[using="Type"] Lemma rticks_ok_big_final : ticks_ok stM -> ticks_ok stF.
Proof. clear - st3 g rid xa n c G0 GN HC NR RR stF stM. first [clear stM | gw_hide stM | idtac]; first [clear stF | gw_hide stF | idtac]; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac]. intros H; gw_exact H. Qed.

#[using="base rvm_wait_entry ralloc_meta_entry rmmap_entry rmunmap_entry NR"] Lemma rbf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmmap_entry rmunmap_entry NR st3 g rid xa n c G0 GN HC RR stF stM. first [clear stM | gw_hide stM | idtac]; first [clear stF | gw_hide stF | idtac]; first [clear RR | gw_hide RR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; try gw_hide n; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac].
unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.

#[using="Type"] Lemma rbf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof. clear - st3 g rid xa n c G0 GN HC NR RR stF stM. first [clear stM | gw_hide stM | idtac]; try gw_hide stF; first [clear RR | gw_hide RR | idtac]; first [clear NR | gw_hide NR | idtac]; first [clear HC | gw_hide HC | idtac]; first [clear GN | gw_hide GN | idtac]; first [clear G0 | gw_hide G0 | idtac]; first [clear c | gw_hide c | idtac]; first [clear n | gw_hide n | idtac]; first [clear xa | gw_hide xa | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear g | gw_hide g | idtac]; first [clear st3 | gw_hide st3 | idtac].
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.

#[using="base RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmmap_entry rmunmap_entry"] Lemma rrepfoot_where2 st m a : rmrep st m -> rrepfoot st a ->
a < alloc_ceiling /\ ((RATP + 131968) <= a < (RATP + 132896) \/ (RATP + 131960) <= a < (RATP + 131964) \/ (RATP + 131728) <= a < (RATP + 131784) \/ RGOT_SSP <= a < (RGOT_SSP + 8) \/ (RATP + 131696) <= a < (RATP + 131704) \/ a < 0x10000 \/ RIMG_HI <= a).
Proof. clear - base RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmmap_entry rmunmap_entry RATP RGOT_SSP RIMG_HI st m a. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
(gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold alloc_ceiling in *).
- lia. - lia. - lia. - lia.
- destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. unfold alloc_ceiling in RC. lia.
- lia. - lia.
Qed.

#[using="base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmmap_entry rmunmap_entry"] Lemma rwrapper_munch_keeps st m m' (spv lo : Z) :
rmrep st m -> munch [(spv - 80, spv); ((RATP + -164), (RATP + -164 + 4))] m m' -> wmono segs m m' -> alloc_ceiling <= spv - 80 ->
rmrep st m'.
Proof. clear - base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved ralloc_meta_entry rmmap_entry rmunmap_entry segs RATP st m m' spv lo RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros MR MU WM HS. eapply (rmrep_transport_unowned st m m' _ MR MU WM).
intros lo' hi' a [E|[E|[]]] Ha RF; inversion E; subst; destruct (rrepfoot_where2 st m a MR RF) as [A B]; (gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold alloc_ceiling in *); lia.
Qed.

#[using="base rvm_wait_entry ralloc_meta_entry rmmap_entry rmunmap_entry"] Lemma rpres_except_of_munch_nw C W m m' :
munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmmap_entry rmunmap_entry C W m m'.
intros MU HW a Ha Hc. assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
split; [gw_exact E|]. unfold wview. rewrite E. auto.
Qed.

#[using="base RIMG_HI rvm_wait_entry RNG_RATP LAY_hi_RATP LAY_win_4 ralloc_meta_entry rmmap_entry rmunmap_entry"] Lemma rfp_below_ceiling K st3 stx m lo spv a :
rmrep st3 m -> spv <= a -> alloc_ceiling <= a -> ~ (ralloc_fp K st3 lo spv a \/ fresh_addr stx a).
Proof. clear - base RIMG_HI rvm_wait_entry RNG_RATP LAY_hi_RATP LAY_win_4 ralloc_meta_entry rmmap_entry rmunmap_entry K st3 stx m lo spv a RATP. gw_expose_fam RATP.
intros MR H1 H2 [[X|[X|[X|(q & rq & Hq & _ & Xa)]]]|[X _]]; try lia.
- rewrite unsigned_lit in X by lia. unfold alloc_ceiling in H2. lia.
- pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR q rq Hq) as (_ & _ & _ & RC & _). lia.
Qed.

#[using="base rvm_wait_entry ralloc_meta_entry rmmap_entry rmunmap_entry"] Lemma rbig_stride n rid : 0 <= n < 2^63 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmmap_entry rmunmap_entry n rid. intros Hn. rewrite rbf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.

#[using="RDATA_LO gw_RTEXT_LO LAY_ref_reserved"] Lemma rregion_facts_hi : forall st m rid r,
rmrep st m -> (s_regions st) !! rid = Some r ->
r_base r + round_up_pg (r_len r) <= gw_RDATA2_LO \/ RIMG_HI <= r_base r.
Proof. clear - RDATA_LO gw_RTEXT_LO LAY_ref_reserved RIMG_HI gw_RDATA2_LO. gw_expose_win.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
destruct (rreserved_disjoint _ _ RFr) as (_ & _ & _ & D). gw_exact D.
Qed.

Definition rAMP_BIG (ram_pre : mstate -> Prop) : Prop :=
forall st LB t xa n, RAREACH st LB -> MMAP_THRESHOLD <= n < 2^63 - 4097 ->
mmap_answer_ok (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
ram_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).

#[using="base rvm_wait_entry ralloc_meta_entry rmmap_entry rmunmap_entry"] Lemma ramp_big : rAMP_BIG (am_pre_g ref_reserved rc_secret).
Proof. clear - base rvm_wait_entry ralloc_meta_entry rmmap_entry rmunmap_entry ref_reserved.
intros st LB t xa n AR NR VOK ISE. unfold am_pre_g. apply AMpre_big_call; [exact (QULt.Mq1.areach_ampre_proof _ _ AR)|].
unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
Qed.

Section BIG.
Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : rAMP_BIG ram_pre.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_40 hi_147 lo_41 lo_148 joff_37 joff_149 joff_152 CODE BASE4 BASER D_37 E_37 D_40 E_40 D_41 E_41 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 ANCH_41 ANCH_148 LINK_37 LINK_149 LINK_152 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmunmap_spec rmmap_anon_spec runlock_spec land_m4096 ralloc_meta_entry rmmap_entry rmunmap_entry ram_pre AM AMP"] Lemma rbig_spec : rbig_stmt.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_40 hi_147 lo_41 lo_148 joff_37 joff_149 joff_152 CODE BASE4 BASER D_37 E_37 D_40 E_40 D_41 E_41 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 ANCH_41 ANCH_148 LINK_37 LINK_149 LINK_152 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmunmap_spec rmmap_anon_spec runlock_spec land_m4096 ralloc_meta_entry rmmap_entry rmunmap_entry ram_pre AM AMP segs RATP RGOT_SSP ref_reserved. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
pose proof AMP as AMP_BIG. unfold rAMP_BIG in AMP_BIG.
intros o m0 st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t m1 errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' st1.
intros AR MF MR0 TP CLO LO NR BL MR1 TK1 UA1 MI1 ST1 FR1 ERR1 AUX1 PE1.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold RAM_STACK in LO. unfold MMAP_THRESHOLD in NR.
rewrite (malloc_core_big_eq st1 n) by (unfold MMAP_THRESHOLD; lia).

riprefixT. unfold alloc_ceiling in CLO. subst tp. gw_expose_fam RATP. rewrite unsigned_lit in ERR1 by lia.
gw_expose_fam RATP.
step. step. step. step. step. step. step. step. step.
apply evt_done.
set (sp' := Z_to_bv 64 (bv_unsigned sp + -48)).
assert (SP' : bv_unsigned sp' = bv_unsigned sp + -48) by (subst sp'; apply unsigned_lit; lia).
eapply rimplT_mmap_rw.
{ eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
[ rewrite SP'; gw_exact ST1 | gw_expose_fam RATP; rewrite unsigned_lit by lia; gw_exact ERR1 | gw_exact MI1 | reflexivity | unfold IB, UNIT; f_equal; lia
| reflexivity | reflexivity | reflexivity | reflexivity | unfold IB, UNIT; lia | rewrite SP'; lia | rewrite Q9A7.Mq0.alloc_ceiling_val; lia
| rewrite SP'; gw_expose_fam RATP; rewrite unsigned_lit by lia; lia | gw_expose_fam RATP; rewrite unsigned_lit by lia; lia ]. }
intros ans ms' PO.
assert (FRAME : forall m2, munch [(bv_unsigned sp' - 80, bv_unsigned sp'); (RATP + -164, RATP + -164 + 4)] m1 m2 -> wmono segs m1 m2 ->
rw_cells segs m2 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] /\ rmrep st1 m2 /\ rauxv_ok m2 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m2 /\ unk_agree st1 o m2).
{ intros m2 MU WM. rewrite SP' in MU. split; [|split; [|split; [|split]]].
- eapply rw_cells_transport; [gw_exact FR1| gw_exact MU| gw_exact WM| cbn; lia].
- eapply (rwrapper_munch_keeps st1 m1 m2 (bv_unsigned sp + -48) lo MR1); [| gw_exact WM| unfold alloc_ceiling; lia].
eapply munch_weaken; [|gw_exact MU]. intros y; cbn; lia.
- eapply rauxv_ok_frame; [gw_exact AUX1| gw_exact MU| gw_exact WM|]. gw_expose_fam RATP.
constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
- eapply rpres_except_trans; [gw_exact PE1|]. eapply rpres_except_of_munch; [gw_exact MU| gw_exact WM|].
intros a Ha NC. cbn. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. rewrite unsigned_lit by lia. lia.
- eapply unk_agree_munch; [gw_exact UA1| gw_exact MU| |].
+ intros rid r Hr Hk. pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). pose proof (rregion_facts_hi st1 m1 rid r MR1 Hr) as R3. unfold alloc_ceiling in R2. cbn. lia.
+ intros rid r Hr. pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). unfold alloc_ceiling in R2. lia. }
destruct ans as [e|xa].
-
cbn [rmmap_anon_post] in PO.
destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & He).
cbn [mmap_val]. destruct (mmap_answer_ok_err (live_ranges st1) (n + IB + UNIT) e ltac:(clear - He RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_40 hi_147 lo_41 lo_148 joff_37 joff_149 joff_152 CODE BASE4 BASER D_37 E_37 D_40 E_40 D_41 E_41 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 ANCH_41 ANCH_148 LINK_37 LINK_149 LINK_152 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_ro_addr_false rmunmap_spec rmmap_anon_spec runlock_spec land_m4096 ralloc_meta_entry rmmap_entry rmunmap_entry segs RATP RGOT_SSP ref_reserved; lia)) as [-> ->]. cbn [negb].
apply rimplT_ret.
gw_expose_fam RATP. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
destruct (FRAME m2 MU2 WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).
try g_ret_pc_any.
eapply evt_cut. { eapply rbig_fail1_walk; [gw_exact FR2| gw_exact ST2| lia| lia]. }
intros ms'' [-> ST3]. apply evt_done. cbn [rcoreQ].
exists m2, (Z_to_bv 64 (Q9A7.Mq0.mmap_fix_errno e)). do 14 eexists. split; [reflexivity|].
split; [gw_exact MR2|]. split; [gw_exact TK1|]. split; [gw_exact MI2|]. split; [gw_exact ST3|].
split; [gw_expose_fam RATP; rewrite unsigned_lit by lia; gw_exact ERR2|]. split; [gw_exact AUX2|]. split; [gw_exact PE2|].
split; [apply mrel_same; reflexivity|]. split; [gw_exact BL|]. rewrite He. repeat split; reflexivity.
-
cbn [rmmap_anon_post] in PO.
destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & AOK).
cbn [mmap_val].
destruct (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) xa) eqn:VOK.
2:{ cbn [negb]. apply rimplT_undef. }
cbn [negb].
destruct (mmap_answer_ok_addr (live_ranges st1) (n + IB + UNIT) xa ltac:(unfold IB, UNIT; lia) AOK VOK) as (X0 & XA & XC & XRF & ISE). rewrite ISE.
gw_expose_fam RATP. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
destruct (FRAME m2 ltac:(eapply munch_weaken; [|gw_exact MU2]; intros y; cbn; lia) WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).

unfold new_region.
set (rid := s_next_rid st1). set (st2 := set_next_rid (N.succ rid) (set_regions (<[rid:={| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}]> (s_regions st1)) st1)).
assert (Est2 : st2 = fst (new_region RKGroup xa (n + IB + UNIT) st1)) by first [reflexivity | (cbn; lia)].
pose proof (mf_ptrs _ _ MF) as [PT0 FRESH0].
assert (PT1 : ptrs_in (fun r => r <> rid) st1).
{ eapply ptrs_in_mono; [|gw_exact PT0]. intros r Hr. cbn in Hr. subst rid. unfold st1. cbn. intros ->. lia. }
destruct (FRESH0 rid ltac:(subst rid; unfold st1; cbn; lia)) as [FRr FRs].
set (L := mmap_len (n + IB + UNIT)).
assert (EL : L = round_up_pg (n + IB + UNIT)) by apply mmap_len_round_up.
pose proof (round_up_pg_ge (n + IB + UNIT)) as LG. rewrite <- EL in LG, XC, XRF.
unfold Q9A7.Mq0.mmap_raw in ST2 |- *. cbn [negb] in ST2 |- *. fold L. fold L in ST2.
assert (ELm : mmap_len (n + IB + UNIT) = L) by first [reflexivity | (cbn; lia)]. clearbody L. unfold alloc_ceiling in XC. unfold IB, UNIT in LG.
set (mz := apply_zeros m2 [(wa xa, Z_to_bv 64 L)]).
assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + L <= a) -> mz (wa a) = m2 (wa a)).
{ intros a Ha Ho. unfold mz. apply (zeros_outside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
assert (ZI : forall a, xa <= a < xa + L -> mz (wa a) = Some (b8 0)).
{ intros a Ha. unfold mz. apply (zeros_inside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
assert (MRz : rmrep st2 mz).
{ rewrite Est2. eapply (rmrep_new_region st1 m2 mz xa (n + IB + UNIT) RKGroup MR2 PT1 FRs X0 XA ltac:(unfold IB, UNIT; lia));
rewrite <- ?EL; [unfold alloc_ceiling; gw_exact XC| gw_exact XRF| gw_exact ZO| intros _; gw_exact ZI]. }
fold mz in ST2 |- *.

pose proof MR1 as (WF1 & _). pose proof WF1 as (RS1 & WR1 & _).
assert (XI : xa + L <= 0x10000 \/ RIMG_HI <= xa).
{ assert (RFimg : ranges_free ref_reserved xa L = true).
{ apply ranges_free_intro. intros b k HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS1. gw_exact HI. }
apply (rreserved_disjoint1 _ _ RFimg). lia. }
assert (MIz : mem_inv segs mz).
{ unfold mz. apply (mem_inv_zeros segs m2 xa L); try lia; [gw_exact MI2|]. intros w Hw. apply ref_ro_addr_false. lia. }
assert (FRz : rw_cells segs mz (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
{ eapply rrw_cells_agree; [gw_exact FR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
assert (TKz : ticks_ok st2) by (rewrite Est2; gw_exact TK1).
assert (UAz : unk_agree st2 o mz).
{ eapply (unk_agree_transfer st1 st2 o m2 mz UA2). intros q r Hq Hk.
rewrite Est2 in Hq. destruct (rnr_lookup_inv st1 xa (n + IB + UNIT) RKGroup q r Hq) as [[-> ->]|[NE Hq1]].
- right. intros off h Ho Hc. exfalso. rewrite Est2 in Hc. rewrite (rnr_shadow st1 xa (n + IB + UNIT) RKGroup) in Hc.
unfold get_shadow in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc. rewrite cell_read_shadow0 in Hc. discriminate.
- left. split; [gw_exact Hq1|]. split; [rewrite Est2; apply rnr_shadow|]. split; [intros off X; gw_exact X|].
intros off h Ho Hc NG. destruct (WR1 q r Hq1) as (B0 & _ & _ & BC & _). unfold alloc_ceiling in BC.
pose proof (rnr_old_disjoint st1 xa (n + IB + UNIT) ltac:(rewrite <- EL; gw_exact XRF) q r Hq1) as D.
pose proof (lr_lo_group r Hk). rewrite <- EL in D. apply ZO; lia. }

riprefixT.
try g_ret_pc_any.
pose proof (mf_ctx _ _ MF) as FC. destruct FC as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6).
change (ctx (strip st)) with (ctx st) in FC1, FC2, FC3, FC4.
eapply evt_cut.
{ eapply (rbig_seq_walk sp gp (Z_to_bv 64 RATP)) with (st := st2) (lo := lo);
[gw_exact MRz| rewrite Est2; gw_exact FC4| rewrite unsigned_lit by lia; lia| gw_exact FRz| gw_exact ST2| lia| unfold alloc_ceiling; lia| gw_exact MIz]. }
intros ms1 (wa0 & wa1 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & MR3).
apply evt_done.

assert (MUz : munch [(xa, xa + L)] m2 mz) by (apply munch_of_pointwise; [lia| lia| gw_exact ZO]).
assert (WMz : wmono segs m2 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono segs m2 xa L); try lia; gw_exact Hw).
assert (AUXz : rauxv_ok mz (bv_unsigned sp)).
{ eapply rauxv_ok_frame; [gw_exact AUX2| gw_exact MUz| gw_exact WMz|]. gw_expose_fam RATP. constructor; [cbn; lia| constructor]. }
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
{ eapply rauxv_ok_frame; [gw_exact AUXz| gw_exact MU3| gw_exact WM3|]. gw_expose_fam RATP.
constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor. }
assert (ERRz : rw_cells segs mz (RATP + -164) [C4 errv]).
{ eapply rrw_cells_agree; [gw_exact ERR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
assert (ERR3 : rw_cells segs m3 (RATP + -164) [C4 errv]).
{ eapply rw_cells_transport; [gw_exact ERRz| gw_exact MU3| gw_exact WM3|]. gw_expose_fam RATP. cbn. lia. }
assert (Hconc2 : forall q, fst q <> rid -> conc st2 q = conc st1 q) by (intros q Hq; rewrite Est2; apply rnr_conc; gw_exact Hq).
assert (BL2 : brk_link_ps (step_seq st2) s).
{ eapply (brk_link_ps_ext st1); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| | gw_exact BL].
intros rb ob Hb. transitivity (conc st2 (rb, ob)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
apply Hconc2. cbn. destruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. gw_exact P7. }
assert (TK2' : ticks_ok (step_seq st2)) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); gw_exact TKz).
eapply AM.
{ apply (AMP_BIG st LB t xa n AR); [unfold MMAP_THRESHOLD; lia| gw_exact VOK| gw_exact ISE]. }
{ gw_exact MR3. }
{ gw_exact TK2'. }
{ gw_exact BL2. }
{ rewrite SP'. eapply rauxv_ok_weaken; [gw_exact AUX3| unfold alloc_ceiling; lia]. }
{ rewrite SP'. gw_exact ST3. }
{ unfold alloc_ceiling; lia. }
{ rewrite SP'. unfold RAM_STACK. lia. }
{ gw_expose_fam RATP. rewrite unsigned_lit by lia. gw_exact ERR3. }
{ gw_exact MI3. }
{ reflexivity. }
intros st3 mo s' ms' PO3 BL3.
destruct PO3 as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m4 & errv4 & -> & MI4 & ST4 & ERR4 & AUX4 & PE4 & MR4 & TK4 & PSM & PSF & PSO & REL & E12).
rewrite SP' in ST4, AUX4, PE4. gw_expose_fam RATP. rewrite unsigned_lit in ERR4 by lia.
try g_ret_pc_any.

lazymatch type of FR3 with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells segs m4 (bv_unsigned sp + -48) cs) end.
{ eapply rpres_except_rw_cells; [gw_exact PE4| gw_exact FR3|]. intros a Ha. cbn in Ha. eapply (rfp_below_ceiling _ st3 _ m4); [gw_exact MR4| lia| unfold alloc_ceiling; lia]. }
assert (RR2 : s_regions (step_seq st2) !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
{ rewrite step_seq_eq. destruct (c_seq (ctx st2) =? 255); (rewrite Est2; apply rnr_lookup_new). }
assert (RR3 : s_regions st3 !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
{ destruct (amr_regions _ _ _ REL rid _ RR2) as (r' & Hr' & K' & B' & L' & G'). rewrite Hr'. f_equal. apply G'. reflexivity. }
assert (PT2 : ptrs_in (fun q => q <> rid) (step_seq st2)) by (apply ptrs_in_step_seq; rewrite Est2; apply ptrs_in_new_region; gw_exact PT1).
assert (PT3 : ptrs_in (fun q => q <> rid) st3).
{ apply (amr_ptrs _ _ _ REL); [|gw_exact PT2]. intros q rq Hq Hk ->. rewrite RR3 in Hq. inversion Hq; subst. apply Hk. reflexivity. }
pose proof MR4 as (WF4 & _ & (ML4 & _) & _). pose proof WF4 as (RS4 & WR4 & DJ4 & _).
assert (RS3 : s_reserved st3 = ref_reserved) by gw_exact RS4.

assert (PE14 : forall stF, s_reserved stF = s_reserved st ->
(forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a) ->
rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m4).
{ intros stF RSF HFP.
eapply rpres_except_trans. { eapply rpres_except_of_munch; [gw_exact MU2| gw_exact WM2|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC; left; left; lia. }
eapply rpres_except_trans. { eapply rpres_except_of_munch; [gw_exact MUz| gw_exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X. apply NC.
do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [gw_exact XRF| lia| lia| lia]. }
eapply rpres_except_trans. { eapply rpres_except_of_munch; [gw_exact MU3| gw_exact WM3|]. intros a Ha NC. cbn. gw_expose_fam RATP.
split; [|split; [|exact I]]; intros X; apply NC; left; [right; right; left; gw_expose_fam RATP; lia| right; right; left; gw_expose_fam RATP; lia]. }
eapply rpres_except_mono; [gw_exact PE4|]. intros a [X|X]; [apply (HFP a X)|].
do 4 right. eapply (fresh_addr_anti st (step_seq st2)); [| |gw_exact X].
{ transitivity (s_reserved st2); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| rewrite Est2; reflexivity]. }
intros q rq Hq. exists rq. split; [|repeat split; auto; lia].
transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2, rnr_lookup_old; [gw_exact Hq|]. intros ->. unfold st1 in Hq. cbn in Hq. fold rid in FRr. unfold st1 in FRr. cbn in FRr. rewrite FRr in Hq. discriminate. }
destruct mo as [g|].
+
apply rimplT_ret.
destruct (amr_result _ _ _ REL g eq_refl) as [G0 MSL].
pose proof (rmeta_chunk_facts st3 m4 g MR4 MSL) as (_ & Gpos & GC & GI1 & GI2 & GRG & (ridg & rg & Hrg & Krg & GLg & GHg)).
set (G := conc st3 g) in *.
assert (HG : bv_unsigned (pw st3 (Some g)) = G) by (unfold pw, oconc; fold G; apply wz_unsigned; unfold alloc_ceiling in GC; lia).
assert (GN3 : forall off, (s_groups st3) !! (rid, off) = None).
{ intros off. destruct ((s_groups st3) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
assert (AN3 : forall off, (s_areas st3) !! (rid, off) = None).
{ intros off. destruct ((s_areas st3) !! (rid, off)) as [ar|] eqn:E; [|reflexivity].
destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
assert (SHN3 : (s_shadow st3) !! rid = None).
{ rewrite (amr_shadow _ _ _ REL). transitivity (s_shadow st2 !! rid); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2. gw_exact FRs. }
assert (HC3 : c_mmap_counter (ctx st3) = c_mmap_counter (ctx st)).
{ rewrite (amr_counter _ _ _ REL). transitivity (c_mmap_counter (ctx st2)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2. reflexivity. }
eapply evt_cut.
{ eapply (rbig_succ_walk st3 m4 g rid xa n (c_mmap_counter (ctx st)) lo MR4 TK4 G0 MSL RR3 GN3 AN3 SHN3 HC3 FC1 ltac:(unfold MMAP_THRESHOLD; lia) ltac:(unfold alloc_ceiling; lia) sp gp (Z_to_bv 64 RATP));
[gw_exact HG| gw_exact FR4| gw_exact ST4| lia| gw_exact MI4]. }
intros ms5 (a0' & a1' & m7 & -> & MU7 & WM7 & MI7 & ST7 & FR7 & MR7 & TK7).
apply evt_done. cbn [rcoreQ].
set (stF := big_final st3 g rid n).
rewrite (rbf_counter st3 g rid n (c_mmap_counter (ctx st)) HC3).
change (pw st3 (Some g)) with (pw stF (Some g)).
exists (rid, 0), {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}, m7, errv4. do 17 eexists.
split; [reflexivity|].
assert (MRF : rmrep stF m7) by (apply (rmrep_big_final st3 g rid n _ G0 (GN3 0) HC3); gw_exact MR7).
split; [gw_exact MRF|].
split; [gw_exact TK7|].
assert (STRIDE : get_stride (big_meta rid n) = L - 16) by (rewrite rbig_stride by lia; rewrite <- EL; reflexivity).
assert (NL : forall q rq, (s_regions st3) !! q = Some rq -> q <> rid -> xa + L <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= xa).
{ intros q rq Hq NE. destruct (DJ4 q rq rid _ Hq RR3 NE) as [D|D]; cbn [r_base r_len lr_lo r_kind] in D; rewrite <- ?EL in D; [|lia]. pose proof (lr_lo_ge rq). lia. }
split.
{
assert (UA3 : unk_agree (step_seq st2) o m3).
{ eapply (unk_agree_transfer st2 (step_seq st2) o mz m3 UAz). intros q r Hq Hk. left.
assert (Hq2 : s_regions st2 !! q = Some r) by (revert Hq; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); intros Hq; gw_exact Hq).
split; [gw_exact Hq2|]. split; [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
split; [intros off X; eapply grp_hdr_cov_same; [|gw_exact X]; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
intros off h Ho Hc NG. pose proof MRz as (WFz & _). pose proof WFz as (_ & WRz & _).
destruct (WRz q r Hq2) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). unfold alloc_ceiling in BC.
apply MU3. rewrite wa_unsigned by lia. cbn. gw_expose_fam RATP. lia. }
assert (UA4 : unk_agree st3 o m4).
{ eapply (unk_agree_transfer (step_seq st2) st3 o m3 m4 UA3). intros q r Hq Hk. left.
assert (Hq2 : s_regions (step_seq st2) !! q = Some r).
{ destruct ((s_regions (step_seq st2)) !! q) as [r2|] eqn:E.
- destruct (amr_regions _ _ _ REL q r2 E) as (r' & Hr' & K' & _ & _ & G'). rewrite Hq in Hr'. inversion Hr'; subst r'. f_equal. symmetry. apply G'. rewrite <- K'. gw_exact Hk.
- exfalso. exact (amr_new _ _ _ REL q r Hq E Hk). }
split; [gw_exact Hq2|]. split; [unfold get_shadow; rewrite (amr_shadow _ _ _ REL); reflexivity|].
split; [intros off X; eapply grp_hdr_cov_same; [|gw_exact X]; exact (amr_groups _ _ _ REL)|].
intros off h Ho Hc NG. destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). unfold alloc_ceiling in BC.
refine (proj1 (PE4 (r_base r + off) ltac:(lia) _)).
intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
- lia.
- rewrite unsigned_lit in X by lia. pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). lia.
- gw_expose_fam RATP. pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). lia.
- assert (NE : q2 <> q) by (intros ->; rewrite Hq in Hq'; inversion Hq'; subst; apply Kq2; gw_exact Hk).
pose proof (lr_lo_group r Hk). destruct (DJ4 q2 rq2 q r Hq' Hq NE); lia.
- pose proof (fresh_live_region (step_seq st2) (r_base r + off) q r X Hq2) as Y. pose proof (lr_lo_group r Hk). lia. }
eapply (unk_agree_transfer st3 stF o m4 m7 UA4). intros q r Hq Hk. change (s_regions stF) with (s_regions st3) in Hq.
destruct (N.eq_dec q rid) as [->|NE].
- right. rewrite RR3 in Hq. inversion Hq; subst r. cbn [r_len]. intros off h Ho Hc.
change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid) in Hc.
rewrite cell_read_hh0 in Hc by (gw_exact SHN3 || lia). destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T.
exists (rid, 0), (mkGhdr (Some g) 0). split; [|cbn; lia]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)). apply lookup_insert_eq.
- left. split; [gw_exact Hq|]. split; [apply rbf_shadow_other; gw_exact NE|].
split. { intros off (b & gh & Hb & Hf & Ho). exists b, gh. split; [|auto]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)).
rewrite lookup_insert_ne; [gw_exact Hb|]. intros <-. cbn in Hf. congruence. }
intros off h Ho Hc NG. destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). unfold alloc_ceiling in BC.
pose proof (NL q r Hq NE). pose proof (lr_lo_group r Hk). pose proof (GRG q r Hq Hk).
apply MU7; rewrite wa_unsigned by lia; cbn; gw_expose_fam RATP; lia. }
split; [gw_exact MI7|]. split; [gw_exact ST7|]. split; [gw_exact FR7|].
assert (ERR8 : rw_cells segs m7 (RATP + -164) [C4 errv4]).
{ eapply rw_cells_transport; [gw_exact ERR4| gw_exact MU7| gw_exact WM7|]. cbn. gw_expose_fam RATP. lia. }
split; [gw_expose_fam RATP; rewrite unsigned_lit by lia; gw_exact ERR8|].
assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
{ intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; gw_exact X| right; right; left; gw_exact X|].
right; right; right. exists q, rq. split; [gw_exact Hq| split; [gw_exact Kq| gw_exact Xa]]. }
assert (PE18 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m7).
{ eapply rpres_except_trans. { apply (PE14 stF); [change (s_reserved stF) with (s_reserved st3); rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| gw_exact HFPF]. }
eapply rpres_except_trans.
{ eapply rpres_except_of_munch; [gw_exact MU7| gw_exact WM7|]. intros a Ha NC. cbn. split; [|split; [|split; [|exact I]]]; intros X; apply NC.
- left. right; right; right. exists ridg, rg. split; [gw_exact Hrg|]. split; [gw_exact Krg|]. lia.
- do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [gw_exact XRF| lia| lia| lia].
- left. right; right; left. gw_expose_fam RATP. lia. }
apply rpres_except_refl. }
split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m7 m1 m7); [gw_exact MR0| gw_exact MRF| gw_exact AUX1| gw_exact PE18| unfold alloc_ceiling; lia| lia]. }
assert (MRELF : mrel st stF).
{ split.
- intros q rq Hq.
assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
{ transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2, rnr_lookup_old by gw_exact NE. gw_exact Hq. }
destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
exists r'. split; [|repeat split; auto]. gw_exact Hr'.
- change (s_next_rid stF) with (s_next_rid st3). pose proof (amr_next_rid _ _ _ REL) as NX.
assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
- change (s_reserved stF) with (s_reserved st3). rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
split. { eapply rpres_except_trans; [| gw_exact PE18]. eapply rpres_except_mono; [gw_exact PE1|]. intros a Ha.
eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| gw_exact Ha]. }
rewrite (rbf_meta st3 g rid n G0). rewrite STRIDE. cbn [fst snd r_base r_len].
split. { intros a Ha. do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [gw_exact XRF| lia| lia| lia]. }
split. { unfold u32. Z.div_mod_to_equations. lia. }
assert (ML1 : 32 <= big_ml n < 2^40) by (rewrite big_ml_eq by lia; Z.div_mod_to_equations; lia).
pose proof (round_up_pg_4115 n ltac:(lia)) as RU. rewrite <- EL in RU.
assert (LUB : L <= n + 4115) by (rewrite RU; Z.div_mod_to_equations; lia).
rewrite <- big_ml_eq in RU by lia.
split.
{  constructor; rewrite ?(rbf_meta st3 g rid n G0), ?STRIDE; cbn [m_mem m_last_idx m_avail m_freed m_freeable m_maplen m_sizeclass big_meta fst snd r_kind r_len].
- reflexivity.
- gw_exact RR3.
- reflexivity.
- lia.
- reflexivity.
- lia.
- lia.
- rewrite <- EL. lia.
- lia.
- rewrite RU. Z.div_mod_to_equations. lia.
- lia.
- lia.
- lia.
- intros b' gh Hb' Hf. unfold stF in Hb'. rewrite (rbf_groups st3 g rid n (GN3 0)) in Hb'.
destruct (decide (b' = (rid, 0))) as [->|NEb]; [cbn; lia|].
rewrite lookup_insert_ne in Hb' by congruence. destruct b' as [b1 b2]. cbn in Hf. subst b1. rewrite GN3 in Hb'. discriminate.
- change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
rewrite cell_read_hh0; [| gw_exact SHN3| lia]. replace (0 + 16 + (L - 16) * 0 - 4 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- intros off Ho Hfit. Z.div_mod_to_equations. lia.
- unfold stF. rewrite rbf_slots. replace (0 + 16 + (L - 16) * 0) with 16 by lia. apply lookup_insert_eq.
- gw_exact MSL.
- lia.
- lia.
- lia.
- lia.
- right. repeat split; lia. }
split. { intros _. unfold Q4J3.Mq1.rdv. change (get_shadow stF (fst (rid, 0))) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
cbn [fst snd]. rewrite cell_read_hh0; [| gw_exact SHN3| lia]. replace (0 + (16 + (L - 16) * 0) + -3 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
split; [gw_exact MRELF|].
split. { eapply (brk_link_ps_ext st3); [reflexivity| intros; reflexivity| gw_exact BL3]. }
repeat split; assumption.
+
cbn [pw oconc].
riprefixT.
eapply evt_cut.
{ apply rbig_fail2a_walk. gw_exact ML4. }
intros ms2 ->. apply evt_done.
eapply rimplT_munmap.
{ eapply (rmunmap_spec) with (A := xa) (L := n + IB + UNIT) (lo := lo);
[ rewrite unsigned_lit by lia; gw_exact ST4 | rewrite unsigned_lit by lia; gw_exact ERR4 | gw_exact MI4 | reflexivity | unfold IB, UNIT; f_equal; lia
| lia | rewrite ELm; lia | unfold IB, UNIT; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; rewrite unsigned_lit by lia; lia | rewrite ELm; left; unfold alloc_ceiling in *; lia
| rewrite ELm, unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia ]. }
intros ans2 ms3 PM. unfold rmunmap_post in PM.
destruct PM as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He6).
rewrite (munmap_answer_ok_range ans2 ltac:(destruct ans2; cbn in He6 |- *; [lia| gw_exact Logic.I])). apply rimplT_ret.
rewrite ELm in MU6. rewrite !unsigned_lit in MU6 by lia. rewrite unsigned_lit in ST6 by lia. rewrite unsigned_lit in ERR6 by lia.
try g_ret_pc_any.
lazymatch type of FR4 with rw_cells _ _ _ ?cs => assert (FR6 : rw_cells segs m6 (bv_unsigned sp + -48) cs) end.
{ eapply rrw_cells_agree; [gw_exact FR4|]. intros a Ha. cbn in Ha. apply MU6. rewrite wa_unsigned by lia. cbn. unfold alloc_ceiling in *. lia. }
eapply evt_cut. { eapply rbig_fail2b_walk; [gw_exact FR6| gw_exact ST6| lia| lia]. }
intros ms4 [-> ST7]. apply evt_done. cbn [rcoreQ].
set (stF := drop_region rid st3).
assert (MRF : rmrep stF m6).
{ eapply (rmrep_drop_region st3 m4 m6 rid _ MR4 RR3 PT3). intros a Ha Hout Hin. cbn [r_base r_len lr_lo r_kind] in Hout.
rewrite <- EL in Hout.
assert (A1 : a < alloc_ceiling /\ (a + 1 <= RATP + -164 \/ RATP + -164 + 4 <= a) /\ (a < xa \/ xa + L <= a)).
{ destruct Hin as [X|[X|[X|[X|(q & rq & Hq & Xa)]]]];
[(gw_expose_fam RATP; unfold alloc_ceiling in *); lia| (gw_expose_fam RATP; unfold alloc_ceiling in *); lia| (gw_expose_fam RGOT_SSP; unfold alloc_ceiling in *); lia| (gw_expose_fam RATP; unfold alloc_ceiling in *); lia|].
destruct (WR4 q rq Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). pose proof (lr_lo_ge rq).
split; [lia|]. split; [lia|].
destruct (N.eq_dec q rid) as [->|NE]; [rewrite RR3 in Hq; inversion Hq; subst; cbn [lr_lo r_kind r_base r_len] in Xa; lia|].
destruct (DJ4 q rq rid _ Hq RR3 NE) as [D2|D2]; cbn [r_base r_len lr_lo r_kind] in D2; rewrite <- ?EL in D2; lia. }
unfold alloc_ceiling in A1.
apply MU6; rewrite wa_unsigned by lia; cbn; lia. }
assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
{ intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; gw_exact X| right; right; left; gw_exact X|].
right; right; right. exists q, rq. split; [|split; [gw_exact Kq|gw_exact Xa]].
unfold stF. rewrite rdr_lookup_old; [gw_exact Hq|]. intros ->. rewrite RR3 in Hq. inversion Hq; subst. apply Kq. reflexivity. }
assert (PE16 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m6).
{ eapply rpres_except_trans. { apply (PE14 stF); [unfold stF, drop_region; cbn [s_reserved set_shadow set_regions]; rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| gw_exact HFPF]. }
eapply rpres_except_of_munch_nw; [gw_exact MU6|]. intros a Ha NC. cbn.
split; [|split; [|split; [|exact I]]]; intros X; apply NC; [left; left; lia| left; right; left; rewrite unsigned_lit by lia; lia|].
do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [gw_exact XRF| lia| lia| lia]. }
exists m6, (Q9A7.Mq0.rg_errno ans2 errv4). do 14 eexists. split; [reflexivity|].
split; [gw_exact MRF|]. split; [apply rticks_ok_drop_region; gw_exact TK4|]. split; [gw_exact MI6|]. split; [gw_exact ST7|].
split; [gw_expose_fam RATP; rewrite unsigned_lit by lia; gw_exact ERR6|].
split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m6 m1 m6); [gw_exact MR0| gw_exact MRF| gw_exact AUX1| gw_exact PE16| unfold alloc_ceiling; lia| lia]. }
assert (MRELF : mrel st stF).
{ split.
- intros q rq Hq.
assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
{ transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2, rnr_lookup_old by gw_exact NE. gw_exact Hq. }
destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
exists r'. split; [|repeat split; auto]. unfold stF. rewrite rdr_lookup_old by gw_exact NE. gw_exact Hr'.
- unfold stF, drop_region. cbn [s_next_rid set_shadow set_regions]. pose proof (amr_next_rid _ _ _ REL) as NX.
change (s_next_rid (step_seq st2)) with (s_next_rid (step_seq st2)) in NX.
assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
- unfold stF, drop_region. cbn [s_reserved set_shadow set_regions]. rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
split. { eapply rpres_except_trans; [| gw_exact PE16]. eapply rpres_except_mono; [gw_exact PE1|]. intros a Ha.
eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| gw_exact Ha]. }
split; [gw_exact MRELF|].
split.
{ eapply (brk_link_ps_ext st3); [reflexivity| | gw_exact BL3]. intros rb ob Hb. unfold stF. apply rdr_conc. cbn.
destruct PT3 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. gw_exact P7. }
repeat split; try assumption.
destruct ans2 as [e2|b2]; cbn [Q9A7.Mq0.rg_errno]; cbn in He6; [rewrite He6; reflexivity| exact (E12 eq_refl)].
Qed.
End BIG.

End RC__1.

End G.
End Mqa.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QULt.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwFold.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G Require Import GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QDXD.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1)))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QDXD.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2)))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QDXD.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3)))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QDXD.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4)))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QDXD.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5)))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QDXD.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6)))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QDXD.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7)))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QDXD.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8)))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QDXD.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9)))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QDXD.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10)))).
Definition RHEAP : ltac:(gw_rebind_ty (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QDXD.Mq3.RHEAP segs RATP RGOT_SSP ref_reserved RC__) (@RHEAP) gw_tbl_11).
Definition rblock_range : ltac:(gw_rebind_ty (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rblock_range RIMG_HI RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QDXD.Mq3.rblock_range RIMG_HI RC__) (@rblock_range) gw_tbl_12).
Definition rclient_write_ok : ltac:(gw_rebind_ty (@QDXD.Mq3.rclient_write_ok RATP RGOT_SSP RIMG_HI RDATA_LO RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QDXD.Mq3.rclient_write_ok RATP RGOT_SSP RIMG_HI RDATA_LO RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QDXD.Mq3.rclient_write_ok RATP RGOT_SSP RIMG_HI RDATA_LO RC__) (@rclient_write_ok) gw_tbl_13).

Definition rreserved_disjoint1 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint1) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint1)).
Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_transport_unowned : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_transport_unowned) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_transport_unowned)).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ | clear - hs segs RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved"] Lemma rregion_addr_facts : forall st m rid r,
rmrep st m -> (s_regions st) !! rid = Some r ->
4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ RIMG_HI <= r_base r).
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved RIMG_HI. gw_expose_win.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
split; [|split; [gw_exact RBAL| split; [gw_exact RBC| intros Hn; exact (rreserved_disjoint1 _ _ RFr Hn)]]].
clear RFr. Z.div_mod_to_equations. lia.
Qed.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved"] Lemma rblock_inside st LB m blk :
MFACTS_g (resv:=ref_reserved) st LB -> rmrep st m -> In blk LB ->
exists r g idx, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
/\ (s_slots st) !! (blk_slot blk) = Some (g, idx)
/\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)
/\ 0 <= blk_size blk
/\ 4096 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ RIMG_HI <= r_base r).
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved RIMG_HI ref_reserved st LB m blk. gw_expose_win.
intros MF MR IN.
pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk IN) as [BS BR BZ].
destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
destruct BR as (r & Hr & Hk).
pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _).
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
pose proof (rregion_addr_facts st m _ r MR Hr) as (R4 & _ & RC & RI1).
exists r, g, idx. split; [gw_exact Hr|]. split; [gw_exact Hk|]. split; [gw_exact SL|].
pose proof (round_up_pg_ge (r_len r)) as RU.
rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
{ rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Esnd in EA. unfold alloc_ceiling in *.
assert (RP : 0 < round_up_pg (r_len r)) by lia. specialize (RI1 RP). lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved"] Lemma RHEAP_blocks_nodup_proof : forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved.
intros s LB m (st & LB0 & HP & _ & _ & [_ AR]). pose proof (mf_nodup _ _ (QTyG.Mq2.areach_facts_proof _ _ AR)) as ND.
eapply Permutation_NoDup; [apply Permutation_map; gw_exact HP|].
clear - ND RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved. induction LB0 as [|b LB0 IH]; cbn in *; [constructor|].
inversion ND; subst. constructor; [|apply IH; assumption].
intros HI. apply H1. apply in_map_iff in HI. destruct HI as (b' & E & HI'). apply in_map_iff. exists b'. split; [|gw_exact HI'].
unfold blk_slot, blk_id in *. rewrite E. reflexivity.
Qed.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved"] Lemma RHEAP_block_range_proof : forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved.
intros s LB m b (st & LB0 & HP & _ & MR & [_ AR]) HIN. pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; gw_exact HP| gw_exact HIN]).
destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) b IN0) as [BS BR _].
destruct BS as (g' & idx' & SL' & _ & _ & _ & (off & OFF0 & EA & FIT)). rewrite SL in SL'. inversion SL'; subst g' idx'. clear SL'.
pose proof (mf_slots _ _ MF (blk_slot b) g idx SL) as (bb & Hm & Efst & Esnd & IDX).
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd, IDX.
pose proof (mf_gmeta _ _ MF g bb Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & B16 & SPAN) & S16 & SMOD & _).
change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RAL & _ & RC' & RF).
unfold sstart_of in SPAN. rewrite Hm in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT in SPAN, S16.
assert (32 <= round_up_pg (r_len r)) by nia.
unfold rblock_range. unfold alloc_ceiling in *. split; [lia|]. split; [|lia].
rewrite EA. rewrite (conc_region' st (blk_slot b) r Hr). rewrite Esnd. unfold sstart_of. rewrite Hm. cbn [default from_option id snd].
replace (r_base r + (snd bb + UNIT + get_stride (get_meta_rec st g) * idx) + UNIT * off)
with (r_base r + snd bb + 16 + get_stride (get_meta_rec st g) * idx + 16 * off) by (unfold UNIT; lia).
apply (mod16_slot (r_base r) (snd bb) (get_stride (get_meta_rec st g)) idx off); try assumption; lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved"] Lemma RHEAP_blocks_disjoint_proof : forall s LB m b1 b2,
RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved.
intros s LB m b1 b2 (st & LB0 & HP & _ & MR & [_ AR]) I1 I2 NE. pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (IN1 : In b1 LB0) by (eapply Permutation_in; [apply Permutation_sym; gw_exact HP| gw_exact I1]).
assert (IN2 : In b2 LB0) by (eapply Permutation_in; [apply Permutation_sym; gw_exact HP| gw_exact I2]).
destruct (decide (blk_slot b1 = blk_slot b2)) as [ES|NS].
- exfalso. apply NE. pose proof (mf_nodup _ _ MF) as ND.
clear - ND IN1 IN2 ES RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved. induction LB0 as [|b LB0 IH]; [destruct IN1|]. cbn in ND. inversion ND; subst.
destruct IN1 as [->|IN1], IN2 as [->|IN2]; [reflexivity| | | apply IH; assumption].
+ exfalso. apply H1. rewrite ES. apply in_map_iff. exists b2; auto.
+ exfalso. apply H1. rewrite <- ES. apply in_map_iff. exists b1; auto.
- destruct (N.eq_dec (fst (blk_slot b1)) (fst (blk_slot b2))) as [EF|NF].
+ exact (mf_blocks_disjoint _ _ MF b1 b2 IN1 IN2 EF NS).
+ destruct (rblock_inside st LB0 m b1 MF MR IN1) as (r1 & g1 & i1 & Hr1 & Hk1 & _ & LO1 & HI1 & _).
destruct (rblock_inside st LB0 m b2 MF MR IN2) as (r2 & g2 & i2 & Hr2 & Hk2 & _ & LO2 & HI2 & _).
pose proof MR as (WF & _). pose proof WF as (_ & _ & DJ & _).
pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved"] Lemma rrepfoot_where st m a : rmrep st m -> rrepfoot st a ->
a < alloc_ceiling /\ ((RATP + 131968) <= a < (RATP + 132896) \/ (RATP + 131960) <= a < (RATP + 131964) \/ (RATP + 131728) <= a < (RATP + 131784)
\/ RGOT_SSP <= a < (RGOT_SSP + 8) \/ (RATP + 131696) <= a < (RATP + 131704) \/ a < 0x10000 \/ RIMG_HI <= a).
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved RATP RGOT_SSP RIMG_HI st m a. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
(gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold alloc_ceiling in *).
- lia. - lia. - lia. - lia.
- destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. unfold alloc_ceiling in RC. lia.
- lia. - lia.
Qed.

#[using="gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma RHEAP_frame_proof : forall s LB m m' W,
RHEAP s LB m -> munch W m m' -> wmono segs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.
Proof. clear - gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros s LB m m' W (st & LB0 & HP & Hst & MR & HI) MU WM FW. exists st, LB0. split; [gw_exact HP|]. split; [gw_exact Hst|].
split; [|gw_exact HI].
destruct HI as [_ AR]. pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
eapply (rmrep_transport_unowned st m m' W MR MU WM).
intros lo hi a Hin Ha RF.
pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as CW. cbn [fst snd] in CW.
destruct (rrepfoot_where st m a MR RF) as [AC AW].
destruct CW as [CW|[CW|(b & Hb & B1 & B2)]]; cbn [fst snd] in *.
- unfold alloc_ceiling in *. lia.
- (gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold alloc_ceiling in *). lia.
-
assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; gw_exact HP| gw_exact Hb]).
destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
+ gw_expose_fam RATP. lia.
+ gw_expose_fam RATP. lia.
+ gw_expose_fam RATP. lia.
+ gw_expose_fam RATP. lia.
+ destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
destruct (DJ _ _ _ _ Hra Hr NEr); lia.
+ destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
* rewrite E, Hr in Hrb. inversion Hrb; subst rb.
pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; gw_exact Hr)) as HC. rewrite Cb in Rb. lia.
* pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
+ destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
* rewrite Hr in Hq. inversion Hq; subst rq.
destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
* pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
+ gw_expose_fam RGOT_SSP. lia.
+ gw_expose_fam RATP. lia.
Qed.

#[using="Type"] Lemma u64arr_of_rw_cells' : forall m A n bs k, rw_cells segs m A [CB n bs] -> bs = u64s (repeat (wz 0) k) -> (n = 8 * k)%nat ->
u64arr segs m A (repeat (wz 0) k).
Proof. clear - segs.
intros m A n bs k [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
split; [gw_exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. gw_exact HW.
Qed.
End RC__1.

Section RC__2.

End RC__2.

End G.
